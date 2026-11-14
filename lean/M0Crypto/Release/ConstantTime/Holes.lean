import M0Crypto.Release.ConstantTime.ReadBounds

/-!
# Stack liveness check

A *hole* is a byte of the entry stack window that may not have been written since SP last moved
to or below it. The hole map has one entry per code offset and call context of the certificate:
the abstract SP offset there, a hole set (a bit mask with bit `q + below` for window offset `q`)
and, optionally, the return labels LR holds there. `certHoleFailure` checks, at every position of
a constant-time certificate:

* the position's SP offset and LR labels are those of its entry;
* every stack access lies in the window; a read lies at or above SP and meets no hole;
* every stack write lies at or above SP, or is a `push`;
* a load site whose offset may read the stack range `ls off` meets no hole there;
* for every entry at every successor offset, either the step cannot reach it (its LR labels
  exclude LR after the step), or the holes after the step are recorded there: the holes before
  the step, plus the bytes a lower SP newly covers, minus the bytes written exactly.

Nothing here is trusted: `HolesRun.lean` proves what a successful check implies for a run.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- A stack access of one instruction: offsets `[lo, hi)` from the entry SP. An `exact` write
writes every byte of the range. -/
structure SAcc where
  read : Bool
  lo : Int
  hi : Int
  exact : Bool
  deriving Repr

/-- The accesses of `i` through SP-tracked addresses, from the abstract state before it. -/
def stackAccs (st : AbsState) : Instr → List SAcc
  | .memImm op _ n imm =>
    match (st.get n.val).addK (imm.toNat * op.width) with
    | .sp x y => [⟨op.isLoad, x, y + (op.width : Int), x == y⟩]
    | _ => []
  | .memReg op _ n m =>
    match (st.get n.val).add (st.get m.val) with
    | .sp x y => [⟨op.isLoad, x, y + (op.width : Int), x == y⟩]
    | _ => []
  | .strSp _ k => [⟨false, st.spOff + (k.toNat * 4 : Nat), st.spOff + (k.toNat * 4 : Nat) + 4, true⟩]
  | .ldrSp _ k => [⟨true, st.spOff + (k.toNat * 4 : Nat), st.spOff + (k.toNat * 4 : Nat) + 4, true⟩]
  | .push l lr => [⟨false, st.spOff - (4 * (bitCount l + lr.toNat) : Nat), st.spOff, true⟩]
  | .pop l pc => [⟨true, st.spOff, st.spOff + (4 * (bitCount l + pc.toNat) : Nat), true⟩]
  | .stm n l =>
    match st.get n.val with
    | .sp x y => [⟨false, x, y + (4 * bitCount l : Nat), x == y⟩]
    | _ => []
  | .ldm n l =>
    match st.get n.val with
    | .sp x y => [⟨true, x, y + (4 * bitCount l : Nat), x == y⟩]
    | _ => []
  | _ => []

/-- The mask of window offsets `[a, b)`, with bit `q + below` for offset `q`. -/
def rangeMask (below : Nat) (a b : Int) : Nat :=
  (2 ^ (b - a).toNat - 1) <<< (a + below).toNat

/-- `h` without the bits of `m`. -/
def maskOff (h m : Nat) : Nat := h ^^^ (h &&& m)

/-- A hole-map entry: call context, SP offset, hole mask, and the return labels LR holds at
every position of the entry (`none`: no constraint). -/
structure HEnt where
  ctx : Option Nat
  o : Int
  h : Nat
  lr : Option (List Nat)
  deriving Repr, Inhabited

/-- Hole maps: a binary tree on the bits of the code offset, each leaf the entries of one offset. -/
inductive HTree where
  | none
  | leaf (es : List HEnt)
  | node (l r : HTree)
  deriving Repr, Inhabited

/-- The entries of offset `k` in a tree of depth `d`. -/
def HTree.get : HTree → Nat → Nat → List HEnt
  | .leaf es, 0, 0 => es
  | .node l r, d + 1, k => if k % 2 = 0 then l.get d (k / 2) else r.get d (k / 2)
  | _, _, _ => []

/-- A hole map: its tree and depth. -/
structure HoleMap where
  depth : Nat
  tree : HTree
  deriving Repr, Inhabited

def HoleMap.get (m : HoleMap) (off : Nat) : List HEnt := m.tree.get m.depth off

/-- The entry of offset `off` in context `ctx`. -/
def HoleMap.find (m : HoleMap) (off : Nat) (ctx : Option Nat) : Option HEnt :=
  (m.get off).find? (·.ctx == ctx)

/-- LR holds one of the labels `lr`, which are even code offsets. -/
def lrOk (lr : Option (List Nat)) (st : AbsState) : Bool :=
  match lr with
  | Option.none => true
  | some ls => ls.all (fun r => r % 2 == 0 && decide (r < 2 ^ 32)) &&
    match st.get 14 with
    | .ret rs => rs.all ls.contains
    | _ => false

def isBl : Instr → Bool
  | .bl _ => true
  | _ => false

/-- A step by `i` from offset `off` with entry `e` cannot reach entry `e'`: LR after the step is
outside the labels of `e'`. -/
def refuted (off : Nat) (e : HEnt) (i : Instr) (e' : HEnt) : Bool :=
  match e'.lr with
  | Option.none => false
  | some ls =>
    if isBl i then decide (off + 4 < 2 ^ 32) && !ls.contains (off + 4)
    else !(i.dsts.contains 14) &&
      match e.lr with
      | some ls0 => ls0.all (fun r => !ls.contains r)
      | Option.none => false

/-- The analyzed target offsets of a transfer. -/
def ptOffs (out : Out) : List Nat :=
  out.succs.filterMap fun t => match t.1 with
    | .pt o _ => some o
    | .exit => Option.none

/-- The code offsets a step from `off` can continue at: the analyzed targets of a control
instruction, the next instruction otherwise. -/
def succOffs (off : Nat) (i : Instr) (out : Out) : List Nat :=
  match i with
  | .bcond .. | .b .. | .bl .. | .pop _ true => ptOffs out
  | _ => [off + i.size]

/-- Instructions whose next PC `succOffs` describes: all but a register move to PC. -/
def pcSafe : Instr → Bool
  | .movHi d _ => d.val != 15
  | _ => true

def isPush : Instr → Bool
  | .push .. => true
  | _ => false

/-- The holes after a step from SP offset `o` to `o'` with stack accesses `accs`. -/
def holesAfter (below : Nat) (o o' : Int) (accs : List SAcc) (h : Nat) : Nat :=
  accs.foldl (fun acc a => if !a.read && a.exact then maskOff acc (rangeMask below a.lo a.hi) else acc)
    (if o' < o then h ||| rangeMask below o' o else h)

/-- One stack access is within the window, at or above SP, and a read meets no hole. -/
def saccOk (below above : Nat) (i : Instr) (o : Int) (h : Nat) (a : SAcc) : Bool :=
  decide (-(below : Int) ≤ a.lo) && decide (a.hi ≤ above) &&
    (if a.read then decide (o ≤ a.lo) && h &&& rangeMask below a.lo a.hi == 0
     else decide (o ≤ a.lo) || isPush i)

/-- The check at one position. A load site at `off` may read the stack range `ls off`. -/
def posHoleOk (env : Env) (ls : Nat → Option (Int × Int)) (m : HoleMap) (off : Nat)
    (ctx : Option Nat) (st : AbsState) (i : Instr) : Bool :=
  match m.find off ctx with
  | Option.none => false
  | some e =>
    e.o == st.spOff && lrOk e.lr st && pcSafe i &&
    (stackAccs st i).all (saccOk env.win.below env.win.above i e.o e.h) &&
    (!loadSite st i || match ls off with
      | Option.none => true
      | some (a, b) => decide (e.o ≤ a) && decide (-(env.win.below : Int) ≤ a) &&
          decide (b ≤ (env.win.above : Int)) && e.h &&& rangeMask env.win.below a b == 0) &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out => (succOffs off i out).all fun tgt =>
        decide (tgt < env.size) && (m.get tgt).all fun e' =>
          refuted off e i e' || (decide (-(env.win.below : Int) ≤ e'.o) &&
            (holesAfter env.win.below e.o e'.o (stackAccs st i) e.h &&& e'.h ==
              holesAfter env.win.below e.o e'.o (stackAccs st i) e.h))

/-- The first failing position of a block, walked as `BlockPoint` walks it. -/
def walkHoleFailure (env : Env) (ls : Nat → Option (Int × Int)) (m : HoleMap)
    (ctx : Option Nat) : Nat → AbsState → List Instr → Option Nat
  | _, _, [] => Option.none
  | off, st, i :: is =>
    if !posHoleOk env ls m off ctx st i then some off
    else
      match xfer env off ctx i st with
      | .error _ => some off
      | .ok out =>
        match out.succs with
        | [(_, next)] => walkHoleFailure env ls m ctx (off + i.size) next is
        | _ => walkHoleFailure env ls m ctx (off + i.size) st is

def certHoleFailure (env : Env) (ls : Nat → Option (Int × Int)) (m : HoleMap) (cert : Cert) :
    Option (Nat × Nat) :=
  cert.findSome? fun b =>
    (walkHoleFailure env ls m b.ctx b.off b.st b.code).map fun off => (b.off, off)

/-! ## Generator (evaluated at build time; not used by the check) -/

/-- Positions of a certificate: offset, abstract state, instruction and transfer output. -/
def holePositions (env : Env) (c : Cert) : List (Nat × Option Nat × AbsState × Instr × Out) :=
  c.flatMap fun b =>
    let rec go : Nat → Nat → AbsState → List Instr → List (Nat × Option Nat × AbsState × Instr × Out)
      | 0, _, _, _ => []
      | _, _, _, [] => []
      | f + 1, off, st, i :: is =>
        match xfer env off b.ctx i st with
        | .error _ => []
        | .ok o =>
          (off, b.ctx, st, i, o) :: match o.succs with
            | [(_, nx)] => go f (off + i.size) nx is
            | _ => go f (off + i.size) st is
    go (b.code.length + 1) b.off b.st b.code

def HTree.build (d : Nat) (f : Nat → List HEnt) (k step : Nat) : HTree :=
  match d with
  | 0 => match f k with
    | [] => .none
    | es => .leaf es
  | d + 1 =>
    let l := HTree.build d f k (2 * step)
    let r := HTree.build d f (k + step) (2 * step)
    match l, r with
    | .none, .none => .none
    | l, r => .node l r

/-- The least hole map closed under the certificate's unrefuted steps, from no holes. -/
def genHoles (env : Env) (entry : Nat) (c : Cert) (rounds : Nat) : HoleMap := Id.run do
  let pts := holePositions env c
  let below := env.win.below
  let mut keys : Std.HashMap (Nat × Option Nat) HEnt := {}
  for (off, ctx, st, _, _) in pts do
    let lr1 : Option (List Nat) := match st.get 14 with
      | .ret rs => some rs
      | _ => Option.none
    match keys.get? (off, ctx) with
    | Option.none => keys := keys.insert (off, ctx) ⟨ctx, st.spOff, 0, lr1⟩
    | some e =>
      let lr := match e.lr, lr1 with
        | some a, some b => some (a ++ b.filter (!a.contains ·))
        | _, _ => Option.none
      keys := keys.insert (off, ctx) { e with lr }
  let mut byOff : Std.HashMap Nat (List (Nat × Option Nat)) := {}
  for ((off, ctx), _) in keys.toList do
    byOff := byOff.insert off (byOff.getD off [] ++ [(off, ctx)])
  for _ in [0:rounds] do
    let mut changed := false
    for (off, ctx, st, i, out) in pts do
      let e := keys.getD (off, ctx) default
      for tgt in succOffs off i out do
        for k in byOff.getD tgt [] do
          let e' := keys.getD k default
          if !refuted off e i e' then
            let h2 := holesAfter below e.o e'.o (stackAccs st i) e.h
            if e'.h &&& h2 != h2 then
              keys := keys.insert k { e' with h := e'.h ||| h2 }
              changed := true
    if !changed then break
  let mut es : Std.HashMap Nat (List HEnt) := {}
  for ((off, _), e) in keys.toList do
    es := es.insert off (es.getD off [] ++ [e])
  let maxOff := pts.foldl (fun a p => max a p.1) entry
  let depth := Nat.log2 maxOff + 1
  return ⟨depth, HTree.build depth (fun k => es.getD k []) 0 1⟩

end M0Crypto.Release.ConstantTime
