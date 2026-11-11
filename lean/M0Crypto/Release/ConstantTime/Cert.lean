import M0Crypto.Release.ConstantTime.Transfer
import M0Crypto.Thumb.SeqScan
import M0Crypto.Artifacts.Release

/-!
# Constant-time analysis certificates

A certificate lists basic blocks. Each block has a start offset, a call context, the
abstract state at its start, and its instructions. `certFailure` checks it and returns
the first problem, or `none`:

* the entry block exists, and the entry state is subsumed by its state;
* each block's instructions are those of the artifact at its offset (`seqAt`, evaluated
  as `seqScan`);
* inside a block every instruction but the last falls through, and every obligation holds;
* every successor of a block's last instruction is a block whose state subsumes the
  transferred state, or the top-level exit.

`certOk` is `certFailure … = none` by definition, so the failure companion of rule 3 is
built in (`certOk_iff`).

The kernel only checks certificates. `gen` computes one with a fixpoint over all points
(with widening) and cuts it into blocks. It runs at build time through `ct_cert%`
(`ConstantTime/Entries.lean`). Nothing is checked in, so code changes need no sync step.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Thumb

structure Blk where
  off : Nat
  ctx : Option Nat
  st : AbsState
  code : List Instr
  deriving Repr, Inhabited

abbrev Cert := List Blk

def findBlk (c : Cert) (off : Nat) (ctx : Option Nat) : Option Blk :=
  c.find? fun b => b.off == off && b.ctx == ctx

/-- A site: an access the analysis does not bound, or the declassified branch. -/
structure Site where
  off : Nat
  ctx : Option Nat
  kind : SiteK
  deriving DecidableEq, Repr

/-- Run a block: the successors of its last instruction and the sites it contains. -/
def runBlock (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr →
    Except String (List (Tgt × AbsState) × List Site)
  | _, _, [] => .error "empty block"
  | off, st, [i] =>
    match xfer env off ctx i st with
    | .error e => .error s!"pc {off}: {e}"
    | .ok o => .ok (o.succs, o.sites.map fun k => ⟨off, ctx, k⟩)
  | off, st, i :: is =>
    match xfer env off ctx i st with
    | .error e => .error s!"pc {off}: {e}"
    | .ok ⟨[(.pt off' ctx', st')], ks⟩ =>
      if off' == off + i.size && ctx' == ctx then
        match runBlock env ctx off' st' is with
        | .error e => .error e
        | .ok (ss, sites) => .ok (ss, ks.map (fun k => ⟨off, ctx, k⟩) ++ sites)
      else .error s!"pc {off}: control transfer inside a block"
    | .ok _ => .error s!"pc {off}: control transfer inside a block"

def succFailure (c : Cert) : List (Tgt × AbsState) → Option String
  | [] => none
  | (.exit, _) :: rest => succFailure c rest
  | (.pt off ctx, st) :: rest =>
    match findBlk c off ctx with
    | none => some s!"successor ({off}, {ctx}) is not a block"
    | some b => if st.le b.st then succFailure c rest
                else some s!"successor ({off}, {ctx}) not subsumed by its block state"

def blkFailure (env : Env) (bytes : List (BitVec 8)) (c : Cert) (b : Blk) : Option String :=
  -- `seqScan` on the cut artifact is `seqAt` (`seqAt_eq_scan`) but linear in the offset
  if !seqScan (bytes.drop b.off) b.code then some s!"block {b.off}: code differs from the artifact"
  else match runBlock env b.ctx b.off b.st b.code with
    | .error e => some s!"block ({b.off}, {b.ctx}): {e}"
    | .ok (ss, _) => (succFailure c ss).map fun e => s!"block ({b.off}, {b.ctx}): {e}"

def certFailure (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState) (c : Cert) :
    Option String :=
  match findBlk c entry none with
  | none => some "no entry block"
  | some b =>
    if !init.le b.st then some "entry state not subsumed"
    else c.findSome? (blkFailure env bytes c)

def certOk (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState) (c : Cert) : Bool :=
  (certFailure env bytes entry init c).isNone

theorem certOk_iff (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState) (c : Cert) :
    certOk env bytes entry init c = true ↔ certFailure env bytes entry init c = none := by
  unfold certOk; cases certFailure env bytes entry init c <;> simp

/-! ## Generator (build time only) -/

abbrev Pt := Nat × Option Nat

/-- Widening after this many growing joins at one point. -/
def widenAfter : Nat := 80

def widenAV (w : StackWindow) (old new : AbsVal) : AbsVal :=
  if old == new then new else
  match new with
  | .num _ _ => .lo
  | .sp _ _ => .sp (-(w.below : Int)) w.above
  | v => v

/-- Standard widening: only components that changed since `old` jump to their limit. -/
def widen (w : StackWindow) (old s : AbsState) : AbsState :=
  AbsState.tighten w { s with
    regs := (List.range numRegs).map fun r => widenAV w (old.get r) (s.get r),
    stk := s.stk.map fun p => (p.1, widenAV w (stkGet old.stk p.1) p.2) }

def lookupSt (m : List (Pt × AbsState × Nat)) (p : Pt) : Option (AbsState × Nat) := m.lookup p

def upd (m : List (Pt × AbsState × Nat)) (p : Pt) (v : AbsState × Nat) : List (Pt × AbsState × Nat) :=
  (p, v) :: m.filter fun q => q.1 != p

/-- Pointwise fixpoint; returns the state at every reachable point, or the first error. -/
def fix (env : Env) (bytes : List (BitVec 8)) :
    Nat → List (Pt × AbsState) → List (Pt × AbsState × Nat) → Except String (List (Pt × AbsState × Nat))
  | 0, _, _ => .error "analysis fuel exhausted"
  | _ + 1, [], m => .ok m
  | fuel + 1, (p, s) :: wl, m =>
    let next : Option (AbsState × Nat) := match lookupSt m p with
      | none => some (s, 0)
      | some (cur, k) =>
        if s.le cur then none
        else match AbsState.join env.win cur s with
          | none => some (cur, k)  -- reported by the checker
          | some j => some (if k ≥ widenAfter then widen env.win cur j else j, k + 1)
    match next with
    | none => fix env bytes fuel wl m
    | some (st, k) =>
      match instrAt bytes p.1 with
      | none => .error s!"no instruction at {p.1}"
      | some i =>
        match xfer env p.1 p.2 i st with
        | .error e => .error s!"pc {p.1} ctx {p.2}: {e}"
        | .ok o =>
          let succs := o.succs.filterMap fun (t, s') => match t with
            | .pt off ctx => some ((off, ctx), s')
            | .exit => none
          fix env bytes fuel (wl ++ succs) (upd m p (st, k))

/-- Cut the fixpoint into blocks. -/
def blocks (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (m : List (Pt × AbsState × Nat)) :
    Except String Cert := do
  -- successors of every point under its fixpoint state
  let succ : List (Pt × List Pt) ← m.mapM fun (p, st, _) => do
    let some i := instrAt bytes p.1 | .error s!"no instruction at {p.1}"
    match xfer env p.1 p.2 i st with
    | .error e => .error e
    | .ok o => pure (p, o.succs.filterMap fun (t, _) => match t with
        | .pt off ctx => some (off, ctx)
        | .exit => none)
  let falls : Pt → Bool := fun p => match succ.lookup p, instrAt bytes p.1 with
    | some [q], some i => q == (p.1 + i.size, p.2)
    | _, _ => false
  let preds : Pt → List Pt := fun q => (succ.filter fun (_, qs) => qs.contains q).map (·.1)
  let isHead : Pt → Bool := fun q =>
    q == (entry, none) || match preds q with
      | [p] => !falls p
      | _ => true
  let rec walk : Nat → Pt → List Instr
    | 0, _ => []
    | fuel + 1, p => match instrAt bytes p.1 with
      | none => []
      | some i =>
        let q := (p.1 + i.size, p.2)
        if falls p && !isHead q && (m.lookup q).isSome then i :: walk fuel q else [i]
  pure <| (m.filter fun (p, _, _) => isHead p).map fun (p, st, _) =>
    ⟨p.1, p.2, st, walk bytes.length p⟩

def gen (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState) (fuel : Nat) :
    Except String Cert := do
  let m ← fix env bytes fuel [((entry, none), init)] []
  blocks env bytes entry m

/-- All certificate block heads are halfword aligned. -/
def certAligned (cert : Cert) : Bool := cert.all fun b => decide (b.off % 2 = 0)

theorem certAligned_head {cert : Cert} {b : Blk}
    (hc : certAligned cert = true) (hm : b ∈ cert) : b.off % 2 = 0 := by
  exact of_decide_eq_true (List.all_eq_true.mp hc b hm)

end M0Crypto.Release.ConstantTime
