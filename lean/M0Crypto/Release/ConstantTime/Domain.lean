import M0Crypto.Thumb.Seq

/-!
# Abstract domain of the constant-time analysis

The analysis relates two runs that share their public inputs. An abstract value describes
a pair of concrete words `(x₁, x₂)`, one from each run (`AbsVal.Sem` in `ConstantTime/Sem.lean`):

* `hi`: no information (secret);
* `lo`: `x₁ = x₂` (public);
* `num a b`: public, `a ≤ x.toNat ≤ b`;
* `sp a b`: public, `x = sp0 + k` for one `k ∈ [a, b]` common to both runs;
* `ret r`: public, the return address `(base + r) ||| 1` into the artifact;
* `lr0`: public, the entry LR.

Flags have the same three-way split (`hi`, `lo`, `known b`). A flag state may also record
that NZCV hold the result of `CMP Rn, op`, which lets conditional branches refine
interval bounds.

The stack is sparse: a list of `(offset, value)` word slots relative to `sp0`. A missing
slot is `hi`. All operations are plain functions over lists and integers, so the kernel can
evaluate them.
-/

namespace M0Crypto.Release.ConstantTime

/-! ## Values -/

inductive AbsVal where
  | hi
  | lo
  | num (a b : Nat)
  | sp (a b : Int)
  | ret (r : Nat)
  | lr0
  deriving DecidableEq, Repr, Inhabited

namespace AbsVal

def cst (w : Nat) : AbsVal := .num w w

def pub : AbsVal → Bool
  | .hi => false
  | _ => true

def isSp : AbsVal → Bool
  | .sp _ _ => true
  | _ => false

/-- `le a b`: `a` is at least as precise as `b`. -/
def le : AbsVal → AbsVal → Bool
  | _, .hi => true
  | .hi, _ => false
  | _, .lo => true
  | .num a b, .num c d => decide (c ≤ a) && decide (b ≤ d)
  | .sp a b, .sp c d => decide (c ≤ a) && decide (b ≤ d)
  | .ret r, .ret r' => r == r'
  | .lr0, .lr0 => true
  | _, _ => false

def join : AbsVal → AbsVal → AbsVal
  | .hi, _ => .hi
  | _, .hi => .hi
  | .num a b, .num c d => .num (min a c) (max b d)
  | .sp a b, .sp c d => .sp (min a c) (max b d)
  | .ret r, .ret r' => if r == r' then .ret r else .lo
  | .lr0, .lr0 => .lr0
  | _, _ => .lo

/-- Label-only result of an operation on public or secret inputs. -/
def ofPub (p : Bool) : AbsVal := if p then .lo else .hi

def word : Nat := 2 ^ 32

/-- `v + k` for a constant `k`. -/
def addK (v : AbsVal) (k : Nat) : AbsVal :=
  match v with
  | .num a b => if b + k < word then .num (a + k) (b + k) else .lo
  | .sp a b => .sp (a + k) (b + k)
  | .hi => .hi
  | _ => .lo

/-- `v - k` for a constant `k`. -/
def subK (v : AbsVal) (k : Nat) : AbsVal :=
  match v with
  | .num a b => if k ≤ a then .num (a - k) (b - k) else .lo
  | .sp a b => .sp (a - k) (b - k)
  | .hi => .hi
  | _ => .lo

/-- `v + w`. -/
def add (v w : AbsVal) : AbsVal :=
  match v, w with
  | .hi, _ => .hi
  | _, .hi => .hi
  | .num a b, .num c d => if b + d < word then .num (a + c) (b + d) else .lo
  | .sp a b, .num c d => .sp (a + c) (b + d)
  | .num c d, .sp a b => .sp (a + c) (b + d)
  | _, _ => .lo

/-- `v - w`. -/
def sub (v w : AbsVal) : AbsVal :=
  match v, w with
  | .hi, _ => .hi
  | _, .hi => .hi
  | .num a b, .num c d => if d ≤ a then .num (a - d) (b - c) else .lo
  | .sp a b, .num c d => .sp (a - d) (b - c)
  | _, _ => .lo

/-- Exact constant, if the value is one. -/
def exact? : AbsVal → Option Nat
  | .num a b => if a == b then some a else none
  | _ => none

end AbsVal

/-! ## Flags -/

inductive AbsFlags where
  | hi
  | lo
  | known (b : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace AbsFlags

def pub : AbsFlags → Bool
  | .hi => false
  | _ => true

def le : AbsFlags → AbsFlags → Bool
  | _, .hi => true
  | .hi, _ => false
  | _, .lo => true
  | .known a, .known b => a == b
  | _, _ => false

def join : AbsFlags → AbsFlags → AbsFlags
  | .hi, _ => .hi
  | _, .hi => .hi
  | .known a, .known b => if a == b then .known a else .lo
  | _, _ => .lo

def ofPub (p : Bool) : AbsFlags := if p then .lo else .hi

end AbsFlags

/-- Second operand of a recorded comparison. -/
inductive Opnd where
  | reg (i : Nat)
  | imm (w : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- NZCV hold the flags of `CMP R[a], op`, and neither register has changed since.
With `zOnly`, only Z is meaningful (`Z ↔ R[a] = op`), as after `ANDS Rd, Rm` with `op = 0`. -/
structure Cmp where
  a : Nat
  b : Opnd
  zOnly : Bool
  deriving DecidableEq, Repr, Inhabited

def Cmp.uses (c : Cmp) (r : Nat) : Bool :=
  c.a == r || c.b == .reg r

structure AFl where
  n : AbsFlags
  z : AbsFlags
  c : AbsFlags
  v : AbsFlags
  cmp : Option Cmp
  deriving DecidableEq, Repr, Inhabited

namespace AFl

def all (f : AbsFlags) : AFl := ⟨f, f, f, f, none⟩

def le (f g : AFl) : Bool :=
  f.n.le g.n && f.z.le g.z && f.c.le g.c && f.v.le g.v &&
    (match g.cmp with
     | none => true
     | some c => f.cmp == some c)

def join (f g : AFl) : AFl :=
  ⟨f.n.join g.n, f.z.join g.z, f.c.join g.c, f.v.join g.v,
    if f.cmp == g.cmp then f.cmp else none⟩

/-- Drop the comparison record if register `r` is overwritten. -/
def touch (f : AFl) (r : Nat) : AFl :=
  match f.cmp with
  | some c => if c.uses r then { f with cmp := none } else f
  | none => f

end AFl

/-! ## Registers (r0–r12 and LR; index 13 is unused, SP is tracked by `spOff`) -/

def numRegs : Nat := 15

def regGet (rs : List AbsVal) (r : Nat) : AbsVal :=
  if r == 13 then .hi else rs.getD r .hi

def regSet (rs : List AbsVal) (r : Nat) (v : AbsVal) : List AbsVal :=
  if r == 13 then rs else rs.set r v

def regsLe (a b : List AbsVal) : Bool :=
  (List.range numRegs).all fun r => (regGet a r).le (regGet b r)

def regsJoin (a b : List AbsVal) : List AbsVal :=
  (List.range numRegs).map fun r => (regGet a r).join (regGet b r)

/-! ## Sparse stack: word slots at `sp0 + off`, missing slot = `hi` -/

abbrev Stk := List (Int × AbsVal)

def stkGet (s : Stk) (o : Int) : AbsVal :=
  match s.lookup o with
  | some v => v
  | none => .hi

/-- Strong update of the word slot at `o`. -/
def stkSet (s : Stk) (o : Int) (v : AbsVal) : Stk :=
  let rest := s.filter fun p => p.1 != o
  if v.pub then (o, v) :: rest else rest

/-- Forget every slot whose bytes `[o, o + 4)` meet the byte range `[x, y)`. -/
def stkForget (s : Stk) (x y : Int) : Stk :=
  s.filter fun p => decide (p.1 + 4 ≤ x) || decide (y ≤ p.1)

def stkLe (a b : Stk) : Bool :=
  b.all fun p => (stkGet a p.1).le p.2

def stkJoin (a b : Stk) : Stk :=
  a.filterMap fun p =>
    let v := p.2.join (stkGet b p.1)
    if v.pub then some (p.1, v) else none

/-! ## Relational facts between registers -/

/-- `(i, j, strict)`: in both runs `R[i].toNat + (strict ? 1 : 0) ≤ R[j].toNat`. -/
abbrev Fact := Nat × Nat × Bool

/-- Unsigned interval of a public register value, if it has one. -/
def ival : AbsVal → Option (Nat × Nat)
  | .num a b => some (a, b)
  | .lo => some (0, AbsVal.word - 1)
  | _ => none

/-- Affine link: in both runs `R[i] = sp0 + c + k * R[j].toNat`. It lets a pointer that
walks the stack stay bounded by its loop counter. -/
structure Lnk where
  i : Nat
  j : Nat
  k : Int
  c : Int
  deriving DecidableEq, Repr, Inhabited

/-- Exact stack offset of an `sp` value. -/
def spExact : AbsVal → Option Int
  | .sp a b => if a == b then some a else none
  | _ => none

/-! ## Stack window -/

/-- Stack window of an entry, as offsets from `sp0`: `[-below, above)`. -/
structure StackWindow where
  below : Nat
  above : Nat
  deriving DecidableEq, Repr

/-- A single integer offset represented within the window. -/
def StackWindow.containsOffset (w : StackWindow) (x : Int) : Bool :=
  decide (-(w.below : Int) ≤ x) && decide (x < (w.above : Int))

/-! ## Abstract state -/

structure AbsState where
  regs : List AbsVal
  spOff : Int
  fl : AFl
  stk : Stk
  rel : List Fact
  lnk : List Lnk
  deriving DecidableEq, Repr, Inhabited

namespace AbsState

def get (s : AbsState) (r : Nat) : AbsVal := regGet s.regs r

/-- The state entails a fact: it is recorded, or the intervals imply it. -/
def entails (s : AbsState) (f : Fact) : Bool :=
  let (i, j, st) := f
  s.rel.contains f || (!st && s.rel.contains (i, j, true)) ||
    match ival (s.get i), ival (s.get j) with
    | some (_, ih), some (jl, _) => decide (ih + (if st then 1 else 0) ≤ jl)
    | _, _ => false

/-- The state entails a link: it is recorded, or both values are exact and on the line. -/
def lnkEntails (s : AbsState) (l : Lnk) : Bool :=
  s.lnk.contains l ||
    match spExact (s.get l.i), (s.get l.j).exact? with
    | some x, some n => x == l.c + l.k * n
    | _, _ => false

/-- Links through two exact points `(x₁, n₁)` and `(x₂, n₂)` of the states `a` and `b`. -/
def newLinks (a b : AbsState) : List Lnk :=
  (List.range numRegs).flatMap fun i =>
    match spExact (a.get i), spExact (b.get i) with
    | some x₁, some x₂ =>
      (List.range numRegs).filterMap fun j =>
        match (a.get j).exact?, (b.get j).exact? with
        | some n₁, some n₂ =>
          if n₁ == n₂ || x₁ == x₂ then none
          else
            let dn : Int := (n₁ : Int) - n₂
            let dx := x₁ - x₂
            if dx % dn == 0 then some ⟨i, j, dx / dn, x₁ - (dx / dn) * n₁⟩ else none
        | _, _ => none
    | _, _ => []

/-- Interval of `c + k * n` for `n ∈ [l, h]`. -/
def lnkRange (k c : Int) (l h : Nat) : Int × Int :=
  if 0 ≤ k then (c + k * l, c + k * h) else (c + k * h, c + k * l)

/-- Tighten the interval of `R[i]` by the facts `R[i] < R[j]` and `R[i] ≤ R[j]`, and the
`sp` interval of a linked pointer by its counter. -/
def tighten (w : StackWindow) (st : AbsState) : AbsState :=
  let st := st.lnk.foldl (fun s l =>
    match s.get l.i, ival (s.get l.j) with
    | .sp a b, some (nl, nh) =>
      let (x, y) := lnkRange l.k l.c nl nh
      let a' := max a x
      let b' := min b y
      -- Modular equality implies integer equality only when both ranges have unique
      -- representatives in this window, whose width is less than one word.
      let bounded := decide (w.below + w.above < AbsVal.word) &&
        w.containsOffset a && w.containsOffset b &&
        w.containsOffset x && w.containsOffset y
      if bounded && a' ≤ b' && (a < a' || b' < b) then
        { s with regs := regSet s.regs l.i (.sp a' b') }
      else s
    | _, _ => s) st
  st.rel.foldl (fun s (i, j, strict) =>
    match ival (s.get i), ival (s.get j) with
    | some (il, ih), some (_, jh) =>
      let d := if strict then 1 else 0
      if d ≤ jh ∧ jh - d < ih ∧ il ≤ jh - d then
        { s with regs := regSet s.regs i (.num il (jh - d)) }
      else s
    | _, _ => s) st

def le (a b : AbsState) : Bool :=
  a.spOff == b.spOff && a.fl.le b.fl && regsLe a.regs b.regs && stkLe a.stk b.stk &&
    b.rel.all a.entails && b.lnk.all a.lnkEntails

def join (w : StackWindow) (a b : AbsState) : Option AbsState :=
  if a.spOff == b.spOff then
    let cand := a.rel ++ b.rel
    let rel := (cand.filter fun f => a.entails f && b.entails f).eraseDups
    let lc := a.lnk ++ b.lnk ++ newLinks a b
    let lnk := (lc.filter fun l => a.lnkEntails l && b.lnkEntails l).eraseDups
    let j : AbsState := ⟨regsJoin a.regs b.regs, a.spOff, a.fl.join b.fl, stkJoin a.stk b.stk, [], []⟩
    -- keep only facts about registers that still have intervals
    some (tighten w { j with
      rel := rel.filter fun (i, k, _) => (ival (j.get i)).isSome && (ival (j.get k)).isSome,
      lnk := lnk.filter fun l => (j.get l.i).isSp && (ival (j.get l.j)).isSome })
  else none

/-- Write register `r`: drop comparison records, facts and links that mention it. -/
def set (s : AbsState) (r : Nat) (v : AbsVal) : AbsState :=
  { s with regs := regSet s.regs r v, fl := s.fl.touch r,
           rel := s.rel.filter (fun (i, j, _) => i != r && j != r),
           lnk := s.lnk.filter fun l => l.i != r && l.j != r }

end AbsState

/-- The byte range `[x, y)` lies in the window. -/
def StackWindow.covers (w : StackWindow) (x y : Int) : Bool :=
  decide (-(w.below : Int) ≤ x) && decide (y ≤ (w.above : Int))

end M0Crypto.Release.ConstantTime
