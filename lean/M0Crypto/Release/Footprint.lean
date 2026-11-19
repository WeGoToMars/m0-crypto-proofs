import Lean
import M0Crypto.Release.Contract
import M0Crypto.Release.FrameBase
import M0Crypto.Thumb.Program

/-!
# Footprints

A footprint is a list of regions `⟨a, n⟩`, the `n` bytes from `a`. A routine states what it
writes and reads as footprints, so that every side condition of a call has one of two forms:
`Sep f g` (every region of `f` lies apart from every region of `g`, neither wrapping) and
`Sub f g` (every region of `f` lies inside a region of `g`). Both unfold to linear arithmetic
on `toNat` of the region bases, which `fp_tac` hands to `omega` with the caller's layout facts.

`MemEq f m m'` (memory `m'` agrees with `m` outside `f`) is the frame fact a call or a block
leaves; `MemEq.bytesAt` carries a `bytesAt` fact across it.
-/

namespace M0Crypto.Release.Footprint

open M0Crypto.Armv6M (Word Mem read32)
open M0Crypto.Thumb (ofNat_add_assoc)
open M0Crypto.Release.Frame (Disj)

/-- The `n` bytes from `a`. -/
structure Rgn where
  a : Word
  n : Nat

/-- `y` is a byte of the region. -/
def Rgn.Has (r : Rgn) (y : Word) : Prop := ∃ o < r.n, y = r.a + BitVec.ofNat 32 o

/-- `y` is a byte of a region of `f`. -/
def Has (f : List Rgn) (y : Word) : Prop := ∃ r ∈ f, r.Has y

/-- Every region of `f` lies apart from every region of `g`, and none of them wraps. -/
def Sep (f g : List Rgn) : Prop := ∀ r ∈ f, ∀ q ∈ g, Disj r.a r.n q.a q.n

/-- Every region of `f` lies inside a region of `g` that does not wrap. -/
def Sub (f g : List Rgn) : Prop :=
  ∀ r ∈ f, ∃ q ∈ g, q.a.toNat ≤ r.a.toNat ∧ r.a.toNat + r.n ≤ q.a.toNat + q.n ∧
    q.a.toNat + q.n ≤ 2 ^ 32

/-- `m'` agrees with `m` outside `f`. -/
def MemEq (f : List Rgn) (m m' : Mem) : Prop := ∀ y, ¬ Has f y → m' y = m y

variable {f g h : List Rgn} {y : Word}

theorem Has.cons {r : Rgn} (hr : r.Has y) (l : List Rgn) : Has (r :: l) y := ⟨r, by simp, hr⟩

theorem Has.append_left (hf : Has f y) (g : List Rgn) : Has (f ++ g) y :=
  let ⟨r, hr, h⟩ := hf
  ⟨r, List.mem_append_left _ hr, h⟩

theorem Has.append_right (hg : Has g y) (f : List Rgn) : Has (f ++ g) y :=
  let ⟨r, hr, h⟩ := hg
  ⟨r, List.mem_append_right _ hr, h⟩

theorem Has.append_iff : Has (f ++ g) y ↔ Has f y ∨ Has g y := by
  constructor
  · rintro ⟨r, hr, h⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl ⟨r, hr, h⟩
    · exact Or.inr ⟨r, hr, h⟩
  · rintro (h | h)
    · exact h.append_left g
    · exact h.append_right f

theorem Has.nil : ¬ Has [] y := fun ⟨_, h, _⟩ => by cases h

theorem Rgn.has_sub {r q : Rgn} (h1 : q.a.toNat ≤ r.a.toNat) (h2 : r.a.toNat + r.n ≤ q.a.toNat + q.n)
    (_h3 : q.a.toNat + q.n ≤ 2 ^ 32) (hy : r.Has y) : q.Has y := by
  obtain ⟨o, ho, rfl⟩ := hy
  refine ⟨r.a.toNat - q.a.toNat + o, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := r.a.isLt
  omega

theorem Sub.has (hs : Sub f g) (hy : Has f y) : Has g y := by
  obtain ⟨r, hr, hy⟩ := hy
  obtain ⟨q, hq, h1, h2, h3⟩ := hs r hr
  exact ⟨q, hq, Rgn.has_sub h1 h2 h3 hy⟩

theorem Sub.refl (f : List Rgn) (hw : ∀ r ∈ f, r.a.toNat + r.n ≤ 2 ^ 32) : Sub f f :=
  fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _, hw r hr⟩

theorem Rgn.disj_ne {r q : Rgn} (h : Disj r.a r.n q.a q.n) (hr : r.Has y) : ¬ q.Has y := by
  rintro ⟨j, hj, rfl⟩
  obtain ⟨i, hi, he⟩ := hr
  obtain ⟨h1, h2, h3⟩ := h
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := r.a.isLt; have := q.a.isLt
  omega

theorem Sep.not_has (hs : Sep f g) (hf : Has f y) : ¬ Has g y := by
  rintro ⟨q, hq, hy⟩
  obtain ⟨r, hr, hx⟩ := hf
  exact Rgn.disj_ne (hs r hr q hq) hx hy

theorem Sep.symm (hs : Sep f g) : Sep g f := fun q hq r hr =>
  let ⟨a, b, c⟩ := hs r hr q hq
  ⟨b, a, c.symm⟩

/-- A footprint inside one that lies apart from `h` lies apart from `h`. -/
theorem Sub.sep (hs : Sub f g) (hg : Sep g h) : Sep f h := by
  intro r hr q hq
  obtain ⟨p, hp, h1, h2, h3⟩ := hs r hr
  obtain ⟨a, b, c⟩ := hg p hp q hq
  exact ⟨by omega, b, by omega⟩

theorem Sep.append_left {f1 f2 : List Rgn} (h1 : Sep f1 g) (h2 : Sep f2 g) : Sep (f1 ++ f2) g := by
  intro r hr q hq
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr q hq
  · exact h2 r hr q hq

/-! ## Byte lists -/

/-- The `n` bytes from `a`. -/
def bytesAt (m : Mem) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m (a + BitVec.ofNat 32 i)

theorem bytesAt_length (m : Mem) (a : Word) (n : Nat) : (bytesAt m a n).length = n := by
  simp [bytesAt]

theorem bytesAt_congr {m1 m2 : Mem} {a : Word} {n : Nat}
    (h : ∀ i < n, m1 (a + BitVec.ofNat 32 i) = m2 (a + BitVec.ofNat 32 i)) :
    bytesAt m1 a n = bytesAt m2 a n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-! ## Memory agreement -/

theorem MemEq.rfl' (f : List Rgn) (m : Mem) : MemEq f m m := fun _ _ => rfl

theorem MemEq.of_eq {m m' : Mem} (h : m' = m) : MemEq f m m' := fun _ _ => by rw [h]

theorem MemEq.trans {m1 m2 m3 : Mem} (h1 : MemEq f m1 m2) (h2 : MemEq g m2 m3) :
    MemEq (f ++ g) m1 m3 := fun y hy => by
  rw [h2 y (fun h => hy (h.append_right f)), h1 y (fun h => hy (h.append_left g))]

theorem MemEq.mono {m m' : Mem} (h : MemEq f m m') (hs : Sub f g) : MemEq g m m' :=
  fun y hy => h y (fun h => hy (hs.has h))

/-- A running frame: a step that writes inside `f` keeps `MemEq f`. -/
theorem MemEq.grow {m0 m1 m2 : Mem} (h1 : MemEq f m0 m1) (h2 : MemEq g m1 m2) (hs : Sub g f) :
    MemEq f m0 m2 := fun y hy => by rw [h2 y (fun h => hy (hs.has h)), h1 y hy]

theorem MemEq.byte {m m' : Mem} (h : MemEq f m m') (hs : Sep [⟨y, 1⟩] f) : m' y = m y :=
  h y (Sep.not_has hs ⟨⟨y, 1⟩, List.mem_singleton.mpr rfl, ⟨0, Nat.one_pos, by simp⟩⟩)

/-- **The frame rule for memory facts**: bytes apart from `f` are unchanged. -/
theorem MemEq.bytes {m m' : Mem} (h : MemEq f m m') {a : Word} {n : Nat} (hs : Sep [⟨a, n⟩] f) :
    bytesAt m' a n = bytesAt m a n :=
  bytesAt_congr fun i hi =>
    h _ (Sep.not_has hs ⟨⟨a, n⟩, List.mem_singleton.mpr rfl, ⟨i, hi, rfl⟩⟩)

theorem MemEq.read32 {m m' : Mem} (h : MemEq f m m') {a : Word} (hs : Sep [⟨a, 4⟩] f) :
    read32 m' a = read32 m a :=
  Frame.read32_congr fun i hi =>
    h _ (Sep.not_has hs ⟨⟨a, 4⟩, List.mem_singleton.mpr rfl, ⟨i, hi, rfl⟩⟩)

/-- A `bytesAt` fact carried across a frame. -/
theorem MemEq.carry {m m' : Mem} (h : MemEq f m m') {a : Word} {n : Nat} {L : List (BitVec 8)}
    (hL : bytesAt m a n = L) (hs : Sep [⟨a, n⟩] f) : bytesAt m' a n = L := by
  rw [h.bytes hs, hL]

/-- Bytes equal pointwise to bytes elsewhere. -/
theorem bytesAt_eq_of {m m' : Mem} {a b : Word} {n : Nat}
    (h : ∀ k < n, m' (a + BitVec.ofNat 32 k) = m (b + BitVec.ofNat 32 k)) :
    bytesAt m' a n = bytesAt m b n :=
  List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

/-- Bytes given pointwise. -/
theorem bytesAt_eq_map {m : Mem} {a : Word} {n : Nat} {g : Nat → BitVec 8}
    (h : ∀ k < n, m (a + BitVec.ofNat 32 k) = g k) : bytesAt m a n = (List.range n).map g :=
  List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

/-- Bytes given as a list, pointwise. -/
theorem bytesAt_eq_list {m : Mem} {a : Word} {n : Nat} {L : List (BitVec 8)} (hl : L.length = n)
    (h : ∀ k < n, m (a + BitVec.ofNat 32 k) = L[k]!) : bytesAt m a n = L := by
  apply List.ext_getElem (by rw [bytesAt_length, hl])
  intro k h1 h2
  rw [bytesAt_length] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h k h1, getElem!_pos L k h2]

/-- The contracts' byte list (`Frame.Ctx.bytesAt`) is `bytesAt`. -/
theorem ctx_bytesAt (m : Mem) : ∀ (n : Nat) (a : Word), Frame.Ctx.bytesAt m a n = bytesAt m a n
  | 0, _ => rfl
  | n + 1, a => by
    rw [Frame.Ctx.bytesAt, ctx_bytesAt m n (a + 1#32)]
    simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congr (congrArg _ (by simp)) (List.map_congr_left fun i _ => ?_)
    show m (a + 1#32 + BitVec.ofNat 32 i) = m (a + BitVec.ofNat 32 (i + 1))
    rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_assoc, Nat.add_comm]

/-- A byte of the region `[a, a + n)` of the contracts is a byte of the footprint region. -/
theorem Rgn.of_region {a y : Word} {n : Nat} (h : Region a n y) : Rgn.Has ⟨a, n⟩ y :=
  Region.exists h

/-! ## The arithmetic tactic -/

theorem sub_sub_ofNat (a : Word) (x y : Nat) :
    a - BitVec.ofNat 32 x - BitVec.ofNat 32 y = a - BitVec.ofNat 32 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem sub_add_ofNat (a : Word) (x y : Nat) (h : y ≤ x) :
    a - BitVec.ofNat 32 x + BitVec.ofNat 32 y = a - BitVec.ofNat 32 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega


/-- Unfolds footprint side conditions to linear arithmetic on `toNat`. -/
theorem sep_cons_left {r : Rgn} {f g : List Rgn} :
    Sep (r :: f) g ↔ (∀ q ∈ g, Disj r.a r.n q.a q.n) ∧ Sep f g := by
  simp [Sep]

theorem sep_nil_left {g : List Rgn} : Sep [] g ↔ True := by simp [Sep]

theorem sub_cons_left {r : Rgn} {f g : List Rgn} :
    Sub (r :: f) g ↔ (∃ q ∈ g, q.a.toNat ≤ r.a.toNat ∧ r.a.toNat + r.n ≤ q.a.toNat + q.n ∧
      q.a.toNat + q.n ≤ 2 ^ 32) ∧ Sub f g := by
  simp [Sub]

theorem sub_nil_left {g : List Rgn} : Sub [] g ↔ True := by simp [Sub]

/-- The lemmas `fp_tac` unfolds with. -/
macro "fp_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Footprint.sep_cons_left, Footprint.sep_nil_left, Footprint.sub_cons_left,
    Footprint.sub_nil_left, List.forall_mem_cons, List.exists_mem_cons, List.not_mem_nil,
    false_and, exists_false, or_false, implies_true, and_true, true_and, Nat.reducePow,
    Frame.Disj, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, List.mem_cons,
    List.mem_singleton, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left] $[$loc]?)

open Lean Meta Elab Tactic in
/-- The hypotheses with conjunctions split into one hypothesis per conjunct. -/
partial def splitAnds (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then
      let l ← mkAppM ``And.left #[d.toExpr]
      let r ← mkAppM ``And.right #[d.toExpr]
      let (_, g') ← g.assertHypotheses #[
        { userName := d.userName, type := ty.getArg! 0, value := l },
        { userName := d.userName, type := ty.getArg! 1, value := r }]
      return ← splitAnds (← g'.tryClear d.fvarId)
  return g

open Lean in
/-- The `toNat` atoms of an expression. -/
partial def toNatAtoms (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
  if e.isAppOfArity ``BitVec.toNat 2 then acc.insert e
  else match e with
    | .app f a => toNatAtoms a (toNatAtoms f acc)
    | .lam _ t b _ | .forallE _ t b _ => toNatAtoms b (toNatAtoms t acc)
    | .letE _ t v b _ => toNatAtoms b (toNatAtoms v (toNatAtoms t acc))
    | .mdata _ b | .proj _ _ b => toNatAtoms b acc
    | _ => acc

open Lean Meta Elab Tactic in
/-- `omega` on the hypotheses that can matter: conjunctions are split, and a disjunction is
dropped when it mentions a `toNat` atom that the goal does not. Layout facts are disjunctions
over pairs of regions, and `omega` splits every one of them; most concern other regions. Atoms
are compared up to reducible defeq: the same register literal can carry different instance
proofs. -/
elab "fp_omega" : tactic => do
  let g ← splitAnds (← getMainGoal)
  let g ← g.withContext do
    let goalAtoms := (toNatAtoms (← instantiateMVars (← g.getType)) {}).toArray
    let mut g := g
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if (ty.find? (·.isAppOf ``Or)).isSome then
        let mut keep := true
        for a in (toNatAtoms ty {}).toList do
          unless ← goalAtoms.anyM (fun b => withReducible (isDefEq a b)) do
            keep := false
            break
        unless keep do g ← g.tryClear d.fvarId
    pure g
  replaceMainGoal [g]
  evalTactic (← `(tactic| omega))

open Lean Elab Tactic in
/-- Succeeds on a containment goal: a disjunction whose first alternative is a conjunction (the
region inside the first candidate). -/
elab "fp_sub_alt" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOfArity ``Or 2 && (ty.getArg! 0).isAppOfArity ``And 2 do
    throwError "fp_sub_alt: not a containment disjunction"

/-- One footprint goal. A containment (the region inside one of several) is tried one candidate
at a time, since `omega` would split the negation of every candidate. Anything else, a
disjointness `a + n ≤ b ∨ b + m ≤ a` included, goes to `omega` whole: its negation is a
conjunction. -/
syntax "fp_goal" : tactic

macro_rules
  | `(tactic| fp_goal) => `(tactic| first
    | (fp_sub_alt; first | (refine Or.inl ?_; fp_omega) | (refine Or.inr ?_; fp_goal))
    | fp_omega
    | omega)

/-- `fp_tac` closes `Sep` and `Sub` goals (and plain `Disj` goals) by unfolding them over
literal lists, splitting the conjunctions and calling `fp_goal` on each part. The layout facts
it needs are hypotheses in `toNat` form, or are given as `fp_tac [h₁, h₂]`; each given fact is
unfolded the same way. -/
syntax "fp_tac" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| fp_tac) => `(tactic| (try fp_simp) <;> (repeat' apply And.intro) <;> fp_goal)
  | `(tactic| fp_tac []) => `(tactic| fp_tac)
  | `(tactic| fp_tac [$h]) => `(tactic| (have hfp := $h; (try fp_simp at hfp); fp_tac))
  | `(tactic| fp_tac [$h, $hs,*]) => `(tactic| (have hfp := $h; (try fp_simp at hfp); fp_tac [$hs,*]))

end M0Crypto.Release.Footprint
