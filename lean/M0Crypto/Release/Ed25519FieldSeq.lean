import M0Crypto.Release.Ed25519FieldSite
import M0Crypto.Release.Ed25519FeAddSub

set_option linter.unusedSimpArgs false

/-!
# A sequence of field calls on frame slots

A run of the generator's `fop` on frame slots, `fop(op₁, S(d₁), S(a₁), S(b₁)); fop(op₂, …); …`,
is one rule, `fops_run`. A macro names its slots by a type `ι` and places them with
`off : ι → Nat`; a call `⟨op, d, a, b⟩` sets slot `d` to `op` of slots `a` and `b`. The
continuation receives every slot's value as `fopsVal` of the calls, a formula in the values at
entry, and one frame fact for the callees' window and the written slots.

What each call needs beyond `fop_site` (each slot valid, each written slot equal to or apart from
every other slot) is one decided check, `fopsOk`, together with the call sites. A macro lemma
generic in its slots takes the check as a hypothesis and its instances decide it, so the generic
proof never reasons about the layout.
-/

namespace M0Crypto.Release.Ed25519FieldSeq

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Ed25519FieldSite
open M0Crypto.Release.Ed25519FeAddSub (feVal_memEq)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)

/-- The two-input field operations. -/
inductive FOp where
  | add | sub | mul

def FOp.fn : FOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

theorem FOp.congr (op : FOp) {x x' y y' : Int} (hx : ModP x x') (hy : ModP y y') :
    ModP (op.fn x y) (op.fn x' y') := by
  cases op
  · exact ModP.add hx hy
  · exact ModP.sub hx hy
  · exact ModP.mul hx hy

/-- The routines `fe_add`, `fe_sub`, `fe_mul`: offset, size and stack of each. -/
structure Callees where
  (oA szA stA oS szS stS oM szM stM : Nat)

/-- Offset, size and stack of the routine of `op`. -/
def Callees.at (c : Callees) : FOp → Nat × Nat × Nat
  | .add => (c.oA, c.szA, c.stA)
  | .sub => (c.oS, c.szS, c.stS)
  | .mul => (c.oM, c.szM, c.stM)

/-- The routine of `op`. -/
def Callees.R (c : Callees) (op : FOp) : Routine :=
  fieldR (c.at op).1 (c.at op).2.1 (c.at op).2.2 true op.fn

/-- `d := op a b` on the slots named `d`, `a`, `b`. -/
structure FCall (ι : Type) where
  (op : FOp) (d a b : ι)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}
variable {ι : Type} [DecidableEq ι]

/-- The pieces of the calls. -/
def fopsP (c : Callees) (off : ι → Nat) : List (FCall ι) → List Piece
  | [] => []
  | x :: xs => fopP (c.R x.op).entry (off x.d) (off x.a) (off x.b) ++ fopsP c off xs

/-- The slot values after the calls, from the values `V` before. -/
def fopsVal : List (FCall ι) → (ι → Int) → ι → Int
  | [], V => V
  | x :: xs, V => fopsVal xs fun i => if i = x.d then x.op.fn (V x.a) (V x.b) else V i

/-- The callees' window, `st` bytes below `sp`, and the written slots. -/
def fopsW (sp : Word) (st : Nat) (off : ι → Nat) (xs : List (FCall ι)) : List Rgn :=
  ⟨sp - BitVec.ofNat 32 st, st⟩ :: xs.map fun x => ⟨sp + BitVec.ofNat 32 (off x.d), 32⟩

/-- The trace of the calls from `o`, then `Ψ`; `T op` is the trace of `op`'s routine. -/
def fopsTr (T : FOp → Word → (Nat → Word) → List Event) (c : Callees) (off : ι → Nat)
    (base sp : Word) : Nat → List (FCall ι) → TrP → TrP
  | _, [], Ψ => Ψ
  | o, x :: xs, Ψ => fopTr (T x.op) base sp o (c.R x.op).entry (off x.d) (off x.a) (off x.b)
      (fopsTr T c off base sp (o + piecesSize (fopP (c.R x.op).entry (off x.d) (off x.a) (off x.b))) xs Ψ)

/-- Two slots lie apart. -/
def far (x y : Nat) : Bool := x + 32 ≤ y || y + 32 ≤ x

/-- Every slot of `names` is a valid frame slot below `top`. -/
def slotsOk (names : List ι) (off : ι → Nat) (top : Nat) : Bool :=
  names.all fun i => off i % 4 == 0 && decide (off i + 32 ≤ top) && decide (off i < 1024)

/-- The checks of the calls from `o`: each call site, each callee's stack within `st`, the slots
named in `names`, and each written slot apart from every other slot of `names`. -/
def callsOk [CodeBytes B BS] (cs : List (Nat × Nat)) (c : Callees) (names : List ι) (off : ι → Nat)
    (top N st : Nat) : Nat → List (FCall ι) → Bool
  | _, [] => true
  | o, x :: xs => siteOk cs (c.R x.op) (fopG (off x.d) (off x.a) (off x.b)) o top N
      (blImm (o + seqSize (fopG (off x.d) (off x.a) (off x.b))) (c.R x.op).entry) [] [] [] && decide ((c.R x.op).stack ≤ st) &&
      names.contains x.d && names.contains x.a && names.contains x.b &&
      names.all (fun j => j == x.d || far (off x.d) (off j)) && callsOk cs c names off top N st
        (o + piecesSize (fopP (c.R x.op).entry (off x.d) (off x.a) (off x.b))) xs

/-- **The decided checks of a field-call sequence** at `o`. -/
def fopsOk [CodeBytes B BS] (cs : List (Nat × Nat)) (c : Callees) (names : List ι) (off : ι → Nat)
    (top N st o : Nat) (xs : List (FCall ι)) : Bool :=
  slotsOk names off top && callsOk cs c names off top N st o xs

theorem apart_of {names : List ι} {off : ι → Nat} {d a : ι}
    (h : names.all (fun j => j == d || far (off d) (off j)) = true) (ha : names.contains a = true) :
    Apart (off d) (off a) := by
  have := List.all_eq_true.mp h a (List.contains_iff_mem.mp ha)
  simp only [Bool.or_eq_true, beq_iff_eq, far, decide_eq_true_eq] at this
  rcases this with rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem slot_of {names : List ι} {off : ι → Nat} {top : Nat} (h : slotsOk names off top = true)
    {i : ι} (hi : names.contains i = true) : SlotOk top (off i) := by
  have := List.all_eq_true.mp h i (List.contains_iff_mem.mp hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **A sequence of field calls on frame slots** (`fop_site` per call). `V` holds the slot values
at entry up to `ModP`; the continuation receives them after the calls as `fopsVal`. -/
theorem fops_run {c : Callees} (hT : ∀ op, Routine.TSpec (fun _ : Unit => c.R op) (fieldPub true))
    {names : List ι} {off : ι → Nat} {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat}
    {Rc Wc : List Rgn} {Q : State → Prop} {Ψ : TrP} {top st : Nat} {rest : List Piece}
    (F : Caller base sp0 N Wc) (hWc : Sub [⟨sp0 - BitVec.ofNat 32 N, N⟩] Wc)
    (hRc : Sub [codeR base, ⟨sp0 - BitVec.ofNat 32 N, N⟩] Rc) (hN : top + st ≤ N)
    (hsl : slotsOk names off top = true) :
    ∀ (xs : List (FCall ι)) (o : Nat) (t : State) (V : ι → Int),
    piecesAt B o (fopsP c off xs ++ rest) = true → callsOk cs c names off top N st o xs = true →
    t.pc = base + BitVec.ofNat 32 o → t.regs 13 = sp0 - BitVec.ofNat 32 top → CodeAt t.mem base B →
    (∀ i ∈ names, ModP (feVal t.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 (off i))) (V i)) →
    (∀ u, u.pc = base + BitVec.ofNat 32 (o + piecesSize (fopsP c off xs)) → u.regs 13 = sp0 - BitVec.ofNat 32 top →
      CodeAt u.mem base B → MemEq (fopsW (sp0 - BitVec.ofNat 32 top) st off xs) t.mem u.mem →
      (∀ i ∈ names, ModP (feVal u.mem (sp0 - BitVec.ofNat 32 top + BitVec.ofNat 32 (off i)))
        (fopsVal xs V i)) →
      piecesAt B (o + piecesSize (fopsP c off xs)) rest = true →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ) →
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (fopsTr (fun op => (hT op).T) c off base (sp0 - BitVec.ofNat 32 top) o xs Ψ)
  | [], o, t, V, hp, _, hpc, h13, hc, hV, k => k t (by simpa [fopsP] using hpc) h13 hc
      (MemEq.rfl' _ _) hV (by simpa [fopsP] using hp)
  | x :: xs, o, t, V, hp, hok, hpc, h13, hc, hV, k => by
    simp only [callsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨hs, hst⟩, hd⟩, ha⟩, hb⟩, hfar⟩, hok⟩ := hok
    have := F.room; have := sp0.isLt
    have hr : (sp0 - BitVec.ofNat 32 top).toNat = sp0.toNat - top := by
      have := (slot_of hsl hd).2.1; rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have e : o + piecesSize (fopsP c off (x :: xs)) = o + piecesSize (fopP (c.R x.op).entry (off x.d)
        (off x.a) (off x.b)) + piecesSize (fopsP c off xs) := by
      rw [fopsP, piecesSize_append, Nat.add_assoc]
    simp only [fopsP, List.append_assoc] at hp
    simp only [fopsTr]
    refine fop_site (hT x.op) F hWc hRc (slot_of hsl hd) (slot_of hsl ha) (slot_of hsl hb)
      (apart_of hfar ha) (apart_of hfar hb) hp hs hpc (Hi.self t) h13 hc
      fun u1 p1 _ s1 c1 m1 v1 hp1 => fops_run hT F hWc hRc hN hsl xs _ u1 _ hp1 hok p1 s1 c1
        (fun i hi => ?_) fun u pu su cu mu vu hpu => k u ?_ su cu ?_ vu ?_
    · -- the slot values after the call
      by_cases hix : i = x.d
      · subst hix; simp only [↓reduceIte]
        exact v1.trans (x.op.congr (hV _ (List.contains_iff_mem.mp ha)) (hV _ (List.contains_iff_mem.mp hb)))
      · simp only [hix, ↓reduceIte]
        have hf := List.all_eq_true.mp hfar i hi
        simp only [Bool.or_eq_true, beq_iff_eq, hix, false_or, far, decide_eq_true_eq] at hf
        obtain ⟨-, _, _⟩ := slot_of hsl hd; obtain ⟨-, _, _⟩ := slot_of hsl (List.contains_iff_mem.mpr hi)
        have : (c.R x.op).stack ≤ (sp0 - BitVec.ofNat 32 top).toNat := by omega
        rw [feVal_memEq m1 (by simp only [Callees.R, fieldR] at this ⊢; fp_tac)]
        exact hV i hi
    · rw [e]; exact pu
    · -- the frame of this call and the rest
      refine fun y hy => (m1.trans mu) y fun hh => hy ?_
      obtain ⟨r, hr', hry⟩ := hh
      simp only [fopsW, List.cons_append, List.nil_append, List.mem_cons, List.map_cons] at hr' ⊢
      rcases hr' with rfl | rfl | rfl | hr'
      · obtain ⟨j, hj, rfl⟩ := hry
        simp only [Callees.R, fieldR] at hj hst
        refine ⟨_, List.mem_cons_self, st - (c.at x.op).2.2 + j, by dsimp only; omega, ?_⟩
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hry⟩
      · exact ⟨_, List.mem_cons_self, hry⟩
      · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr'), hry⟩
    · rw [e]; exact hpu

/-- A slot's value from the continuation of `fops_run`: `fopsVal` at a named slot, evaluated by
`simp`. -/
theorem fops_val {names : List ι} {xs : List (FCall ι)} {V : ι → Int} {W : ι → Int}
    (hv : ∀ i ∈ names, ModP (W i) (fopsVal xs V i)) (i : ι) (hi : i ∈ names := by decide) {e : Int}
    (he : fopsVal xs V i = e := by simp [fopsVal, FOp.fn]) : ModP (W i) e :=
  he ▸ hv i hi

end M0Crypto.Release.Ed25519FieldSeq
