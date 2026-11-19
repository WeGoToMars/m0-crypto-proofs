import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519MulBaseProg

/-!
# `m0c_zero` and `m0c_copy` of `n` field elements

The adapters of the word loops at `8 n` words, for any element count `n` with its decided interface
checks (`zeroOk`, `copyOk`):

* `zeroAd n`: `m0c_zero` over `ioZeroN n`, `n` 32-byte views of zero bytes;
* `copyAdN n`: `m0c_copy` over `ioCopyN n`, `n` field elements from views to views.

`m0c_zero`'s call lemma has the public values `r0, r1, r1, sp` (its counter is `r1`); `TE.repub`
moves it to the callee's `r0, r1, sp`.
-/

namespace M0Crypto.Release.Ed25519WordAd

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb (Event ofNat_add_assoc)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (zero copy)
open M0Crypto.Release.Ed25519MulBaseProg (ioZeroN)
open M0Crypto.Release.StackEffect (InR)
open M0Crypto.Sym (SExpr)

/-- `copy` of `n` field elements: views in, field values out. -/
def ioCopyN (n : Nat) : Iface :=
  { ins := (List.range n).map fun j => (1, 32 * j, .view .fe), outs := (List.range n).map fun j => (0, 32 * j, .fe),
    wr := [⟨0, 0, .k (32 * n)⟩], rd := [⟨1, 0, .k (32 * n)⟩], al := [0, 1], eqd := [(0, 1, 32 * n)],
    kreq := [(2, 8 * n)] }

/-! ## Generic helpers -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **A call lemma at other public values** `pub'`, from which `g` gives `pub`. -/
noncomputable def _root_.M0Crypto.Release.Routine.Routine.TE.repub {α β : Type} {f : Routine}
    {pub : Word → State → α} {E : Word → α → TrP} (te : f.TE pub E) (pub' : Word → State → β) (g : β → α)
    (hg : ∀ b s, g (pub' b s) = pub b s) : f.TE pub' fun b p => E b (g p) :=
  ⟨fun b p => te.T b (g p), by
    have h : (fun base s => Tr.is (te.T base (g (pub' base s)))) = fun base s => Tr.is (te.T base (pub base s)) := by
      funext base s; rw [hg]
    exact (congrArg f.SpecT h).mpr te.spec, fun b p => te.eff b (g p)⟩

end

/-- `All2` over a mapped list, pointwise. -/
theorem all2_map {α β γ : Type} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    ∀ l : List α, (∀ j ∈ l, R (f j) (g j)) → All2 R (l.map f) (l.map g)
  | [], _ => trivial
  | j :: l, h => ⟨h j List.mem_cons_self, all2_map f g l fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

/-- `All2` over a mapped list, carried to another relation. -/
theorem all2_mono {α γ γ' δ : Type} {R : γ → δ → Prop} {R' : γ' → δ → Prop} (f : α → γ) (f' : α → γ') :
    ∀ (l : List α) (vs : List δ), (∀ j ∈ l, ∀ v, R (f j) v → R' (f' j) v) → All2 R (l.map f) vs →
      All2 R' (l.map f') vs
  | [], [], _, _ => trivial
  | j :: l, v :: vs, h, hr =>
    ⟨h j List.mem_cons_self v hr.1, all2_mono f f' l vs (fun i hi => h i (List.mem_cons_of_mem _ hi)) hr.2⟩
  | [], _ :: _, _, hr => hr.elim
  | _ :: _, [], _, hr => hr.elim

/-- Byte `k` of element `j` lies in word `8 j + k / 4`. -/
theorem elem_byte (a : Word) (j k : Nat) :
    a + BitVec.ofNat 32 (32 * j) + BitVec.ofNat 32 k =
      a + BitVec.ofNat 32 (4 * (8 * j + k / 4)) + BitVec.ofNat 32 (k % 4) := by
  rw [ofNat_add_assoc, ofNat_add_assoc]; congr 2; omega

/-- Word `i` of element `j` is word `8 j + i`. -/
theorem elem_word (a : Word) (j i : Nat) :
    a + BitVec.ofNat 32 (32 * j) + BitVec.ofNat 32 (4 * i) = a + BitVec.ofNat 32 (4 * (8 * j + i)) := by
  rw [ofNat_add_assoc]; congr 2; omega

theorem toNat_8n {n : Nat} (hn : 32 * n < 2 ^ 32) : (BitVec.ofNat 32 (8 * n)).toNat = 8 * n := by
  rw [BitVec.toNat_ofNat]; omega

/-! ## `m0c_zero` -/

/-- The decided interface checks of `zero` over `ioZeroN n`. -/
def zeroOk (n : Nat) : Bool :=
  effOk (ioZeroN n) [(.reg0 0, 32 * n)] [] [(.reg0 0, 32 * n)] &&
    Ed25519Leaf.regsOk (calleeAt zero (ioZeroN n) [0, 1]) [0, 1] && decide (0 < n ∧ 32 * n < 2 ^ 32)

/-- `m0c_zero`'s public values from the callee's `r0, r1, sp`. -/
def zeroG (p : Nat → Word) : Nat → Word := pubOf [p 0, p 1, p 1, p 2]

theorem zero_code : rangesSub (Ed25519WordLoop.wordR zero (Thumb.seqSize (Ed25519WordLoop.wloop
    Ed25519WordLoop.zeroPre Ed25519WordLoop.zeroBody 0xfc)) 1 false false (fun _ => True) (fun _ _ _ => 0#32) []).code
    (footprint zero) = true := by decide +kernel

/-- `m0c_zero` of `8 n` words in build `b`, its count pinned, at the callee's public values. -/
noncomputable def zeroN (b : Build) (n : Nat) (hn : 32 * n < 2 ^ 32) := letI := b.codeBytes
  (((Ed25519WordLoop.zero_te b).pin 2 1 (BitVec.ofNat 32 (8 * n)) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 32 * n⟩])
    (fun _ => []) (fun s h => by
      show [Footprint.Rgn.mk (s.regs 0) (4 * (s.regs 1).toNat)] = _; rw [h, toNat_8n hn, show 4 * (8 * n) = 32 * n by omega])
    fun _ _ => rfl).code (footprint zero) zero_code).repub (calleeAt zero (ioZeroN n) [0, 1]).pub zeroG
    fun _ _ => rfl

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The effect of `m0c_zero` of `8 n` words is its callee's. -/
theorem zero_eff {n : Nat} (hok : zeroOk n = true) {base : Word} {p : Nat → Word} {tr : List Event}
    (h : Ed25519WordLoop.wloopE false false base (setPub (zeroG p) 2 (BitVec.ofNat 32 (8 * n))) tr) :
    (calleeAt zero (ioZeroN n) [0, 1]).Eff p base tr := by
  simp only [zeroOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨he, hr⟩, hn0, hn⟩ := hok
  have e8 : 8 * ((BitVec.ofNat 32 (8 * n)).toNat / 2) = 32 * n := by rw [toNat_8n hn]; omega
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, e8, Bool.false_eq_true, false_and,
    or_false] at h
  have r0 : (SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1] 0 p) = p 0 := rfl
  refine Ed25519Leaf.blk_eff (L := [0, 1]) (pc := 0) (fp := [(.reg0 0, 32 * n)]) (ini := [])
    (wo := [(.reg0 0, 32 * n)]) (EffT.mono h (Nat.le_refl _) (fun y hy => .inr ?_) (fun y hy => hy.elim)
    fun y hy => ?_) he hr (by show 4 ≤ stackOf zero; decide)
  · exact Ed25519FePow.inR_of List.mem_cons_self (r0 ▸ hy)
  · obtain ⟨r, hr, o, ho, rfl⟩ := hy
    simp only [List.mem_singleton] at hr; subst hr
    exact region_lt ho

end

/-- `n` elements of zero bytes. -/
def zeroV (n : Nat) (_ : List V) : List V := (List.range n).map fun _ => .b ((List.range 32).map fun _ => 0)

/-- **`m0c_zero`'s adapter** over `ioZeroN n` in build `b`. -/
noncomputable def zeroAd (b : Build) (Rs : Rels) (n : Nat) (hok : zeroOk n = true) :
    AdE Rs (cb := b.codeBytes) (calleeAt zero (ioZeroN n) [0, 1]) :=
  have hn : 0 < n ∧ 32 * n < 2 ^ 32 := by simp only [zeroOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf zero; decide) (zeroN b n hn.2) (fun _ _ _ h => zero_eff hok h) (zeroV n)
    (fun _ _ _ st _ hg _ _ => by
      have h1 : st.regs 1 = BitVec.ofNat 32 (8 * n) := hg.2.2 (1, 8 * n) (by simp [calleeAt, ioZeroN])
      refine ⟨⟨by rw [h1]; unfold Ed25519WordLoop.WordsOk; rw [toNat_8n hn.2]; omega,
        hg.1 0 (by simp [calleeAt, ioZeroN]), by nofun, trivial⟩, h1⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioZeroN, show 32 * n ≠ 0 by omega])
    (fun _ => by simp [rgnsC, calleeAt, ioZeroN])
    fun c sp st m _ vs _ _ hp => by
      obtain ⟨hw, h1⟩ := hp
      simp only [Ed25519WordLoop.wordR, h1, toNat_8n hn.2] at hw
      simp only [OutsRel, calleeAt, ioZeroN, zeroV]
      refine all2_map _ _ _ fun j hj => ?_
      have hj := List.mem_range.mp hj
      simp only [Rel]
      refine Footprint.bytesAt_eq_map fun k hk => ?_
      rw [elem_byte, Frame.byte_of_read32 m (st.regs 0 + BitVec.ofNat 32 (4 * (8 * j + k / 4))) (k % 4) (by omega),
        hw _ (by omega)]
      simp

theorem zeroOk_34 : zeroOk 3 = true ∧ zeroOk 4 = true := by decide +kernel

/-! ## `m0c_copy` -/

/-- The source's elements, read first. -/
def copyIni (n : Nat) : List (SExpr × Nat) := (List.range n).map fun j => rgnE 1 (32 * j) 32

/-- The decided interface checks of `copy` over `ioCopyN n`. -/
def copyOk (n : Nat) : Bool :=
  effOk (ioCopyN n) [(.reg0 0, 32 * n), (.reg0 1, 32 * n)] (copyIni n) [(.reg0 0, 32 * n)] &&
    Ed25519Leaf.regsOk (calleeAt copy (ioCopyN n) [0, 1, 2]) [0, 1, 2] && decide (0 < n ∧ 32 * n < 2 ^ 32)

theorem copy_code : rangesSub (Ed25519WordLoop.wordR copy (Thumb.seqSize (Ed25519WordLoop.wloop []
    Ed25519WordLoop.copyBody 0xfb)) 2 false true (fun _ => True) (fun _ _ b => b) [4]).code (footprint copy) = true := by
  decide +kernel

/-- `m0c_copy` of `8 n` words in build `b`, its count pinned. -/
noncomputable def copyN (b : Build) (n : Nat) (hn : 32 * n < 2 ^ 32) := letI := b.codeBytes
  ((Ed25519WordLoop.copy_te b).pin 2 2 (BitVec.ofNat 32 (8 * n)) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 32 * n⟩])
    (fun s => [⟨s.regs 1, 32 * n⟩])
    (fun s h => by
      show [Footprint.Rgn.mk (s.regs 0) (4 * (s.regs 2).toNat)] = _; rw [h, toNat_8n hn, show 4 * (8 * n) = 32 * n by omega])
    fun s h => by
      show [] ++ [Footprint.Rgn.mk (s.regs 1) (4 * (s.regs 2).toNat)] = _
      rw [h, toNat_8n hn, show 4 * (8 * n) = 32 * n by omega]; rfl).code (footprint copy) copy_code

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The effect of `m0c_copy` of `8 n` words is its callee's. -/
theorem copy_eff {n : Nat} (hok : copyOk n = true) {base : Word} {p : Nat → Word} {tr : List Event}
    (h : Ed25519WordLoop.wloopE false true base (setPub p 2 (BitVec.ofNat 32 (8 * n))) tr) :
    (calleeAt copy (ioCopyN n) [0, 1, 2]).Eff p base tr := by
  simp only [copyOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨he, hr⟩, -, hn⟩ := hok
  have e8 : 8 * ((BitVec.ofNat 32 (8 * n)).toNat / 2) = 32 * n := by rw [toNat_8n hn]; omega
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, e8, true_and, Bool.false_eq_true,
    false_and, false_or] at h
  have r0 : (SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 0 := rfl
  have r1 : (SExpr.reg0 1).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 1 := rfl
  refine Ed25519Leaf.blk_eff (L := [0, 1, 2]) (pc := 0) (fp := [(.reg0 0, 32 * n), (.reg0 1, 32 * n)])
    (ini := copyIni n) (wo := [(.reg0 0, 32 * n)])
    (EffT.mono h (Nat.le_refl _) (fun y hy => .inr ?_) (fun y hy => .inr ?_) fun y hy => ?_) he hr
    (by show 4 ≤ stackOf copy; decide)
  · rcases hy with hy | hy
    · exact Ed25519FePow.inR_of List.mem_cons_self (r0 ▸ hy)
    · exact Ed25519FePow.inR_of (List.mem_cons_of_mem _ List.mem_cons_self) (r1 ▸ hy)
  · have hj : (y - p 1).toNat / 32 < n := by simp only [Region] at hy; omega
    refine Ed25519FePow.inR_of (List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩) ?_
    show ((y - (p 1 + BitVec.ofNat 32 (32 * ((y - p 1).toNat / 32)))).toNat < 32)
    simp only [Region] at hy
    bv_omega
  · obtain ⟨r, hr, o, ho, rfl⟩ := hy
    simp only [List.mem_singleton] at hr; subst hr
    exact region_lt ho

end

/-- **`m0c_copy`'s adapter** over `ioCopyN n` in build `b`: the values carried over. -/
noncomputable def copyAdN (b : Build) (Rs : Rels) (n : Nat) (hok : copyOk n = true) :
    AdE Rs (cb := b.codeBytes) (calleeAt copy (ioCopyN n) [0, 1, 2]) :=
  have hn : 0 < n ∧ 32 * n < 2 ^ 32 := by simp only [copyOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf copy; decide) (copyN b n hn.2) (fun _ _ _ h => copy_eff hok h) id
    (fun _ _ _ st _ hg _ _ => by
      have h2 : st.regs 2 = BitVec.ofNat 32 (8 * n) := hg.2.2 (2, 8 * n) (by simp [calleeAt, ioCopyN])
      refine ⟨⟨by rw [h2]; unfold Ed25519WordLoop.WordsOk; rw [toNat_8n hn.2]; omega,
        hg.1 0 (by simp [calleeAt, ioCopyN]), fun _ => ⟨hg.1 1 (by simp [calleeAt, ioCopyN]), ?_⟩, trivial⟩, h2⟩
      rw [h2, toNat_8n hn.2, show 4 * (8 * n) = 32 * n by omega]
      exact hg.2.1 (0, 1, 32 * n) (by simp [calleeAt, ioCopyN]))
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioCopyN, show 32 * n ≠ 0 by omega])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioCopyN, show 32 * n ≠ 0 by omega])
    fun c sp st m _ vs _ hi hp => by
      obtain ⟨hw, h2⟩ := hp
      simp only [Ed25519WordLoop.wordR, h2, toNat_8n hn.2] at hw
      simp only [InsRel, calleeAt, ioCopyN] at hi
      simp only [OutsRel, calleeAt, ioCopyN, id]
      refine all2_mono _ _ _ vs (fun j hj v hr => ?_) hi
      have hj := List.mem_range.mp hj
      have hf : feVal m (st.regs 0 + BitVec.ofNat 32 (32 * j)) = feVal st.mem (st.regs 1 + BitVec.ofNat 32 (32 * j)) := by
        unfold feVal; congr 1; apply List.map_congr_left; intro i hi
        have := List.mem_range.mp hi
        rw [elem_word, elem_word, hw _ (by omega)]
      cases v <;> simp only [Rel, In.kd] at hr ⊢
      rw [hf]; exact hr

theorem copyOk_23 : copyOk 2 = true ∧ copyOk 3 = true := by decide +kernel

/-- `m0c_copy` of two and of three elements. -/
noncomputable def copyAd2 (b : Build) (Rs : Rels) := copyAdN b Rs 2 copyOk_23.1
noncomputable def copyAd3 (b : Build) (Rs : Rels) := copyAdN b Rs 3 copyOk_23.2

end M0Crypto.Release.Ed25519WordAd
