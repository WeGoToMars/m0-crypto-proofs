import M0Crypto.Release.AeadMac
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
Address bookkeeping for the AEAD stack window `[A - 64, A + 144)` and the
straight-line effects of the `MAC_PADDED` tail.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (accAt keyAt keyAtOK wordAt)

/-- Byte `o` of the window. -/
def W (A : Word) (o : Nat) : Word := A - 64#32 + BitVec.ofNat 32 o

theorem W_add (A : Word) (k j : Nat) : A + BitVec.ofNat 32 k + BitVec.ofNat 32 j = W A (64 + k + j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [W, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ctxW (A : Word) (i k : Nat) :
    A + 8#32 + BitVec.ofNat 32 i + BitVec.ofNat 32 k = W A (72 + i + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [W, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem W_eq (A : Word) (o : Nat) : A - 64#32 + BitVec.ofNat 32 o = W A o := rfl

/-- Offsets of `MacWr` inside the window. -/
def MacOff (o : Nat) : Prop := o < 64 ∨ (72 ≤ o ∧ o < 92) ∨ (136 ≤ o ∧ o < 152)

theorem macWr_W {A y : Word} (h : MacWr A y) : ∃ o, MacOff o ∧ y = W A o := by
  rcases h with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · exact ⟨o, .inl ho, rfl⟩
  · refine ⟨64 + 8 + o, .inr (.inl ⟨by omega, by omega⟩), ?_⟩
    rw [← W_add]
  · refine ⟨64 + 72 + o, .inr (.inr ⟨by omega, by omega⟩), ?_⟩
    rw [← W_add]

theorem W_macWr {A : Word} {o : Nat} (h : MacOff o) : MacWr A (W A o) := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨o, h, rfl⟩
  · refine .inr (.inl ⟨o - 72, by omega, ?_⟩)
    rw [show (8#32 : Word) = BitVec.ofNat 32 8 from rfl, W_add]; congr 1; omega
  · refine .inr (.inr ⟨o - 136, by omega, ?_⟩)
    rw [show (72#32 : Word) = BitVec.ofNat 32 72 from rfl, W_add]; congr 1; omega

namespace MacEnv
variable {base A d n : Word} {M : Mem} (he : MacEnv base A d n M)
include he

theorem W_toNat (o : Nat) (ho : o < 208) : (W A o).toNat = A.toNat - 64 + o := by
  have := he.aLo; have := he.aHi
  simp only [W, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem W_inj {o o' : Nat} (ho : o < 208) (ho' : o' < 208) (h : W A o = W A o') : o = o' := by
  have := congrArg BitVec.toNat h
  rw [he.W_toNat o ho, he.W_toNat o' ho'] at this; omega

omit he in
/-- Bytes of a buffer disjoint from the window are outside `MacWr`. -/
theorem not_macWr {a : Word} {l i : Nat} (hd : Disj a l (A - 64#32) 208) (hi : i < l) :
    ¬ MacWr A (a + BitVec.ofNat 32 i) := by
  intro h
  obtain ⟨o, ho, e⟩ := macWr_W h
  have ho' : o < 208 := by rcases ho with h | h | h <;> omega
  exact ne_of_disj hd.1 hd.2.1 hd.2.2 hi ho' e

/-- Window bytes `[92, 136)` (context words 5..15) and `[64, 72)` are outside `MacWr`. -/
theorem W_not_macWr {o : Nat} (ho : o < 208) (h : ¬ MacOff o) : ¬ MacWr A (W A o) := by
  intro hw
  obtain ⟨o', ho', e⟩ := macWr_W hw
  have ho'' : o' < 208 := by rcases ho' with h | h | h <;> omega
  rw [he.W_inj ho ho'' e] at h; exact h ho'

/-- Context words 5..15 (key, precomputed s words, pad) are untouched by `MAC_PADDED`. -/
theorem ctx_word {m1 m2 : Mem} (hf : ∀ y, ¬ MacWr A y → m1 y = m2 y) (j : Nat) (h5 : 5 ≤ j) (h16 : j < 16) :
    wordAt m1 (A + 8#32) j = wordAt m2 (A + 8#32) j := by
  unfold wordAt; congr 1
  apply read32_congr
  intro k hk
  rw [slot, ctxW]
  exact hf _ (he.W_not_macWr (by omega) (by unfold MacOff; omega))

end MacEnv

end M0Crypto.Release.Aead
