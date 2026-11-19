import SafegcdTermination.FoldRefine

namespace SafegcdTermination.Vectors

open SafegcdRow
open SafegcdTermination.FoldRefine (vec value)
open M0Crypto.Armv6M (Mem)
open SafegcdRow.FoldCode (foldedMemory outDigit incoming foldPrefix truncated)
open M0Crypto.Release.Frame (read32_storeWords_same read32_write32_slot')
open M0Crypto.Thumb (storeWords)

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

def LowLimbs (m : Mem) (a : Word) : Prop := ∀ i < 16, (vec m a i).toNat < 65536

theorem field_top (m : Mem) (a : Word) (hl : LowLimbs m a) :
    (vec m a 16).toInt = value m a / radix^16 := by
  have hN : 0 < radix ^ 16 := by decide
  have range (n : Nat) (hn : n ≤ 16) :
      0 ≤ weighted (limb (vec m a)) n ∧ weighted (limb (vec m a)) n < radix^n := by
    induction n with
    | zero => simp [weighted]
    | succ n ih =>
      obtain ⟨hb, ht⟩ := ih (by omega)
      have hp : 0 < radix^n := Int.pow_pos (by decide : 0 < radix)
      have hI : limb (vec m a) n ≤ radix - 1 := by
        have h := hl n (by omega)
        simp only [limb, radix, show n < 16 by omega, ite_true]
        omega
      have hnI : 0 ≤ limb (vec m a) n := by simp [limb, show n < 16 by omega]
      rw [weighted, Int.pow_succ]
      refine ⟨Int.add_nonneg hb (Int.mul_nonneg (Int.le_of_lt hp) hnI), ?_⟩
      have hM := Int.mul_le_mul_of_nonneg_left hI (Int.le_of_lt hp)
      rw [Int.mul_sub, Int.mul_one] at hM
      omega
  have heq : weighted (limb (vec m a)) 16 + radix^16 * (vec m a 16).toInt = value m a := by
    rfl
  have ⟨hlo, hhi⟩ := range 16 (by decide)
  exact ((Int.ediv_emod_unique hN).mpr ⟨heq, hlo, hhi⟩).1.symm

theorem well_formed_of_range (m : Mem) (a : Word) (hl : LowLimbs m a)
    (hlo : -2 * foldRadix ≤ value m a) (hhi : value m a < 3 * foldRadix) :
    VecWellFormed (vec m a) := by
  refine ⟨hl, ?_⟩
  rw [field_top m a hl]
  have hN : 0 < radix^16 := by decide
  have h₁ : (-1 : Int) * radix^16 = -2 * foldRadix := by decide +kernel
  have h₂ : (2 : Int) * radix^16 ≥ 3 * foldRadix := by decide +kernel
  have hL : -1 ≤ value m a / radix^16 := (Int.le_ediv_iff_mul_le hN).mpr (by rw [h₁]; exact hlo)
  have hH := (Int.ediv_lt_iff_lt_mul hN).mpr (Int.lt_of_lt_of_le hhi h₂)
  omega

theorem folded_low (m : Mem) (a : Word) : LowLimbs (foldedMemory m a) a := by
  intro i hi
  have hr := read32_write32_slot' (foldPrefix m a 16) a (incoming m a 16) 16 i (by decide) (by omega)
  unfold vec foldedMemory
  rw [hr, ite_eq_right (by omega : ¬16 = i)]
  unfold foldPrefix M0Crypto.Armv6M.slot
  have hlen : i < ((List.range 16).map (outDigit m a)).length := by simpa using hi
  have hs : ((List.range 16).map (outDigit m a)).length ≤ 2^28 := by simp
  have hget := read32_storeWords_same (truncated m a) a ((List.range 16).map (outDigit m a)) i hlen hs
  rw [List.getElem_map, List.getElem_range] at hget
  rw [hget]
  exact low_bound _

theorem weighted_congr_low (f : Nat → Int) (n : Nat) :
    weighted f (n+2) ≡ weighted f 2 [ZMOD radix^2] := by
  induction n with
  | zero => exact Congruence.refl _
  | succ n ih =>
    change weighted f (n+2) + radix^(n+2) * f (n+2) ≡ _ [ZMOD radix^2]
    have hm : radix^(n+2) * f (n+2) ≡ 0 [ZMOD radix^2] := by
      rw [Congruence.zero_iff_dvd, Int.pow_add, Int.mul_comm (radix^n), Int.mul_assoc]
      exact Int.dvd_mul_right _ _
    simpa only [Int.add_zero] using ih.add hm

theorem value_low (m : Mem) (a : Word) :
    value m a ≡ (vec m a 0).toNat + radix * (vec m a 1).toNat [ZMOD radix^2] := by
  simpa only [value, limb, weighted, Int.pow_zero, Int.pow_one, Int.one_mul, Int.zero_add,
    show 0 < 16 by decide, show 1 < 16 by decide, ite_true] using
    weighted_congr_low (limb (vec m a)) 15

theorem value_low_correction (m : Mem) (a : Word) :
    ((vec m a 0).toNat : Int) ≡ value m a [ZMOD batchScale] := by
  have hm : batchScale ∣ radix^2 := by decide +kernel
  have hd : batchScale ∣ radix := by decide
  have h := (value_low m a).of_dvd hm
  have hz : radix * ((vec m a 1).toNat : Int) ≡ 0 [ZMOD batchScale] :=
    Congruence.zero_iff_dvd.mpr (Int.dvd_mul_of_dvd_left hd)
  exact (h.trans (by simpa only [Int.add_zero] using (Congruence.refl ((vec m a 0).toNat : Int)).add hz)).symm

theorem value_low_word (m : Mem) (a : Word) (hl : LowLimbs m a) :
    vec m a 0 ||| (vec m a 1 <<< 16) = BitVec.ofInt 32 (value m a) := by
  have hl₀ := hl 0 (by decide)
  have hAnd : vec m a 0 &&& (vec m a 1 <<< 16) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    by_cases ht : i < 16
    · simp [ht]
    · have hn := Nat.lt_of_lt_of_le hl₀ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 16 ≤ i))
      rw [show (vec m a 0).getLsbD i = false from Nat.testBit_lt_two_pow hn]
      simp
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hAnd, BitVec.shiftLeft_eq_mul_twoPow]
  have e : BitVec.twoPow 32 16 = BitVec.ofInt 32 radix := rfl
  rw [e, ← BitVec.ofInt_toInt (x := vec m a 0), ← BitVec.ofInt_toInt (x := vec m a 1),
    ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  have u (i : Nat) (hi : i < 16) : (vec m a i).toInt = (vec m a i).toNat := by
    have h := hl i hi
    rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega : 2 * (vec m a i).toNat < 2^32)]
  rw [u 0 (by decide), u 1 (by decide), Int.mul_comm _ radix]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  exact congrArg Int.toNat (value_low m a).symm

end SafegcdTermination.Vectors
