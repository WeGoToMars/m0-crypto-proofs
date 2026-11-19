import SafegcdTermination.Residue
import SafegcdRow.Arithmetic
import SafegcdRow.Fold

namespace SafegcdTermination.FoldRefine

open SafegcdRow
open SafegcdRow.FoldCode
open M0Crypto.Armv6M (Mem read32 slot)
open M0Crypto.Release.Frame (read32_write32_slot' read32_storeWords_same)
open M0Crypto.Thumb (storeWords)

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def vec (m : Mem) (a : Word) (i : Nat) : Word := read32 m (slot a i)

def value (m : Mem) (a : Word) : Int := weighted (limb (vec m a)) 17

def reduced (m : Mem) (a : Word) (i : Nat) : Int := (vec (truncated m a) a i).toNat

def high (m : Mem) (a : Word) : Int := 2*(vec m a 16).toInt + (vec m a 15).toNat / 32768

private theorem truncate_nat (x : Word) : (truncate x).toNat = x.toNat % 32768 := by
  simp only [truncate, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.reducePow]
  omega

private theorem truncated_word (m : Mem) (a : Word) (i : Nat) (hi : i < 16) :
    vec (truncated m a) a i = if i = 15 then truncate (vec m a 15) else vec m a i := by
  simp only [vec, truncated]
  exact read32_write32_slot' _ _ _ 15 i (by decide) (by omega) |>.trans (by
    by_cases h : i = 15
    · subst i; rfl
    · simp [h, Ne.symm h])

private theorem reduced_range (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) (i : Nat) (hi : i < 16) :
    0 ≤ reduced m a i ∧ reduced m a i < radix := by
  unfold reduced
  rw [truncated_word _ _ _ hi]
  split
  · rw [truncate_nat]
    unfold radix
    omega
  · exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (h.1 i hi)⟩

private theorem weighted_range {f : Nat → Int} (n : Nat) (h : ∀ i < n, 0 ≤ f i ∧ f i < radix) :
    0 ≤ weighted f n ∧ weighted f n < radix^n := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    obtain ⟨hl, hu⟩ := ih fun i hi => h i (by omega)
    have hrl : 0 < radix := by decide
    have hn : 0 < radix^n := Int.pow_pos hrl
    have hf := h n (by omega)
    have hu' := Int.mul_le_mul_of_nonneg_left (show f n ≤ radix - 1 by omega) (Int.le_of_lt hn)
    rw [weighted, Int.pow_succ]
    constructor
    · exact Int.add_nonneg hl (Int.mul_nonneg (Int.le_of_lt hn) hf.1)
    · rw [Int.mul_sub, Int.mul_one] at hu'
      omega

theorem chopped (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) :
    let q := weighted (reduced m a) 16
    q = value m a % foldRadix ∧ high m a = value m a / foldRadix := by
  have hr : weighted (reduced m a) 15 = weighted (limb (vec m a)) 15 := by
    apply weighted_congr
    intro i hi
    simp [reduced, limb, truncated_word _ _ _ (by omega : i < 16), show i ≠ 15 by omega,
      show i < 16 by omega]
  have h15 : reduced m a 15 = ((vec m a 15).toNat : Int) % 32768 := by
    unfold reduced
    rw [truncated_word _ _ _ (by decide), ite_eq_left rfl, truncate_nat]
    omega
  have hl : 0 ≤ weighted (reduced m a) 16 ∧ weighted (reduced m a) 16 < foldRadix := by
    have ⟨hl, hu⟩ := weighted_range 15 (fun i hi => reduced_range m a h i (by omega))
    rw [show weighted (reduced m a) 16 = weighted (reduced m a) 15 + radix^15 * reduced m a 15 from rfl, h15]
    change _ ∧ weighted (reduced m a) 15 + (radix^15)*_ < foldRadix
    have hlim : radix^15 * 32768 = foldRadix := by decide +kernel
    have hp : 0 < radix^15 := by decide
    constructor
    · exact Int.add_nonneg hl (Int.mul_nonneg (Int.le_of_lt hp) (Int.emod_nonneg _ (by decide)))
    · rw [← hlim]
      have he := Int.mul_le_mul_of_nonneg_left
        (show ((vec m a 15).toNat : Int) % 32768 ≤ 32768-1 by omega) (Int.le_of_lt hp)
      rw [Int.mul_sub, Int.mul_one] at he
      omega
  have he : weighted (reduced m a) 16 + foldRadix * high m a = value m a := by
    rw [show weighted (reduced m a) 16 = weighted (reduced m a) 15 + radix^15 * reduced m a 15 from rfl,
      h15, hr]
    change _ = (weighted (limb (vec m a)) 15 + radix^15 * limb (vec m a) 15) + radix^16 * limb (vec m a) 16
    simp only [limb, show 15 < 16 by decide, Nat.lt_irrefl, ite_true, ite_false, high]
    have hz := Int.emod_add_mul_ediv ((vec m a 15).toNat : Int) 32768
    have h1 : foldRadix = radix^15 * 32768 := by decide +kernel
    have h2 : radix^16 = 2 * (radix^15 * 32768) := by decide +kernel
    rw [h1, h2]
    grind only
  obtain ⟨hD, hM⟩ := (Int.ediv_emod_unique (by decide : 0 < foldRadix)).mpr ⟨he, hl.1, hl.2⟩
  exact ⟨hM.symm, hD.symm⟩

def carryInt (m : Mem) (a : Word) : Nat → Int
  | 0 => 19 * high m a
  | i+1 => (carryInt m a i + reduced m a i) / radix

def digitInt (m : Mem) (a : Word) (i : Nat) : Int :=
  (carryInt m a i + reduced m a i) % radix

private theorem spill_word (m : Mem) (a : Word) : spill m a = BitVec.ofInt 32 (high m a) := by
  unfold spill high
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt]
  have hhi : read32 m (slot a 16) * BitVec.twoPow 32 1 = BitVec.ofInt 32 2 * vec m a 16 := by
    unfold vec
    rw [BitVec.mul_comm]
    rfl
  rw [hhi]
  congr 1
  apply BitVec.eq_of_toNat_eq
  change (read32 m (slot a 15) >>> 15).toNat =
    (BitVec.ofInt 32 ((read32 m (slot a 15)).toNat / 32768 : Int)).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

private theorem carry_bound (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) (i : Nat) (hi : i ≤ 16) :
    -2500000 ≤ carryInt m a i ∧ carryInt m a i ≤ 2500000 := by
  induction i with
  | zero =>
    have ht := h.2
    have hb := h.1 15 (by decide)
    simp only [carryInt, high]
    omega
  | succ i ih =>
    obtain ⟨hl, hu⟩ := ih (by omega)
    have hb := reduced_range m a h i (by omega)
    unfold carryInt
    unfold radix at hb ⊢
    omega

theorem carry_matches (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) (i : Nat) (hi : i ≤ 16) :
    incoming m a i = BitVec.ofInt 32 (carryInt m a i) := by
  induction i with
  | zero =>
    rw [incoming, spill_word, carryInt, BitVec.ofInt_mul]
    rfl
  | succ i ih =>
    have hb := carry_bound m a h i (by omega)
    have hw := reduced_range m a h i (by omega)
    have ha : signed32 (carryInt m a i + reduced m a i) := by
      unfold signed32 radix at *
      omega
    rw [incoming, ih (by omega)]
    have hr : vec (truncated m a) a i = BitVec.ofInt 32 (reduced m a i) := by simp [reduced]
    change carry (BitVec.ofInt 32 (carryInt m a i) + vec (truncated m a) a i) = _
    rw [hr, ← BitVec.ofInt_add, carry_int _ ha]
    rfl

private theorem digit_matches (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) (i : Nat) (hi : i < 16) :
    ((outDigit m a i).toNat : Int) = digitInt m a i := by
  unfold outDigit
  have hr : BitVec.ofInt 32 (reduced m a i) = vec (truncated m a) a i := by simp [reduced]
  rw [carry_matches m a h i (by omega)]
  change ((low (BitVec.ofInt 32 (carryInt m a i) + vec (truncated m a) a i)).toNat : Int) = _
  rw [← hr, ← BitVec.ofInt_add, low_int, digitInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem carried (m : Mem) (a : Word) (n : Nat) :
    weighted (digitInt m a) n + radix^n * carryInt m a n =
      weighted (reduced m a) n + 19 * high m a := by
  induction n with
  | zero => simp [weighted, carryInt]
  | succ n ih =>
    have hz := Int.emod_add_mul_ediv (carryInt m a n + reduced m a n) radix
    change digitInt m a n + radix * carryInt m a (n+1) = carryInt m a n + reduced m a n at hz
    simp only [weighted, Int.pow_succ]
    grind only

theorem folded_value (m : Mem) (a : Word) (h : VecWellFormed (vec m a)) :
    value (foldedMemory m a) a = SafegcdTermination.fold (value m a) := by
  have h16 : vec (foldedMemory m a) a 16 = incoming m a 16 := by
    unfold vec foldedMemory
    exact M0Crypto.Armv6M.read32_write32_same _ _ _
  have hTop : limb (vec (foldedMemory m a) a) 16 = carryInt m a 16 := by
    unfold limb
    rw [ite_eq_right (by decide : ¬16 < 16), h16, carry_matches _ _ h 16 (by decide)]
    apply int_of_word
    have hb := carry_bound m a h 16 (by decide)
    unfold signed32
    omega
  have hLo : weighted (limb (vec (foldedMemory m a) a)) 16 = weighted (digitInt m a) 16 := by
    apply weighted_congr
    intro i hi
    have hl : vec (foldedMemory m a) a i = outDigit m a i := by
      have hr := read32_write32_slot' (foldPrefix m a 16) a (incoming m a 16) 16 i (by decide) (by omega)
      unfold vec foldedMemory
      rw [hr, ite_eq_right (by omega : ¬16 = i)]
      unfold foldPrefix slot
      have hlen : i < ((List.range 16).map (outDigit m a)).length := by simpa using hi
      have hsize : ((List.range 16).map (outDigit m a)).length ≤ 2^28 := by simp
      simpa only [List.getElem_map, List.getElem_range] using
        read32_storeWords_same (truncated m a) a ((List.range 16).map (outDigit m a)) i hlen hsize
    simp only [limb, hi, ite_true, hl]
    exact digit_matches m a h i hi
  have hc := chopped m a h
  change weighted (limb (vec (foldedMemory m a) a)) 16 +
      radix^16 * limb (vec (foldedMemory m a) a) 16 = _
  rw [hLo, hTop, carried, hc.1, hc.2]
  rfl

end SafegcdTermination.FoldRefine
