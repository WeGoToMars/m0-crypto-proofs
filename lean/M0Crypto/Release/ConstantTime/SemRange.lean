import M0Crypto.Release.ConstantTime.Domain

/-! Sound bounds for the affine range used by the CT domain. -/
namespace M0Crypto.Release.ConstantTime

/-- Every value `c + k * n` with `n` between `l` and `h` lies in `lnkRange`.
This handles both signs of `k`; the range endpoints are ordered accordingly. -/
theorem lnkRange_sound (k c : Int) (l n h : Nat)
    (hln : l ≤ n) (hnh : n ≤ h) :
    (AbsState.lnkRange k c l h).1 ≤ c + k * (n : Int) ∧
      c + k * (n : Int) ≤ (AbsState.lnkRange k c l h).2 := by
  unfold AbsState.lnkRange
  split
  · rename_i hk
    have hlnI : (l : Int) ≤ (n : Int) := by exact_mod_cast hln
    have hnhI : (n : Int) ≤ (h : Int) := by exact_mod_cast hnh
    have h1 := Int.mul_le_mul_of_nonneg_left hlnI hk
    have h2 := Int.mul_le_mul_of_nonneg_left hnhI hk
    have h1' : k * (l : Int) ≤ k * (n : Int) := by
      simpa only [Int.mul_comm] using h1
    have h2' : k * (n : Int) ≤ k * (h : Int) := by
      simpa only [Int.mul_comm] using h2
    constructor <;> omega
  · rename_i hk
    have hk' : k ≤ 0 := by omega
    have hlnI : (l : Int) ≤ (n : Int) := by exact_mod_cast hln
    have hnhI : (n : Int) ≤ (h : Int) := by exact_mod_cast hnh
    have h1 := Int.mul_le_mul_of_nonpos_left hk' hnhI
    have h2 := Int.mul_le_mul_of_nonpos_left hk' hlnI
    have h1' : k * (h : Int) ≤ k * (n : Int) := by
      simpa only [Int.mul_comm] using h1
    have h2' : k * (n : Int) ≤ k * (l : Int) := by
      simpa only [Int.mul_comm] using h2
    constructor <;> omega

end M0Crypto.Release.ConstantTime
