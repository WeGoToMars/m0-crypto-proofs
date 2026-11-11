import M0Crypto.Release.ConstantTime.StateSem

/-! Integer offsets in one narrow stack window have unique 32-bit representations. -/
namespace M0Crypto.Release.ConstantTime

/-- Equal 32-bit encodings of offsets in the same sub-word window imply equal offsets. -/
theorem ofInt32_injective_on_win (w : StackWindow) (x y : Int)
    (hwidth : w.below + w.above < 2 ^ 32)
    (hxlo : -(w.below : Int) ≤ x) (hxhi : x < (w.above : Int))
    (hylo : -(w.below : Int) ≤ y) (hyhi : y < (w.above : Int))
    (heq : BitVec.ofInt 32 x = BitVec.ofInt 32 y) : x = y := by
  have hmod : x.bmod (2 ^ 32) = y.bmod (2 ^ 32) := by
    have := congrArg BitVec.toInt heq
    simpa only [BitVec.toInt_ofInt] using this
  have hb : 0 < (2 : Nat) ^ 32 := Nat.pow_pos (by decide)
  have hbI : 0 < (2 : Int) ^ 32 := Int.pow_pos (by decide)
  have ⟨_, _, hdivx⟩ := (Int.bmod_eq_iff hb).mp hmod
  have ⟨_, _, hdivy⟩ := (Int.bmod_eq_iff hb).mp hmod.symm
  have hdiv : (2 : Int) ^ 32 ∣ x - y := by
    have h1 : (2 : Int) ^ 32 ∣ (y.bmod (2 ^ 32) - y) := by
      simpa [hmod, Int.natCast_pow] using hdivy
    have h2 : (2 : Int) ^ 32 ∣ (y.bmod (2 ^ 32) - x) := by
      simpa [Int.natCast_pow] using hdivx
    have hsub := Int.dvd_sub h1 h2
    have hrewrite : y.bmod (2 ^ 32) - y - (y.bmod (2 ^ 32) - x) = x - y := by omega
    rw [hrewrite] at hsub
    exact hsub
  have hxy : x - y < 2 ^ 32 := by
    have : x - y < (w.above : Int) - -(w.below : Int) := by omega
    have hwidthI : (w.below : Int) + w.above < (2 : Int) ^ 32 := by
      simpa [Int.natCast_pow] using (Int.ofNat_lt.mpr hwidth)
    omega
  have hyx : y - x < 2 ^ 32 := by
    have : y - x < (w.above : Int) - -(w.below : Int) := by omega
    have hwidthI : (w.below : Int) + w.above < (2 : Int) ^ 32 := by
      simpa [Int.natCast_pow] using (Int.ofNat_lt.mpr hwidth)
    omega
  rcases hdiv with ⟨k, hk⟩
  have hk0 : k = 0 := by
    by_cases hkzero : k = 0
    · exact hkzero
    · have hn : k ≠ 0 := hkzero
      have hkpos : 0 < k ∨ k < 0 := by omega
      rcases hkpos with hp | hn
      · have hkm : k * (2 : Int) ^ 32 = x - y := by
          rw [Int.mul_comm, hk]
        have hm := Int.mul_le_mul_of_nonneg_right
          (show (1 : Int) ≤ k by omega) (Int.le_of_lt hbI)
        rw [hkm] at hm
        have hbound : (2 : Int) ^ 32 ≤ x - y := by
          simpa [Int.one_mul] using hm
        omega
      · have hkm : k * (2 : Int) ^ 32 = x - y := by
          rw [Int.mul_comm, hk]
        have hm := Int.mul_le_mul_of_nonneg_right
          (show k ≤ -1 by omega) (Int.le_of_lt hbI)
        have hm' : x - y ≤ -(2 : Int) ^ 32 := by
          rw [← hkm]
          simpa using hm
        have : (2 : Int) ^ 32 ≤ y - x := by omega
        omega
  rw [hk0] at hk
  omega

end M0Crypto.Release.ConstantTime
