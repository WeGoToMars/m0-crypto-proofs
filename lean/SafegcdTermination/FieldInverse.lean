import SafegcdTermination.Inversion
import M0Crypto.Release.Ed25519PrimeCert

namespace SafegcdTermination

open M0Crypto.Release

theorem coprime_canonical {z : Int} (hz : 0 < z) (hr : z < p) : p.gcd z = 1 := by
  have hP : M0Crypto.Release.Ed25519Prime.Prime p.toNat := Ed25519PrimeCert.prime_p
  have ht : p.natAbs = p.toNat := by omega
  rw [Int.gcd_eq_natAbs_gcd_natAbs, ht]
  obtain h | h := hP.2 _ (Nat.gcd_dvd_left p.toNat z.natAbs)
  · exact h
  · have hdvd := Nat.gcd_dvd_right p.toNat z.natAbs
    rw [h, show z.natAbs = z.toNat by omega] at hdvd
    have hbound := Nat.le_of_dvd (show 0 < z.toNat by omega) hdvd
    omega

/-- The fixed 43-batch arithmetic computes the existing inversion specification.
This includes the library's zero convention. -/
theorem inverse_power {z : Int} (hz : 0 ≤ z) (hr : z < p) :
    inverse z ≡ z ^ (p.toNat - 2) [ZMOD p] := by
  by_cases hz0 : z = 0
  · subst z
    rw [inverse_zero, Int.zero_pow (show p.toNat - 2 ≠ 0 by decide)]
    exact Congruence.refl _
  · have hc := coprime_canonical (show 0 < z by omega) hr
    have hinv := inverse_correct hz hr hc
    have hnat : z.toNat % p.toNat ≠ 0 := by
      rw [Nat.mod_eq_of_lt (show z.toNat < p.toNat by omega)]
      omega
    have hf : z.toNat ^ (p.toNat - 1) % p.toNat = 1 :=
      Ed25519PrimeCert.fermat_p z.toNat hnat
    have hp' : ((p.toNat : Nat) : Int) = p := Int.toNat_of_nonneg (Int.le_of_lt p_pos)
    have hz' : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg hz
    have hpow : z ^ (p.toNat - 2) * z ≡ 1 [ZMOD p] := by
      rw [← Int.pow_succ, show (p.toNat - 2).succ = p.toNat - 1 by decide]
      change z ^ (p.toNat - 1) % p = 1 % p
      have h := congrArg (fun n : Nat => (n : Int)) hf
      simpa only [Int.natCast_pow, Int.natCast_emod, Int.natCast_one, hz', hp',
        show (1 : Int) % p = 1 by decide] using h
    have hs := hinv.trans hpow.symm
    rw [Congruence.iff_dvd, ← Int.sub_mul] at hs
    exact Congruence.iff_dvd.mpr (by
      simpa only [hc, Int.natCast_one, Int.mul_one] using Int.dvd_mul_gcd_iff_dvd_mul.mpr hs)

theorem inverse_reduced_power (z : Int) : inverse (z % p) ≡ z ^ (p.toNat - 2) [ZMOD p] := by
  have h₁ := inverse_power (Int.emod_nonneg z (Int.ne_of_gt p_pos)) (Int.emod_lt_of_pos z p_pos)
  have h₂ : z % p ≡ z [ZMOD p] := Congruence.emod_left z p
  exact h₁.trans (h₂.pow _)

end SafegcdTermination
