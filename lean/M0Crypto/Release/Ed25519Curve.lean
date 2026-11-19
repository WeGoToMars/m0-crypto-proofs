import M0Crypto.Release.Ed25519Field
import M0Crypto.Release.Ed25519EdwardsComplete

/-!
The Ed25519 curve `-x² + y² = 1 + d x² y²` over `F_p` (RFC 8032 section 5.1), and its
completeness.

`d = -121665 / 121666` is not a square, by Euler's criterion: `d ^ ((p - 1) / 2) = -1`,
evaluated in the kernel. `a = -1` is the square of `sqrtM1 = 2 ^ ((p - 1) / 4)`, also
evaluated. So `complete : Complete (-1) d`, and the group laws of
`Ed25519EdwardsComplete` hold on the curve without side conditions.
-/

namespace M0Crypto.Release.Ed25519Curve

open Lean.Grind M0Crypto.Release.Ed25519PrimeCert M0Crypto.Release.Ed25519Field
open M0Crypto.Release.Ed25519Edwards M0Crypto.Release.Ed25519EdwardsComplete

/-- The curve constant `d = -121665 / 121666` of RFC 8032 section 5.1. -/
def d : Fp := -121665 / 121666

theorem d_eq : d = 37095705934669439343138083508754565189542113879843219016388785533085940283555 := by
  decide +kernel

/-- A square root of `-1` (RFC 8032 section 5.1.3): `2 ^ ((p - 1) / 4)`. -/
def sqrtM1 : Fp := 2 ^ ((p - 1) / 4)

theorem sqrtM1_eq :
    sqrtM1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752 := by
  decide +kernel

theorem sqrtM1_sq : sqrtM1 * sqrtM1 = -1 := by decide +kernel

/-- Euler's criterion, one direction: `x ^ ((p - 1) / 2) = -1` makes `x` a non-square. -/
theorem nonsq_of_euler {x : Fp} (h : x ^ ((p - 1) / 2) = -1) : ∀ t : Fp, t * t ≠ x := by
  intro t ht
  subst ht
  have ht : t ≠ 0 := by
    rintro rfl
    rw [Semiring.mul_zero, zero_pow (by decide)] at h
    exact absurd h (by decide)
  rw [← Semiring.pow_two, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by decide,
    pow_p_sub_one ht] at h
  exact absurd h (by decide)

theorem d_euler : d ^ ((p - 1) / 2) = -1 := by decide +kernel

theorem d_nonsq : ∀ t : Fp, t * t ≠ d := nonsq_of_euler d_euler

/-- The Ed25519 curve is complete. -/
theorem complete : Complete (-1 : Fp) d where
  sq_a := ⟨sqrtM1, sqrtM1_sq⟩
  nonsq_d := d_nonsq
  two_ne_zero := by decide

/-- A point of the Ed25519 curve. -/
abbrev OnEd25519 (P : Point Fp) : Prop := OnCurve (-1) d P

/-- Ed25519 point addition (RFC 8032 section 5.1.4). -/
abbrev edAdd (P Q : Point Fp) : Point Fp := add (-1) d P Q

theorem edAdd_comm (P Q : Point Fp) : edAdd P Q = edAdd Q P := add_comm _ _ P Q

theorem edAdd_zero (P : Point Fp) : edAdd P zero = P := add_zero _ _ P

theorem onEd25519_add {P Q : Point Fp} (hP : OnEd25519 P) (hQ : OnEd25519 Q) :
    OnEd25519 (edAdd P Q) :=
  Ed25519EdwardsComplete.onCurve_add complete hP hQ

theorem edAdd_assoc {P Q R : Point Fp} (hP : OnEd25519 P) (hQ : OnEd25519 Q)
    (hR : OnEd25519 R) : edAdd (edAdd P Q) R = edAdd P (edAdd Q R) :=
  Ed25519EdwardsComplete.add_assoc complete hP hQ hR

theorem edAdd_neg {P : Point Fp} (hP : OnEd25519 P) : edAdd P (neg P) = zero :=
  Ed25519EdwardsComplete.add_neg complete hP

end M0Crypto.Release.Ed25519Curve
