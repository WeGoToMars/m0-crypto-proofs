import M0Crypto.Release.Ed25519PrimeCert

/-!
The field `F_p`, `p = 2^255 - 19`: `Fin p` with core's commutative ring structure and
the inverse `x⁻¹ = x ^ (p - 2)` (`inv_zero` holds as `0 ^ (p - 2) = 0`). The field laws
come from Fermat's little theorem at `p` (`Ed25519PrimeCert.fermat_p`).

Powers in `Fp` are `Nat.powMod` (core's `Fin` powers), so closed facts such as Euler's criterion for a constant
evaluate in the kernel (`decide +kernel`).

`Fp` is a `def`, not an `abbrev`, so instance search does not see `Fin p` through it: `Fp` has
only the instances declared here. Its `Div` is the field division `x * y⁻¹`, the one
`Field Fp` carries. Core's `Div (Fin n)`, which divides representatives as natural numbers,
applies to `Fin p` but never to `Fp`.
-/

namespace M0Crypto.Release.Ed25519Field

open Lean.Grind M0Crypto.Release.Ed25519Prime M0Crypto.Release.Ed25519PrimeCert

instance : NeZero p := ⟨by decide⟩

/-- `ℤ / pℤ` for `p = 2^255 - 19`. -/
def Fp := Fin p

instance : CommRing Fp := inferInstanceAs (CommRing (Fin p))
instance : DecidableEq Fp := inferInstanceAs (DecidableEq (Fin p))

/-- The representative in `[0, p)`. -/
def Fp.val (x : Fp) : Nat := Fin.val (n := p) x

/-- `n mod p`. -/
def Fp.ofNat (n : Nat) : Fp := Fin.ofNat p n

theorem Fp.ext {x y : Fp} (h : x.val = y.val) : x = y := Fin.ext h
theorem Fp.val_lt (x : Fp) : x.val < p := Fin.isLt x
theorem Fp.val_ofNat (n : Nat) : (Fp.ofNat n).val = n % p := Fin.val_ofNat p n
theorem Fp.val_zero : (0 : Fp).val = 0 := rfl
theorem Fp.val_add (x y : Fp) : (x + y).val = (x.val + y.val) % p := Fin.val_add x y
theorem Fp.val_mul (x y : Fp) : (x * y).val = x.val * y.val % p := Fin.val_mul x y
theorem Fp.val_sub (x y : Fp) : (x - y).val = (p - y.val + x.val) % p := Fin.val_sub x y
theorem Fp.val_pow (x : Fp) (k : Nat) : (x ^ k).val = x.val ^ k % p := Fin.val_pow x k

theorem p_ge_two : 2 ≤ p := prime_p.1

theorem pow_mul (x : Fp) (m k : Nat) : x ^ (m * k) = (x ^ m) ^ k := by
  induction k with
  | zero => rw [Nat.mul_zero, Semiring.pow_zero, Semiring.pow_zero]
  | succ k ih => rw [Nat.mul_succ, Semiring.pow_add, ih, Semiring.pow_succ]

theorem zero_pow {k : Nat} (hk : 0 < k) : (0 : Fp) ^ k = 0 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Semiring.pow_succ, Semiring.mul_zero]

/-- Fermat's little theorem in `Fp`. -/
theorem pow_p_sub_one {x : Fp} (hx : x ≠ 0) : x ^ (p - 1) = 1 := by
  apply Fp.ext
  rw [Fp.val_pow, fermat_p x.val ?_]
  · decide
  · rw [Nat.mod_eq_of_lt x.val_lt]
    exact fun h => hx (Fp.ext h)

instance : Inv Fp := ⟨fun x => x ^ (p - 2)⟩

theorem inv_def (x : Fp) : x⁻¹ = x ^ (p - 2) := rfl

/-- Field division. -/
instance : Div Fp := ⟨fun x y => x * y⁻¹⟩

theorem div_def (x y : Fp) : x / y = x * y⁻¹ := rfl

theorem mul_inv {x : Fp} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [inv_def, CommRing.mul_comm, ← Semiring.pow_succ, show p - 2 + 1 = p - 1 by decide]
  exact pow_p_sub_one hx

theorem inv_inv' (x : Fp) : x⁻¹⁻¹ = x := by
  rw [inv_def, inv_def, ← pow_mul]
  by_cases hx : x = 0
  · rw [hx, zero_pow (by decide)]
  · rw [show (p - 2) * (p - 2) = (p - 1) * (p - 3) + 1 by decide, Semiring.pow_add, pow_mul,
      pow_p_sub_one hx, Semiring.one_pow, Semiring.pow_one, Semiring.one_mul]

/-- Integer powers: negative exponents invert. -/
def zpow (x : Fp) : Int → Fp
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

instance : HPow Fp Int Fp := ⟨zpow⟩

instance : Field Fp where
  toCommRing := inferInstance
  toDiv := inferInstance
  zpow := inferInstance
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := by decide
  inv_zero := zero_pow (by decide)
  mul_inv_cancel := mul_inv
  zpow_zero _ := Semiring.pow_zero _
  zpow_succ a n := Semiring.pow_succ a n
  zpow_neg a n := by
    rcases n with (_ | n) | n
    · show a ^ (0 : Nat) = (a ^ (0 : Nat))⁻¹
      rw [Semiring.pow_zero, inv_def, Semiring.one_pow]
    · rfl
    · exact (inv_inv' _).symm

end M0Crypto.Release.Ed25519Field
