/-!
Congruence modulo `p = 2^255 - 19` on `Int`, for the X25519 proofs.

`a ≡p b` is `a % p = b % p`. The compatibility lemmas (`add`, `sub`, `mul`, `pow`) carry a
chain of slot congruences, one per field operation of the code, to a congruence between
polynomials. The remaining polynomial equality is a commutative-ring identity, closed by
core `grind` in a small named lemma. No machine term
appears in this file.
-/

namespace M0Crypto.Release.X25519Congr

/-- The field prime of RFC 7748, `2^255 - 19`. -/
def p : Int := 2 ^ 255 - 19

/-- `a` and `b` are congruent modulo `p`. -/
def ModP (a b : Int) : Prop := a % p = b % p

@[inherit_doc] scoped infix:50 " ≡p " => ModP

namespace ModP

theorem refl (a : Int) : a ≡p a := rfl

theorem of_eq {a b : Int} (h : a = b) : a ≡p b := h ▸ refl a

theorem symm {a b : Int} (h : a ≡p b) : b ≡p a := Eq.symm h

theorem trans {a b c : Int} (h₁ : a ≡p b) (h₂ : b ≡p c) : a ≡p c := Eq.trans h₁ h₂

theorem emod_left (a : Int) : a % p ≡p a := Int.emod_emod_of_dvd a (Int.dvd_refl p)

theorem add {a b c d : Int} (h₁ : a ≡p b) (h₂ : c ≡p d) : a + c ≡p b + d := by
  unfold ModP at *
  rw [Int.add_emod, h₁, h₂, ← Int.add_emod]

theorem sub {a b c d : Int} (h₁ : a ≡p b) (h₂ : c ≡p d) : a - c ≡p b - d := by
  unfold ModP at *
  rw [Int.sub_emod, h₁, h₂, ← Int.sub_emod]

theorem mul {a b c d : Int} (h₁ : a ≡p b) (h₂ : c ≡p d) : a * c ≡p b * d := by
  unfold ModP at *
  rw [Int.mul_emod, h₁, h₂, ← Int.mul_emod]

theorem pow {a b : Int} (h : a ≡p b) : ∀ n : Nat, a ^ n ≡p b ^ n
  | 0 => by rw [Int.pow_zero, Int.pow_zero]; exact refl 1
  | n + 1 => by
    rw [Int.pow_succ, Int.pow_succ]
    exact mul (pow h n) h

/-- Multiplication by a constant on the left. -/
theorem mul_left (k : Int) {a b : Int} (h : a ≡p b) : k * a ≡p k * b := mul (refl k) h

instance : Trans ModP ModP ModP := ⟨trans⟩

end ModP

/-! ### Test: one doubling of the ladder

The code computes one doubling as eight field operations on frame slots (generator `dbl`):
`A = x + z`, `B = x - z`, `AA = A^2`, `BB = B^2`, `x' = AA * BB`, `E = AA - BB`,
`T = 121666 * E + BB`, `z' = E * T`. Each operation's result is only congruent to its
value. RFC 7748 writes the doubling as `x' = AA * BB`, `z' = E * (AA + a24 * E)` with
`a24 = 121665`. -/

section DoublingTest

open ModP

theorem mul_self_eq_sq (y : Int) : y * y = y ^ 2 := by grind

/-- The polynomial identity behind `121666 * E + BB = AA + 121665 * E`. -/
theorem dbl_z_identity (x z : Int) :
    ((x + z) ^ 2 - (x - z) ^ 2) * (121666 * ((x + z) ^ 2 - (x - z) ^ 2) + (x - z) ^ 2)
      = ((x + z) ^ 2 - (x - z) ^ 2) * ((x + z) ^ 2 + 121665 * ((x + z) ^ 2 - (x - z) ^ 2)) := by
  grind

theorem dbl_test (x z a b aa bb x' e t z' : Int)
    (ha : a ≡p x + z) (hb : b ≡p x - z) (haa : aa ≡p a * a) (hbb : bb ≡p b * b)
    (hx : x' ≡p aa * bb) (he : e ≡p aa - bb) (ht : t ≡p 121666 * e + bb) (hz : z' ≡p e * t) :
    x' ≡p (x + z) ^ 2 * (x - z) ^ 2 ∧
    z' ≡p ((x + z) ^ 2 - (x - z) ^ 2) * ((x + z) ^ 2 + 121665 * ((x + z) ^ 2 - (x - z) ^ 2)) := by
  have hAA : aa ≡p (x + z) ^ 2 := haa.trans ((mul ha ha).trans (of_eq (mul_self_eq_sq _)))
  have hBB : bb ≡p (x - z) ^ 2 := hbb.trans ((mul hb hb).trans (of_eq (mul_self_eq_sq _)))
  have hE : e ≡p (x + z) ^ 2 - (x - z) ^ 2 := he.trans (sub hAA hBB)
  refine ⟨hx.trans (mul hAA hBB), ?_⟩
  have hT := ht.trans (add (mul_left 121666 hE) hBB)
  exact (hz.trans (mul hE hT)).trans (of_eq (dbl_z_identity x z))

end DoublingTest

end M0Crypto.Release.X25519Congr
