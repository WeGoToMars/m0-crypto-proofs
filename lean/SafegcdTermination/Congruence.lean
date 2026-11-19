module

public import Lean

@[expose] public section

namespace SafegcdTermination

/-- Congruence for the field prime and the powers of two used in the limb proofs. -/
def Congruence (m a b : Int) : Prop := a % m = b % m

scoped notation:50 a " ≡ " b " [ZMOD " m "]" => Congruence m a b

namespace Congruence

theorem refl (a : Int) {m : Int} : a ≡ a [ZMOD m] := rfl

theorem symm {a b m : Int} (h : a ≡ b [ZMOD m]) : b ≡ a [ZMOD m] := Eq.symm h

theorem trans {a b c m : Int} (h₁ : a ≡ b [ZMOD m]) (h₂ : b ≡ c [ZMOD m]) :
    a ≡ c [ZMOD m] := Eq.trans h₁ h₂

theorem emod_left (a m : Int) : a % m ≡ a [ZMOD m] := Int.emod_emod_of_dvd a (Int.dvd_refl m)

theorem add {a b c d m : Int} (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m]) :
    a + c ≡ b + d [ZMOD m] := by
  unfold Congruence at *
  rw [Int.add_emod, h₁, h₂, ← Int.add_emod]

theorem sub {a b c d m : Int} (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m]) :
    a - c ≡ b - d [ZMOD m] := by
  unfold Congruence at *
  rw [Int.sub_emod, h₁, h₂, ← Int.sub_emod]

theorem neg {a b m : Int} (h : a ≡ b [ZMOD m]) : -a ≡ -b [ZMOD m] := by
  simpa only [Int.zero_sub] using (refl 0).sub h

theorem mul {a b c d m : Int} (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m]) :
    a * c ≡ b * d [ZMOD m] := by
  unfold Congruence at *
  rw [Int.mul_emod, h₁, h₂, ← Int.mul_emod]

theorem mul_left {a b m : Int} (k : Int) (h : a ≡ b [ZMOD m]) : k * a ≡ k * b [ZMOD m] :=
  (refl k).mul h

theorem mul_right {a b m : Int} (k : Int) (h : a ≡ b [ZMOD m]) : a * k ≡ b * k [ZMOD m] :=
  h.mul (refl k)

theorem pow {a b m : Int} (h : a ≡ b [ZMOD m]) : ∀ n : Nat, a ^ n ≡ b ^ n [ZMOD m]
  | 0 => by rw [Int.pow_zero, Int.pow_zero]; exact refl 1
  | n + 1 => by rw [Int.pow_succ, Int.pow_succ]; exact (pow h n).mul h

theorem iff_dvd {a b m : Int} : a ≡ b [ZMOD m] ↔ m ∣ b - a := by
  unfold Congruence
  rw [eq_comm, Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]

theorem zero_iff_dvd {a m : Int} : a ≡ 0 [ZMOD m] ↔ m ∣ a := by
  simp only [Congruence, Int.zero_emod, Int.dvd_iff_emod_eq_zero]

theorem of_dvd {a b m n : Int} (hd : n ∣ m) (h : a ≡ b [ZMOD m]) : a ≡ b [ZMOD n] :=
  iff_dvd.mpr (Int.dvd_trans hd (iff_dvd.mp h))

end Congruence
end SafegcdTermination
