import M0Crypto.Release.Ed25519Decode

/-!
The verify equation of `m0c_ed25519_verify` against `Spec.Ed25519.verify` (C3: RFC 8032 section
5.1.3 decoding, S < L, the cofactorless equation with k reduced modulo L as in section 6).

The routine decodes `A` and `R`, rejects `S ≥ L`, reduces `h = k mod L`, computes
`SB = [S]B − [h]A` with `m0c_ge_dsm` (a `p2` point) and accepts when `X_SB = X_R Z_SB` and
`Y_SB = Y_R Z_SB`, comparing with the decoded `R = (X_R, Y_R, 1, ·)`.

* `specRep_of_decode`: a decoded point represents a point of the group, with `Z = 1`.
* `verify_eq`: given both decodings, the specification's verdict is `S < L` and the routine's
  projective comparison.
* `verify_of_decode_R_none`, `verify_of_decode_A_none`: a failed decoding rejects.
-/

namespace M0Crypto.Release.Ed25519Verify

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge M0Crypto.Release.Ed25519Decode

/-- A point that the specification decodes represents a point of the group, with `Z = 1`. -/
theorem specRep_of_decode {s : List Spec.Ed25519.Byte} {R : Spec.Ed25519.Point}
    (h : Spec.Ed25519.decodePoint s = some R) : ∃ A : EdPt, SpecRep R A ∧ (ofSpec R).Z = 1 := by
  have e := decodePoint_eq s
  rw [h, Option.map_some] at e
  have hy : Spec.Ed25519.decodeInt s % 2 ^ 255 < Ed25519PrimeCert.p := by
    apply Nat.lt_of_not_le; intro hp
    unfold decodeCode at e; rw [ite_eq_left hp] at e; exact absurd e (by simp)
  obtain ⟨A, hA, -, hz⟩ := rep_of_decode hy (Nat.mod_lt _ (by decide)) e.symm
  exact ⟨A, hA, hz⟩

/-- The routine's comparison of `SB` (`p2`) with the decoded `R` (`Z = 1`). -/
def eqCode (SB ER : Ext Fp) : Bool := decide (SB.X = ER.X * SB.Z) && decide (SB.Y = ER.Y * SB.Z)

/-- The verify equation: with `R` and `A'` decoded, and `SB` representing `[S]B − [k mod L]A'`
whenever `S < L`, the specification accepts exactly when `S < L` and the routine's
projective comparison holds. -/
theorem verify_eq {sig M Apk : List Spec.Ed25519.Byte} {R A' : Spec.Ed25519.Point}
    (hR : Spec.Ed25519.decodePoint (sig.take 32) = some R)
    (hA : Spec.Ed25519.decodePoint Apk = some A') {Apt : EdPt} (hAr : SpecRep A' Apt)
    {SB : Ext Fp}
    (hSB : Spec.Ed25519.decodeInt (sig.drop 32) < Spec.Ed25519.L →
      Rep2 SB ((Spec.Ed25519.decodeInt (sig.drop 32) : Int) • Bpt -
        ((Spec.Ed25519.decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M))
          % Spec.Ed25519.L : Nat) : Int) • Apt)) :
    Spec.Ed25519.verify sig M Apk =
      (decide (Spec.Ed25519.decodeInt (sig.drop 32) < Spec.Ed25519.L) && eqCode SB (ofSpec R)) := by
  obtain ⟨Rpt, hRr, hRz⟩ := specRep_of_decode hR
  unfold Spec.Ed25519.verify
  simp only [hR, hA]
  generalize Spec.Ed25519.decodeInt (sig.drop 32) = S at hSB ⊢
  generalize Spec.Ed25519.decodeInt (Spec.Sha512.sha512 (sig.take 32 ++ Apk ++ M))
    % Spec.Ed25519.L = h at hSB ⊢
  by_cases hS : S < Spec.Ed25519.L
  · simp only [hS, decide_true, Bool.true_and]
    have h1 := specRep_scalarMul S specRep_B
    have h2 := specRep_add hRr (specRep_scalarMul h hAr)
    have hsb := hSB hS
    -- `[S]B = R + [h]A'` exactly when `[S]B − [h]A' = R`, the comparison with `Z_R = 1`.
    have key : ((S : Int) • Bpt = Rpt + (h : Int) • Apt) ↔
        ((S : Int) • Bpt - (h : Int) • Apt = Rpt) := by
      generalize (S : Int) • Bpt = a
      generalize (h : Int) • Apt = b
      constructor <;> intro e <;> grind
    have hRrep := hRr.rep2
    rw [Rep2.eq_iff hsb hRrep, hRz] at key
    rw [Bool.eq_iff_iff, beq_iff_eq, xy_eq_iff h1 h2, key, eqCode, Bool.and_eq_true,
      decide_eq_true_iff, decide_eq_true_iff, Semiring.mul_one, Semiring.mul_one]
  · simp only [hS, decide_false, Bool.false_and]

theorem verify_of_decode_R_none {sig M Apk : List Spec.Ed25519.Byte}
    (hR : Spec.Ed25519.decodePoint (sig.take 32) = none) : Spec.Ed25519.verify sig M Apk = false := by
  unfold Spec.Ed25519.verify; simp only [hR]

theorem verify_of_decode_A_none {sig M Apk : List Spec.Ed25519.Byte}
    (hA : Spec.Ed25519.decodePoint Apk = none) : Spec.Ed25519.verify sig M Apk = false := by
  unfold Spec.Ed25519.verify
  simp only [hA]
  split
  · rename_i h; exact absurd h (by simp)
  · rfl

end M0Crypto.Release.Ed25519Verify
