import M0Crypto.Release.Ed25519Bridge

/-!
The order of the base point: `[L]B = 0` (`L_smul_B`), so multiples of `B` only depend on the
scalar modulo `L` (`zsmul_B_emod`).

The proof evaluates a double-and-add in extended coordinates (`mulExt`) in the kernel and
relates it to `•` with the formula lemmas of `Ed25519Formulas` (`rep_mulExt`). `mulExt` also
evaluates any multiple of `B`, for example the table entries (`affineMul`).
-/

namespace M0Crypto.Release.Ed25519Order

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519Edwards (Point zero)
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge

/-- `d` as a numeral, for evaluation (`d_eq`). -/
def dLit : Fp := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The sum of two extended points (RFC 8032 section 5.1.4). -/
def addExt (P Q : Ext Fp) : Ext Fp := (addCompleted dLit P Q).toExt

/-- `[k]P` by double-and-add on the bits of `k`, at most `fuel` of them. -/
def mulExt : Nat → Nat → Ext Fp → Ext Fp
  | 0, _, _ => identity
  | fuel + 1, k, P =>
    if k = 0 then identity else
      let Q := mulExt fuel (k / 2) (addExt P P)
      if k % 2 = 1 then addExt Q P else Q

theorem rep_addExt {E G : Ext Fp} {A Q : EdPt} (hE : Rep E A) (hG : Rep G Q) :
    Rep (addExt E G) (A + Q) := by
  unfold addExt; rw [show dLit = d from d_eq.symm]; exact (add_rep hE hG).toExt

theorem rep_mulExt (fuel k : Nat) (hk : k < 2 ^ fuel) {P : Ext Fp} {A : EdPt} (h : Rep P A) :
    Rep (mulExt fuel k P) ((k : Int) • A) := by
  induction fuel generalizing k P A with
  | zero =>
    obtain rfl : k = 0 := by rw [Nat.pow_zero] at hk; omega
    exact rep_identity
  | succ fuel ih =>
    rw [mulExt]
    by_cases h0 : k = 0
    · subst h0; exact rep_identity
    · simp only [h0, ↓reduceIte]
      have hq := ih (k / 2) (by rw [Nat.pow_succ] at hk; omega) (rep_addExt h h)
      have e : (k : Int) • A = ((k / 2 : Nat) : Int) • (A + A) + ((k % 2 : Nat) : Int) • A := by
        rw [IntModule.zsmul_add, ← IntModule.add_zsmul, ← IntModule.add_zsmul]
        congr 1; omega
      by_cases h1 : k % 2 = 1
      · simp only [h1, ↓reduceIte]
        rw [e, h1, show ((1 : Nat) : Int) • A = A from IntModule.one_zsmul A]
        exact rep_addExt hq h
      · simp only [h1, ↓reduceIte]
        rw [e, show k % 2 = 0 by omega, show ((0 : Nat) : Int) • A = 0 from IntModule.zero_zsmul A,
          AddCommMonoid.add_zero]
        exact hq

/-- `B` in extended coordinates. -/
def BExt : Ext Fp := Ext.ofPoint Bpt.pt

theorem rep_BExt : Rep BExt Bpt := rep_ofPoint Bpt

/-- `[k]B` as an affine point, by evaluation: `(mulExt fuel k BExt).toPoint` for `k < 2^fuel`.
This is how the table entries (`Ed25519Comb.CombTable`, `OddBTable`) evaluate in the kernel. -/
theorem pt_zsmul_B {fuel k : Nat} (hk : k < 2 ^ fuel) :
    ((k : Int) • Bpt).pt = (mulExt fuel k BExt).toPoint :=
  (rep_mulExt fuel k hk rep_BExt).2.symm

/-- The group order `L` of RFC 8032 table 1. -/
abbrev L : Nat := M0Crypto.Spec.Ed25519.L

/-- `[L]B`, evaluated: `X = 0` and `Y = Z`, the point `(0, 1)`. -/
theorem mulExt_L : (mulExt 253 L BExt).X = 0 ∧ (mulExt 253 L BExt).Y = (mulExt 253 L BExt).Z := by
  decide +kernel

/-- An extended point `(0, Y, Y, T)` with `Y ≠ 0` represents only the identity. -/
theorem eq_zero_of_rep {E : Ext Fp} {A : EdPt} (h : Rep E A) (hx : E.X = 0) (hy : E.Y = E.Z) :
    A = 0 := by
  have h0 := rep_identity
  apply (Rep2.eq_iff h.rep2 h0.rep2).2
  simp only [identity, hx, hy]
  constructor <;> grind

/-- The order of `B` divides `L`. -/
theorem L_smul_B : (L : Int) • Bpt = 0 :=
  eq_zero_of_rep (rep_mulExt 253 L (by decide) rep_BExt) mulExt_L.1 mulExt_L.2

/-- Multiples of `B` depend only on the scalar modulo `L`. -/
theorem zsmul_B_emod (k : Int) : k • Bpt = (k % (L : Int)) • Bpt := by
  conv => lhs; rw [← Int.emod_add_mul_ediv k L]
  rw [IntModule.add_zsmul, Int.mul_comm, IntModule.mul_zsmul, L_smul_B, IntModule.zsmul_zero,
    AddCommMonoid.add_zero]

end M0Crypto.Release.Ed25519Order
