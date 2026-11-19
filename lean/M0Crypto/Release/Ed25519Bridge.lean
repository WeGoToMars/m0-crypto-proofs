import M0Crypto.Release.Ed25519Formulas
import M0Crypto.Spec.Ed25519

/-!
The bridge from the specification `M0Crypto.Spec.Ed25519` (RFC 8032 over `Nat` with `% p`) to
the group `EdPt`.

`toF n` is `n mod p` in `F_p`; it turns the specification's `% p` arithmetic into field
arithmetic (`toF_add`, `toF_mul`, `toF_fsub`, `toF_pow`). A specification point `P` represents
`A : EdPt` (`SpecRep P A`) when its coordinates, mapped by `toF`, represent `A` (`Rep`). Then:

* `specRep_add`: the specification's `add` (section 5.1.4) is the group sum;
* `specRep_scalarMul`: its `scalarMul s` is `s • A`;
* `specRep_B`: its base point `B` represents `Bpt`;
* `xy_eq`: its affine coordinates `Point.xy` are the canonical values of the coordinates of
  `A`, so two specification points have equal `xy` exactly when they represent the same point.
-/

namespace M0Crypto.Release.Ed25519Bridge

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve
open M0Crypto.Release.Ed25519Edwards (Point OnCurve)
open M0Crypto.Release.Ed25519EdwardsExtended M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas

theorem p_eq : Spec.Ed25519.p = Ed25519PrimeCert.p := rfl

/-! ## Natural numbers in `F_p` -/

/-- `n mod p` as an element of `F_p`. -/
def toF (n : Nat) : Fp := Fp.ofNat n

theorem val_toF (n : Nat) : (toF n).val = n % Ed25519PrimeCert.p := Fp.val_ofNat n

theorem toF_val (x : Fp) : toF x.val = x := Fp.ext (by rw [val_toF, Nat.mod_eq_of_lt x.val_lt])

theorem toF_eq_iff {a b : Nat} : toF a = toF b ↔ a % Spec.Ed25519.p = b % Spec.Ed25519.p :=
  ⟨fun h => by rw [p_eq, ← val_toF, ← val_toF, h], fun h => Fp.ext (by rw [val_toF, val_toF]; exact h)⟩

theorem toF_mod (n : Nat) : toF (n % Spec.Ed25519.p) = toF n :=
  toF_eq_iff.2 (Nat.mod_mod _ _)

theorem toF_add (a b : Nat) : toF (a + b) = toF a + toF b :=
  Fp.ext (by rw [Fp.val_add, val_toF, val_toF, val_toF, Nat.add_mod])

theorem toF_mul (a b : Nat) : toF (a * b) = toF a * toF b :=
  Fp.ext (by rw [Fp.val_mul, val_toF, val_toF, val_toF, Nat.mul_mod])

theorem toF_pow (a k : Nat) : toF (a ^ k) = toF a ^ k :=
  Fp.ext (by rw [Fp.val_pow, val_toF, val_toF, Nat.pow_mod])

theorem toF_zero : toF 0 = 0 := rfl
theorem toF_one : toF 1 = 1 := rfl
theorem toF_two : toF 2 = 2 := rfl

theorem toF_fsub (a b : Nat) : toF (Spec.Ed25519.fsub a b) = toF a - toF b := by
  apply Fp.ext
  rw [Fp.val_sub, val_toF, val_toF, val_toF]
  unfold Spec.Ed25519.fsub
  rw [p_eq, Nat.mod_mod]
  have hb := Nat.mod_lt b (show 0 < Ed25519PrimeCert.p by decide)
  rw [Nat.add_sub_assoc (Nat.le_of_lt hb), Nat.add_comm a, Nat.add_mod_mod]

theorem toF_powp (a e : Nat) : toF (Spec.Ed25519.powp a e) = toF a ^ e := by
  rw [Spec.Ed25519.powp, toF_mod, toF_pow]

theorem toF_inv (a : Nat) : toF (Spec.Ed25519.inv a) = (toF a)⁻¹ := by
  rw [Spec.Ed25519.inv, toF_powp, inv_def]; rfl

theorem toF_d : toF Spec.Ed25519.d = d := by
  rw [d_eq]; rfl

/-! ## Points -/

/-- The specification's point `(X, Y, Z, T)` with coordinates in `F_p`. -/
def ofSpec (P : Spec.Ed25519.Point) : Ext Fp := ⟨toF P.X, toF P.Y, toF P.Z, toF P.T⟩

/-- The specification point `P` represents `A`. -/
def SpecRep (P : Spec.Ed25519.Point) (A : EdPt) : Prop := Rep (ofSpec P) A

/-- The specification's addition is the RFC 8032 completed sum followed by `p1p1_to_p3`. -/
theorem ofSpec_add (P Q : Spec.Ed25519.Point) :
    ofSpec (Spec.Ed25519.add P Q) = (addCompleted d (ofSpec P) (ofSpec Q)).toExt := by
  simp only [Spec.Ed25519.add, ofSpec, addCompleted, Completed.toExt, toF_mul, toF_mod,
    toF_fsub, toF_add, toF_d, toF_two]
  congr 1 <;> grind

theorem specRep_add {P Q : Spec.Ed25519.Point} {A A' : EdPt} (h : SpecRep P A)
    (h' : SpecRep Q A') : SpecRep (Spec.Ed25519.add P Q) (A + A') := by
  unfold SpecRep; rw [ofSpec_add]; exact (add_rep h h').toExt

theorem specRep_neutral : SpecRep Spec.Ed25519.neutral 0 := rep_identity

theorem specRep_scalarMul (s : Nat) {P : Spec.Ed25519.Point} {A : EdPt} (h : SpecRep P A) :
    SpecRep (Spec.Ed25519.scalarMul s P) ((s : Int) • A) := by
  induction s using Nat.strongRecOn generalizing P A with
  | ind s ih =>
    rw [Spec.Ed25519.scalarMul]
    by_cases h0 : s = 0
    · subst h0; exact specRep_neutral
    · simp only [h0, ↓reduceIte]
      have hq := ih (s / 2) (by omega) (specRep_add h h)
      have e : (s : Int) • A = ((s / 2 : Nat) : Int) • (A + A) + ((s % 2 : Nat) : Int) • A := by
        rw [IntModule.zsmul_add, ← IntModule.add_zsmul, ← IntModule.add_zsmul]
        congr 1; omega
      by_cases h1 : s % 2 = 1
      · simp only [h1, ↓reduceIte]
        rw [e, h1]
        have : ((1 : Nat) : Int) • A = A := IntModule.one_zsmul A
        rw [this]
        exact specRep_add hq h
      · simp only [h1, ↓reduceIte]
        rw [e, show s % 2 = 0 by omega]
        have : ((0 : Nat) : Int) • A = 0 := IntModule.zero_zsmul A
        rw [this, AddCommMonoid.add_zero]
        exact hq

/-- The specification's point `(x, y)` with `Z = 1` (`Point.ofXY`) represents the affine point
`(x, y)` mapped to `F_p`, when it lies on the curve. -/
theorem specRep_ofXY {x y : Nat} (h : OnEd25519 ⟨toF x, toF y⟩) :
    SpecRep (Spec.Ed25519.Point.ofXY x y) ⟨⟨toF x, toF y⟩, h⟩ := by
  have e : ofSpec (Spec.Ed25519.Point.ofXY x y) = Ext.ofPoint ⟨toF x, toF y⟩ := by
    simp only [ofSpec, Spec.Ed25519.Point.ofXY, Ext.ofPoint, toF_mod, toF_mul, toF_one]
  unfold SpecRep; rw [e]; exact rep_ofPoint (⟨⟨toF x, toF y⟩, h⟩ : EdPt)

theorem B_on : OnEd25519 ⟨toF Spec.Ed25519.B.X, toF Spec.Ed25519.B.Y⟩ := by
  unfold OnEd25519 OnCurve; decide +kernel

/-- The base point `B` of RFC 8032 table 1. -/
def Bpt : EdPt := ⟨_, B_on⟩

theorem specRep_B : SpecRep Spec.Ed25519.B Bpt := specRep_ofXY B_on

/-- The specification's affine coordinates are the canonical values of the represented
point's coordinates. -/
theorem xy_eq {P : Spec.Ed25519.Point} {A : EdPt} (h : SpecRep P A) :
    P.xy = (A.pt.x.val, A.pt.y.val) := by
  have hx : A.pt.x = toF P.X * (toF P.Z)⁻¹ := by rw [← h.2]; rfl
  have hy : A.pt.y = toF P.Y * (toF P.Z)⁻¹ := by rw [← h.2]; rfl
  simp only [Spec.Ed25519.Point.xy, hx, hy, ← toF_inv, ← toF_mul, val_toF]
  rfl

theorem xy_eq_iff {P Q : Spec.Ed25519.Point} {A A' : EdPt} (h : SpecRep P A)
    (h' : SpecRep Q A') : P.xy = Q.xy ↔ A = A' := by
  rw [xy_eq h, xy_eq h']
  constructor
  · intro e
    simp only [Prod.mk.injEq] at e
    exact EdPt.ext (Point.ext (Fp.ext e.1) (Fp.ext e.2))
  · intro e; rw [e]

end M0Crypto.Release.Ed25519Bridge
