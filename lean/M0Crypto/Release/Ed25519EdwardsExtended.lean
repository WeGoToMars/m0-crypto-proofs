import M0Crypto.Release.Ed25519Edwards

/-!
Extended and completed coordinates for twisted Edwards curves with `a = -1`
(Hisil, Wong, Carter and Dawson 2008; RFC 8032 section 5.1.4).

An extended point `(X, Y, Z, T)` with `Z ≠ 0` and `X Y = Z T` (`Ext.Valid`) represents the
affine point `(X / Z, Y / Z)`, and then `T = x y Z`. Two representatives give the same point
exactly when `X1 Z2 = X2 Z1` and `Y1 Z2 = Y2 Z1` (`Ext.toPoint_eq_iff`).

A completed point `(X, Y, Z, T)` represents `(X / Z, Y / T)` (ref10's `ge_p1p1`).
`Completed.toExt` is the conversion `(X T, Y Z, Z T, X Y)` (`p1p1_to_p3`). `addCompleted`
and `dblCompleted` are the RFC 8032 addition and doubling up to that last conversion, and
their results represent `add (-1) d` of the affine points when the sum is defined.
-/

namespace M0Crypto.Release.Ed25519EdwardsExtended

open Lean.Grind M0Crypto.Release.Ed25519Edwards

universe u

/-- Extended coordinates. -/
@[ext] structure Ext (F : Type u) where
  X : F
  Y : F
  Z : F
  T : F

/-- Completed coordinates: the point `(X / Z, Y / T)`. -/
@[ext] structure Completed (F : Type u) where
  X : F
  Y : F
  Z : F
  T : F

variable {F : Type u} [Field F]

namespace Ext

/-- A valid representative: `Z ≠ 0` and `X Y = Z T`. -/
def Valid (E : Ext F) : Prop := E.Z ≠ 0 ∧ E.X * E.Y = E.Z * E.T

/-- The affine point `(X / Z, Y / Z)`. -/
def toPoint (E : Ext F) : Point F := ⟨E.X / E.Z, E.Y / E.Z⟩

/-- The representative `(x, y, 1, x y)`. -/
def ofPoint (P : Point F) : Ext F := ⟨P.x, P.y, 1, P.x * P.y⟩

theorem valid_ofPoint (P : Point F) : (ofPoint P).Valid :=
  ⟨Field.zero_ne_one.symm, by simp only [ofPoint]; grind⟩

theorem toPoint_ofPoint (P : Point F) : (ofPoint P).toPoint = P := by
  have div_one (u : F) : u / 1 = u := by
    rw [Field.div_eq_mul_inv, Field.inv_one, Semiring.mul_one]
  exact Point.ext (div_one P.x) (div_one P.y)

/-- Equality of the represented points, without division. -/
theorem toPoint_eq_iff {E E' : Ext F} (h : E.Z ≠ 0) (h' : E'.Z ≠ 0) :
    E.toPoint = E'.toPoint ↔ E.X * E'.Z = E'.X * E.Z ∧ E.Y * E'.Z = E'.Y * E.Z := by
  constructor
  · intro e
    have ex := congrArg Point.x e
    have ey := congrArg Point.y e
    simp only [toPoint] at ex ey
    constructor <;> grind
  · intro ⟨ex, ey⟩
    exact Point.ext (div_eq_div h h' (by grind)) (div_eq_div h h' (by grind))

/-- Scaling a representative by a nonzero factor keeps the point. -/
theorem toPoint_scale (E : Ext F) {k : F} (hk : k ≠ 0) :
    (⟨k * E.X, k * E.Y, k * E.Z, k * E.T⟩ : Ext F).toPoint = E.toPoint := by
  ext
  · show k * E.X / (k * E.Z) = E.X / E.Z
    grind
  · show k * E.Y / (k * E.Z) = E.Y / E.Z
    grind

/-- A valid representative is `(x Z, y Z, Z, x y Z)` for its point `(x, y)`. -/
theorem coords {E : Ext F} (h : E.Valid) :
    E.X = E.toPoint.x * E.Z ∧ E.Y = E.toPoint.y * E.Z ∧
      E.T = E.toPoint.x * E.toPoint.y * E.Z := by
  obtain ⟨hz, hxy⟩ := h
  simp only [toPoint]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `T = x y Z`. -/
theorem T_eq {E : Ext F} (h : E.Valid) : E.T = E.toPoint.x * E.toPoint.y * E.Z := by
  obtain ⟨hz, hxy⟩ := h
  simp only [toPoint]
  grind

/-- The curve equation in extended coordinates: `a X² + Y² = Z² + d T²`. -/
theorem onCurve_iff {a d : F} {E : Ext F} (h : E.Valid) :
    OnCurve a d E.toPoint ↔ a * E.X ^ 2 + E.Y ^ 2 = E.Z ^ 2 + d * E.T ^ 2 := by
  obtain ⟨hz, hxy⟩ := h
  simp only [OnCurve, toPoint]
  have hT : E.T = E.X * E.Y / E.Z := by grind
  rw [hT]
  constructor <;> intro e <;> grind

end Ext

namespace Completed

/-- The affine point `(X / Z, Y / T)`. -/
def toPoint (C : Completed F) : Point F := ⟨C.X / C.Z, C.Y / C.T⟩

/-- Conversion to extended coordinates (`p1p1_to_p3`): `(X T, Y Z, Z T, X Y)`. -/
def toExt (C : Completed F) : Ext F := ⟨C.X * C.T, C.Y * C.Z, C.Z * C.T, C.X * C.Y⟩

theorem valid_toExt {C : Completed F} (hZ : C.Z ≠ 0) (hT : C.T ≠ 0) : C.toExt.Valid :=
  ⟨mul_ne_zero hZ hT, by simp only [toExt]; grind⟩

theorem toPoint_toExt {C : Completed F} (hZ : C.Z ≠ 0) (hT : C.T ≠ 0) :
    C.toExt.toPoint = C.toPoint := by
  ext
  · show C.X * C.T / (C.Z * C.T) = C.X / C.Z
    grind
  · show C.Y * C.Z / (C.Z * C.T) = C.Y / C.T
    grind

end Completed

/-- RFC 8032 section 5.1.4 addition for `a = -1`, before the final conversion:
`E = B - A`, `H = B + A`, `G = D + C`, `F = D - C` as the completed point `(E, H, G, F)`. -/
def addCompleted (d : F) (P Q : Ext F) : Completed F :=
  let A := (P.Y - P.X) * (Q.Y - Q.X)
  let B := (P.Y + P.X) * (Q.Y + Q.X)
  let C := P.T * 2 * d * Q.T
  let D := P.Z * 2 * Q.Z
  ⟨B - A, B + A, D + C, D - C⟩

/-- RFC 8032 section 5.1.4 doubling for `a = -1`, before the final conversion:
`H = A + B`, `E = H - (X + Y)²`, `G = A - B`, `F = C + G` as the completed point
`(E, H, G, F)`. -/
def dblCompleted (P : Ext F) : Completed F :=
  let A := P.X ^ 2
  let B := P.Y ^ 2
  let C := 2 * P.Z ^ 2
  let H := A + B
  let G := A - B
  ⟨H - (P.X + P.Y) ^ 2, H, G, C + G⟩

theorem addCompleted_spec {d : F} (h2 : (2 : F) ≠ 0) {P Q : Ext F} (hP : P.Valid)
    (hQ : Q.Valid) (hD : Defined d P.toPoint Q.toPoint) :
    (addCompleted d P Q).Z ≠ 0 ∧ (addCompleted d P Q).T ≠ 0 ∧
      (addCompleted d P Q).toPoint = add (-1) d P.toPoint Q.toPoint := by
  have k := mul_ne_zero (mul_ne_zero h2 hP.1) hQ.1
  obtain ⟨hX1, hY1, hT1⟩ := Ext.coords hP
  obtain ⟨hX2, hY2, hT2⟩ := Ext.coords hQ
  obtain ⟨hdx, hdy⟩ := hD
  simp only [addCompleted, Completed.toPoint, add, numX, denX, numY, denY] at hdx hdy ⊢
  rw [hX1, hY1, hT1, hX2, hY2, hT2]
  generalize P.toPoint = A at *
  generalize Q.toPoint = B at *
  obtain ⟨x1, y1⟩ := A
  obtain ⟨x2, y2⟩ := B
  simp only at hdx hdy ⊢
  have hG : P.Z * 2 * Q.Z + x1 * y1 * P.Z * 2 * d * (x2 * y2 * Q.Z) ≠ 0 := by
    have e : P.Z * 2 * Q.Z + x1 * y1 * P.Z * 2 * d * (x2 * y2 * Q.Z)
        = (1 + d * x1 * x2 * y1 * y2) * (2 * P.Z * Q.Z) := by grind
    exact e ▸ mul_ne_zero hdx k
  have hF : P.Z * 2 * Q.Z - x1 * y1 * P.Z * 2 * d * (x2 * y2 * Q.Z) ≠ 0 := by
    have e : P.Z * 2 * Q.Z - x1 * y1 * P.Z * 2 * d * (x2 * y2 * Q.Z)
        = (1 - d * x1 * x2 * y1 * y2) * (2 * P.Z * Q.Z) := by grind
    exact e ▸ mul_ne_zero hdy k
  exact ⟨hG, hF, Point.ext (div_eq_div hG hdx (by grind)) (div_eq_div hF hdy (by grind))⟩

theorem dblCompleted_spec {d : F} {P : Ext F} (hP : P.Valid) (hon : OnCurve (-1) d P.toPoint)
    (hD : Defined d P.toPoint P.toPoint) :
    (dblCompleted P).Z ≠ 0 ∧ (dblCompleted P).T ≠ 0 ∧
      (dblCompleted P).toPoint = add (-1) d P.toPoint P.toPoint := by
  have k : P.Z * P.Z ≠ 0 := mul_ne_zero hP.1 hP.1
  obtain ⟨hX, hY, -⟩ := Ext.coords hP
  obtain ⟨hdx, hdy⟩ := hD
  simp only [OnCurve] at hon
  simp only [dblCompleted, Completed.toPoint, add, numX, denX, numY, denY] at hdx hdy ⊢
  rw [hX, hY]
  generalize P.toPoint = A at *
  obtain ⟨x, y⟩ := A
  simp only at hdx hdy hon ⊢
  have hG : (x * P.Z) ^ 2 - (y * P.Z) ^ 2 ≠ 0 := by
    have e : (x * P.Z) ^ 2 - (y * P.Z) ^ 2 = -(1 + d * x * x * y * y) * (P.Z * P.Z) := by
      grind
    rw [e]
    exact mul_ne_zero (fun h => hdx (by grind)) k
  have hF : 2 * P.Z ^ 2 + ((x * P.Z) ^ 2 - (y * P.Z) ^ 2) ≠ 0 := by
    have e : 2 * P.Z ^ 2 + ((x * P.Z) ^ 2 - (y * P.Z) ^ 2)
        = (1 - d * x * x * y * y) * (P.Z * P.Z) := by grind
    exact e ▸ mul_ne_zero hdy k
  exact ⟨hG, hF, Point.ext (div_eq_div hG hdx (by grind)) (div_eq_div hF hdy (by grind))⟩

end M0Crypto.Release.Ed25519EdwardsExtended
