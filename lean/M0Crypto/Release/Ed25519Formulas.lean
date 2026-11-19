import M0Crypto.Release.Ed25519Group
import M0Crypto.Release.Ed25519EdwardsExtended

/-!
The point formulas of the Ed25519 unit, over `F_p`, in the order the generator's macros
(`ge_dbl`, `ge_add`, `ge_p1p1_to_p3`, `to_cached`, `neg_a` of `gen_ed25519.py`) compute them,
and what they represent in the group `EdPt`.

Forms, as the code names them:
* `p3`: extended `(X, Y, Z, T)`, `Rep E A`: valid and `(X / Z, Y / Z) = A`.
* `p2`: `p3` whose `T` is stale (a conversion without `T`), `Rep2 E A`: `Z ≠ 0` and
  `(X / Z, Y / Z) = A`. Doubling reads only `X`, `Y`, `Z`.
* `p1p1`: completed `(X, Y, Z, T)` for `(X / Z, Y / T)`, `RepC C A`.
* `niels`: `(y + x, y − x, 2 d x y)` of an affine point (the flash tables, the lookup output).
* `cached`: `(Y + X, Y − X, Z, 2 d T)` of a `p3` point (the odd multiples of `−A` in verify).

The additions take a flag `neg`: `true` is the code's negated addition (pointers to `y + x` and
`y − x` swapped and the destinations of `D + C` and `D − C` swapped), which subtracts.
-/

namespace M0Crypto.Release.Ed25519Formulas

open Lean.Grind M0Crypto.Release.Ed25519Edwards M0Crypto.Release.Ed25519EdwardsExtended

/-! ## The formulas over any field -/

section Generic

universe u

variable {F : Type u} [Field F]

/-- The identity `(0, 1, 1, 0)` (`set_identity`). -/
def identity : Ext F := ⟨0, 1, 1, 0⟩

/-- `ge_dbl`: `A = X²`, `B = Y²`, `C = 2 Z²`, `D = (X + Y)²`, then
`(D − (B + A), B + A, B − A, C − (B − A))`. `T` is not read. -/
def dbl (E : Ext F) : Completed F :=
  let a := E.X * E.X
  let b := E.Y * E.Y
  let c := E.Z * E.Z
  let c := c + c
  let dd := E.X + E.Y
  let dd := dd * dd
  let t1 := b + a
  let t2 := b - a
  ⟨dd - t1, t1, t2, c - t2⟩

theorem dbl_spec {d : F} {E : Ext F} (hz : E.Z ≠ 0) (hon : OnCurve (-1) d E.toPoint)
    (hD : Defined d E.toPoint E.toPoint) :
    (dbl E).Z ≠ 0 ∧ (dbl E).T ≠ 0 ∧ (dbl E).toPoint = add (-1) d E.toPoint E.toPoint := by
  -- The same coordinates with a valid `T`; doubling does not read `T`.
  let E' : Ext F := ⟨E.X, E.Y, E.Z, E.X * E.Y / E.Z⟩
  have hv : E'.Valid := ⟨hz, by show E.X * E.Y = E.Z * (E.X * E.Y / E.Z); grind⟩
  obtain ⟨h1, h2, hpt⟩ := dblCompleted_spec (d := d) hv hon hD
  simp only [dblCompleted, Completed.toPoint] at h1 h2 hpt
  have h1' : E.Y * E.Y - E.X * E.X ≠ 0 := by
    intro e; apply h1; show E.X ^ 2 - E.Y ^ 2 = 0; grind
  have h2' : E.Z * E.Z + E.Z * E.Z - (E.Y * E.Y - E.X * E.X) ≠ 0 := by
    intro e; apply h2; show 2 * E.Z ^ 2 + (E.X ^ 2 - E.Y ^ 2) = 0; grind
  refine ⟨h1', h2', ?_⟩
  show _ = add (-1) d E'.toPoint E'.toPoint
  rw [← hpt]
  clear hpt hv hon hD
  simp only [dbl, Completed.toPoint]
  exact Point.ext (div_eq_div h1' h1 (by grind)) (div_eq_div h2' h2 (by grind))

/-- `(y + x, y − x, 2 d x y)`. -/
structure Niels (F : Type u) where
  ypx : F
  ymx : F
  xy2d : F

/-- The Niels form of an affine point; `d2` is the constant `2 d`. -/
def Niels.of (d2 : F) (P : Point F) : Niels F := ⟨P.y + P.x, P.y - P.x, d2 * P.x * P.y⟩

/-- The negated entry the lookup selects: `y + x` and `y − x` swapped, `0 − 2 d x y`. -/
def Niels.neg (N : Niels F) : Niels F := ⟨N.ymx, N.ypx, 0 - N.xy2d⟩

theorem Niels.of_neg (d2 : F) (P : Point F) :
    Niels.of d2 (Ed25519Edwards.neg P) = (Niels.of d2 P).neg := by
  simp only [Niels.of, Niels.neg, Ed25519Edwards.neg, Niels.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- The identity entry `(1, 1, 0)`. -/
theorem Niels.of_zero (d2 : F) : Niels.of d2 (zero : Point F) = ⟨1, 1, 0⟩ := by
  simp only [Niels.of, zero, Niels.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> grind

/-- `ge_add` with a Niels entry; `neg` swaps the pointers and the last two destinations. -/
def madd (E : Ext F) (N : Niels F) (neg : Bool) : Completed F :=
  let ypx := if neg then N.ymx else N.ypx
  let ymx := if neg then N.ypx else N.ymx
  let a := (E.Y + E.X) * ypx
  let b := (E.Y - E.X) * ymx
  let c := E.T * N.xy2d
  let dd := E.Z + E.Z
  if neg then ⟨a - b, a + b, dd - c, dd + c⟩ else ⟨a - b, a + b, dd + c, dd - c⟩

theorem madd_neg (E : Ext F) (N : Niels F) : madd E N true = madd E N.neg false := by
  simp only [madd, Niels.neg, Bool.false_eq_true, ↓reduceIte, Completed.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The code's mixed addition is the completed sum of RFC 8032 section 5.1.4. -/
theorem madd_eq (d : F) (E : Ext F) (P : Point F) :
    madd E (Niels.of (2 * d) P) false = addCompleted d E (Ext.ofPoint P) := by
  simp only [madd, Niels.of, addCompleted, Ext.ofPoint, Bool.false_eq_true, ↓reduceIte,
    Completed.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- `(Y + X, Y − X, Z, 2 d T)`. -/
structure Cached (F : Type u) where
  ypx : F
  ymx : F
  z : F
  t2d : F

/-- `to_cached`: `Y + X`, `Y − X`, a copy of `Z`, `T · 2d`. -/
def Cached.of (d2 : F) (E : Ext F) : Cached F := ⟨E.Y + E.X, E.Y - E.X, E.Z, E.T * d2⟩

/-- `ge_add` with a cached entry. -/
def cadd (E : Ext F) (K : Cached F) (neg : Bool) : Completed F :=
  let ypx := if neg then K.ymx else K.ypx
  let ymx := if neg then K.ypx else K.ymx
  let a := (E.Y + E.X) * ypx
  let b := (E.Y - E.X) * ymx
  let c := E.T * K.t2d
  let dd := E.Z * K.z
  let dd := dd + dd
  if neg then ⟨a - b, a + b, dd - c, dd + c⟩ else ⟨a - b, a + b, dd + c, dd - c⟩

/-- `neg_a`: `(0 − X, Y, Z, 0 − T)`. -/
def negExt (E : Ext F) : Ext F := ⟨0 - E.X, E.Y, E.Z, 0 - E.T⟩

theorem negExt_valid {E : Ext F} (h : E.Valid) : (negExt E).Valid :=
  ⟨h.1, by have := h.2; simp only [negExt]; grind⟩

theorem negExt_toPoint (E : Ext F) : (negExt E).toPoint = neg E.toPoint := by
  simp only [negExt, Ext.toPoint, neg, Point.mk.injEq]
  exact ⟨by grind, trivial⟩

theorem cadd_neg (d2 : F) (E G : Ext F) :
    cadd E (Cached.of d2 G) true = cadd E (Cached.of d2 (negExt G)) false := by
  simp only [cadd, Cached.of, negExt, Bool.false_eq_true, ↓reduceIte, Completed.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem cadd_eq (d : F) (E G : Ext F) :
    cadd E (Cached.of (2 * d) G) false = addCompleted d E G := by
  simp only [cadd, Cached.of, addCompleted, Bool.false_eq_true, ↓reduceIte, Completed.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end Generic

/-! ## Representation of the group `EdPt` -/

open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve M0Crypto.Release.Ed25519Group

/-- The code's constant `2 d` (`m0c_ed_d2`). -/
def d2 : Fp := 2 * d

/-- `E` (`p3`) represents `A`. -/
def Rep (E : Ext Fp) (A : EdPt) : Prop := E.Valid ∧ E.toPoint = A.pt

/-- `E` (`p2`: `T` arbitrary) represents `A`. -/
def Rep2 (E : Ext Fp) (A : EdPt) : Prop := E.Z ≠ 0 ∧ E.toPoint = A.pt

/-- `C` (`p1p1`) represents `A`. -/
def RepC (C : Completed Fp) (A : EdPt) : Prop := C.Z ≠ 0 ∧ C.T ≠ 0 ∧ C.toPoint = A.pt

theorem Rep.rep2 {E : Ext Fp} {A : EdPt} (h : Rep E A) : Rep2 E A := ⟨h.1.1, h.2⟩

/-- Two represented points are equal exactly when the cross products agree. -/
theorem Rep2.eq_iff {E E' : Ext Fp} {A A' : EdPt} (h : Rep2 E A) (h' : Rep2 E' A') :
    A = A' ↔ E.X * E'.Z = E'.X * E.Z ∧ E.Y * E'.Z = E'.Y * E.Z := by
  rw [← Ext.toPoint_eq_iff h.1 h'.1, h.2, h'.2]
  exact ⟨fun e => e ▸ rfl, fun e => EdPt.ext e⟩

theorem rep_identity : Rep identity 0 := by
  have h1 : (1 : Fp) ≠ 0 := by decide
  refine ⟨⟨h1, by decide⟩, ?_⟩
  show Point.mk (0 / 1) (1 / 1) = zero
  rw [Field.div_eq_mul_inv, Field.div_eq_mul_inv, Field.inv_one, Semiring.mul_one,
    Semiring.mul_one]
  rfl

theorem rep_ofPoint (Q : EdPt) : Rep (Ext.ofPoint Q.pt) Q :=
  ⟨Ext.valid_ofPoint _, Ext.toPoint_ofPoint _⟩

/-- `p1p1_to_p3` with `T`: `(X T, Y Z, Z T, X Y)`. -/
theorem RepC.toExt {C : Completed Fp} {A : EdPt} (h : RepC C A) : Rep C.toExt A :=
  ⟨Completed.valid_toExt h.1 h.2.1, (Completed.toPoint_toExt h.1 h.2.1).trans h.2.2⟩

/-- `p1p1_to_p3` without `T`: the `T` slot keeps any value `t`. -/
theorem RepC.toExt2 {C : Completed Fp} {A : EdPt} (h : RepC C A) (t : Fp) :
    Rep2 ⟨C.X * C.T, C.Y * C.Z, C.Z * C.T, t⟩ A :=
  h.toExt.rep2

theorem dbl_rep {E : Ext Fp} {A : EdPt} (h : Rep2 E A) : RepC (dbl E) (A + A) := by
  have hon : OnEd25519 E.toPoint := h.2 ▸ A.on
  obtain ⟨h1, h2, hp⟩ := dbl_spec h.1 hon (Ed25519EdwardsComplete.defined complete hon hon)
  exact ⟨h1, h2, hp.trans (by rw [h.2]; rfl)⟩

theorem add_rep {E G : Ext Fp} {A Q : EdPt} (hE : Rep E A) (hG : Rep G Q) :
    RepC (addCompleted d E G) (A + Q) := by
  have hA : OnEd25519 E.toPoint := hE.2 ▸ A.on
  have hQ : OnEd25519 G.toPoint := hG.2 ▸ Q.on
  obtain ⟨hz, ht, hp⟩ := addCompleted_spec (by decide) hE.1 hG.1
    (Ed25519EdwardsComplete.defined complete hA hQ)
  exact ⟨hz, ht, hp.trans (by rw [hE.2, hG.2]; rfl)⟩

/-- Mixed addition: `A ± Q` from `A` and the Niels form of `Q`. -/
theorem madd_rep {E : Ext Fp} {A : EdPt} (hE : Rep E A) (Q : EdPt) (neg : Bool) :
    RepC (madd E (Niels.of d2 Q.pt) neg) (if neg then A - Q else A + Q) := by
  cases neg
  · rw [d2, madd_eq]; exact add_rep hE (rep_ofPoint Q)
  · rw [madd_neg, ← Niels.of_neg, d2, madd_eq]; exact add_rep hE (rep_ofPoint (-Q))

theorem negExt_rep {E : Ext Fp} {A : EdPt} (h : Rep E A) : Rep (negExt E) (-A) :=
  ⟨negExt_valid h.1, (negExt_toPoint E).trans (by rw [h.2]; rfl)⟩

/-- Cached addition: `A ± Q` from `A` and the cached form of a representative of `Q`. -/
theorem cadd_rep {E G : Ext Fp} {A Q : EdPt} (hE : Rep E A) (hG : Rep G Q) (neg : Bool) :
    RepC (cadd E (Cached.of d2 G) neg) (if neg then A - Q else A + Q) := by
  cases neg
  · rw [d2, cadd_eq]; exact add_rep hE hG
  · rw [cadd_neg, d2, cadd_eq]; exact add_rep hE (negExt_rep hG)

end M0Crypto.Release.Ed25519Formulas
