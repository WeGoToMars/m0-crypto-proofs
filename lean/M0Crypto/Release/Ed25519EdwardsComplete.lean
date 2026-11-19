import M0Crypto.Release.Ed25519EdwardsAssoc

/-!
Completeness of the twisted Edwards addition (Bernstein and Lange, "Faster addition and
doubling on elliptic curves", Theorem 3.3).

If `a` is a square, `d` is not, and `2 ≠ 0`, no denominator of the addition vanishes on
the curve (`defined`). The group laws then hold for all points on the curve without
side conditions: `add_assoc`, `add_neg`, `onCurve_add` here, and `add_comm`, `add_zero`
from `Ed25519Edwards`.

The proof: if `d x1 x2 y1 y2 = ε` with `ε² = 1`, then
`d (x1 y1)² (c x2 ± y2)² = (c x1 ± ε y1)²` with `c² = a`. Since `d` is not a square, both
`c x2 + y2` and `c x2 - y2` vanish, so `2 y2 = 0`, while `ε ≠ 0` forces `y2 ≠ 0`.
-/

namespace M0Crypto.Release.Ed25519EdwardsComplete

open Lean.Grind M0Crypto.Release.Ed25519Edwards

universe u

variable {F : Type u} [Field F]

/-- The hypotheses of completeness. -/
structure Complete (a d : F) : Prop where
  /-- `a` is a square. -/
  sq_a : ∃ c : F, c * c = a
  /-- `d` is not a square. -/
  nonsq_d : ∀ t : F, t * t ≠ d
  /-- The characteristic is not 2. -/
  two_ne_zero : (2 : F) ≠ 0

/-- `d w² = u²` with `w ≠ 0` makes `d` a square. -/
theorem sq_of_mul_sq {d u w : F} (hw : w ≠ 0) (h : d * w ^ 2 = u ^ 2) :
    (u / w) * (u / w) = d := by
  grind

/-- The identity behind completeness, for one sign `s` of `c x2 + s y2`. -/
theorem key_identity {a d c ε s x1 y1 x2 y2 : F} (hc : c * c = a) (hε : ε * ε = 1)
    (hs : s * s = 1) (hP : a * x1 ^ 2 + y1 ^ 2 = 1 + d * x1 ^ 2 * y1 ^ 2)
    (hQ : a * x2 ^ 2 + y2 ^ 2 = 1 + d * x2 ^ 2 * y2 ^ 2) (ht : d * x1 * x2 * y1 * y2 = ε) :
    d * (x1 * y1 * (c * x2 + s * y2)) ^ 2 = (c * x1 + s * ε * y1) ^ 2 := by
  grind

/-- No sum of two points on the curve has `d x1 x2 y1 y2 = ε` with `ε² = 1`. -/
theorem prod_ne {a d ε : F} (hc : Complete a d) (hε : ε * ε = 1) {P Q : Point F}
    (hP : OnCurve a d P) (hQ : OnCurve a d Q) : d * P.x * Q.x * P.y * Q.y ≠ ε := by
  intro ht
  obtain ⟨c, hcc⟩ := hc.sq_a
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h] at hε
    grind
  have hx1 : P.x ≠ 0 := by intro h; rw [h] at ht; grind
  have hy1 : P.y ≠ 0 := by intro h; rw [h] at ht; grind
  have hy2 : Q.y ≠ 0 := by intro h; rw [h] at ht; grind
  -- `c x2 + s y2 = 0` for both signs `s`, or `d` is a square.
  have zero_of (s : F) (hs : s * s = 1) : c * Q.x + s * Q.y = 0 := by
    apply Classical.byContradiction
    intro hne
    have hw : P.x * P.y * (c * Q.x + s * Q.y) ≠ 0 := mul_ne_zero (mul_ne_zero hx1 hy1) hne
    exact hc.nonsq_d _ (sq_of_mul_sq hw (key_identity hcc hε hs hP hQ ht))
  have hp := zero_of 1 (by grind)
  have hm := zero_of (-1) (by grind)
  have h2 : 2 * Q.y = 0 := by grind
  exact hy2 ((Field.of_mul_eq_zero h2).resolve_left hc.two_ne_zero)

/-- Completeness: on a complete curve every sum of two points on it is defined. -/
theorem defined {a d : F} (hc : Complete a d) {P Q : Point F} (hP : OnCurve a d P)
    (hQ : OnCurve a d Q) : Defined d P Q := by
  constructor
  · intro h
    exact prod_ne hc (ε := -1) (by grind) hP hQ (by simp only [denX] at h; grind)
  · intro h
    exact prod_ne hc (ε := 1) (by grind) hP hQ (by simp only [denY] at h; grind)

theorem onCurve_add {a d : F} (hc : Complete a d) {P Q : Point F} (hP : OnCurve a d P)
    (hQ : OnCurve a d Q) : OnCurve a d (add a d P Q) :=
  Ed25519Edwards.onCurve_add hP hQ (defined hc hP hQ)

/-- Associativity on a complete curve. -/
theorem add_assoc {a d : F} (hc : Complete a d) {P Q R : Point F} (hP : OnCurve a d P)
    (hQ : OnCurve a d Q) (hR : OnCurve a d R) :
    add a d (add a d P Q) R = add a d P (add a d Q R) :=
  Ed25519EdwardsAssoc.add_assoc hP hQ hR (defined hc hP hQ) (defined hc hQ hR)
    (defined hc (onCurve_add hc hP hQ) hR) (defined hc hP (onCurve_add hc hQ hR))

/-- `P + (-P) = 0` on a complete curve. -/
theorem add_neg {a d : F} (hc : Complete a d) {P : Point F} (hP : OnCurve a d P) :
    add a d P (neg P) = zero :=
  Ed25519Edwards.add_neg hP (defined hc hP (onCurve_neg hP)).2

end M0Crypto.Release.Ed25519EdwardsComplete
