import M0Crypto.Release.Ed25519EdwardsCert

/-!
Twisted Edwards curves `a x² + y² = 1 + d x² y²` over a field, with the addition of
RFC 8032 section 5.1.4:

`(x1, y1) + (x2, y2) = ((x1 y2 + y1 x2) / (1 + d x1 x2 y1 y2), (y1 y2 - a x1 x2) / (1 - d x1 x2 y1 y2))`.

The field, `a` and `d` are parameters. Division is total (`x / 0 = 0`), so `add` is defined
everywhere. `Defined d P Q` says both denominators of `add a d P Q` are nonzero; the laws
here take it as a hypothesis. `Ed25519EdwardsComplete` discharges it for complete curves.
This file proves commutativity, the neutral element `(0, 1)`, the inverse `(-x, y)` and
closure. Associativity is in `Ed25519EdwardsAssoc`.
-/

namespace M0Crypto.Release.Ed25519Edwards

open Lean.Grind

universe u

/-- A point in affine coordinates. -/
@[ext] structure Point (F : Type u) where
  x : F
  y : F

variable {F : Type u} [Field F]

/-- `P` lies on `a x² + y² = 1 + d x² y²`. -/
def OnCurve (a d : F) (P : Point F) : Prop :=
  a * P.x ^ 2 + P.y ^ 2 = 1 + d * P.x ^ 2 * P.y ^ 2

/-- The neutral element `(0, 1)`. -/
def zero : Point F := ⟨0, 1⟩

/-- The inverse `(-x, y)`. -/
def neg (P : Point F) : Point F := ⟨-P.x, P.y⟩

/-- Numerator of the x-coordinate of the sum. -/
def numX (P Q : Point F) : F := P.x * Q.y + P.y * Q.x

/-- Denominator of the x-coordinate of the sum. -/
def denX (d : F) (P Q : Point F) : F := 1 + d * P.x * Q.x * P.y * Q.y

/-- Numerator of the y-coordinate of the sum. -/
def numY (a : F) (P Q : Point F) : F := P.y * Q.y - a * P.x * Q.x

/-- Denominator of the y-coordinate of the sum. -/
def denY (d : F) (P Q : Point F) : F := 1 - d * P.x * Q.x * P.y * Q.y

/-- The sum of RFC 8032 section 5.1.4. -/
def add (a d : F) (P Q : Point F) : Point F :=
  ⟨numX P Q / denX d P Q, numY a P Q / denY d P Q⟩

/-- Both denominators of `add a d P Q` are nonzero. -/
def Defined (d : F) (P Q : Point F) : Prop :=
  denX d P Q ≠ 0 ∧ denY d P Q ≠ 0

/-! ### Field helpers -/

theorem mul_ne_zero {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) : u * v ≠ 0 :=
  fun h => (Field.of_mul_eq_zero h).elim hu hv

/-- Scaling numerator and denominator by a nonzero `k`; holds also when `B = 0`. -/
theorem div_scale {A B k : F} (hk : k ≠ 0) : A / B = (A * k) / (B * k) := by grind

/-- Equal cross products give equal quotients. -/
theorem div_eq_div {A B C D : F} (hB : B ≠ 0) (hD : D ≠ 0) (h : A * D = C * B) :
    A / B = C / D := by grind

/-- A point `(n / p, m / q)` with the denominators cleared. -/
theorem onCurve_div {a d n p m q : F} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : a * n ^ 2 * q ^ 2 + m ^ 2 * p ^ 2 = p ^ 2 * q ^ 2 + d * n ^ 2 * m ^ 2) :
    a * (n / p) ^ 2 + (m / q) ^ 2 = 1 + d * (n / p) ^ 2 * (m / q) ^ 2 := by
  grind

/-! ### Laws without associativity -/

theorem Defined.symm {d : F} {P Q : Point F} (h : Defined d P Q) : Defined d Q P := by
  simp only [Defined, denX, denY] at *
  constructor
  · have e : 1 + d * Q.x * P.x * Q.y * P.y = 1 + d * P.x * Q.x * P.y * Q.y := by grind
    exact e ▸ h.1
  · have e : 1 - d * Q.x * P.x * Q.y * P.y = 1 - d * P.x * Q.x * P.y * Q.y := by grind
    exact e ▸ h.2

theorem add_comm (a d : F) (P Q : Point F) : add a d P Q = add a d Q P := by
  have hn : numX P Q = numX Q P := by simp only [numX]; grind
  have hm : numY a P Q = numY a Q P := by simp only [numY]; grind
  have hp : denX d P Q = denX d Q P := by simp only [denX]; grind
  have hq : denY d P Q = denY d Q P := by simp only [denY]; grind
  simp only [add, hn, hm, hp, hq]

theorem add_zero (a d : F) (P : Point F) : add a d P zero = P := by
  ext
  · show (P.x * 1 + P.y * 0) / (1 + d * P.x * 0 * P.y * 1) = P.x
    grind
  · show (P.y * 1 - a * P.x * 0) / (1 - d * P.x * 0 * P.y * 1) = P.y
    grind

theorem zero_add (a d : F) (P : Point F) : add a d zero P = P := by
  rw [add_comm, add_zero]

theorem onCurve_zero (a d : F) : OnCurve a d (zero : Point F) := by
  show a * 0 ^ 2 + 1 ^ 2 = 1 + d * 0 ^ 2 * 1 ^ 2
  grind

theorem onCurve_neg {a d : F} {P : Point F} (h : OnCurve a d P) : OnCurve a d (neg P) := by
  simp only [OnCurve, neg] at *
  grind

/-- `P + (-P) = 0`. The x-denominator may vanish; the y-denominator may not. -/
theorem add_neg {a d : F} {P : Point F} (hP : OnCurve a d P) (hD : denY d P (neg P) ≠ 0) :
    add a d P (neg P) = zero := by
  simp only [OnCurve, denY, neg] at hP hD
  ext
  · show (P.x * P.y + P.y * -P.x) / (1 + d * P.x * -P.x * P.y * P.y) = 0
    grind
  · show (P.y * P.y - a * P.x * -P.x) / (1 - d * P.x * -P.x * P.y * P.y) = 1
    grind

theorem neg_add {a d : F} {P : Point F} (hP : OnCurve a d P) (hD : denY d P (neg P) ≠ 0) :
    add a d (neg P) P = zero := by
  rw [add_comm, add_neg hP hD]

/-- Closure: the sum of two points on the curve is on the curve. -/
theorem onCurve_add {a d : F} {P Q : Point F} (hP : OnCurve a d P) (hQ : OnCurve a d Q)
    (hD : Defined d P Q) : OnCurve a d (add a d P Q) := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  have c := Ed25519EdwardsCert.closure hP hQ
  obtain ⟨hp, hq⟩ := hD
  exact onCurve_div hp hq c

end M0Crypto.Release.Ed25519Edwards
