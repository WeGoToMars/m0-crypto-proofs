import M0Crypto.Release.Ed25519Edwards

/-!
Associativity of the twisted Edwards addition.

`(P1 + P2) + P3` and `P1 + (P2 + P3)` are both quotients once the inner sum
`(n / p, m / q)` is substituted and its denominators are cleared (`add_div_left`,
`add_div_right`). Their cross products agree on the curve by the certificates
`Ed25519EdwardsCert.assoc_x` and `assoc_y`. The hypotheses are the three curve equations
and the four `Defined` conditions of the sums involved; `Ed25519EdwardsComplete` derives
the latter on complete curves.
-/

namespace M0Crypto.Release.Ed25519EdwardsAssoc

open Lean.Grind M0Crypto.Release.Ed25519Edwards

universe u

variable {F : Type u} [Field F]

/-- The sum with a left operand `(n / p, m / q)`, denominators cleared. -/
theorem add_div_left (a d : F) {n p m q : F} (R : Point F) (hp : p ≠ 0) (hq : q ≠ 0) :
    add a d ⟨n / p, m / q⟩ R =
      ⟨(n * q * R.y + m * p * R.x) / (p * q + d * n * m * R.x * R.y),
       (m * p * R.y - a * n * q * R.x) / (p * q - d * n * m * R.x * R.y)⟩ := by
  have hk := mul_ne_zero hp hq
  ext
  · show (n / p * R.y + m / q * R.x) / (1 + d * (n / p) * R.x * (m / q) * R.y) = _
    rw [div_scale hk]
    congr 1 <;> grind
  · show (m / q * R.y - a * (n / p) * R.x) / (1 - d * (n / p) * R.x * (m / q) * R.y) = _
    rw [div_scale hk]
    congr 1 <;> grind

/-- The sum with a right operand `(n / p, m / q)`, denominators cleared. -/
theorem add_div_right (a d : F) {n p m q : F} (P : Point F) (hp : p ≠ 0) (hq : q ≠ 0) :
    add a d P ⟨n / p, m / q⟩ =
      ⟨(P.x * m * p + P.y * n * q) / (p * q + d * P.x * P.y * n * m),
       (P.y * m * p - a * P.x * n * q) / (p * q - d * P.x * P.y * n * m)⟩ := by
  rw [add_comm, add_div_left a d P hp hq]
  ext
  · show _ / _ = _ / _
    congr 1 <;> grind
  · show _ / _ = _ / _
    congr 1 <;> grind

/-- The cleared denominators of `add_div_left` are nonzero when the sum is defined. -/
theorem den_div_left {d n p m q : F} (R : Point F) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : Defined d ⟨n / p, m / q⟩ R) :
    p * q + d * n * m * R.x * R.y ≠ 0 ∧ p * q - d * n * m * R.x * R.y ≠ 0 := by
  have hk := mul_ne_zero hp hq
  obtain ⟨h1, h2⟩ := h
  simp only [denX, denY] at h1 h2
  have e1 : (1 + d * (n / p) * R.x * (m / q) * R.y) * (p * q)
      = p * q + d * n * m * R.x * R.y := by grind
  have e2 : (1 - d * (n / p) * R.x * (m / q) * R.y) * (p * q)
      = p * q - d * n * m * R.x * R.y := by grind
  exact ⟨e1 ▸ mul_ne_zero h1 hk, e2 ▸ mul_ne_zero h2 hk⟩

/-- The cleared denominators of `add_div_right` are nonzero when the sum is defined. -/
theorem den_div_right {d n p m q : F} (P : Point F) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : Defined d P ⟨n / p, m / q⟩) :
    p * q + d * P.x * P.y * n * m ≠ 0 ∧ p * q - d * P.x * P.y * n * m ≠ 0 := by
  obtain ⟨h1, h2⟩ := den_div_left P hp hq h.symm
  have e1 : p * q + d * n * m * P.x * P.y = p * q + d * P.x * P.y * n * m := by grind
  have e2 : p * q - d * n * m * P.x * P.y = p * q - d * P.x * P.y * n * m := by grind
  exact ⟨e1 ▸ h1, e2 ▸ h2⟩

/-- Associativity, for points on the curve whose four sums are defined. -/
theorem add_assoc {a d : F} {P Q R : Point F}
    (hP : OnCurve a d P) (hQ : OnCurve a d Q) (hR : OnCurve a d R)
    (hPQ : Defined d P Q) (hQR : Defined d Q R)
    (hPQ_R : Defined d (add a d P Q) R) (hP_QR : Defined d P (add a d Q R)) :
    add a d (add a d P Q) R = add a d P (add a d Q R) := by
  show add a d ⟨numX P Q / denX d P Q, numY a P Q / denY d P Q⟩ R
    = add a d P ⟨numX Q R / denX d Q R, numY a Q R / denY d Q R⟩
  obtain ⟨hL1, hL2⟩ := den_div_left R hPQ.1 hPQ.2 hPQ_R
  obtain ⟨hR1, hR2⟩ := den_div_right P hQR.1 hQR.2 hP_QR
  rw [add_div_left a d R hPQ.1 hPQ.2, add_div_right a d P hQR.1 hQR.2]
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  obtain ⟨x3, y3⟩ := R
  have cx := Ed25519EdwardsCert.assoc_x hP hQ hR
  have cy := Ed25519EdwardsCert.assoc_y hP hQ hR
  simp only [numX, denX, numY, denY] at hL1 hL2 hR1 hR2 ⊢
  exact Point.ext (div_eq_div hL1 hR1 (by grind)) (div_eq_div hL2 hR2 (by grind))

end M0Crypto.Release.Ed25519EdwardsAssoc
