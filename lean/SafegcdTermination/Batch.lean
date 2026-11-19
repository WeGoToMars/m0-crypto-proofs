module

public import SafegcdTermination.Divsteps

@[expose] public section

namespace SafegcdTermination

/-! Algebraic contracts for the matrix, the two kinds of rows and the fold.
The matrix transports both the exact (f,g) pair and the modular (d,e) pair. -/

structure Row where
  a : Int
  b : Int

def Row.apply (r : Row) (x y : Int) : Int := r.a * x + r.b * y
def Row.norm (r : Row) : Int := magnitude (r.a) + magnitude (r.b)
def Row.twice (r : Row) : Row := ⟨2 * r.a, 2 * r.b⟩
def Row.plus (r s : Row) : Row := ⟨r.a + s.a, r.b + s.b⟩
def Row.minus (r s : Row) : Row := ⟨r.a - s.a, r.b - s.b⟩

theorem Row.twice_apply (r : Row) (x y : Int) :
    r.twice.apply x y = 2 * r.apply x y := by simp [Row.twice, Row.apply]; grind only

theorem Row.plus_apply (r s : Row) (x y : Int) :
    (r.plus s).apply x y = r.apply x y + s.apply x y := by simp [Row.plus, Row.apply]; grind only

theorem Row.minus_apply (r s : Row) (x y : Int) :
    (r.minus s).apply x y = r.apply x y - s.apply x y := by simp [Row.minus, Row.apply]; grind only

theorem Row.twice_norm (r : Row) : r.twice.norm = 2 * r.norm := by
  simp only [Row.norm, Row.twice, magnitude_mul, show magnitude 2 = 2 by decide]
  omega

theorem Row.plus_norm (r s : Row) : (r.plus s).norm ≤ r.norm + s.norm := by
  simp only [Row.norm, Row.plus]
  have h₁ := magnitude_add_le r.a s.a
  have h₂ := magnitude_add_le r.b s.b
  omega

theorem Row.minus_norm (r s : Row) : (r.minus s).norm ≤ r.norm + s.norm := by
  simp only [Row.norm, Row.minus]
  have h₁ := magnitude_add_le r.a (-s.a)
  have h₂ := magnitude_add_le r.b (-s.b)
  simp only [← Int.sub_eq_add_neg, magnitude_neg] at h₁ h₂
  omega

structure Matrix where
  f : Row
  g : Row

def Matrix.identity : Matrix := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩

def Matrix.swap (m : Matrix) : Matrix := ⟨m.g.twice, m.g.minus m.f⟩
def Matrix.odd (m : Matrix) : Matrix := ⟨m.f.twice, m.g.plus m.f⟩
def Matrix.even (m : Matrix) : Matrix := ⟨m.f.twice, m.g⟩

def Matrix.next (m : Matrix) (s : DivstepState) : Matrix :=
  if 0 < s.delta ∧ s.g % 2 = 1 then m.swap
  else if s.g % 2 = 1 then m.odd else m.even

def Matrix.det (m : Matrix) : Int := m.f.a * m.g.b - m.f.b * m.g.a

theorem Matrix.next_det (m : Matrix) (s : DivstepState) :
    (m.next s).det = 2 * m.det := by
  unfold next
  split
  · simp [swap, det, Row.twice, Row.minus]; grind only
  · split
    · simp [odd, det, Row.twice, Row.plus]; grind only
    · simp [even, det, Row.twice]; grind only

def Matrix.Bounds (m : Matrix) (b : Int) : Prop := m.f.norm ≤ b ∧ m.g.norm ≤ b

theorem Matrix.next_bounds (m : Matrix) (s : DivstepState) {b : Int}
    (h : m.Bounds b) (hb : 0 ≤ b) : (m.next s).Bounds (2 * b) := by
  obtain ⟨hf, hg⟩ := h
  unfold next
  split
  · exact ⟨by change m.g.twice.norm ≤ _; rw [Row.twice_norm]; omega,
           Int.le_trans (m.g.minus_norm m.f) (by omega)⟩
  · split
    · exact ⟨by change m.f.twice.norm ≤ _; rw [Row.twice_norm]; omega,
             Int.le_trans (m.g.plus_norm m.f) (by omega)⟩
    · exact ⟨by change m.f.twice.norm ≤ _; rw [Row.twice_norm]; omega, by change m.g.norm ≤ 2 * b; omega⟩

/-- Run the scalar recurrence with the matrix updates driven by the same branch decisions. -/
def accumulate (s : DivstepState) : Nat → DivstepState × Matrix
  | 0 => (s, .identity)
  | n+1 =>
    let (t, m) := accumulate s n
    (step t, m.next t)

private theorem step_odd (s : DivstepState) (h : s.f % 2 = 1) :
    (step s).f % 2 = 1 := by
  unfold step
  split
  · rename_i hs
    exact hs.2
  · exact h

private theorem Matrix.next_image (m : Matrix) (s : DivstepState) (x y scale : Int)
    (ho : s.f % 2 = 1) (hf : m.f.apply x y = scale * s.f)
    (hg : m.g.apply x y = scale * s.g) :
    (m.next s).f.apply x y = (2 * scale) * (step s).f ∧
    (m.next s).g.apply x y = (2 * scale) * (step s).g := by
  unfold Matrix.next step
  split
  · rename_i hs
    have he : 2 * ((s.g - s.f) / 2) = s.g - s.f := by have := hs.2; omega
    simp only [Matrix.swap, Row.twice_apply, Row.minus_apply, hf, hg]
    constructor
    · grind only
    · calc
        _ = scale * (s.g - s.f) := by grind only
        _ = _ := by grind only
  · split
    · rename_i hs
      have he : 2 * ((s.g + s.f) / 2) = s.g + s.f := by omega
      simp only [Matrix.odd, Row.twice_apply, Row.plus_apply, hf, hg, hs, Int.one_mul]
      constructor
      · grind only
      · calc
          _ = scale * (s.g + s.f) := by grind only
          _ = _ := by grind only
    · rename_i hs
      have hp : s.g % 2 = 0 := by omega
      have he : 2 * (s.g / 2) = s.g := by omega
      simp only [Matrix.even, Row.twice_apply, hf, hg, hp, Int.zero_mul, Int.add_zero]
      constructor
      · grind only
      · grind only

theorem accumulate_contract (s : DivstepState) (h : s.f % 2 = 1) (n : Nat) :
    let (t, m) := accumulate s n
    t.f % 2 = 1 ∧ m.det = 2 ^ n ∧ m.Bounds (2 ^ n) ∧
      m.f.apply s.f s.g = 2 ^ n * t.f ∧ m.g.apply s.f s.g = 2 ^ n * t.g := by
  induction n with
  | zero =>
    have hm : Matrix.identity.Bounds 1 := by unfold Matrix.Bounds; decide
    simpa [accumulate, Matrix.identity, Matrix.det, Row.apply, h] using hm
  | succ n ih =>
    simp only [accumulate] at ⊢
    obtain ⟨ho, hd, hb, hf, hg⟩ := ih
    rw [Int.pow_succ', Matrix.next_det, hd]
    exact ⟨step_odd _ ho, rfl, Matrix.next_bounds _ _ hb (Int.pow_nonneg (by decide)),
      Matrix.next_image _ _ _ _ _ ho hf hg⟩

def batchSteps : Nat := 14
def batchCount : Nat := 43
def batchScale : Int := 2 ^ batchSteps

theorem one_matrix (s : DivstepState) (h : s.f % 2 = 1) :
    let (t, m) := accumulate s batchSteps
    t.f % 2 = 1 ∧ m.det = batchScale ∧ m.Bounds batchScale ∧
      m.f.apply s.f s.g = batchScale * t.f ∧ m.g.apply s.f s.g = batchScale * t.g :=
  accumulate_contract s h batchSteps

end SafegcdTermination
