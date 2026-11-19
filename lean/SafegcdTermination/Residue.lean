module

public import SafegcdTermination.Batch
public import SafegcdTermination.Congruence

@[expose] public section

namespace SafegcdTermination

def foldRadix : Int := 2 ^ 255

theorem prime_eq : p = foldRadix - 19 := rfl

/-- The internal fold admits a small range past each end of the canonical interval. -/
def ResidueBounds (x : Int) : Prop := -38 ≤ x ∧ x < foldRadix + 38

def correction (n : Int) : Int := n * 2587 % batchScale

def rowQuotient (n : Int) : Int := (n + correction n * p) / batchScale

def fold (x : Int) : Int := x % foldRadix + 19 * (x / foldRadix)

theorem correction_bounds (n : Int) : 0 ≤ correction n ∧ correction n < batchScale :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem correction_exact (n : Int) : (n + correction n * p) % batchScale = 0 := by
  unfold correction
  rw [Int.add_emod, Int.mul_emod, show p % batchScale = 16365 by decide +kernel, Int.emod_emod]
  change (n % 16384 + (n * 2587 % 16384 * 16365) % 16384) % 16384 = 0
  omega

theorem rowQuotient_exact (n : Int) : batchScale * rowQuotient n = n + correction n * p := by
  have he := Int.mul_ediv_add_emod (n + correction n * p) batchScale
  rw [correction_exact, Int.add_zero] at he
  exact he

private theorem dot_bound {r : Row} {x y b : Int} (hx : magnitude (x) ≤ b) (hy : magnitude (y) ≤ b) :
    magnitude (r.apply x y) ≤ r.norm * b := by
  calc
    _ ≤ magnitude (r.a * x) + magnitude (r.b * y) := magnitude_add_le _ _
    _ = magnitude (r.a) * magnitude (x) + magnitude (r.b) * magnitude (y) := by simp only [magnitude_mul]
    _ ≤ magnitude (r.a) * b + magnitude (r.b) * b := Int.add_le_add
      (Int.mul_le_mul_of_nonneg_left hx (magnitude_nonneg _))
      (Int.mul_le_mul_of_nonneg_left hy (magnitude_nonneg _))
    _ = _ := by unfold Row.norm; grind only

theorem rowQuotient_range {r : Row} {x y : Int} (hr : r.norm ≤ batchScale)
    (hx : ResidueBounds x) (hy : ResidueBounds y) :
    -2 * foldRadix ≤ rowQuotient (r.apply x y) ∧
      rowQuotient (r.apply x y) < 3 * foldRadix := by
  have h₁ : magnitude (x) ≤ foldRadix + 38 := magnitude_le_iff.mpr ⟨by have := (show 0 ≤ foldRadix by decide); unfold ResidueBounds at hx; omega, Int.le_of_lt hx.2⟩
  have h₂ : magnitude (y) ≤ foldRadix + 38 := magnitude_le_iff.mpr ⟨by have := (show 0 ≤ foldRadix by decide); unfold ResidueBounds at hy; omega, Int.le_of_lt hy.2⟩
  have hdot := Int.le_trans (dot_bound h₁ h₂) (Int.mul_le_mul_of_nonneg_right hr
    (show 0 ≤ foldRadix + 38 by decide))
  rw [magnitude_le_iff] at hdot
  have he := rowQuotient_exact (r.apply x y)
  have hc := correction_bounds (r.apply x y)
  have hp : 0 < p := by decide
  have hc₁ := Int.mul_nonneg hc.1 (Int.le_of_lt hp)
  have hc₂ := Int.mul_lt_mul_of_pos_right hc.2 hp
  have hd : 0 < batchScale := by decide
  constructor
  · apply (Int.mul_le_mul_left hd).mp
    rw [he]
    have hn : batchScale * (-2 * foldRadix) ≤ -(batchScale * (foldRadix + 38)) := by decide
    omega
  · apply (Int.mul_lt_mul_left hd).mp
    rw [he]
    have hn : batchScale * (foldRadix + 38) + batchScale * p ≤ batchScale * (3 * foldRadix) := by decide
    omega

theorem fold_range {x : Int} (hlo : -2 * foldRadix ≤ x) (hhi : x < 3 * foldRadix) :
    ResidueBounds (fold x) := by
  have hR : 0 < foldRadix := by decide
  have hlo' : -2 ≤ x / foldRadix := (Int.le_ediv_iff_mul_le hR).mpr (by rwa [Int.mul_comm])
  have hhi' : x / foldRadix < 3 := (Int.ediv_lt_iff_lt_mul hR).mpr (by rwa [Int.mul_comm])
  have hm₀ := Int.emod_nonneg x (Int.ne_of_gt hR)
  have hm₁ := Int.emod_lt_of_pos x hR
  unfold ResidueBounds fold
  omega

theorem fold_congr (x : Int) : fold x ≡ x [ZMOD p] := by
  rw [Congruence.iff_dvd]
  refine ⟨x / foldRadix, ?_⟩
  have he := Int.mul_ediv_add_emod x foldRadix
  rw [prime_eq]; unfold fold
  grind only

private theorem scale_coprime : p.gcd batchScale = 1 := by decide +kernel

theorem scale_cancel {x y : Int} (h : batchScale * x ≡ batchScale * y [ZMOD p]) :
    x ≡ y [ZMOD p] := by
  rw [Congruence.iff_dvd, ← Int.mul_sub] at h
  apply Congruence.iff_dvd.mpr
  simpa only [scale_coprime, Int.natCast_one, Int.one_mul] using Int.dvd_gcd_mul_iff_dvd_mul.mpr h

theorem rowQuotient_congr (n : Int) : batchScale * rowQuotient n ≡ n [ZMOD p] := by
  rw [rowQuotient_exact, Congruence.iff_dvd]
  exact ⟨-correction n, by grind only⟩

/-- A batch's exact remainder state and the accompanying field representatives.
The fixed input z is not stored in the batch state. -/
structure BatchState where
  scalar : DivstepState
  d : Int
  e : Int

def BatchState.valid (z : Int) (s : BatchState) : Prop :=
  s.scalar.f % 2 = 1 ∧ ResidueBounds s.d ∧ ResidueBounds s.e ∧
    (s.d * z ≡ s.scalar.f [ZMOD p]) ∧ (s.e * z ≡ s.scalar.g [ZMOD p])

def BatchState.next (s : BatchState) : BatchState :=
  let (t, m) := accumulate s.scalar batchSteps
  ⟨t, fold (rowQuotient (m.f.apply s.d s.e)), fold (rowQuotient (m.g.apply s.d s.e))⟩

private theorem row_preserves {r : Row} {Q x y F G z : Int}
    (hx : x * z ≡ F [ZMOD p]) (hy : y * z ≡ G [ZMOD p])
    (hi : r.apply F G = batchScale * Q) :
    fold (rowQuotient (r.apply x y)) * z ≡ Q [ZMOD p] := by
  have hrow := ((fold_congr (rowQuotient (r.apply x y))).mul_left batchScale).trans
    (rowQuotient_congr _)
  have hlin := (hx.mul_left r.a).add (hy.mul_left r.b)
  have hc : r.apply x y * z ≡ r.apply F G [ZMOD p] := by
    unfold Row.apply
    simpa only [Int.add_mul, Int.mul_assoc] using hlin
  apply scale_cancel
  rw [← Int.mul_assoc, ← hi]
  exact (hrow.mul_right z).trans hc

theorem batch_valid {z : Int} (s : BatchState) (hs : s.valid z) : s.next.valid z := by
  obtain ⟨ho, hd, he, hf, hg⟩ := hs
  obtain ⟨ho', _, ⟨hF, hG⟩, hFi, hGi⟩ := one_matrix s.scalar ho
  have ⟨df, dt⟩ := rowQuotient_range hF hd he
  have ⟨ef, et⟩ := rowQuotient_range hG hd he
  exact ⟨ho', fold_range df dt, fold_range ef et, row_preserves hf hg hFi, row_preserves hf hg hGi⟩

end SafegcdTermination
