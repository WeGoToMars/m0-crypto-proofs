module

public import SafegcdTermination.Residue

@[expose] public section

namespace SafegcdTermination

private theorem gcd_two {f : Int} (h : f % 2 = 1) : f.gcd 2 = 1 := by
  apply Nat.dvd_one.mp
  have hd := Int.gcd_dvd_left f 2
  have he := Int.gcd_dvd_right f 2
  apply Int.natCast_dvd_natCast.mp
  change (↑(f.gcd 2) : Int) ∣ (1 : Int)
  rw [show (1 : Int) = f % 2 from h.symm]
  rw [Int.emod_def]
  exact Int.dvd_sub hd (Int.dvd_mul_of_dvd_left (c := f / 2) he)

private theorem step_gcd (s : DivstepState) (h : s.f % 2 = 1) :
    (step s).f.gcd (step s).g = s.f.gcd s.g := by
  unfold step
  split
  · rename_i hs
    change s.g.gcd ((s.g - s.f) / 2) = _
    have he : 2 * ((s.g - s.f) / 2) = s.g - s.f := by have := hs.2; omega
    rw [← Int.gcd_mul_right_right_of_gcd_eq_one (gcd_two hs.2), he,
      Int.gcd_self_sub_right, Int.gcd_comm]
  · change s.f.gcd ((s.g + s.g % 2 * s.f) / 2) = _
    have ho : s.g % 2 = 0 ∨ s.g % 2 = 1 := by omega
    have he : 2 * ((s.g + s.g % 2 * s.f) / 2) = s.g + s.g % 2 * s.f := by
      rcases ho with ho | ho <;> rw [ho] <;> simp <;> omega
    rw [← Int.gcd_mul_right_right_of_gcd_eq_one (gcd_two h), he, Int.gcd_add_mul_right_right]

/-- Each scalar remainder stays within the input magnitude bound. -/
theorem step_scalar_bound (s : DivstepState) (b : Int)
    (hf : magnitude (s.f) ≤ b) (hg : magnitude (s.g) ≤ b) :
    magnitude ((step s).f) ≤ b ∧ magnitude ((step s).g) ≤ b := by
  obtain ⟨hf₁, hf₂⟩ := magnitude_le_iff.mp hf
  obtain ⟨hg₁, hg₂⟩ := magnitude_le_iff.mp hg
  unfold step
  split
  · refine ⟨hg, magnitude_le_iff.mpr ?_⟩
    change -b ≤ (s.g - s.f) / 2 ∧ (s.g - s.f) / 2 ≤ b
    constructor <;> omega
  · refine ⟨hf, magnitude_le_iff.mpr ?_⟩
    have hm : s.g % 2 = 0 ∨ s.g % 2 = 1 := by omega
    rcases hm with h | h <;> simp [h] <;> constructor <;> omega

theorem accumulate_scalar_bound (s : DivstepState) (b : Int)
    (hf : magnitude (s.f) ≤ b) (hg : magnitude (s.g) ≤ b) (n : Nat) :
    magnitude ((accumulate s n).1.f) ≤ b ∧ magnitude ((accumulate s n).1.g) ≤ b := by
  induction n with
  | zero => exact ⟨hf, hg⟩
  | succ n ih => exact step_scalar_bound _ b ih.1 ih.2

theorem accumulate_gcd (s : DivstepState) (h : s.f % 2 = 1) (n : Nat) :
    (accumulate s n).1.f.gcd (accumulate s n).1.g = s.f.gcd s.g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step (accumulate s n).1).f.gcd (step (accumulate s n).1).g = _
    rw [step_gcd _ (accumulate_contract s h n).1, ih]

theorem accumulate_append (s : DivstepState) (m n : Nat) :
    (accumulate (accumulate s m).1 n).1 = (accumulate s (m+n)).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (accumulate (accumulate s m).1 n).1 = step (accumulate s (m+n)).1
    rw [ih]

theorem accumulate_zero (s : DivstepState) (h : s.g = 0) (n : Nat) :
    (accumulate s n).1.g = 0 ∧ (accumulate s n).2.f = ⟨2^n, 0⟩ := by
  induction n with
  | zero => exact ⟨h, rfl⟩
  | succ n ih =>
    change (step (accumulate s n).1).g = 0 ∧
      ((accumulate s n).2.next (accumulate s n).1).f = ⟨2^(n+1), 0⟩
    simp [step, Matrix.next, Matrix.even, Row.twice, ih.1, ih.2, Int.pow_succ']

def initial (z : Int) : BatchState := ⟨⟨1, p, z⟩, 0, 1⟩

def iterate (z : Int) : Nat → BatchState
  | 0 => initial z
  | n+1 => (iterate z n).next

theorem iterate_valid (z : Int) (n : Nat) : (iterate z n).valid z := by
  induction n with
  | zero =>
    refine ⟨by change p % 2 = 1; decide +kernel,
      by change -38 ≤ (0 : Int) ∧ 0 < foldRadix + 38; decide +kernel,
      by change -38 ≤ (1 : Int) ∧ 1 < foldRadix + 38; decide +kernel, ?_, ?_⟩
    · change 0 * z ≡ p [ZMOD p]
      rw [Int.zero_mul, Congruence.iff_dvd, Int.sub_zero]; exact Int.dvd_refl _
    · change 1 * z ≡ z [ZMOD p]
      rw [Int.one_mul]; exact Congruence.refl _
  | succ n ih => exact batch_valid _ ih

theorem iterate_scalar (z : Int) (n : Nat) :
    (iterate z n).scalar = (accumulate (initial z).scalar (n * batchSteps)).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (accumulate (iterate z n).scalar batchSteps).1 = _
    rw [ih, accumulate_append, Nat.succ_mul]

theorem accumulate_walk (z : Int) (n : Nat) :
    (accumulate (initial z).scalar n).1 = walk p z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (accumulate (initial z).scalar n).1 = step (walk p z n)
    rw [ih]

theorem terminal {z : Int} (hz : 0 ≤ z) (hp : z < p) :
    (iterate z batchCount).scalar.g = 0 ∧
      (iterate z batchCount).scalar.f.natAbs = p.gcd z := by
  rw [iterate_scalar]
  have h : (accumulate (initial z).scalar (batchCount * batchSteps)).1.g = 0 := by
    rw [accumulate_walk]
    exact curve25519_terminates z hz hp
  have hg := accumulate_gcd (initial z).scalar (by change p % 2 = 1; decide +kernel) (batchCount * batchSteps)
  rw [h, Int.gcd_zero_right] at hg
  exact ⟨h, hg⟩

theorem zero_iterate (n : Nat) : (iterate 0 n).d = 0 ∧ (iterate 0 n).scalar.g = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h := accumulate_zero (iterate 0 n).scalar ih.2 batchSteps
    change fold (rowQuotient ((accumulate (iterate 0 n).scalar batchSteps).2.f.apply
      (iterate 0 n).d (iterate 0 n).e)) = 0 ∧
        (accumulate (iterate 0 n).scalar batchSteps).1.g = 0
    rw [h.2, ih.1]
    exact ⟨by simp [Row.apply, rowQuotient, correction, fold], h.1⟩

theorem zero_final_f (n : Nat) : (iterate 0 n).scalar.f = p := by
  have keep (s : DivstepState) (h : s.g = 0) (k : Nat) : (accumulate s k).1.f = s.f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hz := (accumulate_zero s h k).1
      change (step (accumulate s k).1).f = s.f
      simp [step,hz,ih]
  induction n with
  | zero => rfl
  | succ n ih =>
    change (accumulate (iterate 0 n).scalar batchSteps).1.f = p
    rw [keep _ (zero_iterate n).2,ih]

theorem last_fold_range {x : Int} (h : ResidueBounds x) : 0 ≤ fold x ∧ fold x < foldRadix := by
  have hR : 0 < foldRadix := by decide
  have hRl : 57 < foldRadix := by decide
  have hlo : -1 ≤ x / foldRadix := (Int.le_ediv_iff_mul_le hR).mpr (by
    rw [Int.mul_comm]; have := h.1; omega)
  have hhi : x / foldRadix < 2 := (Int.ediv_lt_iff_lt_mul hR).mpr (by
    rw [Int.mul_comm]; have := h.2; omega)
  have hm0 := Int.emod_nonneg x (Int.ne_of_gt hR)
  have hm1 := Int.emod_lt_of_pos x hR
  have hd := Int.mul_ediv_add_emod x foldRadix
  have hq : x / foldRadix = -1 ∨ x / foldRadix = 0 ∨ x / foldRadix = 1 := by omega
  unfold ResidueBounds at h
  unfold fold
  rcases hq with hq | hq | hq <;> rw [hq] at hd ⊢ <;> simp at hd ⊢ <;> omega

/-- Signed representative before the terminal selection's field encoding. -/
def inverse (z : Int) : Int :=
  let s := iterate z batchCount
  if s.scalar.f < 0 then -fold s.d else fold s.d

theorem inverse_zero : inverse 0 = 0 := by
  dsimp only [inverse]
  rw [(zero_iterate batchCount).1]
  simp [fold]

theorem inverse_correct {z : Int} (hz : 0 ≤ z) (hp : z < p) (hc : p.gcd z = 1) :
    inverse z * z ≡ 1 [ZMOD p] := by
  let s := iterate z batchCount
  have hf : s.scalar.f.natAbs = 1 := (terminal hz hp).2.trans hc
  have h : fold s.d * z ≡ s.scalar.f [ZMOD p] :=
    ((fold_congr s.d).mul_right z).trans (iterate_valid z batchCount).2.2.2.1
  change (if s.scalar.f < 0 then -fold s.d else fold s.d) * z ≡ 1 [ZMOD p]
  split
  · rename_i hn
    have hf' : s.scalar.f = -1 := by omega
    rw [hf'] at h
    simpa only [Int.neg_mul, Int.neg_neg] using h.neg
  · have hf' : s.scalar.f = 1 := by omega
    exact hf' ▸ h

end SafegcdTermination
