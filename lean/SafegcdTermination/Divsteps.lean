module

public import SafegcdTermination.Contraction

@[expose] public section

namespace SafegcdTermination

structure DivstepState where
  delta : Int
  f : Int
  g : Int

/-- Half-delta recurrence, with doubled half-delta counter initialized at 1.
The step continues even after g = 0, as in the assembly schedule. -/
def step (s : DivstepState) : DivstepState :=
  if 0 < s.delta ∧ s.g % 2 = 1 then
    ⟨2 - s.delta, s.g, (s.g - s.f) / 2⟩
  else
    ⟨2 + s.delta, s.f, (s.g + (s.g % 2) * s.f) / 2⟩

def walk (f g : Int) : Nat → DivstepState
  | 0 => ⟨1, f, g⟩
  | n + 1 => step (walk f g n)

private theorem zero_stays (s : DivstepState) (hz : s.g = 0) : (step s).g = 0 := by
  simp [step, hz]

private theorem f_odd_step (s : DivstepState) (hf : s.f % 2 = 1) : (step s).f % 2 = 1 := by
  unfold step
  split
  · rename_i h
    exact h.2
  · exact hf

private theorem step_swap (s : DivstepState) (hf : s.f % 2 = 1)
    (hd : 0 < s.delta) (hg : s.g % 2 = 1) :
    (step s).delta = 2 - s.delta ∧ (step s).f = s.g ∧
    (2 : Int) * ((step s).g : Int) = (s.g : Int) - s.f := by
  simp only [step, hd, hg, and_self, ↓reduceIte, true_and]
  omega

private theorem step_keep (s : DivstepState) (hf : s.f % 2 = 1)
    (hs : ¬ (0 < s.delta ∧ s.g % 2 = 1)) :
    (step s).delta = 2 + s.delta ∧ (step s).f = s.f ∧
    (2 : Int) * ((step s).g : Int) = (s.g : Int) + ((s.g % 2 : Int) : Int) * s.f := by
  simp only [step, hs, ↓reduceIte, true_and]
  have he : s.g % 2 = 0 ∨ s.g % 2 = 1 := by omega
  rcases he with he | he
  · simp only [he, Int.zero_mul, Int.add_zero]
    omega
  · simp only [he, Int.one_mul]
    omega

/-- Since the previous visit to delta=1, only even steps have run. -/
def BeforeSwap (n : Nat) (s : DivstepState) : Prop :=
  ∃ m j : Nat, n = m + j ∧ s.delta = 2 * (j : Int) + 1 ∧
    Bounded m s.f ((2 : Int)^j * s.g)

/-- There were j even steps, a swap, and k < j further steps. The bit
accumulator q records the additions of the new f during those k steps. -/
def AfterSwap (n : Nat) (s : DivstepState) : Prop :=
  ∃ (m j k q : Nat) (f₀ : Int), n = m + j + 1 + k ∧
    s.delta = 2 * ((k : Int) - j) + 1 ∧ k < j ∧ q < 2 ^ k ∧ s.f ≠ 0 ∧
    Bounded m f₀ ((2 : Int)^j * s.f) ∧
    (2 : Int) ^ (k+1) * s.g = (1 + 2 * (q : Int)) * s.f - f₀

private theorem phase_before (n : Nat) (s : DivstepState) (hf : s.f % 2 = 1)
    (h : BeforeSwap n s) : BeforeSwap (n+1) (step s) ∨ AfterSwap (n+1) (step s) := by
  obtain ⟨m, j, rfl, hd, hb⟩ := h
  by_cases hg : s.g % 2 = 1
  · obtain ⟨hδ, hF, hG⟩ := step_swap s hf (by omega) hg
    rcases j with _ | j
    · left
      refine ⟨m + 1, 0, by omega, by simp; omega, ?_⟩
      have h := contract m 0 (1 : Int) hb (by decide)
        (F := ((step s).f : Int)) (G := ((step s).g : Int))
        (by simp [hF]) (by simpa using hG)
      simpa using h
    · right
      refine ⟨m, j+1, 0, 0, (s.f : Int), by omega, by simp only [Int.natCast_succ]; omega, by omega,
        by decide, by omega, ?_, ?_⟩
      · rw [hF]; exact hb
      · simpa [hF] using hG
  · left
    have he : s.g % 2 = 0 := by omega
    obtain ⟨hδ, hF, hG⟩ := step_keep s hf (fun h => hg h.2)
    refine ⟨m, j+1, by omega, by simp only [Int.natCast_succ]; omega, ?_⟩
    have eq : (2 : Int)^(j+1) * (step s).g = (2 : Int)^j * s.g := by
      rw [Int.pow_succ, Int.mul_assoc, hG, he]
      simp
    rw [hF, eq]
    exact hb

private theorem phase_after (n : Nat) (s : DivstepState) (hf : s.f % 2 = 1)
    (h : AfterSwap n s) : BeforeSwap (n+1) (step s) ∨ AfterSwap (n+1) (step s) := by
  obtain ⟨m, j, k, q, f₀, rfl, hδ, hkj, hq, hnz, hb, hG⟩ := h
  have hd : ¬ (0 < s.delta ∧ s.g % 2 = 1) := by omega
  obtain ⟨hd', hF, hG'⟩ := step_keep s hf hd
  let e : Nat := (s.g % 2).toNat
  let Q := q + 2 ^ k * e
  have he : (e : Int) = s.g % 2 := Int.toNat_of_nonneg (by omega)
  have hel : e ≤ 1 := by omega
  have hQ : Q < 2 ^ (k+1) := by
    have h := Nat.mul_le_mul_left (2 ^ k) hel
    unfold Q
    rw [Nat.pow_succ]
    omega
  have hgg : (2 : Int)^((k+1)+1) * (step s).g = (1 + 2 * (Q : Int)) * (step s).f - f₀ := by
    rw [Int.pow_succ, Int.mul_assoc, hG', Int.mul_add, hG, hF, ← he]
    simp only [Q, Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.pow_succ]
    grind only
  by_cases hEnd : k + 1 = j
  · left
    refine ⟨m+(2*j+1), 0, by omega, by simp; omega, ?_⟩
    rw [hEnd] at hgg hQ
    have hQi : Q + 1 ≤ 2 ^ j := by omega
    have hQi' : (Q : Int) + 1 ≤ (2 : Int)^j := by
      have h := Int.ofNat_le.mpr hQi
      simpa using h
    have hG'' : (2 : Int) ^ (2*j+1) * (step s).g =
        (1+2*(Q : Int)) * ((2 : Int)^j * s.f) - (2 : Int)^j * f₀ := by
      rw [show 2*j+1 = j+(j+1) by omega, Int.pow_add, Int.mul_assoc, hgg, hF]
      grind only
    have h := contract m j (1+2*(Q : Int)) hb (by constructor <;> omega)
      (F := ((step s).f : Int)) (G := ((step s).g : Int))
      (by rw [hF]) hG''
    simpa using h
  · right
    refine ⟨m, j, k+1, Q, f₀, by omega, by simp only [Int.natCast_succ]; omega, by omega,
      hQ, by simpa [hF] using hnz, by simpa [hF] using hb, hgg⟩

theorem walk_phases (g : Int) (hg : 0 ≤ g) (hgp : g < p) (n : Nat) :
    let s := walk p g n
    s.f % 2 = 1 ∧ (s.g = 0 ∨ BeforeSwap n s ∨ AfterSwap n s) := by
  induction n with
  | zero =>
    refine ⟨by change p % 2 = 1; decide +kernel, .inr (.inl ⟨0, 0, rfl, rfl, ?_⟩)⟩
    simpa [walk] using seed g hg (Int.le_of_lt hgp)
  | succ n ih =>
    obtain ⟨hf, h⟩ := ih
    refine ⟨f_odd_step _ hf, ?_⟩
    rcases h with hzero | hh | hh
    · exact .inl (zero_stays _ hzero)
    · exact .inr (phase_before _ _ hf hh)
    · exact .inr (phase_after _ _ hf hh)

private theorem before_cut (m j : Nat) (hm : m ≤ 602) (hj : 601 ≤ m + 2*j) :
    1055 * boundNumerator m < (2 : Int)^j * boundDenominator m := by
  let k := (602-m)/2
  have hk : k ≤ j := by dsimp [k]; omega
  have he : m + 2*k = 601 ∨ m + 2*k = 602 := by dsimp [k]; omega
  have hEnd : 1055 * boundNumerator (m + 2*k) < boundDenominator (m + 2*k) := by
    rcases he with he | he <;> rw [he]
    · simpa only [boundNumerator, boundDenominator, Int.mul_assoc] using terminal601
    · simpa only [boundNumerator, boundDenominator, Int.mul_assoc] using terminal602
  rw [boundNumerator_add, boundDenominator_add] at hEnd
  have hneg : 0 ≤ 1055 * boundNumerator m := Int.mul_nonneg (by decide) (boundNumerator_nonneg m)
  have hkpos : (0 : Int) < 2^k := Int.pow_pos (by decide)
  have hdecay := Int.mul_le_mul_of_nonneg_left (decay k) hneg
  have hlt := Int.mul_lt_mul_of_pos_left hEnd hkpos
  have hcancel : 1055 * boundNumerator m < (2 : Int)^k * boundDenominator m := by
    apply Int.lt_of_mul_lt_mul_right _ (Int.pow_nonneg (n := 125) (m := 2*k) (by decide))
    exact Int.lt_of_le_of_lt hdecay (by
      simpa only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using hlt)
  have hmon : (2 : Int)^k ≤ (2 : Int)^j := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hk
    simpa using Int.ofNat_le.mpr h
  exact Int.lt_of_lt_of_le hcancel
    (Int.mul_le_mul_of_nonneg_right hmon (Int.le_of_lt (boundDenominator_pos m)))

private theorem cut_nonzero {m j : Nat} {f g : Int}
    (h : Bounded m f ((2 : Int)^j * g)) (hm : m ≤ 602) (hj : 601 ≤ m + 2*j)
    (hg : g ≠ 0) : False := by
  have hhi := g_bound h
  have hp : (0 : Int) ≤ 2^j := Int.pow_nonneg (by decide)
  rw [magnitude_mul, magnitude_of_nonneg hp] at hhi
  have hlo := Int.mul_le_mul_of_nonneg_left (magnitude_nonzero hg) hp
  rw [Int.mul_one] at hlo
  have h := Int.le_trans
    (Int.mul_le_mul_of_nonneg_right hlo (Int.le_of_lt (boundDenominator_pos m))) hhi
  exact Int.not_lt_of_ge h (before_cut m j hm hj)

/-- Every canonical Curve25519 input has g=0 after the 43 × 14 schedule. -/
theorem curve25519_terminates (g : Int) (hg : 0 ≤ g) (hgp : g < p) :
    (walk p g 602).g = 0 := by
  generalize hs : walk p g 602 = s
  have hh := (walk_phases g hg hgp 602).2
  rw [hs] at hh
  rcases hh with h | h | h
  · exact h
  · obtain ⟨m, j, hsum, _, hbound⟩ := h
    by_cases hg : s.g = 0
    · exact hg
    · exact False.elim (cut_nonzero hbound (by omega) (by omega) hg)
  · obtain ⟨m, j, k, _, _, hsum, _, hkj, _, hnz, hbound, _⟩ := h
    exact False.elim (cut_nonzero hbound (by omega) (by omega) hnz)

end SafegcdTermination
