import M0Crypto.Release.ConstantTime.Sem

/-! Soundness of the abstract value order and join for the relational concretisation. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word)

namespace AbsVal

private theorem eq_of_sem {p : Params} {v : AbsVal} {x y : Word}
    (hv : Sem p v x y) (hpub : v.pub = true) : x = y :=
  sem_public hv hpub

/-- A more precise abstract value denotes only values denoted by its upper bound. -/
theorem le_sem {p : Params} {a b : AbsVal} {x y : Word}
    (hle : a.le b = true) (ha : Sem p a x y) : Sem p b x y := by
  cases a <;> cases b <;> simp [AbsVal.le] at hle <;> simp_all [Sem]
  case num.num a₁ a₂ b₁ b₂ =>
    rcases ha with ⟨hxy, hlo, hhi⟩
    subst y
    exact ⟨Nat.le_trans (by omega) hlo, Nat.le_trans hhi (by omega)⟩
  case sp.sp a₁ a₂ b₁ b₂ =>
    rcases ha with ⟨k, hlo, hhi, hx, hy⟩
    exact ⟨k, Int.le_trans (by omega) hlo, Int.le_trans hhi (by omega), hx, hy⟩
  case sp.lo =>
    rcases ha with ⟨_, _, _, _, hy⟩
    exact hy.symm
  all_goals
    try
      have hxy := sem_public ha (by simp [AbsVal.pub])
      simpa [Sem] using hxy

/-- Every concrete pair described by the left operand is described by its join. -/
theorem join_sem_left {p : Params} {a b : AbsVal} {x y : Word}
    (ha : Sem p a x y) : Sem p (a.join b) x y := by
  cases a with
  | hi => simp [AbsVal.join, Sem]
  | lo =>
    have hxy := eq_of_sem ha (by simp [AbsVal.pub])
    cases b <;> simp [AbsVal.join, Sem, hxy]
  | num a₁ a₂ =>
    cases b with
    | hi => simp [AbsVal.join, Sem]
    | num b₁ b₂ =>
      rcases ha with ⟨hxy, hlo, hhi⟩
      subst y
      exact ⟨rfl, Nat.le_trans (Nat.min_le_left _ _) hlo,
        Nat.le_trans hhi (Nat.le_max_left _ _)⟩
    | _ =>
      have hxy := eq_of_sem ha (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | sp a₁ a₂ =>
    cases b with
    | hi => simp [AbsVal.join, Sem]
    | sp b₁ b₂ =>
      rcases ha with ⟨k, hlo, hhi, hx, hy⟩
      subst y
      exact ⟨k, Int.le_trans (Int.min_le_left _ _) hlo,
        Int.le_trans hhi (Int.le_max_left _ _), hx, rfl⟩
    | _ =>
      have hxy := eq_of_sem ha (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | ret r =>
    cases b with
    | ret r' =>
      by_cases h : r == r'
      · have hr : r = r' := of_decide_eq_true h
        subst r'
        simpa [AbsVal.join, Sem] using ha
      · have hxy := eq_of_sem ha (by simp [AbsVal.pub])
        simp [AbsVal.join, h, Sem, hxy]
    | hi => simp [AbsVal.join, Sem]
    | _ =>
      have hxy := eq_of_sem ha (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | lr0 =>
    cases b with
    | lr0 => simpa [AbsVal.join] using ha
    | hi => simp [AbsVal.join, Sem]
    | _ =>
      have hxy := eq_of_sem ha (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]

/-- Every concrete pair described by the right operand is described by its join. -/
theorem join_sem_right {p : Params} {a b : AbsVal} {x y : Word}
    (hb : Sem p b x y) : Sem p (a.join b) x y := by
  cases b with
  | hi => cases a <;> simp [AbsVal.join, Sem]
  | lo =>
    have hxy := eq_of_sem hb (by simp [AbsVal.pub])
    cases a <;> simp [AbsVal.join, Sem, hxy]
  | num b₁ b₂ =>
    cases a with
    | hi => simp [AbsVal.join, Sem]
    | num a₁ a₂ =>
      rcases hb with ⟨hxy, hlo, hhi⟩
      subst y
      exact ⟨rfl, Nat.le_trans (Nat.min_le_right _ _) hlo,
        Nat.le_trans hhi (Nat.le_max_right _ _)⟩
    | _ =>
      have hxy := eq_of_sem hb (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | sp b₁ b₂ =>
    cases a with
    | hi => simp [AbsVal.join, Sem]
    | sp a₁ a₂ =>
      rcases hb with ⟨k, hlo, hhi, hx, hy⟩
      subst y
      exact ⟨k, Int.le_trans (Int.min_le_right _ _) hlo,
        Int.le_trans hhi (Int.le_max_right _ _), hx, rfl⟩
    | _ =>
      have hxy := eq_of_sem hb (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | ret r =>
    cases a with
    | ret r' =>
      by_cases h : r' == r
      · have hr : r' = r := of_decide_eq_true h
        subst r'
        simpa [AbsVal.join, Sem] using hb
      · have hxy := eq_of_sem hb (by simp [AbsVal.pub])
        simp [AbsVal.join, h, Sem, hxy]
    | hi => simp [AbsVal.join, Sem]
    | _ =>
      have hxy := eq_of_sem hb (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]
  | lr0 =>
    cases a with
    | lr0 => simpa [AbsVal.join] using hb
    | hi => simp [AbsVal.join, Sem]
    | _ =>
      have hxy := eq_of_sem hb (by simp [AbsVal.pub])
      simp [AbsVal.join, Sem, hxy]

end AbsVal
end M0Crypto.Release.ConstantTime
