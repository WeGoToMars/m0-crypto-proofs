import M0Crypto.Release.ConstantTime.SemValue

/-! Soundness lemmas for updates to the sparse stack component of the
relational abstract state. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word Mem read32)

private theorem lookup_filter_ne (s : Stk) (t : Int) :
    (s.filter (fun p => p.1 != t)).lookup t = none := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rcases a with ⟨k, w⟩
    by_cases hkt : k = t
    · simp [List.lookup_cons, hkt, ih]
    · have hbeq : (t == k) = false := by simp [Ne.symm hkt]
      simp [List.lookup_cons, hkt, hbeq, ih]

private theorem stkGet_set_of_ne (s : Stk) (o t : Int) (v : AbsVal) (h : o ≠ t) :
    stkGet (stkSet s t v) o = stkGet s o := by
  have hfilter : (s.filter (fun p => p.1 != t)).lookup o = s.lookup o := by
    have hot : (o == t) = false := by simp [h]
    induction s with
    | nil => simp
    | cons a s ih =>
      rcases a with ⟨k, w⟩
      by_cases hkt : k = t
      · subst k
        simp [List.lookup_cons, hot]
        exact ih
      · simp [List.lookup_cons, ih, hkt]
  simp only [stkSet, stkGet]
  have hne : (o == t) = false := by simp [h]
  cases hp : v.pub <;> simp [hp, List.lookup_cons, hne, hfilter]

/-- A strong stack update is sound after a memory write when every other
tracked slot is unchanged and the new word has the assigned label. The frame
condition is stated over tracked slots because arbitrary integer offsets can
alias modulo the machine word size. -/
theorem stkSet_write_sem {p : Params} {s : Stk} {t : Int} {v : AbsVal}
    {m₁ m₂ m₁' m₂' : Mem}
    (hs : StkSem p s m₁ m₂)
    (hw : AbsVal.Sem p v
      (read32 m₁' (p.sp0 + BitVec.ofInt 32 t))
      (read32 m₂' (p.sp0 + BitVec.ofInt 32 t)))
    (hframe : ∀ o, o ≠ t → (stkGet s o).pub = true →
      read32 m₁' (p.sp0 + BitVec.ofInt 32 o) = read32 m₁ (p.sp0 + BitVec.ofInt 32 o) ∧
      read32 m₂' (p.sp0 + BitVec.ofInt 32 o) = read32 m₂ (p.sp0 + BitVec.ofInt 32 o)) :
    StkSem p (stkSet s t v) m₁' m₂' := by
  intro o
  by_cases hot : o = t
  · subst o
    cases hp : v.pub with
    | false =>
      have hv : v = .hi := by cases v <;> simp_all [AbsVal.pub]
      subst v
      simp [stkSet, stkGet, AbsVal.pub, AbsVal.Sem, lookup_filter_ne]
    | true =>
      simpa [stkSet, stkGet, hp] using hw
  · rw [stkGet_set_of_ne s o t v hot]
    cases hp : (stkGet s o).pub with
    | false =>
      have hv : stkGet s o = .hi := by
        cases hv : stkGet s o <;> simp_all [AbsVal.pub]
      simp [hv, AbsVal.Sem]
    | true =>
      obtain ⟨h₁, h₂⟩ := hframe o hot hp
      rw [h₁, h₂]
      exact hs o

end M0Crypto.Release.ConstantTime
