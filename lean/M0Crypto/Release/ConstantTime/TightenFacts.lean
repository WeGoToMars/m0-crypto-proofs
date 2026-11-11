import M0Crypto.Release.ConstantTime.StateUpdate

/-! Preservation of relational state during fact-based interval narrowing. -/
namespace M0Crypto.Release.ConstantTime

def tightenFact (s : AbsState) (f : Fact) : AbsState :=
  let (i, j, strict) := f
  match ival (s.get i), ival (s.get j) with
  | some (il, ih), some (_, jh) =>
    let d := if strict then 1 else 0
    if d ≤ jh ∧ jh - d < ih ∧ il ≤ jh - d then
      { s with regs := regSet s.regs i (.num il (jh - d)) }
    else s
  | _, _ => s

/-- A single fact-based narrowing preserves the relational interpretation. -/
theorem tightenFact_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {f : Fact}
    (h : LowEq p bytes off s s₁ s₂) (hmem : f ∈ s.rel)
    (hidx : factIndexOk f) : LowEq p bytes off (tightenFact s f) s₁ s₂ := by
  rcases f with ⟨i, j, strict⟩
  rcases hidx with ⟨hi, hj⟩
  unfold tightenFact
  cases hia : ival (s.get i) with
  | none => simp [hia]; exact h
  | some ia =>
    cases hib : ival (s.get j) with
    | none => simp [hia, hib]; exact h
    | some ja =>
      rcases ia with ⟨il, ih⟩
      rcases ja with ⟨jl, jh⟩
      simp only [hia, hib]
      cases strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split
      all_goals try exact h
      all_goals
        rename_i hnarrow
        apply h.withRegSet
        have ha := h.regs i hi.1 hi.2
        have hb := h.regs j hj.1 hj.2
        have hf := (h.facts (i, j, _) hmem).1
        exact fact_narrow _ ha hb hia hib hf hnarrow.1

theorem tightenFact_rel (s : AbsState) (f : Fact) : (tightenFact s f).rel = s.rel := by
  rcases f with ⟨i, j, strict⟩
  cases strict <;> simp only [tightenFact, Bool.false_eq_true, ↓reduceIte] <;>
    split <;> try rfl
  all_goals split <;> rfl

/-- All fact-based refinements preserve the state relation. -/
theorem tightenFacts_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (fs : List Fact)
    (h : LowEq p bytes off s s₁ s₂)
    (hmem : ∀ f ∈ fs, f ∈ s.rel) (hidx : ∀ f ∈ fs, factIndexOk f) :
    LowEq p bytes off (fs.foldl tightenFact s) s₁ s₂ := by
  induction fs generalizing s with
  | nil => exact h
  | cons f fs ih =>
    simp only [List.foldl_cons]
    have hf : f ∈ s.rel := hmem f (by simp)
    apply ih (tightenFact_sound h hf (hidx f (by simp)))
    · intro g hg
      rw [tightenFact_rel]
      exact hmem g (by simp [hg])
    · intro g hg
      exact hidx g (by simp [hg])

end M0Crypto.Release.ConstantTime
