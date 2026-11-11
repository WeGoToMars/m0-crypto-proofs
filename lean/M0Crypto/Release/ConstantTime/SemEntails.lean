import M0Crypto.Release.ConstantTime.StateSem
import M0Crypto.Release.ConstantTime.SemIndex

/-! Soundness of relational-fact entailment in the concrete state semantics. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State Word)

private theorem fact_non_strict_of_strict {f : Fact} {s : State}
    (h : FactSem f s) (hs : f.2.2 = true) :
    FactSem (f.1, f.2.1, false) s := by
  rcases f with ⟨i, j, strict⟩
  simp only [FactSem] at h ⊢
  cases strict with
  | false => simp at hs
  | true => simp at h ⊢; omega

theorem interval_bounds {p : Params} {v : AbsVal} {x y : Word}
    {a b : Nat} (hsem : AbsVal.Sem p v x y)
    (hival : ival v = some (a, b)) :
    a ≤ x.toNat ∧ x.toNat ≤ b ∧ a ≤ y.toNat ∧ y.toNat ≤ b := by
  cases v with
  | hi => simp [ival] at hival
  | lo =>
    simp only [ival] at hival
    cases hival
    simp only [AbsVal.Sem] at hsem
    subst y
    have hx : x.toNat < AbsVal.word := by simpa [AbsVal.word] using x.isLt
    omega
  | num l h =>
    simp only [ival] at hival
    cases hival
    simp only [AbsVal.Sem] at hsem
    rcases hsem with ⟨hxy, hxl, hxh⟩
    subst y
    exact ⟨hxl, hxh, hxl, hxh⟩
  | sp _ _ => simp [ival] at hival
  | ret _ => simp [ival] at hival
  | lr0 => simp [ival] at hival

/-- If `s.entails f` holds, then `f` holds in both concrete states related by
`LowEq`. Requested indices must name represented registers. -/
theorem AbsState.entails_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {s : AbsState} {s₁ s₂ : State} {f : Fact}
    (hlow : LowEq p bytes off s s₁ s₂)
    (hf : factIndexOk f) (hent : s.entails f = true) :
    FactSem f s₁ ∧ FactSem f s₂ := by
  rcases f with ⟨i, j, strict⟩
  rcases hf with ⟨hi, hj⟩
  have h := hlow
  have hi15 : i < 15 := by simpa [numRegs] using hi.1
  have hj15 : j < 15 := by simpa [numRegs] using hj.1
  have hi' : i % 16 = i := Nat.mod_eq_of_lt (by omega)
  have hj' : j % 16 = j := Nat.mod_eq_of_lt (by omega)
  have hsi := h.regs i hi.1 hi.2
  have hsj := h.regs j hj.1 hj.2
  change (s.rel.contains (i, j, strict) ||
    (!strict && s.rel.contains (i, j, true)) ||
    match ival (s.get i), ival (s.get j) with
    | some (_, ih), some (jl, _) => decide (ih + (if strict then 1 else 0) ≤ jl)
    | _, _ => false) = true at hent
  by_cases hexact : s.rel.contains (i, j, strict) = true
  · have hmem : (i, j, strict) ∈ s.rel := by
      simpa [List.contains_iff_mem] using hexact
    rcases h.facts (i, j, strict) hmem with ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
  · simp only [hexact, Bool.false_or] at hent
    by_cases hweak : (!strict && s.rel.contains (i, j, true)) = true
    · have hparts := Bool.and_eq_true_iff.mp hweak
      have hmem : (i, j, true) ∈ s.rel := by
        simpa [List.contains_iff_mem] using hparts.2
      have hstrict : strict = false := by simpa using hparts.1
      subst strict
      rcases h.facts (i, j, true) hmem with ⟨h₁, h₂⟩
      exact ⟨fact_non_strict_of_strict h₁ rfl, fact_non_strict_of_strict h₂ rfl⟩
    · simp only [hweak, Bool.false_or] at hent
      cases hiVal : ival (s.get i) with
      | none => simp [hiVal] at hent
      | some ib₁ => cases ibVal : ival (s.get j) with
        | none => simp [hiVal, ibVal] at hent
        | some jb₁ =>
          rcases ib₁ with ⟨il, ih⟩
          rcases jb₁ with ⟨jl, jh⟩
          have hbound : ih + (if strict then 1 else 0) ≤ jl := of_decide_eq_true (by simpa [hiVal, ibVal] using hent)
          have hsi' : AbsVal.Sem p (s.get i) (regAt s₁ i) (regAt s₂ i) := by
            simpa [AbsState.get] using hsi
          have hsj' : AbsVal.Sem p (s.get j) (regAt s₁ j) (regAt s₂ j) := by
            simpa [AbsState.get] using hsj
          have hiBounds := interval_bounds hsi' hiVal
          have hjBounds := interval_bounds hsj' ibVal
          rcases hiBounds with ⟨_, h₁hi, _, h₂hi⟩
          rcases hjBounds with ⟨h₁lo, _, h₂lo, _⟩
          constructor <;> simp [FactSem] <;> omega

end M0Crypto.Release.ConstantTime
