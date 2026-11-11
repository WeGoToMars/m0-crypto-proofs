import M0Crypto.Thumb.Exec

/-! A generic induction for paired execution traces. The step relation must be
proved separately for the concrete analysis and every reachable instruction. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb

/-- Paired steps either fail with the same fault or produce the same event and
related successors. -/
def PairedStep (R : State → State → Prop) (s₁ s₂ : State) : Prop :=
  match step s₁, step s₂ with
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (t₁, e₁), .ok (t₂, e₂) => e₁ = e₂ ∧ R t₁ t₂
  | _, _ => False

/-- Equal PCs and a locally preserved paired-step relation imply equal trace
results for every fuel. This is an induction helper, not a concrete entry theorem. -/
theorem runUntil_trace_eq (R : State → State → Prop) (stop : Word)
    (hpc : ∀ s₁ s₂, R s₁ s₂ → s₁.pc = s₂.pc)
    (hstep : ∀ s₁ s₂, R s₁ s₂ → s₁.pc ≠ stop → PairedStep R s₁ s₂)
    (fuel : Nat) : ∀ s₁ s₂, R s₁ s₂ →
      (runUntil stop fuel s₁).map Prod.snd = (runUntil stop fuel s₂).map Prod.snd := by
  induction fuel with
  | zero =>
    intro s₁ s₂ hr
    have hp := hpc s₁ s₂ hr
    by_cases hs : s₂.pc = stop <;> simp [runUntil, hp, hs, Except.map]
  | succ fuel ih =>
    intro s₁ s₂ hr
    have hp := hpc s₁ s₂ hr
    by_cases hstop : s₁.pc = stop
    · simp [runUntil, hstop, ← hp, Except.map]
    · have hstop₂ : s₂.pc ≠ stop := by simpa [← hp] using hstop
      have hs := hstep s₁ s₂ hr hstop
      simp only [runUntil, hstop, hstop₂, ↓reduceIte]
      unfold PairedStep at hs
      cases h₁ : step s₁ with
      | error err₁ =>
        cases h₂ : step s₂ with
        | error err₂ => simp_all
        | ok pair₂ => simp_all
      | ok pair₁ =>
        cases pair₁ with
        | mk t₁ e₁ =>
          cases h₂ : step s₂ with
          | error err₂ => simp_all
          | ok pair₂ =>
            cases pair₂ with
            | mk t₂ e₂ =>
              simp only [h₁, h₂] at hs
              obtain ⟨he, ht⟩ := hs
              subst e₂
              have htr := ih t₁ t₂ ht
              cases ha : runUntil stop fuel t₁ <;>
                cases hb : runUntil stop fuel t₂ <;>
                simp_all [Except.map]

end M0Crypto.Release.ConstantTime
