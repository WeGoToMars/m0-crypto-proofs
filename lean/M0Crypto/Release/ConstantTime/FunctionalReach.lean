import M0Crypto.Release.ConstantTime.DecryptVerdict

/-! Connecting functional artifact execution to recorded machine states. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release

/-- A successful artifact step records the source PC. -/
theorem stepH_event_pc {bytes : List (BitVec 8)} {base : Word} {s t : State} {e : Event}
    (h : stepH bytes base s = .ok (t, e)) : e.pc = s.pc := by
  unfold stepH at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.2]
          · cases h
        · cases h
      · cases h

/-- An artifact execution with intact code and no stop-PC visits reaches the
same state through ordinary machine steps. -/
theorem runH_beforeStop {bytes : List (BitVec 8)} {base stop : Word}
    {initial target : State} {n : Nat} {tr : List Event}
    (hc : CodeAt initial.mem base bytes)
    (hr : runH bytes base n initial = .ok (target, tr))
    (hmiss : TraceMissesCode bytes base tr)
    (hstop : ∀ e ∈ tr, e.pc ≠ stop) : BeforeStop stop initial target := by
  have aux : ∀ n (s t : State) tr, CodeAt s.mem base bytes →
      runH bytes base n s = .ok (t, tr) → TraceMissesCode bytes base tr →
      (∀ e ∈ tr, e.pc ≠ stop) → BeforeStop stop initial s → BeforeStop stop initial t := by
    intro n
    induction n with
    | zero =>
      intro s t tr hc hr _ _ hs
      simp only [runH, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hs
    | succ n ih =>
      intro s t tr hc hr hmiss hstop hs
      simp only [runH] at hr
      cases hstep : stepH bytes base s with
      | error err => simp [hstep] at hr
      | ok pair =>
        obtain ⟨next, event⟩ := pair
        simp only [hstep] at hr
        cases htail : runH bytes base n next with
        | error err => simp [htail] at hr
        | ok pair =>
          obtain ⟨last, tail⟩ := pair
          simp only [htail, Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          have hconcrete := step_of_stepH hc hstep
          have hcode := codeAt_step hc hconcrete (hmiss event (by simp))
          have hpc : s.pc ≠ stop := by
            rw [← stepH_event_pc hstep]
            exact hstop event (by simp)
          apply ih next last tail hcode htail
            (fun e he => hmiss e (by simp [he]))
            (fun e he => hstop e (by simp [he]))
          exact BeforeStop.next hs hpc hconcrete
  exact aux n initial target tr hc hr hmiss hstop BeforeStop.initial

end M0Crypto.Release.ConstantTime
