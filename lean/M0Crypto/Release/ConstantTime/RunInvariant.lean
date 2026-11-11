import M0Crypto.Release.RunStates

/-! Generic induction for invariants of all states visited by execution. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release

/-- A single-step invariant holds at every state of a successful recorded run.
The caller must prove preservation for the actual machine steps separately. -/
theorem runStates_invariant (P : State → Prop) (stop : Word)
    (hstep : ∀ s t e, P s → s.pc ≠ stop → step s = .ok (t, e) → P t)
    (fuel : Nat) {s : State} {states : List State} {tr : List Event}
    (hs : P s) (hrun : runStates stop fuel s = .ok (states, tr)) :
    ∀ t ∈ states, P t := by
  induction fuel generalizing s states tr with
  | zero =>
    unfold runStates at hrun
    split at hrun
    · cases hrun; simpa using hs
    · contradiction
  | succ fuel ih =>
    unfold runStates at hrun
    split at hrun
    · cases hrun; simpa using hs
    · rename_i hstop
      cases hst : step s with
      | error e => simp [hst] at hrun
      | ok pair =>
        obtain ⟨next, event⟩ := pair
        simp only [hst] at hrun
        cases hn : runStates stop fuel next with
        | error e => simp [hn] at hrun
        | ok result =>
          obtain ⟨rest, events⟩ := result
          simp only [hn, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hp := hstep s next event hs hstop hst
          have hall := ih hp hn
          intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact hs
          · exact hall t ht

/-- A locally proved event property holds for every event of a successful run. -/
theorem runStates_events_invariant (P : State → Prop) (Q : Event → Prop) (stop : Word)
    (hstep : ∀ s t e, P s → s.pc ≠ stop → step s = .ok (t, e) → P t ∧ Q e)
    (fuel : Nat) {s : State} {states : List State} {tr : List Event}
    (hs : P s) (hrun : runStates stop fuel s = .ok (states, tr)) :
    ∀ e ∈ tr, Q e := by
  induction fuel generalizing s states tr with
  | zero =>
    unfold runStates at hrun
    split at hrun
    · cases hrun; simp
    · contradiction
  | succ fuel ih =>
    unfold runStates at hrun
    split at hrun
    · cases hrun; simp
    · rename_i hstop
      cases hst : step s with
      | error e => simp [hst] at hrun
      | ok pair =>
        obtain ⟨next, event⟩ := pair
        simp only [hst] at hrun
        cases hn : runStates stop fuel next with
        | error e => simp [hn] at hrun
        | ok result =>
          obtain ⟨rest, events⟩ := result
          simp only [hn, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hp, he⟩ := hstep s next event hs hstop hst
          have hall := ih hp hn
          intro e hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact he
          · exact hall e hm

end M0Crypto.Release.ConstantTime
