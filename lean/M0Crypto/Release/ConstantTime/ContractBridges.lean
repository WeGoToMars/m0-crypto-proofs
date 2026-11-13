import M0Crypto.Release.ConstantTime.Entries
import M0Crypto.Release.ConstantTime.FunctionalWrites

/-! Contract consequences needed by the analysis and return-state bounds. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)
open M0Crypto.Release

/-- A returned state with restored SP lies in any stack window at entry SP. -/
theorem restored_sp_in_stack_window {sp0 : M0Crypto.Armv6M.Word} {s : State}
    (hsp : s.regs 13 = sp0) (below : Nat) :
    TraceSpec.InStackWindow sp0 below (s.regs 13) := by
  exact ⟨0, Nat.zero_le _, by simpa using hsp⟩

/-- The final recorded state agrees with the state returned by `runUntil`. -/
theorem runStates_final {stop : M0Crypto.Armv6M.Word} {fuel : Nat} {s : State}
    {states : List State} {events : List M0Crypto.Thumb.Event}
    (hrun : runStates stop fuel s = .ok (states, events)) :
    ∃ last, states.getLast? = some last ∧
      M0Crypto.Thumb.runUntil stop fuel s = .ok (last, events) := by
  induction fuel generalizing s states events with
  | zero =>
    simp only [runStates] at hrun
    split at hrun
    · rename_i hp
      cases hrun
      exact ⟨s, by simp, by simp [M0Crypto.Thumb.runUntil, hp]⟩
    · contradiction
  | succ fuel ih =>
    simp only [runStates] at hrun
    split at hrun
    · rename_i hp
      cases hrun
      exact ⟨s, by simp, by simp [M0Crypto.Thumb.runUntil, hp]⟩
    · rename_i hp
      cases hs : M0Crypto.Thumb.step s with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨last, hlast, hfinal⟩ := ih ht
          have hne : rest ≠ [] := (runStates_nonempty ht).1
          refine ⟨last, ?_, ?_⟩
          · cases rest with
            | nil => contradiction
            | cons x xs => simpa using hlast
          · simp [M0Crypto.Thumb.runUntil, hp, hs, hfinal]

end M0Crypto.Release.ConstantTime
