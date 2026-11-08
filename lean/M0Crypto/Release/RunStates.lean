import M0Crypto.Thumb.Exec

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-- Run until PC = `stop` (checked before each step), with at most `fuel` steps.
Returns the list of all visited states (starting with `s` and ending with the state
where PC = `stop`) and the trace of executed events. -/
def runStates (stop : Word) : Nat → State → Except Fault (List State × List Event)
  | fuel, s =>
    if s.pc = stop then .ok ([s], [])
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step s with
        | .error e => .error e
        | .ok (s', e) =>
          match runStates stop n s' with
          | .error e' => .error e'
          | .ok (states, es) => .ok (s :: states, e :: es)

theorem runStates_events (stop : Word) (fuel : Nat) (s : State) :
    (runStates stop fuel s).map Prod.snd = (Thumb.runUntil stop fuel s).map Prod.snd := by
  induction fuel generalizing s with
  | zero =>
    unfold runStates Thumb.runUntil
    split <;> rfl
  | succ n ih =>
    unfold runStates Thumb.runUntil
    split
    · rfl
    · cases hstep : step s with
      | error e =>
        simp only [hstep]
        rfl
      | ok p =>
        obtain ⟨s', e⟩ := p
        simp only [hstep]
        have h := ih s'
        cases hrs : runStates stop n s' with
        | error e' =>
          cases hru : Thumb.runUntil stop n s' with
          | error e'' =>
            simp only [hrs, hru, Except.map] at h ⊢
            cases h
            rfl
          | ok res =>
            simp only [hrs, hru, Except.map] at h
            contradiction
        | ok res1 =>
          cases hru : Thumb.runUntil stop n s' with
          | error e'' =>
            simp only [hrs, hru, Except.map] at h
            contradiction
          | ok res2 =>
            obtain ⟨states, es1⟩ := res1
            obtain ⟨s_final, es2⟩ := res2
            simp only [hrs, hru, Except.map] at h ⊢
            cases h
            rfl

theorem runStates_nonempty {stop : Word} {fuel : Nat} {s : State} {states : List State} {tr : List Event}
    (h : runStates stop fuel s = .ok (states, tr)) :
    states ≠ [] ∧ states.head? = some s := by
  induction fuel generalizing s states tr with
  | zero =>
    unfold runStates at h
    split at h
    · cases h; simp
    · contradiction
  | succ n ih =>
    unfold runStates at h
    split at h
    · cases h; simp
    · cases hstep : step s with
      | error e =>
        simp only [hstep] at h
        contradiction
      | ok p =>
        obtain ⟨s', e⟩ := p
        simp only [hstep] at h
        cases hrs : runStates stop n s' with
        | error e' =>
          simp only [hrs] at h
          contradiction
        | ok p2 =>
          obtain ⟨states', es'⟩ := p2
          simp only [hrs] at h
          cases h
          simp

theorem runStates_of_runUntil {stop : Word} {fuel : Nat} {s s' : State} {tr : List Event}
    (h : Thumb.runUntil stop fuel s = .ok (s', tr)) :
    ∃ states, runStates stop fuel s = .ok (states, tr) ∧ states.head? = some s ∧ states ≠ [] := by
  induction fuel generalizing s s' tr with
  | zero =>
    unfold Thumb.runUntil at h
    split at h
    · cases h
      refine ⟨[s], ?_, by simp, by simp⟩
      unfold runStates
      split
      · rfl
      · contradiction
    · contradiction
  | succ n ih =>
    unfold Thumb.runUntil at h
    split at h
    · cases h
      refine ⟨[s], ?_, by simp, by simp⟩
      unfold runStates
      split
      · rfl
      · contradiction
    · cases hstep : step s with
      | error e =>
        simp only [hstep] at h
        contradiction
      | ok p =>
        obtain ⟨s1, e⟩ := p
        simp only [hstep] at h
        cases hrec : Thumb.runUntil stop n s1 with
        | error e' =>
          simp only [hrec] at h
          contradiction
        | ok p2 =>
          obtain ⟨s2, es⟩ := p2
          simp only [hrec] at h
          cases h
          obtain ⟨states', hst', hhead', hne'⟩ := ih hrec
          refine ⟨s :: states', ?_, by simp, by simp⟩
          unfold runStates
          split
          · contradiction
          · simp only [hstep, hst']

end M0Crypto.Release
