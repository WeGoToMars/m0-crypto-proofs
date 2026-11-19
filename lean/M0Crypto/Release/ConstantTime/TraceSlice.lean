import M0Crypto.Release.ConstantTime.TraceFragment

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word State)
open M0Crypto.Release (runStates)
open M0Crypto.Thumb

/-- A successful recorded run started at its state at index `k` records the
suffix starting there. -/
theorem runStates_drop_at {stop : Word} {fuel : Nat} {s u : State}
    {states : List State} {tr : List Event} {k : Nat}
    (h : runStates stop fuel s = .ok (states,tr)) (hu : states[k]? = some u) :
    runStates stop (fuel-k) u = .ok (states.drop k,tr.drop k) := by
  induction fuel generalizing s states tr k with
  | zero =>
    by_cases hstop : s.pc = stop
    · simp only [runStates,hstop,ite_true,Except.ok.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      cases k with
      | zero => cases hu; simp [runStates,hstop]
      | succ k => simp at hu
    · simp [runStates,hstop] at h
  | succ fuel ih =>
    cases k with
    | zero =>
      have h0 : states[0]? = some s := by
        have hh := (M0Crypto.Release.runStates_nonempty h).2
        cases states with
        | nil => simp at hh
        | cons a as => exact hh
      have he := Option.some.inj (h0.symm.trans hu)
      subst u
      simpa using h
    | succ k =>
      by_cases hstop : s.pc = stop
      · simp only [runStates,hstop,ite_true,Except.ok.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp at hu
      · simp only [runStates,hstop,ite_false] at h
        cases hs : step s with
        | error e => simp [hs] at h
        | ok pair =>
          obtain ⟨v,ev⟩ := pair
          simp only [hs] at h
          cases hr : runStates stop fuel v with
          | error e => simp [hr] at h
          | ok pair =>
            obtain ⟨rest,es⟩ := pair
            simp only [hr,Except.ok.injEq,Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            simpa using ih hr (show rest[k]? = some u from hu)

/-- A checked fragment starting at the recorded run's head is its exact
prefix, with the local step predicate holding at each recorded index. -/
theorem TraceFragment.recorded_prefix {stop : Word} {P : State → Event → Prop}
    {s t : State} {frag : List Event} (f : TraceFragment stop P s frag t) :
    ∀ {fuel : Nat} {states tr}, runStates stop fuel s = .ok (states,tr) →
      states[frag.length]? = some t ∧
      ∀ (i : Nat) e, frag[i]? = some e → tr[i]? = some e ∧ ∃ u, states[i]? = some u ∧ P u e := by
  induction f with
  | nil =>
    intro fuel states tr h
    refine ⟨?_,fun i e he => by simp at he⟩
    have hh := (M0Crypto.Release.runStates_nonempty h).2
    cases states with
    | nil => simp at hh
    | cons a as => exact hh
  | @cons s u t ev es hn hs hp hf ih =>
    intro fuel states tr h
    cases fuel with
    | zero => simp [runStates,hn] at h
    | succ fuel =>
      simp only [runStates,hn,ite_false,hs] at h
      cases hr : runStates stop fuel u with
      | error e => simp [hr] at h
      | ok pair =>
        obtain ⟨rest,events⟩ := pair
        simp only [hr,Except.ok.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        have hRec := ih hr
        refine ⟨hRec.1,?_⟩
        intro i e he
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at he
          subst e
          exact ⟨rfl,s,rfl,hp⟩
        | succ i => exact hRec.2 i e he

/-- The same guarantees at an arbitrary recorded index. -/
theorem TraceFragment.recorded_slice {stop : Word} {P : State → Event → Prop}
    {s u t : State} {fuel : Nat} {states : List State} {tr frag : List Event} {k : Nat}
    (hr : runStates stop fuel s = .ok (states,tr)) (hu : states[k]? = some u)
    (f : TraceFragment stop P u frag t) :
    states[k+frag.length]? = some t ∧
    ∀ i e, frag[i]? = some e →
      tr[k+i]? = some e ∧ ∃ v, states[k+i]? = some v ∧ P v e := by
  obtain ⟨hF,hE⟩ := f.recorded_prefix (runStates_drop_at hr hu)
  simp only [List.getElem?_drop] at hF hE ⊢
  exact ⟨hF,hE⟩

end M0Crypto.Release.ConstantTime
