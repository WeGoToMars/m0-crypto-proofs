import SafegcdRow.Correct

namespace SafegcdRow

set_option maxRecDepth 12000
open M0Crypto.Armv6M (State slot)
open M0Crypto.Thumb

/-- Use the release model's unified-memory instruction fetch for the body. -/
def runSteps : Nat → State → Except Fault (State × List Event)
  | 0, s => .ok (s, [])
  | n+1, s =>
    match step s with
    | .error e => .error e
    | .ok (t, e) =>
      match runSteps n t with
      | .error e' => .error e'
      | .ok (u, es) => .ok (u, e :: es)

/-- The pilot extension recognizes the row's Thumb BX r12 encoding and
executes its return semantics against the fetched halfword. -/
def returnLoaded (s : State) : Except Fault (State × (Word × Word)) :=
  if s.pc.getLsbD 0 then .error (.pcOdd s.pc)
  else if fetch16 s.mem s.pc == 0x4760#16 then executeReturn s
  else .error (.undefined s.pc)

def runLoaded (s : State) : Except Fault (State × (List Event × (Word × Word))) :=
  match runSteps body.length s with
  | .error e => .error e
  | .ok (t, events) =>
    match returnLoaded t with
    | .error e => .error e
    | .ok (u, ret) => .ok (u, events, ret)

private theorem runSteps_refines (code : List (BitVec 8)) (base : Word) (n : Nat)
    (s t : State) (es : List Event) (hc : CodeAt s.mem base code)
    (hr : runH code base n s = .ok (t, es)) (hm : TraceMissesCode code base es) :
    runSteps n s = .ok (t, es) ∧ CodeAt t.mem base code := by
  induction n generalizing s t es with
  | zero =>
    cases hr
    exact ⟨rfl, hc⟩
  | succ n ih =>
    cases hh : stepH code base s with
    | error e => rw [runH, hh] at hr; contradiction
    | ok res =>
      obtain ⟨s₁, event⟩ := res
      rw [runH, hh] at hr
      cases htail : runH code base n s₁ with
      | error f =>
        change (match runH code base n s₁ with
          | .error f => Except.error f
          | .ok (u, els) => Except.ok (u, event :: els)) = _ at hr
        rw [htail] at hr
        contradiction
      | ok res =>
        obtain ⟨t₁, es₁⟩ := res
        change (match runH code base n s₁ with
          | .error f => Except.error f
          | .ok (u, els) => Except.ok (u, event :: els)) = _ at hr
        rw [htail] at hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        have hstep := step_of_stepH hc hh
        have hc' := codeAt_step hc hstep (hm event List.mem_cons_self)
        have htrace : TraceMissesCode code base es₁ := fun e' he' =>
          hm e' (List.mem_cons_of_mem _ he')
        obtain ⟨hr', hco⟩ := ih _ _ _ hc' htail htrace
        refine ⟨?_, hco⟩
        rw [runSteps, hstep]
        exact congrArg (fun q => match q with
          | .error f => Except.error f
          | .ok (u, els) => Except.ok (u, event :: els)) hr'

private theorem return_refines (s : State) (base : Word) (code : List (BitVec 8))
    (hc : CodeAt s.mem base code) (t : State) (tr : Word × Word)
    (h : returnStep code base s = .ok (t, tr)) :
    returnLoaded s = .ok (t, tr) := by
  unfold returnStep at h
  split at h
  · contradiction
  · rename_i hpc
    split at h
    · rename_i hd
      have hb := Bool.and_eq_true_iff.mp hd
      have hb₁ := of_decide_eq_true hb.1
      have hb₂ := beq_iff_eq.mp hb.2
      have hf := fetch16_of_codeAt hc _ hb₁
      rw [base_add_sub] at hf
      unfold returnLoaded
      rw [ite_eq_right hpc, hf, hb₂]
      simpa only [beq_self_eq_true, ite_true] using h
    · contradiction

/-- Disjoint output and code, stated in bytes to permit any legal placement. -/
def OutputMissesCode (p : Pins) (base : Word) : Prop :=
  ∀ i < bytes.length, ∀ j < 68, base + BitVec.ofNat 32 i ≠ p.out + BitVec.ofNat 32 j

private theorem writes_miss (p : Pins) (base : Word) (tr : List Event)
    (hp : OutputMissesCode p base) (h : TraceIn p tr) :
    TraceMissesCode bytes base tr := by
  intro e he i hi hw
  obtain ⟨a, ha, hw, j, hj, eq⟩ := hw
  obtain ⟨k, hk, rfl | rfl | rfl⟩ := h e he a ha
  · change Kind.read = Kind.write at hw; cases hw
  · change Kind.read = Kind.write at hw; cases hw
  · simp only [storeAt, slot, ofNat_add_assoc] at hj eq
    exact hp i hi (4*k+j) (by omega) eq

/-- The byte-bound row theorem also holds with ordinary instruction fetches
when the artifact is loaded and writes stay disjoint from it. -/
theorem loaded_matches (base : Word) (s : State) (h : Entry base s)
    (hc : CodeAt s.mem base bytes) (hp : OutputMissesCode (Pins.load s) base) :
    runLoaded s = runRow bytes base s := by
  obtain ⟨u, hr, _⟩ := row_correct base s h
  change runRow bytes base s = _ at hr
  rw [hr]
  unfold runRow at hr
  cases hb : runH bytes base body.length s with
  | error f =>
    rw [hb] at hr
    contradiction
  | ok p =>
    obtain ⟨t, es⟩ := p
    rw [hb] at hr
    change (match returnStep bytes base t with
      | .error f => Except.error f
      | .ok (tt, br) => Except.ok (tt, es, br)) = _ at hr
    cases hret : returnStep bytes base t with
    | error f =>
      rw [hret] at hr
      contradiction
    | ok p =>
      obtain ⟨u', br⟩ := p
      rw [hret] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have hm := writes_miss _ _ _ hp (body_trace_in (Pins.load s) base)
      obtain ⟨hs, hc'⟩ := runSteps_refines bytes base _ s t _ hc hb hm
      have hr' := return_refines t base bytes hc' _ _ hret
      unfold runLoaded
      rw [hs]
      change (match returnLoaded t with
        | .error f => Except.error f
        | .ok (tt, br) => Except.ok (tt, _, br)) = _
      rw [hr']

end SafegcdRow
