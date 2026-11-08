import M0Crypto.Thumb.FastRun

/-!
Harvard view of the whole-function model, for proofs.

The model has one memory for code and data (`Exec.lean`). Proofs are easier when
instructions come from the fixed artifact bytes instead: `stepH bytes base`
fetches with `instrAt bytes (pc - base)` and otherwise executes exactly as `step`.

* `step_of_stepH`: when the artifact sits at `base` in memory (`CodeAt`), a
  successful `stepH` is a successful `step` with the same result and event.
* `codeAt_step`: a step whose writes miss the code keeps `CodeAt`.
* `runUntil_of_runH`: an `n`-step Harvard run whose writes all miss the code,
  which never passes through `stop` before its last state and ends at `stop`, is
  what `runUntil stop fuel` returns for any `fuel ≥ n`.

So a theorem about `runH` plus "no write hits the code" is a theorem about the
model's `runUntil`. Nothing here weakens the single-memory semantics.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

variable (bytes : List (BitVec 8)) (base : Word)

/-- `step`, fetching from the artifact bytes at offset `pc - base`. -/
def stepH (s : State) : Except Fault (State × Event) :=
  let pc := s.pc
  if pc.getLsbD 0 then .error (.pcOdd pc)
  else
    let off := (pc - base).toNat
    match instrAt bytes off with
    | none => .error (.undefined pc)
    | some i =>
      if off + i.size ≤ bytes.length then
        let acc := i.accesses s
        if acc.all Access.aligned then
          match i.exec s with
          | .ok s' => .ok (s', ⟨pc, i, acc⟩)
          | .error e => .error e
        else .error (.unaligned pc)
      else .error (.undefined pc)

/-- Exactly `n` Harvard steps. -/
def runH : Nat → State → Except Fault (State × List Event)
  | 0, s => .ok (s, [])
  | n + 1, s =>
    match stepH bytes base s with
    | .error e => .error e
    | .ok (s1, e) =>
      match runH n s1 with
      | .error e' => .error e'
      | .ok (s2, es) => .ok (s2, e :: es)

variable {bytes base}

theorem base_add_sub (pc : Word) : base + BitVec.ofNat 32 (pc - base).toNat = pc := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_omega

theorem step_of_stepH {s s' : State} {e : Event} (hc : CodeAt s.mem base bytes)
    (h : stepH bytes base s = .ok (s', e)) : step s = .ok (s', e) := by
  unfold stepH at h
  simp only at h
  split at h
  · cases h
  · rename_i hodd
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hlen
        have hpc := base_add_sub (base := base) s.pc
        have hd := decode_at hc _ i hi hlen
        rw [hpc] at hd
        simp only [step, hodd, hd]
        exact h
      · cases h

/-- Byte `i` of the code is not written by `acc`. -/
def MissesCode (bytes : List (BitVec 8)) (base : Word) (acc : List Access) : Prop :=
  ∀ i, i < bytes.length → ¬ Writes acc (base + BitVec.ofNat 32 i)

theorem codeAt_step {s s' : State} {e : Event} (hc : CodeAt s.mem base bytes)
    (h : step s = .ok (s', e)) (hm : MissesCode bytes base e.accesses) :
    CodeAt s'.mem base bytes := by
  intro i hi
  rw [step_mem_other h _ (by rw [mem_writtenAddrs]; exact hm i hi)]
  exact hc i hi

/-- Every event of a trace misses the code. -/
def TraceMissesCode (bytes : List (BitVec 8)) (base : Word) (tr : List Event) : Prop :=
  ∀ e ∈ tr, MissesCode bytes base e.accesses

theorem runUntil_of_runH {stop : Word} : ∀ (n fuel : Nat) (s s' : State) (tr : List Event),
    CodeAt s.mem base bytes → runH bytes base n s = .ok (s', tr) →
    TraceMissesCode bytes base tr → (∀ e ∈ tr, e.pc ≠ stop) → s'.pc = stop → n ≤ fuel →
    runUntil stop fuel s = .ok (s', tr)
  | 0, fuel, s, s', tr, _, h, _, _, hstop, _ => by
    simp only [runH, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases fuel <;> simp [runUntil, hstop]
  | n + 1, fuel, s, s', tr, hc, h, hm, hne, hstop, hfuel => by
    simp only [runH] at h
    split at h
    · cases h
    · rename_i s1 e h1
      split at h
      · cases h
      · rename_i s2 es h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hs := step_of_stepH hc h1
        have hepc : e.pc = s.pc := by
          unfold stepH at h1; simp only at h1
          split at h1; · cases h1
          split at h1; · cases h1
          split at h1
          · split at h1
            · split at h1
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h1; rw [← h1.2]
              · cases h1
            · cases h1
          · cases h1
        have hc1 := codeAt_step hc hs (hm e (List.mem_cons_self))
        obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have ih := runUntil_of_runH n f s1 s2 es hc1 h2
          (fun e' he' => hm e' (List.mem_cons_of_mem _ he'))
          (fun e' he' => hne e' (List.mem_cons_of_mem _ he')) hstop (by omega)
        have hpc : s.pc ≠ stop := hepc ▸ hne e List.mem_cons_self
        rw [runUntil]
        simp [hpc, hs, ih]

/-! ## Composition -/

theorem runH_add (m n : Nat) (s : State) :
    runH bytes base (m + n) s =
      match runH bytes base m s with
      | .error e => .error e
      | .ok (s1, t1) =>
        match runH bytes base n s1 with
        | .error e => .error e
        | .ok (s2, t2) => .ok (s2, t1 ++ t2) := by
  induction m generalizing s with
  | zero =>
    simp only [Nat.zero_add, runH, List.nil_append]
    cases runH bytes base n s <;> rfl
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [runH]
    cases stepH bytes base s with
    | error e => rfl
    | ok r =>
      obtain ⟨s1, e⟩ := r
      simp only [ih]
      cases runH bytes base m s1 with
      | error e => rfl
      | ok r1 =>
        obtain ⟨s2, t1⟩ := r1
        simp only
        cases runH bytes base n s2 with
        | error e => rfl
        | ok r2 => rfl

end M0Crypto.Thumb
