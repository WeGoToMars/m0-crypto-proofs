import M0Crypto.Release.AccessReach
import M0Crypto.Release.RunStates

set_option linter.unusedSimpArgs false

/-!
`ReachS`: one reachability judgment whose step condition sees the state before each step.

`ReachS base P s Q` says that a Harvard run of the release bytes from `s` reaches a
state satisfying `Q`, and that every step of the run satisfies `P` on its pre-state
and its event. The other judgments (`Reach`, `ReachA`, `ReachRW`, `ReachEvents`) only
constrain events; they are the instances whose `P` ignores the pre-state
(`reach_iff_reachS`, `reachA_iff_reachS`, `reachEvents_iff_reachS`).

The pre-state matters for constant-time site obligations. A store's separation or a
branch's disclosed flag is a fact about the machine state at that instruction, which
the functional proof knows and an event-only predicate cannot carry.
`ReachS.recorded` transfers `P` to every non-final state of a recorded `runStates`
execution of the same call, which is the form the certificate soundness theorem uses.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- Every step of the first `n` Harvard steps from `s` satisfies `P` on its pre-state
and event. Steps after a fault impose nothing; `ReachS` pairs this with a successful run. -/
def StepsOk (base : Word) (P : State → Event → Prop) : Nat → State → Prop
  | 0, _ => True
  | n + 1, s => ∀ s1 e, stepH B base s = .ok (s1, e) → P s e ∧ StepsOk base P n s1

def ReachS (base : Word) (P : State → Event → Prop) (s : State) (Q : State → Prop) : Prop :=
  ∃ n t tr, runH B base n s = .ok (t, tr) ∧ StepsOk base P n s ∧ Q t

variable {base : Word} {P : State → Event → Prop}

/-! ## `StepsOk` -/

theorem StepsOk.cons {n : Nat} {s s1 : State} {e : Event} (hs : stepH B base s = .ok (s1, e))
    (hp : P s e) (h : StepsOk base P n s1) : StepsOk base P (n + 1) s := by
  intro s1' e' h'
  rw [hs] at h'
  cases h'
  exact ⟨hp, h⟩

theorem StepsOk.uncons {n : Nat} {s s1 : State} {e : Event} (hs : stepH B base s = .ok (s1, e))
    (h : StepsOk base P (n + 1) s) : P s e ∧ StepsOk base P n s1 :=
  h s1 e hs

theorem StepsOk.mono {P' : State → Event → Prop} (hm : ∀ x e, P x e → P' x e) :
    ∀ {n : Nat} {s : State}, StepsOk base P n s → StepsOk base P' n s
  | 0, _, _ => trivial
  | _ + 1, _, h => fun s1 e hs => ⟨hm _ _ (h s1 e hs).1, StepsOk.mono hm (h s1 e hs).2⟩

/-- Decompose a successful run into its first step and the rest. -/
theorem runH_succ_ok {n : Nat} {s t : State} {tr : List Event}
    (h : runH B base (n + 1) s = .ok (t, tr)) :
    ∃ s1 e tr', stepH B base s = .ok (s1, e) ∧ runH B base n s1 = .ok (t, tr') ∧ tr = e :: tr' := by
  simp only [Thumb.runH] at h
  split at h
  · cases h
  · rename_i s1 e h1
    split at h
    · cases h
    · rename_i t' tr' h2
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s1, e, tr', h1, h2, rfl⟩

theorem StepsOk.append : ∀ {m n : Nat} {s s1 : State} {t1 : List Event},
    runH B base m s = .ok (s1, t1) → StepsOk base P m s → StepsOk base P n s1 →
    StepsOk base P (m + n) s
  | 0, n, s, s1, t1, hr, _, h2 => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    simpa using h2
  | m + 1, n, s, s1, t1, hr, h1, h2 => by
    obtain ⟨s', e, tr', hs, hr', -⟩ := runH_succ_ok hr
    obtain ⟨hp, h1'⟩ := h1.uncons hs
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact StepsOk.cons hs hp (StepsOk.append hr' h1' h2)

/-- For a predicate that ignores the pre-state, `StepsOk` is a condition on the trace. -/
theorem stepsOk_events_iff {p : Event → Prop} : ∀ {n : Nat} {s t : State} {tr : List Event},
    runH B base n s = .ok (t, tr) → (StepsOk base (fun _ e => p e) n s ↔ ∀ e ∈ tr, p e)
  | 0, s, t, tr, hr => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    simp [StepsOk]
  | n + 1, s, t, tr, hr => by
    obtain ⟨s1, e, tr', hs, hr', rfl⟩ := runH_succ_ok hr
    have ih := stepsOk_events_iff (p := p) hr'
    constructor
    · intro h
      obtain ⟨hp, h'⟩ := h.uncons hs
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hp
      · exact ih.mp h' e' he'
    · intro h
      exact StepsOk.cons hs (h e List.mem_cons_self)
        (ih.mpr fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-! ## Combinators -/

theorem ReachS.done {s : State} {Q : State → Prop} (h : Q s) : ReachS base P s Q :=
  ⟨0, s, [], rfl, trivial, h⟩

theorem ReachS.mono {P' : State → Event → Prop} {s : State} {Q Q' : State → Prop}
    (h : ReachS base P s Q) (hp : ∀ x e, P x e → P' x e) (hq : ∀ t, Q t → Q' t) :
    ReachS base P' s Q' := by
  obtain ⟨n, t, tr, hr, hok, hQ⟩ := h
  exact ⟨n, t, tr, hr, hok.mono hp, hq t hQ⟩

theorem ReachS.bind {s : State} {Q : State → Prop}
    (h : ReachS base P s fun t => ReachS base P t Q) : ReachS base P s Q := by
  obtain ⟨n, t, tr, hr, hok, m, u, tail, hr', hok', hq⟩ := h
  refine ⟨n + m, u, tr ++ tail, ?_, StepsOk.append hr hok hok', hq⟩
  rw [runH_add, hr]; simp only [hr']

/-- Execute one instruction; `P` must hold at its pre-state and event. -/
theorem ReachS.step {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hp : P s ⟨s.pc, i, i.accesses s⟩) (hq : ReachS base P s1 Q) : ReachS base P s Q := by
  obtain ⟨n, u, tr, hr, hok, hq⟩ := hq
  have hs := stepH_of_instr hb (by rw [B_len]; decide) hpc ho hi hsz ha hex
  exact ⟨n + 1, u, _ :: tr, by rw [runH_one_step n hs, hr], StepsOk.cons hs hp hok, hq⟩

/-- `P` at every pre-state and event of a fall-through block. -/
def BlockOk (P : State → Event → Prop) : List Instr → State → Prop
  | [], _ => True
  | i :: is, s => P s ⟨s.pc, i, i.accesses s⟩ ∧ BlockOk P is (i.next s)

/-- An event-only condition on a block is a condition on its trace. -/
theorem blockOk_events_iff {p : Event → Prop} :
    ∀ (is : List Instr) (s : State), BlockOk (fun _ e => p e) is s ↔ ∀ e ∈ traceAll is s, p e
  | [], s => by simp [BlockOk, traceAll]
  | i :: is, s => by simp [BlockOk, traceAll, blockOk_events_iff is]

theorem ReachS.block {Q : State → Prop} (hb : base.toNat % 2 = 0) :
    ∀ (is : List Instr) (off : Nat) (s : State), s.pc = base + BitVec.ofNat 32 off →
      off % 2 = 0 → seqAt B off is = true → is.all Instr.falls = true →
      alignedAll is s = true → BlockOk P is s → ReachS base P (execAll is s) Q →
      ReachS base P s Q
  | [], _, _, _, _, _, _, _, _, hq => hq
  | i :: is, off, s, hpc, ho, hseq, hf, ha, hok, hq => by
    simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hseq
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [alignedAll, Bool.and_eq_true] at ha
    have hex := exec_ok_of_falls hf.1 s
    refine ReachS.step hb off i hpc ho hseq.1.1 hseq.1.2 ha.1 hex hok.1 ?_
    have hpc1 : (i.next s).pc = base + BitVec.ofNat 32 (off + i.size) := by
      rw [exec_pc hf.1 hex, hpc, ofNat_add_assoc]
    exact ReachS.block hb is (off + i.size) (i.next s) hpc1
      (by have := instr_size_even i; omega) hseq.2 hf.2 ha.2 hok.2 hq

/-- A conditional branch at `off` with target offset `tgt`. -/
theorem ReachS.bcond {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .bcond cond imm, []⟩)
    (hT : condPassed cond s = true →
      ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachS base P s Q := by
  cases hc : condPassed cond s
  · apply ReachS.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, Bool.false_eq_true, ite_false]; rfl)
      (by simpa [Instr.accesses] using hp)
    have := hF hc
    rwa [show s.pc + BitVec.ofNat 32 (Instr.bcond cond imm).size =
        base + BitVec.ofNat 32 (off + 2) by rw [hpc, ofNat_add_assoc]; rfl]
  · apply ReachS.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, ite_true]; rfl)
      (by simpa [Instr.accesses] using hp)
    have := hT hc
    rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- An unconditional branch at `off` with target offset `tgt`. -/
theorem ReachS.b {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .b imm, []⟩)
    (hq : ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachS base P s Q := by
  apply ReachS.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by simpa [Instr.accesses] using hp)
  rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
    rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- A branch-with-link at `off` with target offset `tgt`. -/
theorem ReachS.bl {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .bl imm, []⟩)
    (hq : ReachS base P ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachS base P s Q := by
  apply ReachS.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by simpa [Instr.accesses] using hp)
  rw [show s.pc + 4#32 = base + BitVec.ofNat 32 (off + 4) by rw [hpc, ofNat_add_assoc],
    show base + BitVec.ofNat 32 (off + 4) + imm.signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [← ht, ← ofNat_add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]]
  exact hq

/-! ## The event-only judgments are instances -/

/-- The event-only form of a `ReachS` judgment. -/
theorem reachS_events_iff (p : Event → Prop) (s : State) (Q : State → Prop) :
    ReachS base (fun _ e => p e) s Q ↔
      ∃ n t tr, runH B base n s = .ok (t, tr) ∧ (∀ e ∈ tr, p e) ∧ Q t := by
  constructor
  · rintro ⟨n, t, tr, hr, hok, hq⟩
    exact ⟨n, t, tr, hr, (stepsOk_events_iff hr).mp hok, hq⟩
  · rintro ⟨n, t, tr, hr, hp, hq⟩
    exact ⟨n, t, tr, hr, (stepsOk_events_iff hr).mpr hp, hq⟩

theorem reach_iff_reachS (Wr : Word → Prop) (s : State) (Q : State → Prop) :
    Reach base Wr s Q ↔ ReachS base (fun _ e => ∀ y, Writes e.accesses y → Wr y) s Q := by
  rw [reachS_events_iff]; rfl

theorem reachA_iff_reachS (ap : Access → Prop) (s : State) (Q : State → Prop) :
    ReachA base ap s Q ↔ ReachS base (fun _ e => ∀ a ∈ e.accesses, ap a) s Q := by
  rw [reachS_events_iff]; rfl

theorem reachRW_iff_reachS (Rd Wr : Word → Prop) (s : State) (Q : State → Prop) :
    ReachRW base Rd Wr s Q ↔ ReachS base (fun _ e => ∀ a ∈ e.accesses, RWAccess Rd Wr a) s Q :=
  reachA_iff_reachS _ s Q

theorem reachEvents_iff_reachS (allowed : Word → Kind → Word → Prop) (s : State)
    (Q : State → Prop) :
    ConstantTime.ReachEvents base allowed s Q ↔
      ReachS base (fun _ e => ∀ a ∈ e.accesses, ∀ k < a.width,
        allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k)) s Q := by
  rw [reachS_events_iff]; rfl

/-! ## Transfer to recorded executions -/

/-- Every non-final state of a recorded run of the same call satisfies `P` with the event
of its step. Requires that the code is in memory, that steps allowed by `P` do not write
it, and that the run reaches `stop`. -/
theorem ReachS.recorded {stop : Word} {Q : State → Prop}
    (hwc : ∀ x e, P x e → MissesCode B base e.accesses) :
    ∀ {s : State}, CodeAt s.mem base B → ReachS base P s (fun t => t.pc = stop ∧ Q t) →
      ∀ {fuel : Nat} {states : List State} {events : List Event},
      runStates stop fuel s = .ok (states, events) →
      ∀ x ∈ states, x.pc ≠ stop → ∃ t e, Thumb.step x = .ok (t, e) ∧ P x e := by
  intro s hc h
  obtain ⟨n, t, tr, hr, hok, hstop, -⟩ := h
  induction n generalizing s tr with
  | zero =>
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    intro fuel states events hrun x hx hne
    unfold runStates at hrun
    simp only [hstop, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun
    simp only [List.mem_singleton] at hx
    exact absurd (hx ▸ hstop) hne
  | succ n ih =>
    obtain ⟨s1, e, tr', hs, hr', -⟩ := runH_succ_ok hr
    obtain ⟨hp, hok'⟩ := hok.uncons hs
    have hstep := step_of_stepH hc hs
    have hc1 := codeAt_step hc hstep (hwc _ _ hp)
    intro fuel states events hrun x hx hne
    unfold runStates at hrun
    split at hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [List.mem_singleton] at hx
      subst hx
      exact absurd ‹_› hne
    · split at hrun
      · cases hrun
      · rename_i f
        rw [hstep] at hrun
        simp only at hrun
        split at hrun
        · cases hrun
        · rename_i states' es' hrun'
          simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨s1, e, hstep, hp⟩
          · exact ih hc1 tr' hr' hok' hrun' x hx hne

/-! ## Conjunction of two judgments about the same run

Two successful runs from one state that both end outside the code are the same run: the
step at a state outside the code faults, so neither can be extended. -/

theorem stepH_ok_code {s s1 : State} {e : Event} (h : stepH B base s = .ok (s1, e)) :
    ∃ off < B.length, s.pc = base + BitVec.ofNat 32 off := by
  unfold Thumb.stepH at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i i _
  split at h
  · rename_i hlen
    refine ⟨(s.pc - base).toNat, ?_, (Thumb.base_add_sub s.pc).symm⟩
    have := instr_size_even i
    cases i <;> simp [Instr.size] at hlen ⊢ <;> omega
  · cases h

theorem runH_unique {stop : Word} (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i) :
    ∀ {m n : Nat} {s t1 t2 : State} {tr1 tr2 : List Event},
    runH B base m s = .ok (t1, tr1) → t1.pc = stop →
    runH B base n s = .ok (t2, tr2) → t2.pc = stop → m = n ∧ t1 = t2 ∧ tr1 = tr2
  | 0, 0, s, t1, t2, tr1, tr2, h1, _, h2, _ => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, rfl, rfl⟩
  | 0, n + 1, s, t1, t2, tr1, tr2, h1, p1, h2, _ => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨s1, e, tr', hs, -, -⟩ := runH_succ_ok h2
    obtain ⟨off, ho, hp⟩ := stepH_ok_code hs
    exact absurd (p1 ▸ hp) (hstop off ho)
  | m + 1, 0, s, t1, t2, tr1, tr2, h1, _, h2, p2 => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨s1, e, tr', hs, -, -⟩ := runH_succ_ok h1
    obtain ⟨off, ho, hp⟩ := stepH_ok_code hs
    exact absurd (p2 ▸ hp) (hstop off ho)
  | m + 1, n + 1, s, t1, t2, tr1, tr2, h1, p1, h2, p2 => by
    obtain ⟨s1, e, tr', hs, hr, rfl⟩ := runH_succ_ok h1
    obtain ⟨s1', e', tr'', hs', hr', rfl⟩ := runH_succ_ok h2
    rw [hs] at hs'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    obtain ⟨hmn, rfl, rfl⟩ := runH_unique hstop hr p1 hr' p2
    exact ⟨by omega, rfl, rfl⟩

/-- Two judgments about runs ending at an address outside the code hold of one run. -/
theorem ReachS.and {stop : Word} {P1 P2 : State → Event → Prop} {s : State} {Q1 Q2 : State → Prop}
    (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i)
    (h1 : ReachS base P1 s (fun t => t.pc = stop ∧ Q1 t))
    (h2 : ReachS base P2 s (fun t => t.pc = stop ∧ Q2 t)) :
    ReachS base (fun x e => P1 x e ∧ P2 x e) s (fun t => t.pc = stop ∧ Q1 t ∧ Q2 t) := by
  obtain ⟨m, t1, tr1, r1, ok1, p1, q1⟩ := h1
  obtain ⟨n, t2, tr2, r2, ok2, p2, q2⟩ := h2
  obtain ⟨rfl, rfl, rfl⟩ := runH_unique hstop r1 p1 r2 p2
  refine ⟨m, t1, tr1, r1, ?_, p1, q1, q2⟩
  clear r1 r2
  induction m generalizing s with
  | zero => trivial
  | succ k ih =>
    intro s1 e hs
    exact ⟨⟨(ok1 s1 e hs).1, (ok2 s1 e hs).1⟩, ih (ok1 s1 e hs).2 (ok2 s1 e hs).2⟩

/-! ## Region-tracking write-bounded judgment

`ReachW base Pc Wr` is `Reach base Wr` that also records that every executed instruction lies
at a program counter in `Pc`. Proofs written with it yield `Reach` (`ReachW.toReach`) and,
by `ReachS.mono`, any step condition that holds at the PCs of the region. -/

/-- Every executed instruction is at a PC in `Pc` and writes only inside `Wr`. -/
def RegionWrites (Pc Wr : Word → Prop) (_ : State) (e : Event) : Prop :=
  Pc e.pc ∧ ∀ y, Writes e.accesses y → Wr y

abbrev ReachW (base : Word) (Pc Wr : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachS base (RegionWrites Pc Wr) s Q

/-- The `n` code bytes from offset `off` are at PCs in `Pc`. -/
def InRegion (Pc : Word → Prop) (base : Word) (off n : Nat) : Prop :=
  ∀ j < n, Pc (base + BitVec.ofNat 32 (off + j))

theorem InRegion.sub {Pc : Word → Prop} {base : Word} {m N a n : Nat} (h : InRegion Pc base m N)
    (hn : a + n ≤ N) : InRegion Pc base (m + a) n := fun j hj => by
  have := h (a + j) (by omega)
  rwa [show m + a + j = m + (a + j) by omega]

theorem InRegion.prefix {Pc : Word → Prop} {base : Word} {m N n : Nat} (h : InRegion Pc base m N)
    (hn : n ≤ N) : InRegion Pc base m n := fun j hj => h j (by omega)

theorem InRegion.at {Pc : Word → Prop} {base : Word} {m N a : Nat} (h : InRegion Pc base m N)
    (ha : a < N) : Pc (base + BitVec.ofNat 32 (m + a)) := by
  simpa using h a ha

theorem inRegion_pcBetween {lo hi off n : Nat} (h1 : lo ≤ off) (h2 : off + n ≤ hi) :
    InRegion (ConstantTime.PCBetween base lo hi) base off n :=
  fun j hj => ⟨off + j, by omega, by omega, rfl⟩

theorem ReachW.toReach {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pc Wr s Q) : Reach base Wr s Q :=
  (reach_iff_reachS Wr s Q).mpr (h.mono (fun _ _ h => h.2) (fun _ h => h))

/-- Every `Reach` is a `ReachW` for the trivial region. -/
theorem Reach.toReachW {Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : Reach base Wr s Q) : ReachW base (fun _ => True) Wr s Q :=
  ((reach_iff_reachS Wr s Q).mp h).mono (fun _ _ h => ⟨trivial, h⟩) (fun _ h => h)

theorem ReachW.monoPc {Pc Pc' Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pc Wr s Q) (hp : ∀ pc, Pc pc → Pc' pc) : ReachW base Pc' Wr s Q :=
  h.mono (fun _ _ h => ⟨hp _ h.1, h.2⟩) (fun _ h => h)

theorem ReachW.monoW {Pc Wr Wr' : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachW base Pc Wr s Q) (hw : ∀ y, Wr y → Wr' y) : ReachW base Pc Wr' s Q :=
  h.mono (fun _ _ h => ⟨h.1, fun y hy => hw y (h.2 y hy)⟩) (fun _ h => h)

theorem ReachW.block {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hr : InRegion Pc base off (seqSize is))
    (hq : ReachW base Pc Wr (execAll is s) Q) : ReachW base Pc Wr s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf ha ?_ hq
  rw [show RegionWrites Pc Wr = fun _ e => Pc e.pc ∧ ∀ y, Writes e.accesses y → Wr y from rfl,
    blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  refine ⟨?_, fun y hy => hw e he y hy⟩
  rw [hep, hpc, ofNat_add_assoc]
  exact hr j hj

theorem ReachW.step {Pc Wr : Word → Prop} {s s1 : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off : Nat) (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y) (hr : Pc (base + BitVec.ofNat 32 off))
    (hq : ReachW base Pc Wr s1 Q) : ReachW base Pc Wr s Q :=
  ReachS.step hb off i hpc ho hi hsz ha hex ⟨by rw [hpc]; exact hr, hw⟩ hq

theorem ReachW.bcond {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (hT : condPassed cond s = true →
      ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachW base Pc Wr s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩ hT hF

theorem ReachW.b {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (hq : ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    ReachW base Pc Wr s Q :=
  ReachS.b hb off tgt imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩ hq

theorem ReachW.bl {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (hq : ReachW base Pc Wr ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachW base Pc Wr s Q :=
  ReachS.bl hb off tgt imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩ hq


/-! Variants taking the region fact first, so that `apply` leaves the other obligations as goals. -/

theorem InRegion.head {Pc : Word → Prop} {base : Word} {m N : Nat} (h : InRegion Pc base m N)
    (hN : 0 < N) : Pc (base + BitVec.ofNat 32 m) := by
  simpa using h 0 hN

theorem ReachW.blockR {Pc Wr : Word → Prop} {s : State} {Q : State → Prop} {base : Word}
    {off : Nat} {is : List Instr} (hr : InRegion Pc base off (seqSize is))
    (hb : base.toNat % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hq : ReachW base Pc Wr (execAll is s) Q) : ReachW base Pc Wr s Q :=
  ReachW.block hb is off hpc ho hseq hf ha hw hr hq

theorem ReachW.stepR {Pc Wr : Word → Prop} {s s1 : State} {Q : State → Prop} {base : Word}
    {off : Nat} (hr : Pc (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y)
    (hq : ReachW base Pc Wr s1 Q) : ReachW base Pc Wr s Q :=
  ReachW.step hb off i hpc ho hi hsz ha hex hw hr hq

theorem ReachW.bcondR {Pc Wr : Word → Prop} {s : State} {Q : State → Prop} {base : Word}
    {off : Nat} (hr : Pc (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true →
      ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachW base Pc Wr s Q :=
  ReachW.bcond hb off tgt cond imm hpc ho hi hsz ht hr hT hF

theorem ReachW.bR {Pc Wr : Word → Prop} {s : State} {Q : State → Prop} {base : Word}
    {off : Nat} (hr : Pc (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachW base Pc Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    ReachW base Pc Wr s Q :=
  ReachW.b hb off tgt imm hpc ho hi hsz ht hr hq

theorem ReachW.blR {Pc Wr : Word → Prop} {s : State} {Q : State → Prop} {base : Word}
    {off : Nat} (hr : Pc (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachW base Pc Wr ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachW base Pc Wr s Q :=
  ReachW.bl hb off tgt imm hpc ho hi hsz ht hr hq

end M0Crypto.Release
