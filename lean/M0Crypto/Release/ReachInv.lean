import M0Crypto.Release.ReachSteps
import M0Crypto.Thumb.FastRun
import M0Crypto.Release.FrameBase

set_option linter.unusedSimpArgs false

/-!
# State invariants and run determinism for `ReachS`

* `stepH_mem_other`: a Harvard step changes memory only at the bytes of its write accesses.
* `ReachS.add_inv`: a state predicate preserved by every step the step condition admits holds at
  every pre-state of the run, and so can be added to the step condition.
* `ReachS.and_region`: two judgments about the same start state end in the same run, provided one
  of their step conditions keeps the run away from the stop address (the stop address may lie
  inside the code, as a return address does).
-/

namespace M0Crypto.Release
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

variable {base : Word}

theorem stepH_mem_other {s s1 : State} {e : Event} (h : stepH B base s = .ok (s1, e)) (y : Word)
    (hy : ¬ Writes e.accesses y) : s1.mem y = s.mem y := by
  unfold Thumb.stepH at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i i _
  split at h
  · split at h
    · split at h
      · rename_i s' hex
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact exec_mem_other i s s' hex y hy
      · cases h
    · cases h
  · cases h

theorem stepH_pc {s s1 : State} {e : Event} (h : stepH B base s = .ok (s1, e)) : e.pc = s.pc := by
  unfold Thumb.stepH at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
      · cases h
    · cases h
  · cases h

theorem StepsOk.add_inv {P : State → Event → Prop} {Inv : State → Prop}
    (hstep : ∀ s e s1, stepH B base s = .ok (s1, e) → P s e → Inv s → Inv s1) :
    ∀ {n : Nat} {s : State}, StepsOk base P n s → Inv s → StepsOk base (fun x e => P x e ∧ Inv x) n s
  | 0, _, _, _ => trivial
  | n + 1, s, h, h0 => fun s1 e hs =>
    ⟨⟨(h s1 e hs).1, h0⟩, StepsOk.add_inv hstep (h s1 e hs).2 (hstep s e s1 hs (h s1 e hs).1 h0)⟩

theorem ReachS.add_inv {P : State → Event → Prop} {Inv : State → Prop} {s : State}
    {Q : State → Prop}
    (hstep : ∀ s e s1, stepH B base s = .ok (s1, e) → P s e → Inv s → Inv s1)
    (h : ReachS base P s Q) (h0 : Inv s) : ReachS base (fun x e => P x e ∧ Inv x) s Q := by
  obtain ⟨n, t, tr, hr, hok, hq⟩ := h
  exact ⟨n, t, tr, hr, StepsOk.add_inv hstep hok h0, hq⟩

/-- A 32-bit word of memory untouched by the step condition's writes is an invariant. -/
theorem ReachS.add_read32 {P : State → Event → Prop} {s : State} {Q : State → Prop} (a v : Word)
    (hw : ∀ x e, P x e → ∀ k < 4, ¬ Writes e.accesses (a + BitVec.ofNat 32 k))
    (h : ReachS base P s Q) (h0 : M0Crypto.Armv6M.read32 s.mem a = v) :
    ReachS base (fun x e => P x e ∧ M0Crypto.Armv6M.read32 x.mem a = v) s Q :=
  ReachS.add_inv (Inv := fun x => M0Crypto.Armv6M.read32 x.mem a = v)
    (fun x e x1 hs hp hx => by
      rw [← hx]
      exact M0Crypto.Release.Frame.read32_congr (fun k hk => stepH_mem_other hs _ (hw x e hp k hk))) h h0

/-- If one run reaches `stop` and the step condition forbids steps that start at `stop`, no run
satisfying that condition is longer than a run that reaches `stop` (here `m` is the length of
the run that never steps from `stop`). -/
theorem runH_le_of_stop {stop : Word} {P : State → Event → Prop}
    (hP : ∀ x e, P x e → e.pc ≠ stop) :
    ∀ {n m : Nat} {s t2 : State} {tr2 : List Event} {t1 : State} {tr1 : List Event},
    runH B base n s = .ok (t2, tr2) → t2.pc = stop → StepsOk base P m s →
    runH B base m s = .ok (t1, tr1) → m ≤ n
  | 0, 0, _, _, _, _, _, _, _, _, _ => Nat.le_refl _
  | 0, m + 1, s, t2, tr2, t1, tr1, h2, p2, o1, h1 => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, -⟩ := h2
    obtain ⟨s1, e, tr', hs, -, -⟩ := runH_succ_ok h1
    exact absurd (by rw [stepH_pc hs]; exact p2) (hP _ _ (o1 s1 e hs).1)
  | n + 1, 0, _, _, _, _, _, _, _, _, _ => Nat.zero_le _
  | n + 1, m + 1, s, t2, tr2, t1, tr1, h2, p2, o1, h1 => by
    obtain ⟨s1, e, tr', hs, h2', -⟩ := runH_succ_ok h2
    obtain ⟨s1', e', tr'', hs', h1', -⟩ := runH_succ_ok h1
    rw [hs] at hs'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    exact Nat.succ_le_succ (runH_le_of_stop hP h2' p2 (o1 s1 e hs).2 h1')

theorem StepsOk.prefix {P : State → Event → Prop} :
    ∀ {m n : Nat} {s : State} {t : State} {tr : List Event},
    m ≤ n → StepsOk base P n s → runH B base m s = .ok (t, tr) → StepsOk base P m s
  | 0, _, _, _, _, _, _, _ => trivial
  | m + 1, 0, _, _, _, h, _, _ => absurd h (by omega)
  | m + 1, n + 1, s, t, tr, hmn, hok, hr => fun s1 e hs => by
    obtain ⟨s1', e', tr', hs', hr', -⟩ := runH_succ_ok hr
    have := hs'
    rw [hs] at this
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨(hok s1 e hs).1, StepsOk.prefix (Nat.le_of_succ_le_succ hmn) (hok s1 e hs).2 hr'⟩

theorem StepsOk.and {P1 P2 : State → Event → Prop} :
    ∀ {m : Nat} {s : State}, StepsOk base P1 m s → StepsOk base P2 m s →
      StepsOk base (fun x e => P1 x e ∧ P2 x e) m s
  | 0, _, _, _ => trivial
  | m + 1, s, h1, h2 => fun s1 e hs =>
    ⟨⟨(h1 s1 e hs).1, (h2 s1 e hs).1⟩, StepsOk.and (h1 s1 e hs).2 (h2 s1 e hs).2⟩

/-- Two judgments about one start state hold of one run when the first never steps from the stop
address and the second only asks to reach it. The stop address may lie inside the code. -/
theorem ReachS.and_stop {stop : Word} {P1 P2 : State → Event → Prop} {s : State}
    {Q1 : State → Prop} (hP : ∀ x e, P1 x e → e.pc ≠ stop)
    (h1 : ReachS base P1 s (fun t => t.pc = stop ∧ Q1 t))
    (h2 : ReachS base P2 s (fun t => t.pc = stop)) :
    ReachS base (fun x e => P1 x e ∧ P2 x e) s (fun t => t.pc = stop ∧ Q1 t) := by
  obtain ⟨m, t1, tr1, r1, ok1, p1, q1⟩ := h1
  obtain ⟨n, t2, tr2, r2, ok2, p2⟩ := h2
  have hmn := runH_le_of_stop hP r2 p2 ok1 r1
  have ok2' := StepsOk.prefix hmn ok2 r1
  refine ⟨m, t1, tr1, r1, StepsOk.and ok1 ok2', p1, q1⟩

/-- A run reaching `stop` under a state-aware step condition is the model's `runStates`, and the
condition holds at every non-final state of it. -/
theorem runStates_of_runH_pol {stop : Word} {P : State → Event → Prop} :
    ∀ (n fuel : Nat) (s s' : State) (tr : List Event), CodeAt s.mem base B →
    runH B base n s = .ok (s', tr) →
    StepsOk base (fun x e => MissesCode B base e.accesses ∧ e.pc ≠ stop ∧ P x e) n s →
    s'.pc = stop → n ≤ fuel →
    ∃ states, runStates stop fuel s = .ok (states, tr) ∧
      ∀ x ∈ states, x.pc ≠ stop → ∀ x' e, step x = .ok (x', e) → P x e
  | 0, fuel, s, s', tr, _, h, _, hstop, _ => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[s], ?_, ?_⟩
    · cases fuel <;> simp [runStates, hstop]
    · intro x hx hne
      simp only [List.mem_singleton] at hx
      exact absurd (hx ▸ hstop) hne
  | n + 1, fuel, s, s', tr, hc, h, hok, hstop, hfuel => by
    obtain ⟨s1, e, tr', hs, h', rfl⟩ := runH_succ_ok h
    obtain ⟨⟨hm, hne, hP⟩, hrest⟩ := hok s1 e hs
    have hst := step_of_stepH hc hs
    have hc1 := codeAt_step hc hst hm
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨states, hr, hpol⟩ := runStates_of_runH_pol n f s1 s' tr' hc1 h' hrest hstop (by omega)
    have hpc : s.pc ≠ stop := stepH_pc hs ▸ hne
    refine ⟨s :: states, ?_, ?_⟩
    · simp [runStates, hpc, hst, hr]
    · intro x hx hxne x' e' hx'
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [hst] at hx'
        simp only [Except.ok.injEq, Prod.mk.injEq] at hx'
        obtain ⟨-, rfl⟩ := hx'
        exact hP
      · exact hpol x hx hxne x' e' hx'


/-! ## Blocks and calls under a step condition implied by a region-and-write bound -/

theorem BlockOk.mono {P Q : State → Event → Prop} (hPQ : ∀ x e, P x e → Q x e) :
    ∀ (is : List Instr) (s : State), BlockOk P is s → BlockOk Q is s
  | [], _, _ => trivial
  | i :: is, s, h => ⟨hPQ _ _ h.1, BlockOk.mono hPQ is _ h.2⟩

/-- `ReachW.block`, for any step condition implied by region membership and the write bound. -/
theorem ReachS.blockW {Pn Wr : Word → Prop} {P : State → Event → Prop} {s : State}
    {Q : State → Prop} {off : Nat} {is : List Instr}
    (hP : ∀ x e, RegionWrites Pn Wr x e → P x e)
    (hr : InRegion Pn base off (seqSize is)) (hb : base.toNat % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hq : ReachS base P (execAll is s) Q) : ReachS base P s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf ha ?_ hq
  refine BlockOk.mono hP is s ?_
  rw [show RegionWrites Pn Wr = fun _ e => Pn e.pc ∧ ∀ y, Writes e.accesses y → Wr y from rfl,
    blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  refine ⟨?_, fun y hy => hw e he y hy⟩
  rw [hep, hpc, ofNat_add_assoc]
  exact hr j hj

/-- `ReachW.bl`, for any step condition implied by region membership. -/
theorem ReachS.blW {Pn Wr : Word → Prop} {P : State → Event → Prop} {s : State}
    {Q : State → Prop} {off : Nat}
    (hP : ∀ x e, RegionWrites Pn Wr x e → P x e) (hr : Pn (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat) (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachS base P ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachS base P s Q :=
  ReachS.bl hb off tgt imm hpc ho hi hsz ht
    (hP _ _ ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩) hq

theorem ReachS.bcondW {Pn Wr : Word → Prop} {P : State → Event → Prop} {s : State} {Q : State → Prop}
    {off : Nat} (hP : ∀ x e, RegionWrites Pn Wr x e → P x e) (hr : Pn (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat) (cond : BitVec 4) (imm : BitVec 8)
    (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) : ReachS base P s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht
    (hP _ _ ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩) hT hF

theorem ReachS.bW {Pn Wr : Word → Prop} {P : State → Event → Prop} {s : State} {Q : State → Prop}
    {off : Nat} (hP : ∀ x e, RegionWrites Pn Wr x e → P x e) (hr : Pn (base + BitVec.ofNat 32 off))
    (hb : base.toNat % 2 = 0) (tgt : Nat) (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachS base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachS base P s Q :=
  ReachS.b hb off tgt imm hpc ho hi hsz ht
    (hP _ _ ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y)⟩) hq

end M0Crypto.Release
