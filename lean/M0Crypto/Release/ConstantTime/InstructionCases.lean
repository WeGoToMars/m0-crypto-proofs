import M0Crypto.Release.ConstantTime.MultiStore
import M0Crypto.Release.ConstantTime.DataProcessingSound
import M0Crypto.Release.ConstantTime.BitwiseSound
import M0Crypto.Release.ConstantTime.CompareSound
import M0Crypto.Release.ConstantTime.InstructionSound
import M0Crypto.Release.ConstantTime.ReturnSound
import M0Crypto.Release.ConstantTime.RunInvariant
import M0Crypto.Release.ConstantTime.WriteBounds
import M0Crypto.Release.ConstantTime.Alignment

/-! Paired certificate execution for register-only instructions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb
open M0Crypto.Armv6M (State)

/-- Instructions whose certificate step needs no memory-separation premise. -/
def registerInstruction : Instr → Bool
  | .lslImm .. | .lsrImm .. | .addReg .. | .subReg .. | .addImm3 .. | .subImm3 ..
  | .movImm .. | .cmpImm .. | .addImm8 .. | .subImm8 .. | .movHi .. | .addRdSp ..
  | .addSp .. | .subSp .. | .uxth .. | .ldrSp .. | .ldm .. => true
  | .dp .. => true
  | _ => false

/-- All register-only instruction forms and read-only multiple loads preserve
paired certificate execution. -/
theorem certPoint_register_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (i : Instr)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (h : LowEq p bytes off st s₁ s₂) (hr : registerInstruction i = true)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  cases i with
  | lslImm d m k => exact certPoint_lslImm_paired d m k hc hi hm hp h heven
  | lsrImm d m k => exact certPoint_lsrImm_paired d m k hc hi hm hp h heven
  | addReg d n m => exact certPoint_addReg_paired d n m hc hi hm hp h heven
  | subReg d n m => exact certPoint_subReg_paired d n m hc hi hm hp h heven
  | addImm3 d n k => exact certPoint_addImm3_paired d n k hc hi hm hp h heven
  | subImm3 d n k => exact certPoint_subImm3_paired d n k hc hi hm hp h heven
  | movImm d k => exact certPoint_movImm_paired d k hc hi hm hp h heven
  | cmpImm n k => exact certPoint_cmpImm_paired n k hc hi hm hp h heven
  | addImm8 d k => exact certPoint_addImm8_paired d k hc hi hm hp h heven
  | subImm8 d k => exact certPoint_subImm8_paired d k hc hi hm hp h heven
  | movHi d m => exact certPoint_movHi_paired d m hc hi hm hp h heven
  | addRdSp d k => exact certPoint_addRdSp_paired d k hc hi hm hp h heven
  | addSp k => exact certPoint_addSp_paired k hc hi hm hp h heven
  | subSp k => exact certPoint_subSp_paired k hc hi hm hp h heven
  | uxth d m => exact certPoint_uxth_paired d m hc hi hm hp h heven
  | ldrSp d k => exact certPoint_ldrSp_paired d k hc hi hm hp h heven
  | ldm n l => exact certPoint_ldm_paired n l hc hi hm hp h heven
  | dp op d m =>
    cases op with
    | ands => exact certPoint_ands_paired d m hc hi hm hp h heven
    | eors => exact certPoint_logical_paired .eors d m (by simp) hc hi hm hp h heven
    | orrs => exact certPoint_logical_paired .orrs d m (by simp) hc hi hm hp h heven
    | muls => exact certPoint_logical_paired .muls d m (by simp) hc hi hm hp h heven
    | adcs => exact certPoint_adcs_paired d m hc hi hm hp h heven
    | rors => exact certPoint_rors_paired d m hc hi hm hp h heven
    | tst => exact certPoint_tst_paired d m hc hi hm hp h heven
    | rsbs => exact certPoint_rsbs_paired d m hc hi hm hp h heven
    | cmp => exact certPoint_cmpReg_paired d m hc hi hm hp h heven
    | mvns => exact certPoint_mvns_paired d m hc hi hm hp h heven
  | _ => simp [registerInstruction] at hr

/-- Memory instructions handled by the general single-step proof. -/
def memoryInstruction : Instr → Bool
  | .memImm .. | .memReg .. | .strSp .. | .push .. | .stm .. | .ldrLit .. => true
  | _ => false

/-- Separation obligations for stores with an untracked buffer address. -/
def BufferStoreOk (env : Env) (p : Params) (bytes : List (BitVec 8))
    (st : AbsState) (s : State) : Instr → Prop
  | .memImm op _ n k => ((st.get n.val).addK (k.toNat * op.width)).isSp = false →
      op.isLoad = false →
      M0Crypto.Release.Frame.Disj p.base bytes.length (s.reg n + BitVec.ofNat 32 (k.toNat * op.width)) op.width ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s.reg n + BitVec.ofNat 32 (k.toNat * op.width)) op.width
  | .memReg op _ n m => ((st.get n.val).add (st.get m.val)).isSp = false →
      op.isLoad = false →
      M0Crypto.Release.Frame.Disj p.base bytes.length (s.reg n + s.reg m) op.width ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s.reg n + s.reg m) op.width
  | .stm n l => (∀ lo hi, st.get n.val ≠ .sp lo hi) →
      M0Crypto.Release.Frame.Disj p.base bytes.length (s.reg n) (4 * bitCount l) ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s.reg n) (4 * bitCount l)
  | _ => True

/-- Checked memory instructions preserve paired execution under their concrete
separation and code-alignment obligations. -/
theorem certPoint_memory_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (i : Instr)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : BufferStoreOk env p bytes st s₁ i)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hmemory : memoryInstruction i = true) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  cases i with
  | memImm op t n k => exact certPoint_memImm_paired op t n k hc hi hslots hm hp h hwidth hdisj hbuffer heven
  | memReg op t n m => exact certPoint_memReg_paired op t n m hc hi hslots hm hp h hwidth hdisj hbuffer heven
  | strSp t k => exact certPoint_strSp_paired t k hc hi hslots hm hp h hwidth hdisj heven
  | push l lr => exact certPoint_push_paired l lr hc hi hslots hm hp h hwidth hdisj heven
  | stm n l => exact certPoint_stm_paired n l hc hi hslots hm hp h hwidth hdisj hbuffer heven
  | ldrLit t k => exact certPoint_ldrLit_paired t k hc hi hm hp h hsize hbase hnowrap heven
  | _ => simp [memoryInstruction] at hmemory

/-- At a checked position, the remaining forms are control-flow instructions. -/
def controlInstruction : Instr → Bool
  | .bcond .. | .b .. | .bl .. | .pop .. => true
  | _ => false

theorem instruction_coverage (i : Instr) :
    registerInstruction i || memoryInstruction i || controlInstruction i = true := by
  cases i <;> rfl

/-- All non-control instructions preserve paired certificate execution under
the shared memory and artifact assumptions. -/
theorem certPoint_noncontrol_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (i : Instr)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : BufferStoreOk env p bytes st s₁ i)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hnoncontrol : controlInstruction i = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  have hall := instruction_coverage i
  simp only [hnoncontrol, Bool.false_eq_true, decide_false, Bool.or_false] at hall
  cases hr : registerInstruction i with
  | true => exact certPoint_register_paired i hc hi hm hp h hr heven
  | false =>
    have hm' : memoryInstruction i = true := by simpa [hr] using hall
    exact certPoint_memory_paired i hc hi hslots hm hp h hwidth hdisj hbuffer hsize hbase hnowrap heven hm'

/-- Final direct branches, calls and internal returns preserve the certificate
relation; an outer return advances both runs to their common stop address. -/
theorem certPoint_final_control_paired {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {p : Params} {s₁ s₂ : State} (i : Instr)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st [i]) (h : LowEq p bytes off st s₁ s₂)
    (hlr : p.lr0.getLsbD 0 = true)
    (hform : (∃ imm, i = .b imm) ∨ (∃ imm, i = .bl imm) ∨ (∃ l, i = .pop l true)) :
    PairedStep (RunRel env cert p bytes (p.lr0 &&& ~~~1#32)) s₁ s₂ := by
  have heven := certPoint_pc_even p.base hbase ha hm hp
  rcases hform with ⟨imm, rfl⟩ | ⟨imm, rfl⟩ | ⟨l, rfl⟩
  · exact (certPoint_branch_paired imm hc hi hm hp h heven).toRunRel
  · exact (certPoint_call_paired imm hc hi hm hp h heven).toRunRel
  · cases hctx : b.ctx with
    | none => exact certPoint_pop_exit_paired l hc hm hp hctx h hlr heven
    | some ret =>
      exact (certPoint_pop_return_aligned_paired l hc hi ha hbase hm hp hctx h).toRunRel

/-- A direct branch within a checked block is valid only when its analyzed
target is the next instruction; the concrete branch then follows that target. -/
theorem certPoint_branch_nonfinal_paired {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {j : Instr} {is : List Instr} {p : Params} {s₁ s₂ : State} (imm : BitVec 11)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.b imm :: j :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  obtain ⟨next, hsingle⟩ := certPoint_nonfinal_successor hc hm hp hx
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  obtain ⟨target, t₁, t₂, e, hs₁, hs₂, _, hmem, hnext⟩ :=
    branch_checked_step imm hx hidx h heven hdecode hlen
  rw [hsingle] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq, Tgt.pt.injEq] at hmem
  obtain ⟨⟨htarget, _⟩, hstate⟩ := hmem
  subst target
  subst next
  exact certAt_paired_step hc hi hm (BlockPoint.next hp hx hsingle) hnext hs₁ hs₂

/-- A call cannot be followed by another instruction in the same checked
block, since a successful call changes the certificate context. -/
theorem certPoint_call_final {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {is : List Instr} (imm : BitVec 25)
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.bl imm :: is)) : is = [] := by
  cases is with
  | nil => rfl
  | cons j js =>
    obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
    obtain ⟨next, hs⟩ := certPoint_nonfinal_successor hc hm hp hx
    have hb := xfer_sp_bounds hx
    have hw : env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers, hb.1, hb.2.2]
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    cases hctx : b.ctx with
    | some r => simp [hctx] at hx
    | none =>
      simp only [hctx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hx
      cases ht : relTarget off (blDisp imm) with
      | none => simp [ht] at hx
      | some target =>
        simp only [ht, Except.ok.injEq] at hx
        subst out
        simp [hctx] at hs

/-- A PC-restoring pop leaves the current certificate context and therefore
cannot be followed by another instruction in that checked block. -/
theorem certPoint_return_final {env : Env} {bytes : List (BitVec 8)}
    {entry : Nat} {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {is : List Instr} (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.pop l true :: is)) : is = [] := by
  cases is with
  | nil => rfl
  | cons j js =>
    obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
    obtain ⟨next, hs⟩ := certPoint_nonfinal_successor hc hm hp hx
    have hb := xfer_sp_bounds hx
    have hw : env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers, hb.1, hb.2.2]
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    split at hx
    · contradiction
    · cases hctx : b.ctx with
      | none =>
        cases hv : stkGet st.stk (st.spOff + (4 * (regsOf l).length : Nat)) <;>
          simp_all
        subst out
        simp at hs
      | some ret =>
        cases hv : stkGet st.stk (st.spOff + (4 * (regsOf l).length : Nat)) <;>
          simp_all <;> split at hx <;> simp_all
        subst out
        simp at hs

/-- A checked instruction advances the paired run under the local buffer and
declassification obligations. -/
theorem certPoint_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (i : Instr)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : BufferStoreOk env p bytes st s₁ i)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hdecision : ∀ cond imm, i = .bcond cond imm → env.declass = some off →
      condPassed cond s₁ = condPassed cond s₂) :
    PairedStep (RunRel env cert p bytes (p.lr0 &&& ~~~1#32)) s₁ s₂ := by
  have hbase2 : p.base.toNat % 2 = 0 := by omega
  have heven := certPoint_pc_even p.base hbase2 ha hm hp
  by_cases hn : controlInstruction i = false
  · exact (certPoint_noncontrol_paired i hc hi hslots hm hp h hwidth hdisj hbuffer
      hsize hbase hnowrap heven hn).toRunRel
  · cases i with
    | bcond cond imm =>
      exact (certPoint_bcond_aligned_paired cond imm hc hi ha hbase2 hm hp h
        (hdecision cond imm rfl)).toRunRel
    | pop l pc =>
      cases pc with
      | false => exact (certPoint_pop_paired l hc hi hm hp h heven).toRunRel
      | true =>
        have hs := certPoint_return_final l hc hm hp
        subst is
        exact certPoint_final_control_paired (.pop l true) hc hi ha hbase2 hm hp h hlr (by simp)
    | b imm =>
      cases is with
      | nil => exact (certPoint_branch_paired imm hc hi hm hp h heven).toRunRel
      | cons j js => exact (certPoint_branch_nonfinal_paired imm hc hi hm hp h heven).toRunRel
    | bl imm =>
      have hs := certPoint_call_final imm hc hm hp
      subst is
      exact (certPoint_call_paired imm hc hi hm hp h heven).toRunRel
    | _ => simp [controlInstruction] at hn

/-- Local obligations required at all certificate positions of a paired run. -/
def PositionObligations (env : Env) (cert : Cert) (p : Params) (bytes : List (BitVec 8))
    (s₁ s₂ : State) : Prop :=
  ∀ b off st i is, b ∈ cert → BlockPoint env b off st (i :: is) →
    LowEq p bytes off st s₁ s₂ → BufferStoreOk env p bytes st s₁ i ∧
      (∀ cond imm, i = .bcond cond imm → env.declass = some off →
        condPassed cond s₁ = condPassed cond s₂)

/-- The certificate relation takes a matching run step whenever the local
buffer and disclosed-decision obligations hold at the current position. -/
theorem certAt_run_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (h : CertAt env cert p bytes s₁ s₂) (hlocal : PositionObligations env cert p bytes s₁ s₂) :
    PairedStep (RunRel env cert p bytes (p.lr0 &&& ~~~1#32)) s₁ s₂ := by
  obtain ⟨b, off, st, code, hm, hp, hne, hrel⟩ := h
  cases code with
  | nil => contradiction
  | cons i is =>
    have ⟨hbuffer, hdecision⟩ := hlocal b off st i is hm hp hrel
    exact certPoint_paired i hc hi ha hslots hm hp hrel hwidth hdisj hbuffer
      hsize hbase hnowrap hlr hdecision

/-- If the site obligations hold at all reachable certificate states, paired
executions produce equal traces up to their shared return address. -/
theorem certificate_trace_eq {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (fuel : Nat) (h : CertAt env cert p bytes s₁ s₂) :
    (runUntil (p.lr0 &&& ~~~1#32) fuel s₁).map Prod.snd =
      (runUntil (p.lr0 &&& ~~~1#32) fuel s₂).map Prod.snd := by
  apply runRel_trace_eq (fuel := fuel) (h := Or.inl h)
  intro u₁ u₂ hrel hstop
  rcases hrel with hcert | ⟨hret, _⟩
  · exact certAt_run_paired hc hi ha hslots hwidth hdisj hsize hbase hnowrap hlr hcert (hlocal _ _ hcert)
  · contradiction

/-- States reachable by successful machine steps before the chosen stop PC. -/
inductive BeforeStop (stop : M0Crypto.Armv6M.Word) (initial : State) : State → Prop
  | initial : BeforeStop stop initial initial
  | next {s t : State} {event : Event} : BeforeStop stop initial s → s.pc ≠ stop →
      step s = .ok (t, event) → BeforeStop stop initial t

/-- Every state in a successful recorded execution is reachable before stop. -/
theorem runStates_beforeStop {stop : M0Crypto.Armv6M.Word} {initial : State}
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates stop fuel initial = .ok (states, events)) :
    ∀ s ∈ states, BeforeStop stop initial s := by
  apply runStates_invariant (BeforeStop stop initial) stop
  · intro s t e hs hstop hstep
    exact BeforeStop.next hs hstop hstep
  · exact BeforeStop.initial
  · exact hrun

/-- A successful recorded run contains the successor of each visited state
that has not reached the stop address. -/
theorem runStates_member_next {stop : M0Crypto.Armv6M.Word} {initial : State}
    {fuel : Nat} {states : List State} {events : List Event} {s t : State} {e : Event}
    (hrun : M0Crypto.Release.runStates stop fuel initial = .ok (states, events))
    (hmem : s ∈ states) (hstop : s.pc ≠ stop) (hstep : step s = .ok (t, e)) :
    t ∈ states := by
  induction fuel generalizing initial states events with
  | zero =>
    unfold M0Crypto.Release.runStates at hrun
    split at hrun
    · cases hrun
      simp at hmem
      subst s
      contradiction
    · contradiction
  | succ fuel ih =>
    unfold M0Crypto.Release.runStates at hrun
    split at hrun
    · cases hrun
      simp at hmem
      subst s
      contradiction
    · cases hs : step initial with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : M0Crypto.Release.runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          simp only [List.mem_cons] at hmem ⊢
          rcases hmem with rfl | hm
          · have heq := hstep.symm.trans hs
            cases heq
            exact Or.inr (by
              have hh := (M0Crypto.Release.runStates_nonempty ht).2
              cases rest <;> simp_all)
          · exact Or.inr (ih ht hm)

/-- Every visited non-final state in a successful recorded run has its
corresponding successful step and event in that run's trace. -/
theorem runStates_member_event {stop : M0Crypto.Armv6M.Word} {initial : State}
    {fuel : Nat} {states : List State} {events : List Event} {s : State}
    (hrun : M0Crypto.Release.runStates stop fuel initial = .ok (states, events))
    (hmem : s ∈ states) (hstop : s.pc ≠ stop) :
    ∃ t e, step s = .ok (t, e) ∧ e ∈ events := by
  induction fuel generalizing initial states events with
  | zero =>
    unfold M0Crypto.Release.runStates at hrun
    split at hrun
    · cases hrun
      simp at hmem
      subst s
      contradiction
    · contradiction
  | succ fuel ih =>
    unfold M0Crypto.Release.runStates at hrun
    split at hrun
    · cases hrun
      simp at hmem
      subst s
      contradiction
    · cases hs : step initial with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : M0Crypto.Release.runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hm
          · exact ⟨next, ev, hs, by simp⟩
          · obtain ⟨t, e, he, hm'⟩ := ih ht hm
            exact ⟨t, e, he, by simp [hm']⟩

/-- At a checked position in a successful recorded run, the concrete event
for that instruction occurs in the recorded trace. -/
theorem certPoint_recorded_event {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {initial s s₂ : State} {fuel : Nat} {states : List State} {events : List Event}
    (i : Instr) (hc : certOk env bytes entry init cert = true)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (h : LowEq p bytes off st s s₂) (hmem : s ∈ states)
    (hstop : s.pc ≠ (p.lr0 &&& ~~~1#32))
    (hrun : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel initial = .ok (states, events)) :
    ⟨s.pc, i, i.accesses s⟩ ∈ events := by
  obtain ⟨t, e, hstep, hevent⟩ := runStates_member_event hrun hmem hstop
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hd := decode_at h.code₁ off i hdecode hlen
  have heven := certPoint_pc_even p.base hbase ha hm hp
  have hpc := h.pc
  unfold step at hstep
  simp only [hpc] at hstep
  rw [heven, hd] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · cases hex : i.exec s <;> simp_all
  · simp at hstep

/-- Whole-run write bounds apply to each byte of a checked immediate store. -/
theorem certPoint_memImm_recorded_writes {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {initial s s₂ : State} {fuel : Nat} {states : List State} {events : List Event}
    {Wr : M0Crypto.Armv6M.Word → Prop} (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hc : certOk env bytes entry init cert = true) (ha : certAligned cert = true)
    (hbase : p.base.toNat % 2 = 0) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memImm op t n imm :: is))
    (h : LowEq p bytes off st s s₂) (hmem : s ∈ states)
    (hstop : s.pc ≠ (p.lr0 &&& ~~~1#32))
    (hrun : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel initial = .ok (states, events))
    (hop : op.isLoad = false) (hw : M0Crypto.Release.WritesTo Wr events) :
    ∀ k, k < op.width → Wr (s.reg n + BitVec.ofNat 32 (imm.toNat * op.width) + BitVec.ofNat 32 k) := by
  have he := certPoint_recorded_event (.memImm op t n imm) hc ha hbase hm hp h hmem hstop hrun
  exact memImm_trace_write_bounds op t n imm s hop hw he rfl

/-- Whole-run write bounds apply to each byte of a checked register-offset store. -/
theorem certPoint_memReg_recorded_writes {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {initial s s₂ : State} {fuel : Nat} {states : List State} {events : List Event}
    {Wr : M0Crypto.Armv6M.Word → Prop} (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hc : certOk env bytes entry init cert = true) (ha : certAligned cert = true)
    (hbase : p.base.toNat % 2 = 0) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memReg op t n m :: is))
    (h : LowEq p bytes off st s s₂) (hmem : s ∈ states)
    (hstop : s.pc ≠ (p.lr0 &&& ~~~1#32))
    (hrun : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel initial = .ok (states, events))
    (hop : op.isLoad = false) (hw : M0Crypto.Release.WritesTo Wr events) :
    ∀ k, k < op.width → Wr (s.reg n + s.reg m + BitVec.ofNat 32 k) := by
  have he := certPoint_recorded_event (.memReg op t n m) hc ha hbase hm hp h hmem hstop hrun
  exact memReg_trace_write_bounds op t n m s hop hw he rfl

/-- Any state reachable before stop occurs in every successful recorded run
from the same initial state. -/
theorem BeforeStop.mem_runStates {stop : M0Crypto.Armv6M.Word} {initial s : State}
    (hreach : BeforeStop stop initial s) {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates stop fuel initial = .ok (states, events)) : s ∈ states := by
  induction hreach with
  | initial =>
    have hh := (M0Crypto.Release.runStates_nonempty hrun).2
    cases states <;> simp_all
  | next hreach hstop hstep ih => exact runStates_member_next hrun ih hstop hstep

/-- The certificate trace theorem with obligations restricted to pairs of
states actually reachable from the two specified initial states. -/
theorem certificate_reachable_trace_eq {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s₂ u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (fuel : Nat) (h : CertAt env cert p bytes s₁ s₂) :
    (runUntil (p.lr0 &&& ~~~1#32) fuel s₁).map Prod.snd =
      (runUntil (p.lr0 &&& ~~~1#32) fuel s₂).map Prod.snd := by
  let stop := p.lr0 &&& ~~~1#32
  let R : State → State → Prop := fun u₁ u₂ =>
    RunRel env cert p bytes stop u₁ u₂ ∧ BeforeStop stop s₁ u₁ ∧ BeforeStop stop s₂ u₂
  apply runUntil_trace_eq R stop
  · intro u₁ u₂ hr
    exact hr.1.pc_eq
  · intro u₁ u₂ hr hstop
    obtain ⟨hrel, hr₁, hr₂⟩ := hr
    have hs : PairedStep (RunRel env cert p bytes stop) u₁ u₂ := by
      rcases hrel with hcert | ⟨hret, _⟩
      · exact certAt_run_paired hc hi ha hslots hwidth hdisj hsize hbase hnowrap hlr hcert
          (hlocal u₁ u₂ hr₁ hr₂ hcert)
      · contradiction
    unfold PairedStep at hs ⊢
    cases h₁ : step u₁ with
    | error e₁ => cases h₂ : step u₂ <;> simp_all
    | ok a =>
      rcases a with ⟨t₁, e₁⟩
      cases h₂ : step u₂ with
      | error e₂ => simp_all
      | ok b =>
        rcases b with ⟨t₂, e₂⟩
        simp only [h₁, h₂] at hs ⊢
        obtain ⟨he, hn⟩ := hs
        refine ⟨he, hn, BeforeStop.next hr₁ hstop h₁, ?_⟩
        have hstop₂ : u₂.pc ≠ stop := by rw [← hrel.pc_eq]; exact hstop
        exact BeforeStop.next hr₂ hstop₂ h₂
  · exact ⟨Or.inl h, BeforeStop.initial, BeforeStop.initial⟩

/-- For two successful recorded executions, it is enough to establish site
obligations for pairs of states occurring in those executions. -/
theorem certificate_recorded_trace_eq {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    {fuel : Nat} {states₁ states₂ : List State} {events₁ events₂ : List Event}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hrun₁ : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel s₁ = .ok (states₁, events₁))
    (hrun₂ : M0Crypto.Release.runStates (p.lr0 &&& ~~~1#32) fuel s₂ = .ok (states₂, events₂))
    (hlocal : ∀ u₁ ∈ states₁, ∀ u₂ ∈ states₂, CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s₁ s₂) : events₁ = events₂ := by
  have ht := certificate_reachable_trace_eq hc hi ha hslots hwidth hdisj hsize hbase hnowrap hlr
    (fun u₁ u₂ hr₁ hr₂ hcert => hlocal u₁ (hr₁.mem_runStates hrun₁)
      u₂ (hr₂.mem_runStates hrun₂) hcert) fuel h
  have h₁ := M0Crypto.Release.runStates_events (p.lr0 &&& ~~~1#32) fuel s₁
  have h₂ := M0Crypto.Release.runStates_events (p.lr0 &&& ~~~1#32) fuel s₂
  rw [hrun₁] at h₁
  rw [hrun₂] at h₂
  change Except.ok events₁ = (runUntil (p.lr0 &&& ~~~1#32) fuel s₁).map Prod.snd at h₁
  change Except.ok events₂ = (runUntil (p.lr0 &&& ~~~1#32) fuel s₂).map Prod.snd at h₂
  rw [← h₁, ← h₂] at ht
  exact Except.ok.inj ht

end M0Crypto.Release.ConstantTime
