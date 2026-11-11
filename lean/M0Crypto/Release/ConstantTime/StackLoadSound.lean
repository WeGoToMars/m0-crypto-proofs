import M0Crypto.Release.ConstantTime.MovSound

/-! Paired execution of SP-relative loads. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg read32)
open M0Crypto.Thumb

/-- The two executions use the stack slot selected by an SP-relative immediate. -/
theorem stack_load_address {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (imm : BitVec 8)
    (h : LowEq p bytes off st s₁ s₂) :
    s₁.sp + BitVec.ofNat 32 (imm.toNat * 4) =
        p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)) ∧
    s₂.sp + BitVec.ofNat 32 (imm.toNat * 4) =
        p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)) := by
  have haddr : p.sp0 + BitVec.ofInt 32 st.spOff + BitVec.ofNat 32 (imm.toNat * 4) =
      p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  constructor
  · simpa [State.sp, h.sp] using haddr
  · simpa [State.sp, h.sp_eq, h.sp] using haddr

/-- An SP-relative word load preserves the state relation, independently of the
loaded value's secrecy. Alignment is handled by the machine-step layer. -/
theorem ldrSp_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (t : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.ldrSp t imm).exec s₁ = .ok t₁ ∧
      (Instr.ldrSp t imm).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.ldrSp t imm).size)
        (st.set t.val (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat)))) t₁ t₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have ⟨ha₁, ha₂⟩ := stack_load_address imm h
  have hload : AbsVal.Sem p (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat)))
      (read32 s₁.mem (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4)))
      (read32 s₂.mem (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4))) := by
    simpa only [ha₁, ha₂] using h.stack (st.spOff + (imm.toNat * 4 : Nat))
  have hnext := h.withPC hidx (next := off + (Instr.ldrSp t imm).size)
  have hw := paired_setReg_sound ht hidx hnext hload
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  refine ⟨_, _, ?_, ?_, hw⟩
  · simp [Instr.exec, hpc₁, ofNat_add_assoc]
  · simp [Instr.exec, hpc₂, ofNat_add_assoc]

/-- Checked SP loads take the same step, including a matching unaligned fault. -/
theorem ldrSp_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (t : LowReg) (imm : BitVec 8)
    (hx : xfer env off ctx (.ldrSp t imm) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.ldrSp t imm))
    (hlen : off + (Instr.ldrSp t imm).size ≤ bytes.length) :
    (∃ fault, step s₁ = .error fault ∧ step s₂ = .error fault) ∨
    ∃ t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      out.sites = [] ∧
      ((.pt (off + (Instr.ldrSp t imm).size) ctx,
        st.set t.val (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat)))) ∈ out.succs) ∧
      LowEq p bytes (off + (Instr.ldrSp t imm).size)
        (st.set t.val (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat)))) t₁ t₂ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hsps : s₁.sp = s₂.sp := by simpa [State.sp] using h.sp_eq.symm
  have hacc : (Instr.ldrSp t imm).accesses s₁ = (Instr.ldrSp t imm).accesses s₂ := by
    simp [Instr.accesses, hsps]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.ldrSp t imm).accesses s₁).all Access.aligned = true
  · right
    have hal₂ : ((Instr.ldrSp t imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨t₁, t₂, he₁, he₂, hrel⟩ := ldrSp_sound t imm hidx h
    have hs₁ := step_of_instrAt hc₁ off (.ldrSp t imm) hpc₁ heven hi hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.ldrSp t imm) hpc₂ heven hi hlen hal₂ he₂
    have hout : out = ⟨[(.pt (off + (Instr.ldrSp t imm).size) ctx,
        st.set t.val (stkGet st.stk (st.spOff + (imm.toNat * 4 : Nat))))], []⟩ := by
      simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
        xferCore] at hx
      split at hx <;> simp_all [fall]
    subst out
    refine ⟨t₁, t₂, ⟨s₁.pc, .ldrSp t imm, (Instr.ldrSp t imm).accesses s₁⟩,
      hs₁, ?_, rfl, by simp, hrel⟩
    simpa [h.pc_eq, hacc] using hs₂
  · left
    have hd₁ := decode_at hc₁ off (.ldrSp t imm) hi hlen
    have hd₂ := decode_at hc₂ off (.ldrSp t imm) hi hlen
    have hal₂ : ((Instr.ldrSp t imm).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    refine ⟨.unaligned s₁.pc, ?_, ?_⟩
    · simp [step, hpc₁, heven', hd₁, hal]
    · simp [step, hpc₁, hpc₂, heven', hd₂, hal₂]

end M0Crypto.Release.ConstantTime
