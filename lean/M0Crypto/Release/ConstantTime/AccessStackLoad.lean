import M0Crypto.Release.ConstantTime.AccessStackCode

/-! Paired loads through checked stack-relative addresses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem State LowReg read32)
open M0Crypto.Thumb

/-- Concrete value loaded by a load operation. -/
def loadMem (op : MemOp) (m : Mem) (a : Word) : Word :=
  match op with
  | .ldr => read32 m a
  | .ldrh => read16 m a
  | .ldrb => read8 m a
  | _ => 0

/-- A checked stack load's abstract value describes both concrete loads. -/
theorem stkLoad_sem {p : Params} {st : AbsState} {x y : Int} {a₁ a₂ : Word}
    {m₁ m₂ : Mem} (op : MemOp) (hop : op.isLoad = true)
    (ha : AbsVal.Sem p (.sp x y) a₁ a₂) (hs : StkSem p st.stk m₁ m₂) :
    AbsVal.Sem p (stkLoad st x y op.width) (loadMem op m₁ a₁) (loadMem op m₂ a₂) := by
  obtain ⟨o, hxo, hoy, he₁, he₂⟩ := ha
  subst a₂
  subst a₁
  cases op with
  | ldr =>
    simp only [stkLoad, MemOp.width, beq_self_eq_true, Bool.and_true]
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      have hox : o = x := by omega
      subst o
      exact hs x
    · trivial
  | ldrh => simp [stkLoad, MemOp.width, loadMem, AbsVal.Sem]
  | ldrb => simp [stkLoad, MemOp.width, loadMem, AbsVal.Sem]
  | str | strh | strb => simp [MemOp.isLoad] at hop

/-- Immediate-offset stack loads preserve the paired state relation. -/
theorem memImm_stack_load_sound {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State} {x y : Int}
    (op : MemOp) (t n : LowReg) (imm : BitVec 5) (hop : op.isLoad = true)
    (ha : (st.get n.val).addK (imm.toNat * op.width) = .sp x y)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.memImm op t n imm).exec s₁ = .ok u₁ ∧
      (Instr.memImm op t n imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memImm op t n imm).size)
        (st.set t.val (stkLoad st x y op.width)) u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have haddr := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
  rw [ha] at haddr
  have hv := stkLoad_sem op hop haddr h.stack
  have hw := paired_setReg_sound ht hidx (h.withPC hidx (next := off + (Instr.memImm op t n imm).size)) hv
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc, ofNat_add_assoc]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Register-offset stack loads preserve the paired state relation. -/
theorem memReg_stack_load_sound {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State} {x y : Int}
    (op : MemOp) (t n m : LowReg) (hop : op.isLoad = true)
    (ha : (st.get n.val).add (st.get m.val) = .sp x y)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.memReg op t n m).exec s₁ = .ok u₁ ∧
      (Instr.memReg op t n m).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memReg op t n m).size)
        (st.set t.val (stkLoad st x y op.width)) u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have haddr := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
  rw [ha] at haddr
  have hv := stkLoad_sem op hop haddr h.stack
  have hw := paired_setReg_sound ht hidx (h.withPC hidx (next := off + (Instr.memReg op t n m).size)) hv
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc, ofNat_add_assoc]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- An immediate-offset load classified as a stack access advances paired
certificate executions or produces matching alignment faults. -/
theorem certPoint_memImm_stack_load_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hop : op.isLoad = true)
    (ha : (st.get n.val).addK (imm.toNat * op.width) = .sp x y)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memImm op t n imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hcover : env.win.covers x (y + op.width) = true := by
    cases hcover' : env.win.covers x (y + op.width) <;>
      simp_all [xfer, xferCore, access]
  have hout : out = ⟨[(.pt (off + 2) b.ctx,
      st.set t.val (stkLoad st x y op.width))], []⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, ha, access, hop, hcover] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memImm_accesses_eq op t n imm hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memImm op t n imm).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memImm_stack_load_sound op t n imm hop ha hidx hrel
    have hs₁ := step_of_instrAt hc₁ off (.memImm op t n imm) hrel.pc heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.memImm op t n imm) (hrel.pc_eq.trans hrel.pc)
      heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [hrel.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.memImm op t n imm) hdecode hlen
    have hd₂ := decode_at hc₂ off (.memImm op t n imm) hdecode hlen
    have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    apply certAt_paired_fault (fault := .unaligned s₁.pc)
    · simp [step, hrel.pc, heven', hd₁, hal]
    · simp [step, hrel.pc, hrel.pc_eq.trans hrel.pc, heven', hd₂, hal₂]

/-- A register-offset load classified as a stack access advances paired
certificate executions or produces matching alignment faults. -/
theorem certPoint_memReg_stack_load_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : M0Crypto.Armv6M.State} {x y : Int}
    (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hop : op.isLoad = true)
    (ha : (st.get n.val).add (st.get m.val) = .sp x y)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memReg op t n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hcover : env.win.covers x (y + op.width) = true := by
    cases hcover' : env.win.covers x (y + op.width) <;>
      simp_all [xfer, xferCore, access]
  have hout : out = ⟨[(.pt (off + 2) b.ctx,
      st.set t.val (stkLoad st x y op.width))], []⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, ha, access, hop, hcover] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memReg_accesses_eq op t n m hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memReg op t n m).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memReg_stack_load_sound op t n m hop ha hidx hrel
    have hs₁ := step_of_instrAt hc₁ off (.memReg op t n m) hrel.pc heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.memReg op t n m) (hrel.pc_eq.trans hrel.pc)
      heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [hrel.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.memReg op t n m) hdecode hlen
    have hd₂ := decode_at hc₂ off (.memReg op t n m) hdecode hlen
    have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    apply certAt_paired_fault (fault := .unaligned s₁.pc)
    · simp [step, hrel.pc, heven', hd₁, hal]
    · simp [step, hrel.pc, hrel.pc_eq.trans hrel.pc, heven', hd₂, hal₂]

end M0Crypto.Release.ConstantTime
