import M0Crypto.Release.ConstantTime.AccessBuffer

/-! Paired buffer loads. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Mem State LowReg)
open M0Crypto.Thumb

/-- Immediate-offset buffer loads preserve the paired state relation. -/
theorem memImm_buffer_load_sound {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State}
    (op : MemOp) (t n : LowReg) (imm : BitVec 5) (hop : op.isLoad = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.memImm op t n imm).exec s₁ = .ok u₁ ∧
      (Instr.memImm op t n imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memImm op t n imm).size)
        (st.set t.val AbsVal.hi) u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have hv : AbsVal.Sem p AbsVal.hi (loadMem op s₁.mem (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)))
      (loadMem op s₂.mem (s₂.reg n + BitVec.ofNat 32 (imm.toNat * op.width))) := by trivial
  have hw := paired_setReg_sound ht hidx (h.withPC hidx (next := off + (Instr.memImm op t n imm).size)) hv
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc, ofNat_add_assoc]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Register-offset buffer loads preserve the paired state relation. -/
theorem memReg_buffer_load_sound {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State}
    (op : MemOp) (t n m : LowReg) (hop : op.isLoad = true)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.memReg op t n m).exec s₁ = .ok u₁ ∧
      (Instr.memReg op t n m).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.memReg op t n m).size)
        (st.set t.val AbsVal.hi) u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have hv : AbsVal.Sem p AbsVal.hi (loadMem op s₁.mem (s₁.reg n + s₁.reg m))
      (loadMem op s₂.mem (s₂.reg n + s₂.reg m)) := by trivial
  have hw := paired_setReg_sound ht hidx (h.withPC hidx (next := off + (Instr.memReg op t n m).size)) hv
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc, ofNat_add_assoc]
  · cases op <;> simp [MemOp.isLoad] at hop <;>
      simp [Instr.exec, Instr.exec.memOp, loadMem, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Public non-stack addresses use the buffer-load transfer. -/
theorem access_public_buffer_load (env : Env) (st : AbsState) (a : AbsVal) (w t : Nat)
    (hp : a.pub = true) (hn : a.isSp = false) :
    access env st a w true t = .ok (st.set t .hi, [.load]) := by
  cases a <;> simp_all [access, AbsVal.pub, AbsVal.isSp]

/-- A non-stack immediate load advances paired certificate executions when
its concrete write is disjoint from the code and tracked stack. -/
theorem certPoint_memImm_buffer_load_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n : LowReg) (imm : BitVec 5)
    (hop : op.isLoad = true)
    (hn : ((st.get n.val).addK (imm.toNat * op.width)).isSp = false)
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
  have hpub : ((st.get n.val).addK (imm.toNat * op.width)).pub = true := by
    cases ha : (st.get n.val).addK (imm.toNat * op.width) <;>
      simp_all [xfer, xferCore, access, AbsVal.pub]
  have haccess := access_public_buffer_load env st _ op.width t.val hpub hn
  have hout : out = ⟨[(.pt (off + 2) b.ctx, st.set t.val .hi)], [.load]⟩ := by
    simpa [xfer, xferCore, hw, hb.2.1, hop, haccess] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memImm_accesses_eq op t n imm hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memImm op t n imm).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memImm op t n imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memImm_buffer_load_sound op t n imm hop hidx hrel
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

/-- A non-stack register-offset load advances paired certificate executions when
its concrete write is disjoint from the code and tracked stack. -/
theorem certPoint_memReg_buffer_load_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n m : LowReg)
    (hop : op.isLoad = true)
    (hn : ((st.get n.val).add (st.get m.val)).isSp = false)
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
  have hpub : ((st.get n.val).add (st.get m.val)).pub = true := by
    cases ha : (st.get n.val).add (st.get m.val) <;>
      simp_all [xfer, xferCore, access, AbsVal.pub]
  have haccess := access_public_buffer_load env st _ op.width t.val hpub hn
  have hout : out = ⟨[(.pt (off + 2) b.ctx, st.set t.val .hi)], [.load]⟩ := by
    cases hna : st.get n.val <;> cases hma : st.get m.val <;>
      simp_all [xfer, xferCore, AbsVal.add, access, AbsVal.isSp, AbsVal.pub]
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc := memReg_accesses_eq op t n m hx hrel
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.memReg op t n m).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.memReg op t n m).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
      memReg_buffer_load_sound op t n m hop hidx hrel
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
