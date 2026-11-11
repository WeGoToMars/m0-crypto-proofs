import M0Crypto.Release.ConstantTime.LiteralSound

/-! Paired execution of stack-relative address formation. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg)
open M0Crypto.Thumb

/-- Forming a stack-relative address preserves the abstract state relation. -/
theorem addRdSp_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.addRdSp d imm).exec s₁ = .ok u₁ ∧
      (Instr.addRdSp d imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.addRdSp d imm).size)
        (st.set d.val (.sp (st.spOff + (imm.toNat * 4 : Nat))
          (st.spOff + (imm.toNat * 4 : Nat)))) u₁ u₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have ⟨ha₁, ha₂⟩ := stack_load_address imm h
  have hv : AbsVal.Sem p (.sp (st.spOff + (imm.toNat * 4 : Nat))
      (st.spOff + (imm.toNat * 4 : Nat)))
      (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4))
      (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4)) := by
    refine ⟨_, by omega, by omega, ha₁, ?_⟩
    rw [ha₁, ha₂]
  have hw := paired_setReg_sound hd hidx (h.withPC hidx (next := off + (Instr.addRdSp d imm).size)) hv
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked stack-relative address formation advances paired certificate executions. -/
theorem certPoint_addRdSp_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.addRdSp d imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.addRdSp d imm).size) b.ctx,
      st.set d.val (.sp (st.spOff + (imm.toNat * 4 : Nat))
        (st.spOff + (imm.toNat * 4 : Nat))))], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := addRdSp_sound d imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.addRdSp d imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.addRdSp d imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
