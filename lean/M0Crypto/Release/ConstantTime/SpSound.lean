import M0Crypto.Release.ConstantTime.PcSound
import M0Crypto.Release.ConstantTime.Reach

/-! Preservation of the relational state across stack-pointer updates. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State)

theorem cmp_uses_sp_false {c : Cmp} (hc : cmpIndexOk c) : c.uses 13 = false := by
  have ha := hc.1.2
  cases hb : c.b with
  | imm n => simp [Cmp.uses, ha, hb]
  | reg r =>
    have hr : regIndexOk r := by simpa [opndIndexOk, hb] using hc.2
    simp [Cmp.uses, ha, hb, hr.2]

/-- Replacing both stack pointers with the address represented by `next`
preserves all relational records, which cannot refer to SP. -/
theorem LowEq.withSP {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (h : LowEq p bytes off st s₁ s₂)
    (hidx : st.indicesOk) (next : Int) :
    LowEq p bytes off { st with spOff := next }
      (s₁.setReg 13 (p.sp0 + BitVec.ofInt 32 next))
      (s₂.setReg 13 (p.sp0 + BitVec.ofInt 32 next)) := by
  rcases h with ⟨hpc₁, hpc₂, _, _, hregs, hflags, hcmp,
    hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsize, ?_, ?_⟩
  · simpa [State.pc, State.setReg] using hpc₁
  · simpa [State.pc, State.setReg] using hpc₂
  · simp [State.setReg]
  · simp [State.setReg]
  · intro i hi hi13
    have hi16 : i < 16 := by simp [numRegs] at hi; omega
    change AbsVal.Sem p (st.get i)
      (regAt (s₁.setReg ⟨13, by decide⟩ (p.sp0 + BitVec.ofInt 32 next)) i)
      (regAt (s₂.setReg ⟨13, by decide⟩ (p.sp0 + BitVec.ofInt 32 next)) i)
    rw [regAt_setReg_ne s₁ 13 i (by decide) hi16 hi13,
      regAt_setReg_ne s₂ 13 i (by decide) hi16 hi13]
    exact hregs i hi hi13
  · exact hflags
  · intro c hc
    have hwf := hidx.1 c hc
    have hu := cmp_uses_sp_false hwf
    have h := hcmp c hc
    exact ⟨(cmpSem_setReg (by decide) _ hwf hu).mpr h.1,
      (cmpSem_setReg (by decide) _ hwf hu).mpr h.2⟩
  · exact hstk
  · intro f hf
    have hfi := hidx.2.1 f hf
    have h := hrel f hf
    exact ⟨(factSem_setReg (by decide) _ hfi hfi.1.2 hfi.2.2).mpr h.1,
      (factSem_setReg (by decide) _ hfi hfi.1.2 hfi.2.2).mpr h.2⟩
  · intro l hl
    have hli := hidx.2.2 l hl
    have h := hlnk l hl
    exact ⟨(lnkSem_setReg (by decide) _ hli hli.1.2 hli.2.2).mpr h.1,
      (lnkSem_setReg (by decide) _ hli hli.1.2 hli.2.2).mpr h.2⟩
  · exact hcode₁
  · exact hcode₂

/-- Checked SP arithmetic advances both executions and the block position. -/
theorem certPoint_addSp_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List M0Crypto.Thumb.Instr}
    {p : Params} {s₁ s₂ : State} (imm : BitVec 7)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.addSp imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let i := M0Crypto.Thumb.Instr.addSp imm
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + i.size) b.ctx,
      { st with spOff := st.spOff + (imm.toNat * 4 : Nat) })], []⟩ := by
    simpa [i, xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  have hpc := h.withPC hidx (next := off + i.size)
  have hnext := hpc.withSP hidx (st.spOff + (imm.toNat * 4 : Nat))
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have haddr : p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)) =
      (p.sp0 + BitVec.ofInt 32 st.spOff) + BitVec.ofNat 32 (imm.toNat * 4) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp [Int.natCast_mul, BitVec.add_assoc] at haddr
  have he₁ : i.exec s₁ = .ok ((s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + i.size))).setReg 13
      (p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)))) := by
    simp [i, M0Crypto.Thumb.Instr.exec, h.pc, hsp₁, haddr, BitVec.ofNat_add, BitVec.add_assoc]
  have he₂ : i.exec s₂ = .ok ((s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + i.size))).setReg 13
      (p.sp0 + BitVec.ofInt 32 (st.spOff + (imm.toNat * 4 : Nat)))) := by
    simp [i, M0Crypto.Thumb.Instr.exec, h.pc_eq, h.pc, hsp₂, haddr, BitVec.ofNat_add, BitVec.add_assoc]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := M0Crypto.Thumb.step_of_instrAt hc₁ off i h.pc heven hdecode hlen
    (by simp [i, M0Crypto.Thumb.Instr.accesses]) he₁
  have hs₂ := M0Crypto.Thumb.step_of_instrAt hc₂ off i (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [i, M0Crypto.Thumb.Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [h.pc_eq, i, M0Crypto.Thumb.Instr.accesses] using hs₂


/-- Checked SP arithmetic advances both executions and the block position. -/
theorem certPoint_subSp_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List M0Crypto.Thumb.Instr}
    {p : Params} {s₁ s₂ : State} (imm : BitVec 7)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.subSp imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let i := M0Crypto.Thumb.Instr.subSp imm
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + i.size) b.ctx,
      { st with spOff := st.spOff - (imm.toNat * 4 : Nat) })], []⟩ := by
    simpa [i, xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  have hpc := h.withPC hidx (next := off + i.size)
  have hnext := hpc.withSP hidx (st.spOff - (imm.toNat * 4 : Nat))
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have haddr : p.sp0 + BitVec.ofInt 32 (st.spOff - (imm.toNat * 4 : Nat)) =
      (p.sp0 + BitVec.ofInt 32 st.spOff) - BitVec.ofNat 32 (imm.toNat * 4) := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]
  simp [Int.natCast_mul, BitVec.sub_eq_add_neg, BitVec.add_assoc] at haddr
  have he₁ : i.exec s₁ = .ok ((s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + i.size))).setReg 13
      (p.sp0 + BitVec.ofInt 32 (st.spOff - (imm.toNat * 4 : Nat)))) := by
    simp [i, M0Crypto.Thumb.Instr.exec, h.pc, hsp₁, haddr, BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have he₂ : i.exec s₂ = .ok ((s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + i.size))).setReg 13
      (p.sp0 + BitVec.ofInt 32 (st.spOff - (imm.toNat * 4 : Nat)))) := by
    simp [i, M0Crypto.Thumb.Instr.exec, h.pc_eq, h.pc, hsp₂, haddr, BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := M0Crypto.Thumb.step_of_instrAt hc₁ off i h.pc heven hdecode hlen
    (by simp [i, M0Crypto.Thumb.Instr.accesses]) he₁
  have hs₂ := M0Crypto.Thumb.step_of_instrAt hc₂ off i (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [i, M0Crypto.Thumb.Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [h.pc_eq, i, M0Crypto.Thumb.Instr.accesses] using hs₂

end M0Crypto.Release.ConstantTime
