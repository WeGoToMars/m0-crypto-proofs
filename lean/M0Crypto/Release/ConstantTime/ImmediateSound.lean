import M0Crypto.Release.ConstantTime.HalfwordSound
import M0Crypto.Release.ConstantTime.ArithmeticSound

/-! Paired execution of immediate arithmetic. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg addWithCarry)
open M0Crypto.Thumb

private theorem addRes_no_cmp (a b v : AbsVal) (c : AbsFlags) : (addRes a b c v).2.cmp = none := by
  unfold addRes
  split <;> simp_all [AFl.all]
  split <;> simp_all

/-- Subtracting a small immediate preserves the result and flag relations. -/
theorem subImm3_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d n : LowReg) (imm : BitVec 3)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.subImm3 d n imm).exec s₁ = .ok u₁ ∧
      (Instr.subImm3 d n imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.subImm3 d n imm).size)
        { st.set d.val (addRes (st.get n.val) (notWord (.cst imm.toNat)) (.known true)
          ((st.get n.val).subK imm.toNat)).1 with
          fl := (addRes (st.get n.val) (notWord (.cst imm.toNat)) (.known true)
            ((st.get n.val).subK imm.toNat)).2 } u₁ u₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have ha := lowReg_sem n h
  have hc : AbsVal.Sem p (.cst imm.toNat) (imm.setWidth 32) (imm.setWidth 32) := by
    have hk : imm.toNat < 2^32 := by have := imm.isLt; omega
    simp [AbsVal.Sem, AbsVal.cst, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk]
  have hs := addRes_sound ha (notWord_sound hc) (show AbsFlags.Sem (.known true) true true from by simp [AbsFlags.Sem])
    (by simpa [M0Crypto.Release.sub_flags, BitVec.setWidth_eq] using AbsVal.subK_sound imm.toNat ha)
  have hw := paired_setReg_sound hd hidx (h.withPC hidx (next := off + (Instr.subImm3 d n imm).size)) hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.subImm3 d n imm).size)))
      d.toReg (s₁.reg n) (~~~(imm.setWidth 32)) true,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.subImm3 d n imm).size)))
      d.toReg (s₂.reg n) (~~~(imm.setWidth 32)) true, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, State.setNZCV, State.setNZ, State.reg, LowReg.toReg] using hs.2
    · intro c hc'
      have hn := addRes_no_cmp (st.get n.val) (notWord (.cst imm.toNat))
        ((st.get n.val).subK imm.toNat) (.known true)
      simp_all

/-- Checked small-immediate subtraction advances paired certificate executions. -/
theorem certPoint_subImm3_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d n : LowReg) (imm : BitVec 3)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.subImm3 d n imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.subImm3 d n imm).size) b.ctx,
      { st.set d.val (addRes (st.get n.val) (notWord (.cst imm.toNat)) (.known true)
          ((st.get n.val).subK imm.toNat)).1 with
        fl := (addRes (st.get n.val) (notWord (.cst imm.toNat)) (.known true)
          ((st.get n.val).subK imm.toNat)).2 })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := subImm3_sound d n imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.subImm3 d n imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.subImm3 d n imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
