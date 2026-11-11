import M0Crypto.Release.ConstantTime.MemoryStep

/-! Paired execution of literal-pool loads. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg read32)
open M0Crypto.Thumb

/-- Words read within the same checked code bytes agree in both memories. -/
theorem codeAt_read32_eq {bytes : List (BitVec 8)} {p : Params} {m₁ m₂ : M0Crypto.Armv6M.Mem}
    (hc₁ : CodeAt m₁ p.base bytes) (hc₂ : CodeAt m₂ p.base bytes)
    (offset : Nat) (hbound : offset + 4 ≤ bytes.length) :
    read32 m₁ (p.base + BitVec.ofNat 32 offset) = read32 m₂ (p.base + BitVec.ofNat 32 offset) := by
  apply M0Crypto.Release.Frame.read32_congr
  intro k hk
  rw [ofNat_add_assoc, hc₁ (offset + k) (by omega), hc₂ (offset + k) (by omega)]

/-- A literal-pool load preserves the relational state when the code base is
word-aligned and the artifact does not wrap around the address space. -/
theorem ldrLit_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (t : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hbase : p.base.toNat % 4 = 0) (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32)
    (hbound : (off + 4) / 4 * 4 + imm.toNat * 4 + 4 ≤ bytes.length) :
    ∃ u₁ u₂, (Instr.ldrLit t imm).exec s₁ = .ok u₁ ∧
      (Instr.ldrLit t imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.ldrLit t imm).size) (st.set t.val .lo) u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  let lit := (off + 4) / 4 * 4 + imm.toNat * 4
  have hlinear : p.base.toNat + off + 4 + imm.toNat * 4 < 2 ^ 32 := by
    dsimp [lit] at *
    omega
  have ha := M0Crypto.Release.Frame.lit_addr p.base hbase off imm.toNat hlinear
  have hc₁ := h.code₁
  have hc₂ := h.code₂
  have hr := codeAt_read32_eq hc₁ hc₂ lit hbound
  have hv : AbsVal.Sem p .lo
      (read32 s₁.mem (((s₁.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4)))
      (read32 s₂.mem (((s₂.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4))) := by
    simp only [AbsVal.Sem, h.pc, h.pc_eq.trans h.pc, ha]
    exact hr
  have hw := paired_setReg_sound ht hidx (h.withPC hidx (next := off + (Instr.ldrLit t imm).size)) hv
  have hreg : (⟨t.val, by have := ht.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = t.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  refine ⟨_, _, ?_, ?_, hw⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- A checked literal load advances paired certificate executions or produces
a matching alignment fault. -/
theorem certPoint_ldrLit_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (t : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldrLit t imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hbound : (off + 4) / 4 * 4 + imm.toNat * 4 + 4 ≤ bytes.length := by
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    split at hx <;> simp_all
  have hout : out = ⟨[(.pt (off + (Instr.ldrLit t imm).size) b.ctx,
      st.set t.val .lo)], []⟩ := by
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    split at hx <;> simp_all [fall]
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hacc : (Instr.ldrLit t imm).accesses s₁ = (Instr.ldrLit t imm).accesses s₂ := by
    simp [Instr.accesses, hrel.pc_eq]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := hrel
  by_cases hal : ((Instr.ldrLit t imm).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.ldrLit t imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := ldrLit_sound t imm hidx hrel hbase hnowrap hbound
    have hs₁ := step_of_instrAt hc₁ off (.ldrLit t imm) hrel.pc heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.ldrLit t imm) (hrel.pc_eq.trans hrel.pc)
      heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [hrel.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.ldrLit t imm) hdecode hlen
    have hd₂ := decode_at hc₂ off (.ldrLit t imm) hdecode hlen
    have hal₂ : ((Instr.ldrLit t imm).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    apply certAt_paired_fault (fault := .unaligned s₁.pc)
    · simp [step, hrel.pc, heven', hd₁, hal]
    · simp [step, hrel.pc, hrel.pc_eq.trans hrel.pc, heven', hd₂, hal₂]

end M0Crypto.Release.ConstantTime
