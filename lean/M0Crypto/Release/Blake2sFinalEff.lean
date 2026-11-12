import M0Crypto.Release.Blake2sStreamEff

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # Per-instruction effects used by the streaming proofs (flags included) -/

namespace M0Crypto.Release.Blake2sStreamEff

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb

theorem regs_lsl (s : State) (d m : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lslImm d m i).next s).regs r =
      if r = d.toReg then (lslC (s.reg m) i.toNat s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZ, State.reg, hr]

theorem z_lsl (s : State) (d m : LowReg) (i : BitVec 5) :
    ((Instr.lslImm d m i).next s).z = ((lslC (s.reg m) i.toNat s.c).1 == 0#32) := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZ, State.reg]

theorem mem_lsl (s : State) (d m : LowReg) (i : BitVec 5) : ((Instr.lslImm d m i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, State.setNZ]

theorem regs_ldr (s : State) (t n : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memImm .ldr t n i).next s).regs r =
      if r = t.toReg then read32 s.mem (s.reg n + BitVec.ofNat 32 (i.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width, hr]

theorem mem_ldr (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .ldr t n i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem c_addReg (s : State) (d n m : LowReg) :
    ((Instr.addReg d n m).next s).c = (addWithCarry (s.reg n) (s.reg m) false).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg]

theorem regs_adcs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .adcs d m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (s.reg m) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr]

theorem mem_adcs (s : State) (d m : LowReg) : ((Instr.dp .adcs d m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem regs_mvns (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .mvns d m).next s).regs r = if r = d.toReg then ~~~(s.reg m) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, hr]

theorem mem_mvns (s : State) (d m : LowReg) : ((Instr.dp .mvns d m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem regs_memReg_st (s : State) (op : MemOp) (t n m : LowReg) (h : op = .str ∨ op = .strb) (r : Reg)
    (hr : r ≠ 15) : ((Instr.memReg op t n m).next s).regs r = s.regs r := by
  rcases h with rfl | rfl <;>
    simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, hr]

theorem mem_strw (s : State) (t n m : LowReg) :
    ((Instr.memReg .str t n m).next s).mem = write32 s.mem (s.reg n + s.reg m) (s.reg t) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, M0Crypto.Release.Blake2s.toReg_ne15]

theorem mem_strb (s : State) (t n m : LowReg) :
    ((Instr.memReg .strb t n m).next s).mem = write8 s.mem (s.reg n + s.reg m) (s.reg t) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, M0Crypto.Release.Blake2s.toReg_ne15]

theorem regs_ldrb (s : State) (t n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memReg .ldrb t n m).next s).regs r =
      if r = t.toReg then read8 s.mem (s.reg n + s.reg m) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, hr]

theorem mem_ldrb (s : State) (t n m : LowReg) :
    ((Instr.memReg .ldrb t n m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem regs_cmpImm (s : State) (n : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.cmpImm n i).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, hr]

theorem mem_cmpImm (s : State) (n : LowReg) (i : BitVec 8) : ((Instr.cmpImm n i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem z_cmpImm (s : State) (n : LowReg) (i : BitVec 8) :
    ((Instr.cmpImm n i).next s).z = (s.reg n == i.setWidth 32) := by
  simp only [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg]
  have h : (addWithCarry (s.regs n.toReg) (~~~(i.setWidth 32)) true).1 = s.regs n.toReg - i.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [addWithCarry, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  simp only [h]
  by_cases hab : s.regs n.toReg = BitVec.setWidth 32 i
  · simp [hab]
  · have : s.regs n.toReg - BitVec.setWidth 32 i ≠ (0 : BitVec 32) := fun h0 => hab (by bv_omega)
    rw [beq_false_of_ne this, beq_false_of_ne hab]

theorem regs_addImm8 (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addImm8 d i).next s).regs r = if r = d.toReg then s.reg d + i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Proofs.addWithCarry_fst]

theorem mem_addImm8 (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.addImm8 d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem regs_addImm3 (s : State) (d n : LowReg) (i : BitVec 3) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addImm3 d n i).next s).regs r = if r = d.toReg then s.reg n + i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Proofs.addWithCarry_fst]

theorem mem_addImm3 (s : State) (d n : LowReg) (i : BitVec 3) : ((Instr.addImm3 d n i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem regs_subSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subSp i).next s).regs r = if r = 13 then s.regs 13 - BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem regs_addSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addSp i).next s).regs r = if r = 13 then s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem mem_subSp (s : State) (i : BitVec 7) : ((Instr.subSp i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem mem_addSp (s : State) (i : BitVec 7) : ((Instr.addSp i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

end M0Crypto.Release.Blake2sStreamEff
