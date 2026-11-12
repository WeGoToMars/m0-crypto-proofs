import M0Crypto.Thumb.SpBlock
import M0Crypto.Proofs.Common

/-!
# Per-instruction effects used by the BLAKE2s proofs

One lemma per instruction form: the register file after `Instr.next` (away from the PC), and
the memory. The BLAKE2s code is straight-line, so block lemmas rewrite with these.
-/

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M
open M0Crypto.Thumb

theorem toReg_ne15 (d : LowReg) : d.toReg ≠ 15 := by
  intro h; have := congrArg Fin.val h; simp [LowReg.toReg] at this; omega

theorem regs_addReg (s : State) (d n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addReg d n m).next s).regs r =
      if r = d.toReg then s.reg n + s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Proofs.addWithCarry_fst]

theorem regs_eors (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .eors d m).next s).regs r =
      if r = d.toReg then s.reg d ^^^ s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, hr]

theorem regs_rors (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .rors d m).next s).regs r =
      if r = d.toReg then (rorC (s.reg d) ((s.reg m).toNat % 256) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, State.reg, hr]

theorem regs_movImm (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.movImm d i).next s).regs r =
      if r = d.toReg then i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_movHi (s : State) (d m : Reg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.movHi d m).next s).regs r = if r = d then s.regs m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem regs_ldrSp (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Thumb.Instr.ldrSp t i).next s).regs r =
      if r = t.toReg then read32 s.mem (s.sp + BitVec.ofNat 32 (i.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem regs_strSp (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Thumb.Instr.strSp t i).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_strSp (s : State) (t : LowReg) (i : BitVec 8) :
    ((Thumb.Instr.strSp t i).next s).mem =
      write32 s.mem (s.sp + BitVec.ofNat 32 (i.toNat * 4)) (s.reg t) := by
  simp [Instr.next, Instr.exec, State.reg]

theorem mem_movHi (s : State) (d m : Reg) : ((Instr.movHi d m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem mem_ldrSp (s : State) (t : LowReg) (i : BitVec 8) :
    ((Thumb.Instr.ldrSp t i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem mem_addReg (s : State) (d n m : LowReg) : ((Instr.addReg d n m).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem mem_dp (s : State) (op : DpOp) (d m : LowReg) (h : op = .eors ∨ op = .rors) :
    ((Instr.dp op d m).next s).mem = s.mem := by
  rcases h with rfl | rfl <;> simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.setNZC]

theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

end M0Crypto.Release.Blake2s
