import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.Blake2sStreamCode

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! Single-instruction effects used by the streaming functions. -/

namespace M0Crypto.Release.Blake2sStreamEff

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb

theorem pc_next (i : Instr) (hf : i.falls = true) (s : State) :
    (i.next s).pc = s.pc + BitVec.ofNat 32 i.size := by
  exact exec_pc hf (exec_ok_of_falls hf s)

theorem regs_str (s : State) (t n : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memImm .str t n i).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, hr, MemOp.width]

theorem mem_str (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .str t n i).next s).mem =
      write32 s.mem (s.regs n.toReg + BitVec.ofNat 32 (i.toNat * 4)) (s.regs t.toReg) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, MemOp.width, State.reg,
    M0Crypto.Release.Blake2s.toReg_ne15]

end M0Crypto.Release.Blake2sStreamEff
