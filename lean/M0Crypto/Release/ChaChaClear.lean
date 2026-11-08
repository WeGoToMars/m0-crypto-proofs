import M0Crypto.Release.ChaChaInit
import M0Crypto.Release.ChaChaLayout

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Fixed-batch frame clearing, with the same memory effect as word stores. -/
namespace M0Crypto.Release.ChaChaXor
open M0Crypto.Armv6M (State Word LowReg slot)
open M0Crypto.Thumb

private theorem clearRegs : listRegs 31#8 = [0, 1, 2, 3, 4] := by decide
private theorem clearCount : bitCount 31#8 = 5 := by decide

/-- Batching changes the transfer instructions, not the bytes cleared. -/
theorem clr_mem (t : State) : (execAll clr t).mem =
    (execAll (stores ChaChaLayout.chFrameWords) (t.setReg 0 0)).mem := by
  rw [ChaChaLayout.chFrameWords_eq]
  simp (config := { decide := true }) [clr, stores, execAll, Instr.next, Instr.exec,
    clearRegs, clearCount, storeWords, List.range_succ, List.range_zero,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, LowReg.toReg, BitVec.add_assoc,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5]

theorem clr_regs (t : State) :
    let u := execAll clr t
    u.regs 0 = 0 ∧ u.regs 1 = 0 ∧ u.regs 2 = 0 ∧ u.regs 3 = 0 ∧
    u.regs 12 = 0 ∧ u.regs 13 = t.regs 13 := by
  simp (config := { decide := true }) [clr, execAll, Instr.next, Instr.exec,
    clearRegs, clearCount, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, LowReg.toReg,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5]

/-- The seven batches write precisely the 35 frame words, in order. -/
theorem clr_accesses (t : State) :
    (traceAll clr t).flatMap Event.accesses =
      (List.range ChaChaLayout.chFrameWords).map
        (fun i => (⟨.write, slot (t.regs 13) i, 4⟩ : Access)) := by
  rw [ChaChaLayout.chFrameWords_eq]
  simp (config := { decide := true }) [clr, traceAll, Instr.next, Instr.exec, Instr.accesses,
    clearRegs, clearCount, wordAccesses, List.range_succ, List.range_zero,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, LowReg.toReg, slot, BitVec.add_assoc,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5]

theorem clr_aligned (t : State) (hsp : (t.regs 13).toNat % 4 = 0) : alignedAll clr t = true := by
  simp (config := { decide := true }) [clr, alignedAll, Instr.next, Instr.exec, Instr.accesses,
    clearRegs, clearCount, wordAccesses, List.range_succ, List.range_zero, Access.aligned,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, LowReg.toReg, BitVec.add_assoc,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end M0Crypto.Release.ChaChaXor
