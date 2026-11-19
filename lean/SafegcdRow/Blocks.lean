import SafegcdRow.Code
import SafegcdRow.Words
import M0Crypto.Release.FrameBase

namespace SafegcdRow
open M0Crypto.Armv6M (State Reg Mem LowReg read32 write32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release (add_flags sub_flags)

set_option maxRecDepth 4000

/-- The parts of the calling convention kept across the column macros. -/
structure Pins where
  out : Word
  x : Word
  y : Word
  a : Word
  b : Word
  t : Word
  ret : Word
  sp : Word

def Pins.load (s : State) (modular : Bool := true) : Pins :=
  ⟨s.regs 0, s.regs 1, s.regs 2, s.regs 3, s.regs 4, (if modular then s.regs 5 else 0), s.regs 14, s.sp⟩

def Pins.held (p : Pins) (s : State) (modular : Bool := true) : Prop :=
  s.regs 7 = p.out ∧ s.regs 8 = p.x ∧ s.regs 10 = p.y ∧ s.regs 2 = p.a ∧ s.regs 3 = p.b ∧
  (modular = true → s.regs 14 = p.t) ∧ (modular = true → s.regs 11 = -(p.t * 19#32)) ∧ s.regs 12 = p.ret ∧ s.sp = p.sp

private theorem negFlag (x : Word) : (addWithCarry (~~~x) 0#32 true).1 = -x := by
  rw [show (addWithCarry (~~~x) 0#32 true).1 = (addWithCarry 0#32 (~~~x) true).1 by
    simp [addWithCarry, Nat.add_comm]]
  simpa using sub_flags 0#32 x

macro "row_simps" : tactic =>
  `(tactic| simp (config := { decide := true }) [
    execAll, Instr.next, Instr.exec, Instr.exec.memOp, Instr.size,
    Instr.accesses, MemOp.isLoad, MemOp.width,
    State.setReg, State.pc, State.sp, State.reg, State.setNZ, State.setNZC, State.setNZCV,
    LowReg.toReg, addFlags, add_flags, sub_flags, negFlag, asrC, lslC, lsrC,
    BitVec.ofNat_add, BitVec.add_assoc, low, carry, remainder, emit, emitTop, slot])

theorem prologue_effect (s : State) (modular : Bool := true) :
    let t := execAll (prologue modular) s
    (Pins.load s modular).held t modular ∧ t.mem = s.mem ∧ t.regs 5 = 0 := by
  cases modular <;> simp only [Pins.held, Pins.load, prologue,
    Bool.false_eq_true, ite_false, ite_true, List.append_nil, List.cons_append]
  all_goals row_simps
  rfl

theorem accumulate_word (s : State) (i : BitVec 5) :
    (execAll (accumulate i) s).regs 0 =
      s.regs 2 * read32 s.mem (slot (s.regs 8) i.toNat) +
      s.regs 3 * read32 s.mem (slot (s.regs 10) i.toNat) + s.regs 5 := by
  unfold accumulate
  row_simps
  rw [Nat.mul_comm]
  rfl

theorem correction_word (s : State) (i : BitVec 5) :
    (execAll (correction i) s).regs 0 =
      s.regs 0 + (if i = 0#5 then s.regs 11 else if i = 15#5 then s.regs 14 <<< 15 else 0) := by
  unfold correction
  split
  · row_simps
  · split <;> row_simps

theorem split_effect (s : State) :
    let t := execAll splitAccumulator s
    t.regs 5 = carry (s.regs 0) ∧ t.regs 0 = low (s.regs 0) := by
  unfold splitAccumulator
  row_simps

theorem shift_effect (s : State) (i : BitVec 5) :
    let t := execAll (emitShifted i) s
    t.mem = write32 s.mem (slot (s.regs 7) i.toNat) (emit (s.regs 0) (s.regs 4)) ∧
    t.regs 4 = remainder (s.regs 0) := by
  unfold emitShifted
  row_simps
  rw [Nat.mul_comm]
  rfl

theorem finish_mem (s : State) :
    (execAll finish s).mem = write32 s.mem (slot (s.regs 7) 16) (emitTop (s.regs 5) (s.regs 4)) := by
  unfold finish
  row_simps
  exact congrArg (write32 s.mem _) (BitVec.or_comm _ _)

theorem head_remainder (s : State) :
    (execAll [.lsrImm 4 0 14] s).regs 4 = remainder (s.regs 0) := by
  row_simps

end SafegcdRow
