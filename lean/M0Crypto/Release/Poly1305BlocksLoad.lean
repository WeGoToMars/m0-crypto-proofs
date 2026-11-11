import M0Crypto.Release.Poly1305Blocks
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-!
The aligned LDM and unaligned byte-load paths read the same four little-endian
words. `load_words` applies to any message-pointer alignment.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7

theorem leword (a b c d : BitVec 8) :
    a.setWidth 32 ||| (b.setWidth 32 <<< 8 ||| (c.setWidth 32 <<< 16 ||| d.setWidth 32 <<< 24)) =
      d ++ c ++ b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [hi, h8, show i < 16 by omega, show i < 24 by omega]
  by_cases h16 : i < 16
  · simp [hi, h8, h16, show i < 24 by omega, show i-8 < 8 by omega, show i-8 < 32 by omega,
      BitVec.getLsbD_of_ge a i (by omega)]
  by_cases h24 : i < 24
  · simp [hi, h8, h16, h24, show ¬i-8 < 8 by omega, show i-16 < 8 by omega,
      BitVec.getLsbD_of_ge b (i-8) (by omega), BitVec.getLsbD_of_ge a i (by omega),
      show i-16 < 32 by omega, Nat.sub_sub]
  · simp [hi, h8, h16, h24, show ¬i-8 < 8 by omega, show ¬i-8-8 < 8 by omega,
      show i-24 < 8 by omega, BitVec.getLsbD_of_ge b (i-8) (by omega),
      BitVec.getLsbD_of_ge c (i-16) (by omega), BitVec.getLsbD_of_ge a i (by omega),
      show i-24 < 32 by omega, show ¬i-16 < 8 by omega, Nat.sub_sub]


theorem ldle_word (s : State) (d : LowReg) (hd : d.val < 4) (off : Nat) (hoff : off+3 < 32) :
    (execAll (ldle d off) s).regs d.toReg = read32 s.mem (s.regs 6 + BitVec.ofNat 32 off) := by
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
    rcases d with ⟨d, hd'⟩; simp only [Fin.ext_iff]; simp at hd ⊢; omega
  rcases hd' with rfl | rfl | rfl | rfl
  all_goals
    simp only [execAll, ldle, Instr.next, Instr.exec, Instr.exec.memOp,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.reg,
      M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_6,
      MemOp.width, lslC, read8]
    simp (config := { decide := true }) only [ite_true, ite_false, Nat.mul_one]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 32 by omega),
      Nat.mod_eq_of_lt (show off+1 < 32 by omega), Nat.mod_eq_of_lt (show off+2 < 32 by omega),
      Nat.mod_eq_of_lt (show off+3 < 32 by omega)]
    simp [read32, BitVec.or_assoc, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl,
      show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
      show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, ofNat_add_assoc]
    exact leword _ _ _ _

theorem ldle_regs (s : State) (d : LowReg) (off : Nat) (r : Reg)
    (hd : r.val ≠ d.val) (h4 : r.val ≠ 4) (h15 : r.val ≠ 15) :
    (execAll (ldle d off) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ h15
  simp [ldle, Instr.dsts, MemOp.isLoad]; omega

theorem ldle_mem (s : State) (d : LowReg) (off : Nat) : (execAll (ldle d off) s).mem = s.mem :=
  execAll_mem _ _ (by simp [ldle, Instr.writesMem, MemOp.isLoad])

theorem ldle0_word (s : State) (off : Nat) (hoff : off+3 < 32) :
    (execAll (ldle 0 off) s).regs 0 = read32 s.mem (s.regs 6 + BitVec.ofNat 32 off) := by
  simpa only [M0Crypto.Proofs.toReg_0] using ldle_word s 0 (by decide) off hoff

theorem ldle1_word (s : State) (off : Nat) (hoff : off+3 < 32) :
    (execAll (ldle 1 off) s).regs 1 = read32 s.mem (s.regs 6 + BitVec.ofNat 32 off) := by
  simpa only [M0Crypto.Proofs.toReg_1] using ldle_word s 1 (by decide) off hoff

theorem ldle2_word (s : State) (off : Nat) (hoff : off+3 < 32) :
    (execAll (ldle 2 off) s).regs 2 = read32 s.mem (s.regs 6 + BitVec.ofNat 32 off) := by
  simpa only [M0Crypto.Proofs.toReg_2] using ldle_word s 2 (by decide) off hoff

theorem ldle3_word (s : State) (off : Nat) (hoff : off+3 < 32) :
    (execAll (ldle 3 off) s).regs 3 = read32 s.mem (s.regs 6 + BitVec.ofNat 32 off) := by
  simpa only [M0Crypto.Proofs.toReg_3] using ldle_word s 3 (by decide) off hoff

theorem ldle_r6 (s : State) (d : LowReg) (hd : d.val < 4) (off : Nat) :
    (execAll (ldle d off) s).regs 6 = s.regs 6 :=
  ldle_regs s d off 6 (by omega) (by decide) (by decide)

theorem loadU_words (s : State) (j : Nat) (hj : j < 4) :
    (execAll loadU s).regs ⟨j, by omega⟩ = read32 s.mem (slot (s.regs 6) j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · change (execAll loadU s).regs 0 = read32 s.mem (slot (s.regs 6) 0)
    simp only [loadU, execAll_append]
    rw [execAll_regs_other [.addImm8 6 16] _ 0 (by decide) (by decide)]
    rw [ldle_regs _ 3 12 0 (by decide) (by decide) (by decide),
      ldle_regs _ 2 8 0 (by decide) (by decide) (by decide),
      ldle_regs _ 1 4 0 (by decide) (by decide) (by decide), ldle0_word s 0 (by decide)]
    rfl
  · change (execAll loadU s).regs 1 = read32 s.mem (slot (s.regs 6) 1)
    simp only [loadU, execAll_append]
    rw [execAll_regs_other [.addImm8 6 16] _ 1 (by decide) (by decide)]
    rw [ldle_regs _ 3 12 1 (by decide) (by decide) (by decide),
      ldle_regs _ 2 8 1 (by decide) (by decide) (by decide), ldle1_word _ 4 (by decide)]
    simp only [ldle_mem, ldle_r6 _ 0 (by decide), ldle_r6 _ 1 (by decide), ldle_r6 _ 2 (by decide)]; rfl
  · change (execAll loadU s).regs 2 = read32 s.mem (slot (s.regs 6) 2)
    simp only [loadU, execAll_append]
    rw [execAll_regs_other [.addImm8 6 16] _ 2 (by decide) (by decide)]
    rw [ldle_regs _ 3 12 2 (by decide) (by decide) (by decide), ldle2_word _ 8 (by decide)]
    simp only [ldle_mem, ldle_r6 _ 0 (by decide), ldle_r6 _ 1 (by decide), ldle_r6 _ 2 (by decide)]; rfl
  · change (execAll loadU s).regs 3 = read32 s.mem (slot (s.regs 6) 3)
    simp only [loadU, execAll_append]
    rw [execAll_regs_other [.addImm8 6 16] _ 3 (by decide) (by decide)]
    rw [ldle3_word _ 12 (by decide)]
    simp only [ldle_mem, ldle_r6 _ 0 (by decide), ldle_r6 _ 1 (by decide), ldle_r6 _ 2 (by decide)]; rfl

theorem loadA_words (s : State) (j : Nat) (hj : j < 4) :
    (execAll loadA s).regs ⟨j, by omega⟩ = read32 s.mem (slot (s.regs 6) j) := by
  have hl : listRegs 15#8 = [0, 1, 2, 3] := by decide
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [loadA, execAll, Instr.next, Instr.exec, hl,
      loadRegs, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, slot,
      BitVec.add_assoc]

/-- Both alignment paths load the same four little-endian words. -/
theorem load_words (s : State) (j : Nat) (hj : j < 4) :
    (loadState s).regs ⟨j, by omega⟩ =
      read32 s.mem (slot (read32 s.mem (slot (s.regs 13) slotMsg)) j) := by
  have hj15 : (⟨j, by omega⟩ : Reg) ≠ 15 := by intro h; have := congrArg Fin.val h; simp at this; omega
  rw [loadState]
  try dsimp only
  split
  · rw [setReg_regs_ne _ 15 _ _ hj15, loadA_words _ j hj]
    simp only [setReg_regs_ne _ 15 6 _ (by decide), setReg_mem, (test_regs s).1,
      execAll_mem testAlign s (by decide)]
  · rw [loadU_words _ j hj]
    simp only [setReg_regs_ne _ 15 6 _ (by decide), setReg_mem, (test_regs s).1,
      execAll_mem testAlign s (by decide)]

end M0Crypto.Release.Poly1305Blocks
