import M0Crypto.Release.Poly1305BlockStep
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Mac (v64)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

def foldPrep : List Instr :=
  [.strSp 0 3, .movHi 2 14, .memImm .ldr 3 7 5, .dp .muls 2 3, .addReg 4 1 2,
   .lsrImm 5 4 2, .movImm 2 3, .dp .ands 2 4, .subReg 4 4 2, .addReg 5 5 4]
def foldAdd : List Instr :=
  [.movImm 6 0, .ldrSp 0 0, .addReg 0 0 5, .ldrSp 1 1, .dp .adcs 1 6,
   .ldrSp 3 2, .dp .adcs 3 6, .ldrSp 4 3, .dp .adcs 4 6, .dp .adcs 2 6,
   .movHi 8 0, .movHi 9 1, .movHi 10 3, .movHi 11 4, .movHi 14 2]

theorem fold_eq : fold = foldPrep ++ foldAdd := rfl

def gw (s : State) : Word := s.regs 1 + s.regs 14 * read32 s.mem (slot (s.regs 7) 5)
def fw (s : State) : Word := (gw s >>> 2) + (gw s - (gw s &&& 3#32))

theorem foldPrep_effect (s : State) (hs : Sep s) :
    let t := execAll foldPrep s
    t.regs 2 = gw s &&& 3#32 ∧ t.regs 5 = fw s ∧ t.regs 13 = s.regs 13 ∧
    t.mem = write32 s.mem (slot (s.regs 13) 3) (s.regs 0) := by
  have cw5 := cw_write s hs 3 (by decide) (s.regs 0) 5 (by decide)
  simp (config := { decide := true }) only [foldPrep, execAll, Instr.next, Instr.exec,
    Instr.exec.memOp, MemOp.width, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3,
    M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_7,
    ite_true, ite_false, lsrC, M0Crypto.Proofs.addWithCarry_fst, M0Crypto.Release.sub_flags]
  simp only [show (3 : BitVec 8).toNat = 3 from rfl, show (5 : BitVec 5).toNat = 5 from rfl,
    show (2 : BitVec 5).toNat = 2 from rfl, Nat.reduceMul]
  rw [show read32 (write32 s.mem (s.regs 13 + 12#32) (s.regs 0)) (s.regs 7 + 20#32) =
    read32 s.mem (slot (s.regs 7) 5) from cw5]
  simp [gw, fw, slot, BitVec.mul_comm, BitVec.and_comm]

theorem foldAdd_h (s : State) :
    hval (execAll foldAdd s) =
      (Poly1305Arith.val5 (read32 s.mem (slot (s.regs 13) 0)).toNat
        (read32 s.mem (slot (s.regs 13) 1)).toNat (read32 s.mem (slot (s.regs 13) 2)).toNat
        (read32 s.mem (slot (s.regs 13) 3)).toNat (s.regs 2).toNat + (s.regs 5).toNat) % 2^160 := by
  have h := Poly1305Carry.adc5_mod (read32 s.mem (slot (s.regs 13) 0))
    (read32 s.mem (slot (s.regs 13) 1)) (read32 s.mem (slot (s.regs 13) 2))
    (read32 s.mem (slot (s.regs 13) 3)) (s.regs 2) (s.regs 5) 0 0 0 0
  simp (config := { decide := true }) only [foldAdd, hval, execAll, Instr.next, Instr.exec,
    addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3,
    M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6,
    ite_true, ite_false]
  change _ = _
  dsimp only at h
  have hz : Poly1305Arith.val5 (s.regs 5).toNat (0 : Word).toNat (0 : Word).toNat
      (0 : Word).toNat (0 : Word).toNat = (s.regs 5).toNat := by simp [Poly1305Arith.val5]
  rw [hz] at h
  exact h

theorem and3_nat (x : Word) : (x &&& 3#32).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

theorem gw_nat (s : State) :
    (gw s).toNat = (v64 s / 2^32 + (s.regs 14).toNat * cw s 5 % 2^32) % 2^32 := by
  have := (s.regs 0).isLt
  simp only [gw, BitVec.toNat_add, BitVec.toNat_mul, cw, v64]
  omega

theorem fw_nat (s : State) :
    (fw s).toNat = ((gw s).toNat / 4 + ((gw s).toNat - (gw s).toNat % 4)) % 2^32 := by
  simp only [fw, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_sub, and3_nat]
  have := (gw s).isLt
  omega

/-- Final carry fold, including all 32-bit truncations actually performed. -/
theorem fold_h (s : State) (hs : Sep s) :
    hval (execAll fold s) =
      (Poly1305Arith.val4 (read32 s.mem (slot (s.regs 13) 0)).toNat
        (read32 s.mem (slot (s.regs 13) 1)).toNat (read32 s.mem (slot (s.regs 13) 2)).toNat
        (v64 s % 2^32) + 2^128 * ((gw s).toNat % 4) + (fw s).toNat) % 2^160 := by
  rw [fold_eq, execAll_append, foldAdd_h]
  obtain ⟨r2, r5, sp, hm⟩ := foldPrep_effect s hs
  rw [r2, r5, sp, hm]
  simp only [M0Crypto.Armv6M.read32_write32_slot _ _ _ 3 0 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 3 1 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 3 2 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 3 3 (by decide) (by decide),
    ite_true, ite_false, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, and3_nat, v64_low, Poly1305Arith.val5, Poly1305Arith.val4]

end M0Crypto.Release.Poly1305Blocks
