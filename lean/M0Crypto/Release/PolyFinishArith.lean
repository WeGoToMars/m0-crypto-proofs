import M0Crypto.Release.PolyFinishCode
import M0Crypto.Release.PolyCarry
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace M0Crypto.Release.PolyFinish
open M0Crypto.Armv6M (Word Reg State Mem read32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.AEAD (p)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

def hw (s : State) (j : Nat) : Word := read32 s.mem (slot (s.regs 7) j)
def hv (s : State) : Nat := PolyArith.val5 (hw s 0).toNat (hw s 1).toNat (hw s 2).toNat (hw s 3).toNat (hw s 4).toNat
def pv (s : State) : Nat := PolyArith.val4 (hw s 12).toNat (hw s 13).toNat (hw s 14).toNat (hw s 15).toNat
def low (s : State) : Nat := PolyArith.val4 (s.regs 2).toNat (s.regs 3).toNat (s.regs 4).toNat (s.regs 5).toNat

def bump : List Instr :=
  [.memImm .ldr 0 7 0, .addImm8 0 5, .memImm .ldr 0 7 1, .dp .adcs 0 6,
   .memImm .ldr 0 7 2, .dp .adcs 0 6, .memImm .ldr 0 7 3, .dp .adcs 0 6,
   .memImm .ldr 0 7 4, .dp .adcs 0 6]
def choose : List Instr := [.lsrImm 0 0 2, .dp .rsbs 0 0, .movImm 1 5, .dp .ands 1 0]

theorem carry_eq : carry = bump ++ choose := rfl

/-- The last word of h+5 yields exactly the carry past bit 129. -/
theorem top_carry (x0 x1 x2 x3 x4 : Word)
    (hh : PolyArith.val5 x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat < 2*p) :
    let a0 := addWithCarry x0 5 false
    let a1 := addWithCarry x1 0 a0.2.1
    let a2 := addWithCarry x2 0 a1.2.1
    let a3 := addWithCarry x3 0 a2.2.1
    let a4 := addWithCarry x4 0 a3.2.1
    a4.1.toNat / 4 = (PolyArith.val5 x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat + 5) / 2^130 := by
  have h := PolyCarry.adc5 x0 x1 x2 x3 x4 5 0 0 0 0
  have h0 := (addWithCarry x0 5 false).1.isLt
  have h1 := (addWithCarry x1 0 (addWithCarry x0 5 false).2.1).1.isLt
  have h2 := (addWithCarry x2 0 (addWithCarry x1 0 (addWithCarry x0 5 false).2.1).2.1).1.isLt
  have h3 := (addWithCarry x3 0 (addWithCarry x2 0 (addWithCarry x1 0 (addWithCarry x0 5 false).2.1).2.1).2.1).1.isLt
  simp only [PolyArith.val5, show (0 : Word).toNat = 0 from rfl, show (5 : Word).toNat = 5 from rfl,
    Nat.mul_zero, Nat.add_zero, PolyArith.p_eq] at h hh ⊢
  try dsimp only at h ⊢
  omega

theorem bump_top (s : State) (hz : s.regs 6 = 0#32) (hh : hv s < 2*p) :
    ((execAll bump s).regs 0).toNat / 4 = (hv s + 5) / 2^130 := by
  have h := top_carry (hw s 0) (hw s 1) (hw s 2) (hw s 3) (hw s 4) hh
  simp (config := { decide := true }) only [bump, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    MemOp.width, addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_6, M0Crypto.Proofs.toReg_7, ite_true, ite_false, hz]
  exact h

theorem choose_word (s : State) (h : (s.regs 0).toNat / 4 ≤ 1) :
    ((execAll choose s).regs 1).toNat = 5 * ((s.regs 0).toNat / 4) := by
  simp (config := { decide := true }) only [choose, execAll, Instr.next, Instr.exec, addFlags,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_1, ite_true, ite_false, lsrC, ChaChaLoop.sub_flags]
  have hq : (s.regs 0 >>> 2).toNat = (s.regs 0).toNat / 4 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hq' : (s.regs 0 >>> 2) = 0#32 ∨ (s.regs 0 >>> 2) = 1#32 := by
    rcases (by omega : (s.regs 0).toNat / 4 = 0 ∨ (s.regs 0).toNat / 4 = 1) with h0 | h1
    · left; apply BitVec.eq_of_toNat_eq; simpa [hq] using h0
    · right; apply BitVec.eq_of_toNat_eq; simpa [hq] using h1
  rcases hq' with h0 | h1
  · have q0 : (s.regs 0).toNat / 4 = 0 := by rw [← hq, h0]; rfl
    simp only [show (2 : BitVec 5).toNat = 2 from rfl, h0, q0]
    rfl
  · have q1 : (s.regs 0).toNat / 4 = 1 := by rw [← hq, h1]; rfl
    simp only [show (2 : BitVec 5).toNat = 2 from rfl, h1, q1]
    rfl

/-- The branchless subtraction selector is 5 exactly when h >= p. -/
theorem carry_correct (s : State) (hz : s.regs 6 = 0#32) (hh : hv s < 2*p) :
    ((execAll carry s).regs 1).toNat = 5 * ((hv s + 5) / 2^130) := by
  have ht := bump_top s hz hh
  have hb : ((execAll bump s).regs 0).toNat / 4 ≤ 1 := by
    rw [ht]; simp only [PolyArith.p_eq] at hh; omega
  rw [carry_eq, execAll_append, choose_word _ hb, ht]

theorem hw_preserved (is : List Instr) (hn : is.all (!·.writesMem) = true)
    (hr : is.all (fun i => !(i.dsts.contains 7)) = true) (s : State) (j : Nat) : hw (execAll is s) j = hw s j := by
  simp only [hw, execAll_mem is s hn, execAll_regs_other is s 7 (by decide) hr]

theorem carry_hw (s : State) (j : Nat) : hw (execAll carry s) j = hw s j :=
  hw_preserved carry (by decide) (by decide) s j
theorem reduce_hw (s : State) (j : Nat) : hw (execAll reduce s) j = hw s j :=
  hw_preserved reduce (by decide) (by decide) s j

theorem reduce_correct (s : State) (hz : s.regs 6 = 0#32) :
    low (execAll reduce s) = (hv s + (s.regs 1).toNat) % 2^128 := by
  have h := PolyCarry.adc4_mod (hw s 0) (hw s 1) (hw s 2) (hw s 3) (s.regs 1) 0 0 0
  simp (config := { decide := true }) only [reduce, low, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    MemOp.width, addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_1,
    M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4,
    M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6, M0Crypto.Proofs.toReg_7, ite_true, ite_false, hz]
  have hz4 : PolyArith.val4 (s.regs 1).toNat (0 : Word).toNat (0 : Word).toNat (0 : Word).toNat =
      (s.regs 1).toNat := by simp [PolyArith.val4]
  dsimp only at h
  rw [hz4] at h
  change _ = _ at h
  apply h.trans
  simp only [hv, PolyArith.val4, PolyArith.val5]
  omega

theorem pad_correct (s : State) : low (execAll pad s) = (low s + pv s) % 2^128 := by
  have h := PolyCarry.adc4_mod (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5)
    (hw s 12) (hw s 13) (hw s 14) (hw s 15)
  simp (config := { decide := true }) only [pad, low, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    MemOp.width, addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0,
    M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4,
    M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_7, ite_true, ite_false]
  exact h

theorem carry_six (s : State) : (execAll carry s).regs 6 = s.regs 6 :=
  execAll_regs_other _ _ _ (by decide) (by decide)
attribute [local irreducible] carry reduce pad

/-- The exact release arithmetic computes the RFC tag integer modulo 2^128. -/
theorem arithmetic_correct (s : State) (hz : s.regs 6 = 0#32) (hh : hv s < 2*p) :
    low (execAll arithmetic s) = (hv s % p + pv s) % 2^128 := by
  have hz' : (execAll carry s).regs 6 = 0#32 := by
    rw [carry_six]; exact hz
  rw [arithmetic, execAll_append, execAll_append, pad_correct, reduce_correct _ hz', carry_correct s hz hh]
  simp only [hv, pv, reduce_hw, carry_hw]
  have hred := PolySpec.tag_reduce (hv s) (pv s) hh
  simp only [hv, pv] at hred
  omega

end M0Crypto.Release.PolyFinish
