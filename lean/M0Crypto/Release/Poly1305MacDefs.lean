import M0Crypto.Thumb.Seq

/-! Instruction lists shared by Poly1305 code checks and macro proofs.
They do not depend on the arithmetic or execution proofs of those macros. -/

namespace M0Crypto.Release.Poly1305Mac
open M0Crypto.Armv6M (Reg)
open M0Crypto.Thumb

/-- `mov r5, h; lsrs r6, r5, #16; uxth r5, r5; ldrh r3, [r7, #2k]; ldrh r4, [r7, #2k+2]; ...` -/
def mac (h : Reg) (k : Nat) : List Instr :=
  [.movHi 5 h, .lsrImm 6 5 16, .uxth 5 5, .memImm .ldrh 3 7 (BitVec.ofNat 5 k),
   .memImm .ldrh 4 7 (BitVec.ofNat 5 (k + 1)), .lslImm 2 5 0, .dp .muls 2 4, .dp .muls 4 6,
   .dp .muls 6 3, .dp .muls 3 5, .addReg 0 0 3, .dp .adcs 1 4, .lslImm 3 2 16, .lsrImm 2 2 16,
   .addReg 0 0 3, .dp .adcs 1 2, .lslImm 3 6 16, .lsrImm 6 6 16, .addReg 0 0 3, .dp .adcs 1 6]

def narrow (j : Nat) : List Instr :=
  [.movHi 2 14, .memImm .ldr 3 7 (BitVec.ofNat 5 j), .dp .muls 2 3, .movImm 3 0, .addReg 0 0 2, .dp .adcs 1 3]

def colend (j : Nat) : List Instr := [.strSp 0 (BitVec.ofNat 8 j), .lslImm 0 1 0, .movImm 1 0]

end M0Crypto.Release.Poly1305Mac
