import M0Crypto.Armv6M.State

/-!
Thumb decoder for the pilot instruction subset (ARMv6-M ARM, DDI 0419, §A5/§A6).

Only the encodings emitted by the pilot kernel are accepted. Every other 16-bit
halfword decodes to `unsupported16`, and every first halfword of a 32-bit
encoding (bits[15:11] ∈ {0b11101, 0b11110, 0b11111}) decodes to `unsupported32`.
Executing either is a fault, never a silent no-op.

Supported (ARMv6-M has no IT blocks, so these always set flags):
* `MOVS Rd, #imm8`       T1  `00100 ddd iiiiiiii`
* `ADDS Rd, Rn, Rm`      T1  `0001100 mmm nnn ddd`
* `EORS Rdn, Rm`         T1  `0100000001 mmm ddd`
* `RORS Rdn, Rm`         T1  `0100000111 mmm ddd`
* `LDR Rt, [SP, #imm8*4]` T2  `10011 ttt iiiiiiii`  (A6.7.26)
* `STR Rt, [SP, #imm8*4]` T2  `10010 ttt iiiiiiii`  (A6.7.59)
-/

namespace M0Crypto.Armv6M

inductive Instr where
  | movsImm (d : LowReg) (imm8 : BitVec 8)
  | addsReg (d n m : LowReg)
  | eorsReg (dn m : LowReg)
  | rorsReg (dn m : LowReg)
  | ldrSp (t : LowReg) (imm8 : BitVec 8)
  | strSp (t : LowReg) (imm8 : BitVec 8)
  deriving DecidableEq, Repr

inductive Decoded where
  | ok (i : Instr)
  | unsupported16 (hw : BitVec 16)
  | unsupported32 (hw : BitVec 16)
  deriving DecidableEq, Repr

/-- 3-bit register field starting at bit `lo`. -/
def lowField (hw : BitVec 16) (lo : Nat) : LowReg :=
  ⟨(hw.toNat >>> lo) % 8, Nat.mod_lt _ (by decide)⟩

def decode (hw : BitVec 16) : Decoded :=
  let op := hw.toNat
  if op >>> 11 ≥ 0b11101 then .unsupported32 hw
  else if op >>> 11 = 0b00100 then .ok (.movsImm (lowField hw 8) (hw.extractLsb' 0 8))
  else if op >>> 9 = 0b0001100 then .ok (.addsReg (lowField hw 0) (lowField hw 3) (lowField hw 6))
  else if op >>> 6 = 0b0100000001 then .ok (.eorsReg (lowField hw 0) (lowField hw 3))
  else if op >>> 6 = 0b0100000111 then .ok (.rorsReg (lowField hw 0) (lowField hw 3))
  else if op >>> 11 = 0b10011 then .ok (.ldrSp (lowField hw 8) (hw.extractLsb' 0 8))
  else if op >>> 11 = 0b10010 then .ok (.strSp (lowField hw 8) (hw.extractLsb' 0 8))
  else .unsupported16 hw

/-! Decoder spot checks, including rejection of encodings outside the subset. -/

example : decode 0x2410#16 = .ok (.movsImm 4 16) := by decide
example : decode 0x1840#16 = .ok (.addsReg 0 0 1) := by decide
example : decode 0x4043#16 = .ok (.eorsReg 3 0) := by decide
example : decode 0x41e3#16 = .ok (.rorsReg 3 4) := by decide
example : decode 0x9803#16 = .ok (.ldrSp 0 3) := by decide     -- ldr r0, [sp, #12]
example : decode 0x970f#16 = .ok (.strSp 7 15) := by decide    -- str r7, [sp, #60]
-- LDR/STR with a register base (T1, 01101/01100) and LDR literal: not in the subset.
example : decode 0x6808#16 = .unsupported16 0x6808#16 := by decide
example : decode 0x6008#16 = .unsupported16 0x6008#16 := by decide
example : decode 0x4801#16 = .unsupported16 0x4801#16 := by decide
-- NOP, ADD (high registers, T2), MOV (high registers), LSLS #imm, BX LR: not in the subset.
example : decode 0xbf00#16 = .unsupported16 0xbf00#16 := by decide
example : decode 0x4448#16 = .unsupported16 0x4448#16 := by decide
example : decode 0x4680#16 = .unsupported16 0x4680#16 := by decide
example : decode 0x0100#16 = .unsupported16 0x0100#16 := by decide
example : decode 0x4770#16 = .unsupported16 0x4770#16 := by decide
-- First halfwords of 32-bit encodings (BL prefix, and a Thumb-2 prefix).
example : decode 0xf000#16 = .unsupported32 0xf000#16 := by decide
example : decode 0xe800#16 = .unsupported32 0xe800#16 := by decide
-- 0b11100 is the 16-bit unconditional branch B, not a 32-bit prefix; unsupported here.
example : decode 0xe000#16 = .unsupported16 0xe000#16 := by decide

end M0Crypto.Armv6M
