import M0Crypto.Armv6M.State

/-!
Thumb decoder for the instruction forms of the release artifact
(ARMv6-M Architecture Reference Manual, DDI 0419E, §A5.2 and §A6.7).

This is the whole-function model. It is separate from the fragment model in
`M0Crypto.Armv6M`, which covers six instructions of the standalone ChaCha20 fragments.

Accepted encodings are exactly the forms the artifact uses, plus the other
non-signed load/store widths of the two load/store groups. Everything else decodes
to `none` and executing it is a fault, never a silent no-op. In particular:
* the data-processing group (`010000 oooo`) accepts only ANDS, EORS, ADCS, RORS,
  TST, RSBS, CMP, ORRS, MULS, MVNS; LSLS/LSRS/ASRS (register), SBCS, CMN and
  BICS are rejected;
* of the special data group (`010001`) only MOV is accepted, and only when neither
  register is SP or PC (no ADD/CMP high, no BX/BLX);
* STM is rejected when its base register is in the list (UNPREDICTABLE unless it
  is the lowest register; the artifact never does it);
* the only 32-bit encoding accepted is BL;
* ASRS (immediate), ADR, LDRSB/LDRSH, SXT*/UXTB, REV*, CPS, BKPT, hints, SVC, UDF,
  the conditional-branch encodings with cond = 1110 or 1111 are rejected.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M (Word Reg LowReg)

/-- Data-processing operations of the `010000` group that the artifact uses. -/
inductive DpOp where
  | ands | eors | adcs | rors | tst | rsbs | cmp | orrs | muls | mvns
  deriving DecidableEq, Repr

/-- Width and direction of a non-signed load or store. -/
inductive MemOp where
  | str | strh | strb | ldr | ldrh | ldrb
  deriving DecidableEq, Repr

def MemOp.width : MemOp → Nat
  | .str | .ldr => 4
  | .strh | .ldrh => 2
  | .strb | .ldrb => 1

def MemOp.isLoad : MemOp → Bool
  | .ldr | .ldrh | .ldrb => true
  | _ => false

/-- Decoded instructions. Immediates are kept as raw fields; `Exec.lean` scales them. -/
inductive Instr where
  /-- LSLS Rd, Rm, #imm5 (T1). imm5 = 0 is MOVS Rd, Rm (T2). -/
  | lslImm (d m : LowReg) (imm5 : BitVec 5)
  /-- LSRS Rd, Rm, #imm5 (T1); imm5 = 0 encodes a shift by 32. -/
  | lsrImm (d m : LowReg) (imm5 : BitVec 5)
  | addReg (d n m : LowReg)
  | subReg (d n m : LowReg)
  | addImm3 (d n : LowReg) (imm3 : BitVec 3)
  | subImm3 (d n : LowReg) (imm3 : BitVec 3)
  | movImm (d : LowReg) (imm8 : BitVec 8)
  | cmpImm (n : LowReg) (imm8 : BitVec 8)
  | addImm8 (dn : LowReg) (imm8 : BitVec 8)
  | subImm8 (dn : LowReg) (imm8 : BitVec 8)
  /-- Data processing `op Rdn, Rm`; for RSBS the immediate is #0. -/
  | dp (op : DpOp) (dn m : LowReg)
  /-- MOV Rd, Rm (T1); d, m ∉ {SP, PC}; flags unchanged. -/
  | movHi (d m : Reg)
  /-- LDR Rt, [PC, #imm8*4] (literal). -/
  | ldrLit (t : LowReg) (imm8 : BitVec 8)
  /-- op Rt, [Rn, Rm]. -/
  | memReg (op : MemOp) (t n m : LowReg)
  /-- op Rt, [Rn, #imm5 * width]. -/
  | memImm (op : MemOp) (t n : LowReg) (imm5 : BitVec 5)
  | strSp (t : LowReg) (imm8 : BitVec 8)
  | ldrSp (t : LowReg) (imm8 : BitVec 8)
  /-- ADD Rd, SP, #imm8*4. -/
  | addRdSp (d : LowReg) (imm8 : BitVec 8)
  /-- ADD SP, SP, #imm7*4. -/
  | addSp (imm7 : BitVec 7)
  /-- SUB SP, SP, #imm7*4. -/
  | subSp (imm7 : BitVec 7)
  | uxth (d m : LowReg)
  /-- PUSH {low registers, LR if `lr`}. -/
  | push (list : BitVec 8) (lr : Bool)
  /-- POP {low registers, PC if `pc`}. -/
  | pop (list : BitVec 8) (pc : Bool)
  /-- STM Rn!, {list}. -/
  | stm (n : LowReg) (list : BitVec 8)
  /-- LDM Rn{!}, {list}; writeback iff Rn is not in the list. -/
  | ldm (n : LowReg) (list : BitVec 8)
  /-- B<cond> with cond < 14. -/
  | bcond (cond : BitVec 4) (imm8 : BitVec 8)
  | b (imm11 : BitVec 11)
  /-- BL with the 25-bit signed offset `S:I1:I2:imm10:imm11:'0'`. -/
  | bl (imm25 : BitVec 25)
  deriving DecidableEq, Repr

/-- Encoding size in bytes. -/
def Instr.size : Instr → Nat
  | .bl _ => 4
  | _ => 2

/-- 3-bit register field starting at bit `lo`. -/
def low (hw : BitVec 16) (lo : Nat) : LowReg :=
  ⟨(hw.toNat >>> lo) % 8, Nat.mod_lt _ (by decide)⟩

def bits (hw : BitVec 16) (lo w : Nat) : BitVec w := hw.extractLsb' lo w

/-- A first halfword with bits[15:11] ∈ {11101, 11110, 11111} starts a 32-bit encoding. -/
def is32 (hw : BitVec 16) : Bool := hw.toNat >>> 11 ≥ 0b11101

def decodeDp (hw : BitVec 16) : Option Instr :=
  let dn := low hw 0
  let m := low hw 3
  match (hw.toNat >>> 6) % 16 with
  | 0b0000 => some (.dp .ands dn m)
  | 0b0001 => some (.dp .eors dn m)
  | 0b0101 => some (.dp .adcs dn m)
  | 0b0111 => some (.dp .rors dn m)
  | 0b1000 => some (.dp .tst dn m)
  | 0b1001 => some (.dp .rsbs dn m)
  | 0b1010 => some (.dp .cmp dn m)
  | 0b1100 => some (.dp .orrs dn m)
  | 0b1101 => some (.dp .muls dn m)
  | 0b1111 => some (.dp .mvns dn m)
  | _ => none

def memOpOfRegForm : Nat → Option MemOp
  | 0b000 => some .str
  | 0b001 => some .strh
  | 0b010 => some .strb
  | 0b100 => some .ldr
  | 0b101 => some .ldrh
  | 0b110 => some .ldrb
  | _ => none

/-- Decode a 16-bit encoding. `none` for every encoding outside the accepted set,
including the first halfword of any 32-bit encoding. -/
def decode16 (hw : BitVec 16) : Option Instr :=
  let op := hw.toNat
  if is32 hw then none
  else if op >>> 11 = 0b00000 then some (.lslImm (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b00001 then some (.lsrImm (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 9 = 0b0001100 then some (.addReg (low hw 0) (low hw 3) (low hw 6))
  else if op >>> 9 = 0b0001101 then some (.subReg (low hw 0) (low hw 3) (low hw 6))
  else if op >>> 9 = 0b0001110 then some (.addImm3 (low hw 0) (low hw 3) (bits hw 6 3))
  else if op >>> 9 = 0b0001111 then some (.subImm3 (low hw 0) (low hw 3) (bits hw 6 3))
  else if op >>> 11 = 0b00100 then some (.movImm (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b00101 then some (.cmpImm (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b00110 then some (.addImm8 (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b00111 then some (.subImm8 (low hw 8) (bits hw 0 8))
  else if op >>> 10 = 0b010000 then decodeDp hw
  else if op >>> 8 = 0b01000110 then
    -- MOV Rd, Rm (T1): D:Rd = bits 7, 2:0; Rm = bits 6:3.
    let d := ((op >>> 7) % 2) * 8 + op % 8
    let m := (op >>> 3) % 16
    -- PC and SP are excluded on both sides: writing PC is a branch, writing SP
    -- needs the SP alignment rule, and reading PC is not used by the artifact.
    if d = 15 ∨ d = 13 ∨ m = 15 ∨ m = 13 then none
    else some (.movHi ⟨d, by omega⟩ ⟨m, by omega⟩)
  else if op >>> 11 = 0b01001 then some (.ldrLit (low hw 8) (bits hw 0 8))
  else if op >>> 12 = 0b0101 then
    (memOpOfRegForm ((op >>> 9) % 8)).map fun o => .memReg o (low hw 0) (low hw 3) (low hw 6)
  else if op >>> 11 = 0b01100 then some (.memImm .str (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b01101 then some (.memImm .ldr (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b01110 then some (.memImm .strb (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b01111 then some (.memImm .ldrb (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b10000 then some (.memImm .strh (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b10001 then some (.memImm .ldrh (low hw 0) (low hw 3) (bits hw 6 5))
  else if op >>> 11 = 0b10010 then some (.strSp (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b10011 then some (.ldrSp (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b10101 then some (.addRdSp (low hw 8) (bits hw 0 8))
  else if op >>> 7 = 0b101100000 then some (.addSp (bits hw 0 7))
  else if op >>> 7 = 0b101100001 then some (.subSp (bits hw 0 7))
  else if op >>> 6 = 0b1011001010 then some (.uxth (low hw 0) (low hw 3))
  else if op >>> 9 = 0b1011010 then
    if op % 512 = 0 then none   -- empty list is UNPREDICTABLE
    else some (.push (bits hw 0 8) ((op >>> 8) % 2 = 1))
  else if op >>> 9 = 0b1011110 then
    if op % 512 = 0 then none
    else some (.pop (bits hw 0 8) ((op >>> 8) % 2 = 1))
  else if op >>> 11 = 0b11000 then
    if op % 256 = 0 ∨ ((op % 256) >>> ((op >>> 8) % 8)) % 2 = 1 then none
    else some (.stm (low hw 8) (bits hw 0 8))
  else if op >>> 11 = 0b11001 then
    if op % 256 = 0 then none else some (.ldm (low hw 8) (bits hw 0 8))
  else if op >>> 12 = 0b1101 then
    if (op >>> 8) % 16 ≥ 14 then none
    else some (.bcond (bits hw 8 4) (bits hw 0 8))
  else if op >>> 11 = 0b11100 then some (.b (bits hw 0 11))
  else none

/-- Decode BL from its two halfwords (T1: `11110 S imm10`, `11 J1 1 J2 imm11`).
`I1 = NOT(J1 XOR S)`, `I2 = NOT(J2 XOR S)`. -/
def decodeBL (hw1 hw2 : BitVec 16) : Option Instr :=
  if hw1.toNat >>> 11 = 0b11110 ∧ (hw2.toNat >>> 14) % 4 = 0b11 ∧ (hw2.toNat >>> 12) % 2 = 1 then
    let s := (hw1.toNat >>> 10) % 2
    let j1 := (hw2.toNat >>> 13) % 2
    let j2 := (hw2.toNat >>> 11) % 2
    let i1 := 1 - (j1 ^^^ s)
    let i2 := 1 - (j2 ^^^ s)
    let v := (((s * 2 + i1) * 2 + i2) * 1024 + hw1.toNat % 1024) * 2048 + hw2.toNat % 2048
    some (.bl (BitVec.ofNat 25 (v * 2)))
  else none

/-- Decode the instruction whose first halfword is `hw1`; `hw2` is the following
halfword, used only by 32-bit encodings. -/
def decode (hw1 hw2 : BitVec 16) : Option Instr :=
  if is32 hw1 then decodeBL hw1 hw2 else decode16 hw1

/-! Decoder spot checks against encodings in the artifact (llvm-objdump). -/

example : decode 0x0a12#16 0 = some (.lsrImm 2 2 8) := by decide         -- lsrs r2, r2, #8
example : decode 0x0021#16 0 = some (.lslImm 1 4 0) := by decide         -- movs r1, r4
example : decode 0x4148#16 0 = some (.dp .adcs 0 1) := by decide         -- adcs r0, r1
example : decode 0x4364#16 0 = some (.dp .muls 4 4) := by decide         -- muls r4, r4, r4
example : decode 0x4264#16 0 = some (.dp .rsbs 4 4) := by decide         -- rsbs r4, r4, #0
example : decode 0x464d#16 0 = some (.movHi 5 9) := by decide            -- mov r5, r9
example : decode 0x4686#16 0 = some (.movHi 14 0) := by decide           -- mov lr, r0
example : decode 0x5d08#16 0 = some (.memReg .ldrb 0 1 4) := by decide   -- ldrb r0, [r1, r4]
example : decode 0x8838#16 0 = some (.memImm .ldrh 0 7 0) := by decide   -- ldrh r0, [r7]
example : decode 0xb5f0#16 0 = some (.push 0xf0 true) := by decide       -- push {r4-r7, lr}
example : decode 0xbdf0#16 0 = some (.pop 0xf0 true) := by decide        -- pop {r4-r7, pc}
example : decode 0xc80f#16 0 = some (.ldm 0 0x0f) := by decide           -- ldm r0, {r0-r3}
example : decode 0xd1fe#16 0 = some (.bcond 1 0xfe) := by decide         -- bne .
example : decode 0xb2ad#16 0 = some (.uxth 5 5) := by decide             -- uxth r5, r5
example : decode 0xf000#16 0xf800#16 = some (.bl 0) := by decide         -- bl .+4
example : decode 0xf7ff#16 0xfffe#16 = some (.bl 0x1fffffc) := by decide -- bl .  (offset -4)
-- Rejected: MOV PC, BX LR, ADD (high), ASRS, BICS, LDRSB, UDF, SVC, NOP, a Thumb-2 prefix.
example : decode 0x46f7#16 0 = none := by decide
example : decode 0x46e8#16 0 = none := by decide   -- mov r8, sp
example : decode 0xc103#16 0 = none := by decide   -- stm r1!, {r0, r1}: base in list
example : decode 0xc50f#16 0 = some (.stm 5 0x0f) := by decide   -- stm r5!, {r0-r3}
example : decode 0x4770#16 0 = none := by decide
example : decode 0x4448#16 0 = none := by decide
example : decode 0x1008#16 0 = none := by decide
example : decode 0x4388#16 0 = none := by decide
example : decode 0x5608#16 0 = none := by decide
example : decode 0xde00#16 0 = none := by decide
example : decode 0xdf00#16 0 = none := by decide
example : decode 0xbf00#16 0 = none := by decide
example : decode 0xe800#16 0 = none := by decide
example : decode 0xf3ef#16 0x8000#16 = none := by decide   -- MRS

end M0Crypto.Thumb
