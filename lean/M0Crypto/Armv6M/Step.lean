import M0Crypto.Armv6M.Decode
import M0Crypto.Armv6M.Memory

/-!
Execution semantics for the pilot subset, transcribed from the ARMv6-M ARM
pseudocode (`AddWithCarry`, `Shift_C`, `ROR_C`, and the per-instruction
operation blocks).

The executed trace records, for every step, the instruction address, the decoded
instruction and its data accesses (kind, address, width).

Memory assumptions: data accesses go to ordinary little-endian RAM
(AIRCR.ENDIANNESS = 0), are not bus-faulted, and never alias the immutable code
region. On ARMv6-M `MemU` behaves as `MemA` (DDI 0419E B2-218): an unaligned
access takes HardFault. The model stops with `Fault.unaligned` instead of
modelling exception entry.
-/

namespace M0Crypto.Armv6M

/-- ARMv6-M `AddWithCarry(x, y, carry_in)` returning `(result, carry_out, overflow)`. -/
def addWithCarry (x y : Word) (carryIn : Bool) : Word × Bool × Bool :=
  let unsignedSum := x.toNat + y.toNat + carryIn.toNat
  let signedSum := x.toInt + y.toInt + (carryIn.toNat : Int)
  let result := BitVec.ofNat 32 unsignedSum
  (result, decide (result.toNat ≠ unsignedSum), decide (result.toInt ≠ signedSum))

/-- ARMv6-M `Shift_C(value, SRType_ROR, amount, carry_in)`.
`amount = 0` returns the input unchanged; otherwise `ROR_C` with `m = amount MOD 32`,
`result = LSR(x, m) OR LSL(x, 32 - m)`, `carry_out = result<31>`. -/
def rorC (x : Word) (amount : Nat) (carryIn : Bool) : Word × Bool :=
  if amount = 0 then (x, carryIn)
  else
    let m := amount % 32
    let result := (x >>> m) ||| (x <<< (32 - m))
    (result, result.msb)

/-! Boundary checks of the helper transcriptions (DDI 0419E pp. A2-33, A2-34, A6-95). -/

-- Unsigned carry out, no signed overflow.
example : addWithCarry 0xffffffff#32 1#32 false = (0#32, true, false) := by decide
-- Signed overflow, no carry.
example : addWithCarry 0x7fffffff#32 1#32 false = (0x80000000#32, false, true) := by decide
-- Both: 0x80000000 + 0x80000000.
example : addWithCarry 0x80000000#32 0x80000000#32 false = (0#32, true, true) := by decide
-- Amount 0 (from R[m]<7:0> = 0): value and carry_in unchanged.
example : rorC 0x80000001#32 0 false = (0x80000001#32, false) := by decide
-- Nonzero multiple of 32: value unchanged, carry_out = bit 31.
example : rorC 0x80000001#32 32 false = (0x80000001#32, true) := by decide
example : rorC 0x00000001#32 64 true = (0x00000001#32, false) := by decide
-- 33 behaves as 1; carry_out is the new bit 31.
example : rorC 0x00000001#32 33 false = (0x80000000#32, true) := by decide
-- Maximum bottom-byte amount 255 = 7 * 32 + 31.
example : rorC 0x00000002#32 255 false = (0x00000004#32, false) := by decide

/-- `SP + ZeroExtend(imm8:'00', 32)` for the SP-relative T2 encodings. -/
def spAddr (s : State) (imm8 : BitVec 8) : Word :=
  s.regs 13 + BitVec.ofNat 32 (imm8.toNat * 4)

inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- One data-memory access: kind, byte address and width in bytes. -/
structure Access where
  kind : AccessKind
  addr : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- Data accesses an instruction makes in state `s`. -/
def Instr.accesses (i : Instr) (s : State) : List Access :=
  match i with
  | .ldrSp _ imm8 => [⟨.read, (spAddr s imm8).toNat, 4⟩]
  | .strSp _ imm8 => [⟨.write, (spAddr s imm8).toNat, 4⟩]
  | _ => []

/-- All data accesses of `i` in `s` are naturally aligned. -/
def Instr.aligned (i : Instr) (s : State) : Bool :=
  (i.accesses s).all fun a => a.addr % a.width == 0

/-- Execute one decoded instruction. Advances PC by 2 (all supported encodings are 16-bit
and none writes PC). -/
def exec (i : Instr) (s : State) : State :=
  let s' :=
    match i with
    | .movsImm d imm8 =>
      -- (imm32, carry) = (ZeroExtend(imm8, 32), APSR.C); V unchanged.
      let r := imm8.setWidth 32
      (s.setReg d.toReg r).setNZ r
    | .addsReg d n m =>
      let (r, c, v) := addWithCarry (s.reg n) (s.reg m) false
      { ((s.setReg d.toReg r).setNZ r) with c := c, v := v }
    | .eorsReg dn m =>
      -- shift_t = LSL, shift_n = 0, so the shifter carry is APSR.C; V unchanged.
      let r := s.reg dn ^^^ s.reg m
      (s.setReg dn.toReg r).setNZ r
    | .rorsReg dn m =>
      -- shift_n = UInt(R[m]<7:0>); V unchanged.
      let (r, c) := rorC (s.reg dn) ((s.reg m).toNat % 256) s.c
      { ((s.setReg dn.toReg r).setNZ r) with c := c }
    | .ldrSp t imm8 =>
      -- R[t] = MemU[address, 4]; flags unchanged.
      s.setReg t.toReg (read32 s.mem (spAddr s imm8))
    | .strSp t imm8 =>
      -- MemU[address, 4] = R[t]; flags unchanged.
      { s with mem := write32 s.mem (spAddr s imm8) (s.reg t) }
  s'.setReg 15 (s.pc + 2#32)

/-- An immutable code region: `bytes` are linked at address `base`. -/
structure Code where
  base : Nat
  bytes : List (BitVec 8)

/-- Little-endian, halfword-aligned instruction fetch. `none` outside the region. -/
def Code.fetch (c : Code) (addr : Nat) : Option (BitVec 16) :=
  if addr % 2 = 0 ∧ c.base ≤ addr ∧ addr + 2 ≤ c.base + c.bytes.length then
    let o := addr - c.base
    some (c.bytes[o + 1]! ++ c.bytes[o]!)
  else none

inductive Fault where
  | fetch (pc : Nat)
  | unsupported16 (pc : Nat) (hw : BitVec 16)
  | unsupported32 (pc : Nat) (hw : BitVec 16)
  | unaligned (pc : Nat)
  deriving DecidableEq, Repr

/-- One trace event: instruction address, decoded instruction and data accesses. -/
structure Event where
  pc : Nat
  instr : Instr
  accesses : List Access
  deriving DecidableEq, Repr

def step (c : Code) (s : State) : Except Fault (State × Event) :=
  let pc := s.pc.toNat
  match c.fetch pc with
  | none => .error (.fetch pc)
  | some hw =>
    match decode hw with
    | .ok i =>
      if i.aligned s then .ok (exec i s, ⟨pc, i, i.accesses s⟩)
      else .error (.unaligned pc)
    | .unsupported16 hw => .error (.unsupported16 pc hw)
    | .unsupported32 hw => .error (.unsupported32 pc hw)

/-- Run exactly `n` steps, returning the final state and the executed trace. -/
def run (c : Code) : Nat → State → Except Fault (State × List Event)
  | 0, s => .ok (s, [])
  | n + 1, s =>
    match step c s with
    | .error e => .error e
    | .ok (s', e) =>
      match run c n s' with
      | .error e' => .error e'
      | .ok (s'', es) => .ok (s'', e :: es)

end M0Crypto.Armv6M
