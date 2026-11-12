import M0Crypto.Thumb.Decode
import M0Crypto.Armv6M.Step

/-!
Execution semantics of the whole-function Thumb model, transcribed from the
ARMv6-M ARM pseudocode (DDI 0419E §A2.2 `AddWithCarry`, `Shift_C`; §A6.7 the
per-instruction operation blocks; §A5.2 `BXWritePC`/`LoadWritePC`).

Scope and assumptions (in addition to `M0Crypto.Armv6M.State`):
* Thumb state, one execution thread, no exceptions or interrupts. Faults are not
  modelled as exception entry: the step function stops with a `Fault`.
* **One memory for code and data.** Instructions are fetched from `State.mem`, so
  literal-pool loads read the code bytes. Executing a function correctly therefore
  needs a separate proof that it never writes its own code; the whole-function
  theorems state that every write goes to the caller's buffers or the stack.
* Memory is ordinary little-endian RAM: no bus faults, no device side effects.
  On ARMv6-M every access must be naturally aligned (`MemU` behaves as `MemA`);
  an unaligned access stops with `Fault.unaligned`.
* `PC` reads as the instruction address + 4 where the pseudocode reads it.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

/-! ## Memory -/

def read8 (m : Mem) (a : Word) : Word := (m a).setWidth 32

def read16 (m : Mem) (a : Word) : Word := (m (a + 1#32) ++ m a).setWidth 32

def write8 (m : Mem) (a : Word) (v : Word) : Mem := fun x =>
  if x = a then v.extractLsb' 0 8 else m x

def write16 (m : Mem) (a : Word) (v : Word) : Mem := fun x =>
  if x = a then v.extractLsb' 0 8
  else if x = a + 1#32 then v.extractLsb' 8 8
  else m x

/-- Halfword fetch (little-endian) used for instructions. -/
def fetch16 (m : Mem) (a : Word) : BitVec 16 := m (a + 1#32) ++ m a

/-! ## Helpers -/

/-- `Shift_C(x, SRType_LSL, n, c)` for `n < 32`. -/
def lslC (x : Word) (n : Nat) (c : Bool) : Word × Bool :=
  if n = 0 then (x, c) else (x <<< n, x.getLsbD (32 - n))

/-- `Shift_C(x, SRType_LSR, n, c)` for `1 ≤ n ≤ 32`. -/
def lsrC (x : Word) (n : Nat) : Word × Bool :=
  (x >>> n, x.getLsbD (n - 1))

/-- `ConditionPassed()` for cond < 14 (DDI 0419E §A6.3). -/
def condPassed (cond : BitVec 4) (s : State) : Bool :=
  match cond.toNat with
  | 0 => s.z
  | 1 => !s.z
  | 2 => s.c
  | 3 => !s.c
  | 4 => s.n
  | 5 => !s.n
  | 6 => s.v
  | 7 => !s.v
  | 8 => s.c && !s.z
  | 9 => !s.c || s.z
  | 10 => s.n == s.v
  | 11 => s.n != s.v
  | 12 => !s.z && s.n == s.v
  | 13 => s.z || s.n != s.v
  | _ => false

/-- Low registers in a list, in ascending order (the transfer order). -/
def listRegs (l : BitVec 8) : List LowReg :=
  (List.finRange 8).filter fun i => l.getLsbD i.val

/-- Number of registers in a list (`BitCount`), defined from the transfer list so the
two cannot disagree. -/
def bitCount (l : BitVec 8) : Nat := (listRegs l).length

/-- Set N, Z from `r` and also C (V unchanged). -/
def _root_.M0Crypto.Armv6M.State.setNZC (s : State) (r : Word) (c : Bool) : State :=
  { s.setNZ r with c := c }

/-- Set N, Z, C, V. -/
def _root_.M0Crypto.Armv6M.State.setNZCV (s : State) (r : Word) (c v : Bool) : State :=
  { s.setNZ r with c := c, v := v }

def _root_.M0Crypto.Armv6M.State.sp (s : State) : Word := s.regs 13

/-- Write `r ← x` with NZCV from `AddWithCarry(a, b, cin)`. -/
def addFlags (s : State) (d : Reg) (a b : Word) (cin : Bool) (write : Bool := true) : State :=
  let (r, c, v) := addWithCarry a b cin
  let s := if write then s.setReg d r else s
  s.setNZCV r c v

/-! ## Accesses, events and faults -/

inductive Kind where
  | read
  | write
  deriving DecidableEq, Repr

/-- One data access: kind, address and width in bytes. -/
structure Access where
  kind : Kind
  addr : Word
  width : Nat
  deriving DecidableEq, Repr

def Access.aligned (a : Access) : Bool := a.addr.toNat % a.width == 0

/-- One trace event: instruction address, decoded instruction and its data accesses. -/
structure Event where
  pc : Word
  instr : Instr
  accesses : List Access
  deriving DecidableEq, Repr

inductive Fault where
  /-- PC is odd (cannot happen from a valid entry; kept for totality). -/
  | pcOdd (pc : Word)
  /-- The halfword(s) at PC are not an accepted encoding. -/
  | undefined (pc : Word)
  | unaligned (pc : Word)
  /-- POP {..., PC} loaded an address with bit 0 clear (EPSR.T = 0 → HardFault). -/
  | interworking (pc : Word)
  /-- `runUntil` ran out of fuel. -/
  | fuel
  deriving DecidableEq, Repr

/-! ## Load and store multiple -/

/-- Store `regs` (values) at ascending word addresses from `a`. -/
def storeWords (m : Mem) : Word → List Word → Mem
  | _, [] => m
  | a, v :: vs => storeWords (write32 m a v) (a + 4#32) vs

/-- Accesses of a transfer of `n` words from `a`. -/
def wordAccesses (k : Kind) (a : Word) (n : Nat) : List Access :=
  (List.range n).map fun i => ⟨k, a + BitVec.ofNat 32 (4 * i), 4⟩

/-- Load the registers `rs` from ascending word addresses from `a`. -/
def loadRegs (s : State) : Word → List Reg → State
  | _, [] => s
  | a, r :: rs => loadRegs (s.setReg r (read32 s.mem a)) (a + 4#32) rs

/-! ## Single instruction -/

/-- Data accesses of `i` in state `s` (before execution). -/
def Instr.accesses (i : Instr) (s : State) : List Access :=
  let pc := s.pc
  match i with
  | .ldrLit _ imm8 =>
    [⟨.read, ((pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm8.toNat * 4), 4⟩]
  | .memReg op _ n m =>
    [⟨if op.isLoad then .read else .write, s.reg n + s.reg m, op.width⟩]
  | .memImm op _ n imm5 =>
    [⟨if op.isLoad then .read else .write,
      s.reg n + BitVec.ofNat 32 (imm5.toNat * op.width), op.width⟩]
  | .strSp _ imm8 => [⟨.write, s.sp + BitVec.ofNat 32 (imm8.toNat * 4), 4⟩]
  | .ldrSp _ imm8 => [⟨.read, s.sp + BitVec.ofNat 32 (imm8.toNat * 4), 4⟩]
  | .push l lr =>
    let n := bitCount l + lr.toNat
    wordAccesses .write (s.sp - BitVec.ofNat 32 (4 * n)) n
  | .pop l pc => wordAccesses .read s.sp (bitCount l + pc.toNat)
  | .stm n l => wordAccesses .write (s.reg n) (bitCount l)
  | .ldm n l => wordAccesses .read (s.reg n) (bitCount l)
  | _ => []

/-- Execute `i`, whose accesses are known to be aligned. Returns the next state;
`POP {..., PC}` with an even target address faults. -/
def Instr.exec (i : Instr) (s : State) : Except Fault State :=
  let pc := s.pc
  let next := s.setReg 15 (pc + BitVec.ofNat 32 i.size)
  let r := fun (x : LowReg) => s.reg x
  match i with
  | .lslImm d m imm5 =>
    let (x, c) := lslC (r m) imm5.toNat s.c
    .ok ((next.setReg d.toReg x).setNZC x c)
  | .lsrImm d m imm5 =>
    let (x, c) := lsrC (r m) (if imm5.toNat = 0 then 32 else imm5.toNat)
    .ok ((next.setReg d.toReg x).setNZC x c)
  | .addReg d n m => .ok (addFlags next d.toReg (r n) (r m) false)
  | .subReg d n m => .ok (addFlags next d.toReg (r n) (~~~(r m)) true)
  | .addImm3 d n imm3 => .ok (addFlags next d.toReg (r n) (imm3.setWidth 32) false)
  | .subImm3 d n imm3 => .ok (addFlags next d.toReg (r n) (~~~(imm3.setWidth 32)) true)
  | .movImm d imm8 =>
    let x := imm8.setWidth 32
    .ok ((next.setReg d.toReg x).setNZ x)
  | .cmpImm n imm8 => .ok (addFlags next 0 (r n) (~~~(imm8.setWidth 32)) true false)
  | .addImm8 dn imm8 => .ok (addFlags next dn.toReg (r dn) (imm8.setWidth 32) false)
  | .subImm8 dn imm8 => .ok (addFlags next dn.toReg (r dn) (~~~(imm8.setWidth 32)) true)
  | .dp op dn m =>
    -- Field roles: bits 2:0 = `dn`, bits 5:3 = `m`. For RSBS these are Rd and Rn;
    -- for CMP and TST, Rn and Rm; for MULS, Rdm and Rn.
    match op with
    | .ands => let x := r dn &&& r m; .ok ((next.setReg dn.toReg x).setNZ x)
    | .eors => let x := r dn ^^^ r m; .ok ((next.setReg dn.toReg x).setNZ x)
    | .orrs => let x := r dn ||| r m; .ok ((next.setReg dn.toReg x).setNZ x)
    | .mvns => let x := ~~~(r m); .ok ((next.setReg dn.toReg x).setNZ x)
    | .muls => let x := r m * r dn; .ok ((next.setReg dn.toReg x).setNZ x)
    | .tst => .ok (next.setNZ (r dn &&& r m))
    | .adcs => .ok (addFlags next dn.toReg (r dn) (r m) s.c)
    | .rsbs => .ok (addFlags next dn.toReg (~~~(r m)) 0#32 true)
    | .cmp => .ok (addFlags next 0 (r dn) (~~~(r m)) true false)
    | .rors =>
      let (x, c) := rorC (r dn) ((r m).toNat % 256) s.c
      .ok ((next.setReg dn.toReg x).setNZC x c)
  | .movHi d m => .ok (next.setReg d (s.regs m))
  | .ldrLit t imm8 =>
    let a := ((pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm8.toNat * 4)
    .ok (next.setReg t.toReg (read32 s.mem a))
  | .memReg op t n m => .ok (memOp next op t (r n + r m))
  | .memImm op t n imm5 => .ok (memOp next op t (r n + BitVec.ofNat 32 (imm5.toNat * op.width)))
  | .strSp t imm8 =>
    .ok { next with mem := write32 s.mem (s.sp + BitVec.ofNat 32 (imm8.toNat * 4)) (r t) }
  | .ldrSp t imm8 =>
    .ok (next.setReg t.toReg (read32 s.mem (s.sp + BitVec.ofNat 32 (imm8.toNat * 4))))
  | .addRdSp d imm8 => .ok (next.setReg d.toReg (s.sp + BitVec.ofNat 32 (imm8.toNat * 4)))
  | .addSp imm7 => .ok (next.setReg 13 (s.sp + BitVec.ofNat 32 (imm7.toNat * 4)))
  | .subSp imm7 => .ok (next.setReg 13 (s.sp - BitVec.ofNat 32 (imm7.toNat * 4)))
  | .uxth d m => .ok (next.setReg d.toReg ((r m).setWidth 16 |>.setWidth 32))
  | .push l lr =>
    let n := bitCount l + lr.toNat
    let a := s.sp - BitVec.ofNat 32 (4 * n)
    let vals := (listRegs l).map r ++ (if lr then [s.regs 14] else [])
    .ok ({ next with mem := storeWords s.mem a vals }.setReg 13 a)
  | .pop l pcBit =>
    let s1 := loadRegs next s.sp ((listRegs l).map LowReg.toReg)
    let a := s.sp + BitVec.ofNat 32 (4 * bitCount l)
    let s2 := s1.setReg 13 (s.sp + BitVec.ofNat 32 (4 * (bitCount l + pcBit.toNat)))
    if pcBit then
      let target := read32 s.mem a
      if target.getLsbD 0 then .ok (s2.setReg 15 (target &&& ~~~1#32))
      else .error (.interworking pc)
    else .ok s2
  | .stm n l =>
    let vals := (listRegs l).map r
    .ok ({ next with mem := storeWords s.mem (r n) vals }.setReg n.toReg
      (r n + BitVec.ofNat 32 (4 * bitCount l)))
  | .ldm n l =>
    let s1 := loadRegs next (r n) ((listRegs l).map LowReg.toReg)
    if l.getLsbD n.val then .ok s1
    else .ok (s1.setReg n.toReg (r n + BitVec.ofNat 32 (4 * bitCount l)))
  | .bcond cond imm8 =>
    if condPassed cond s then
      .ok (s.setReg 15 (pc + 4#32 + (imm8 ++ 0#1).signExtend 32))
    else .ok next
  | .b imm11 => .ok (s.setReg 15 (pc + 4#32 + (imm11 ++ 0#1).signExtend 32))
  | .bl imm25 =>
    .ok ((s.setReg 14 ((pc + 4#32) ||| 1#32)).setReg 15 (pc + 4#32 + imm25.signExtend 32))
where
  /-- One non-multiple load or store at `a`, applied to `next` (PC already advanced). -/
  memOp (next : State) (op : MemOp) (t : LowReg) (a : Word) : State :=
    let v := next.reg t
    match op with
    | .str => { next with mem := write32 next.mem a v }
    | .strh => { next with mem := write16 next.mem a v }
    | .strb => { next with mem := write8 next.mem a v }
    | .ldr => next.setReg t.toReg (read32 next.mem a)
    | .ldrh => next.setReg t.toReg (read16 next.mem a)
    | .ldrb => next.setReg t.toReg (read8 next.mem a)

/-! ## Step and run -/

/-- Fetch, decode and execute one instruction. -/
def step (s : State) : Except Fault (State × Event) :=
  let pc := s.pc
  if pc.getLsbD 0 then .error (.pcOdd pc)
  else
    match decode (fetch16 s.mem pc) (fetch16 s.mem (pc + 2#32)) with
    | none => .error (.undefined pc)
    | some i =>
      let acc := i.accesses s
      if acc.all Access.aligned then
        match i.exec s with
        | .ok s' => .ok (s', ⟨pc, i, acc⟩)
        | .error e => .error e
      else .error (.unaligned pc)

/-- Run until PC = `stop` (checked before each step), with at most `fuel` steps.
Returns the final state and the trace of executed events. -/
def runUntil (stop : Word) : Nat → State → Except Fault (State × List Event)
  | fuel, s =>
    if s.pc = stop then .ok (s, [])
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step s with
        | .error e => .error e
        | .ok (s', e) =>
          match runUntil stop n s' with
          | .error e' => .error e'
          | .ok (s'', es) => .ok (s'', e :: es)

/-! ## Code placement and written bytes -/

/-- The bytes `bytes` are in memory at `base`. -/
def CodeAt (m : Mem) (base : Word) (bytes : List (BitVec 8)) : Prop :=
  ∀ i (h : i < bytes.length), m (base + BitVec.ofNat 32 i) = bytes[i]

/-- Byte addresses written by an access list. -/
def Writes (acc : List Access) (y : Word) : Prop :=
  ∃ a ∈ acc, a.kind = .write ∧ ∃ k, k < a.width ∧ y = a.addr + BitVec.ofNat 32 k

/-! Helper checks against the pseudocode boundary cases. -/

-- LSRS #32 (imm5 = 0): result 0, carry = bit 31.
example : lsrC 0x80000000#32 32 = (0#32, true) := by decide
example : lslC 0x80000001#32 1 false = (2#32, true) := by decide
example : lslC 0x80000001#32 0 true = (0x80000001#32, true) := by decide
example : bitCount 0xf0#8 = 4 := by decide
/-- HI (cond 8) passes with C set and Z clear. -/
example : condPassed 8 ⟨fun _ => 0, false, false, true, false, fun _ => 0⟩ = true := by decide
example : condPassed 8 ⟨fun _ => 0, false, true, true, false, fun _ => 0⟩ = false := by decide

end M0Crypto.Thumb
