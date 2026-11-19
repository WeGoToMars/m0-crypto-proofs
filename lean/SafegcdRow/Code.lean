import M0Crypto.Thumb.Diagnose
import SafegcdRow.Artifact
import SafegcdRow.ExactArtifact

/-! Instruction layout of the shared sparse row, in the private calling convention
documented in row.S. All spans are derived from the instruction lists. -/

namespace SafegcdRow
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

def prologue (modular : Bool := true) : List Instr :=
  [.movHi 12 14, .movHi 7 0, .movHi 8 1, .movHi 10 2, .movHi 2 3, .movHi 3 4] ++ (if modular then
    [.movHi 14 5, .movImm 6 19, .dp .muls 6 5, .dp .rsbs 6 6, .movHi 11 6] else []) ++ [.movImm 5 0]

def accumulate (i : BitVec 5) : List Instr :=
  [.movHi 6 8, .memImm .ldr 0 6 i, .movHi 6 10, .memImm .ldr 1 6 i,
   .dp .muls 0 2, .dp .muls 1 3, .addReg 0 0 1, .addReg 0 0 5]

def correction (i : BitVec 5) : List Instr :=
  if i = 0#5 then [.movHi 6 11, .addReg 0 0 6]
  else if i = 15#5 then [.movHi 6 14, .lslImm 6 6 15, .addReg 0 0 6] else []

def splitAccumulator : List Instr := [.asrImm 5 0 16, .uxth 0 0]

def emitShifted (i : BitVec 5) : List Instr :=
  [.lslImm 1 0 2, .dp .orrs 1 4, .uxth 1 1, .memImm .str 1 7 i, .lsrImm 4 0 14]

def correctionFor (i : BitVec 5) (modular : Bool) : List Instr :=
  if modular then correction i else []

def column (i : Nat) (modular : Bool := true) : List Instr :=
  accumulate (BitVec.ofNat 5 i) ++ correctionFor (BitVec.ofNat 5 i) modular ++ splitAccumulator ++
    (if i = 0 then [.lsrImm 4 0 14] else emitShifted (BitVec.ofNat 5 (i - 1)))

def finish : List Instr := [.lslImm 5 5 2, .dp .orrs 4 5, .memImm .str 4 7 16]

def body (modular : Bool := true) : List Instr :=
  prologue modular ++ (List.range 17).flatMap (fun i => column i modular) ++ finish

def rowBytes (modular : Bool) : List (BitVec 8) := if modular then bytes else ExactArtifact.bytes

theorem body_matches : seqAt bytes 0 body = true := by decide +kernel

theorem body_falls : body.all Instr.falls = true := by decide +kernel

/-- The row uses the ARMv6-M T1 BX form with Rm=12. In this pilot only that
form extends the release decoder, at the one instruction after the body. -/
def returnOffset (modular : Bool := true) : Nat := seqSize (body modular)

def decodeReturn (code : List (BitVec 8)) (off : Nat) : Bool :=
  decide (off + 2 ≤ code.length) && (hwAt code off == 0x4760#16)

theorem return_matches : decodeReturn bytes returnOffset = true := by decide +kernel

theorem code_size : bytes.length = returnOffset + 2 := by decide +kernel

theorem body_matches_for (modular : Bool) : seqAt (rowBytes modular) 0 (body modular) = true := by
  cases modular
  · decide +kernel
  · exact body_matches

theorem body_falls_for (modular : Bool) : (body modular).all Instr.falls = true := by
  cases modular
  · decide +kernel
  · exact body_falls

theorem return_matches_for (modular : Bool) :
    decodeReturn (rowBytes modular) (returnOffset modular) = true := by
  cases modular
  · decide +kernel
  · exact return_matches

/-- ARMv6-M BXWritePC for the decoded BX r12, with the Thumb bit required.
The second component records the branch PC and its target. No data access. -/
def executeReturn (s : State) : Except Fault (State × (Word × Word)) :=
  let target := s.regs 12
  if target.getLsbD 0 then
    let pc := target &&& ~~~1#32
    .ok (s.setReg 15 pc, (s.pc, pc))
  else .error (.interworking s.pc)

def returnStep (code : List (BitVec 8)) (base : Word) (s : State) :
    Except Fault (State × (Word × Word)) :=
  if s.pc.getLsbD 0 then .error (.pcOdd s.pc)
  else if decodeReturn code (s.pc - base).toNat then executeReturn s
  else .error (.undefined s.pc)

def runRow (code : List (BitVec 8)) (base : Word) (s : State) (modular : Bool := true) :
    Except Fault (State × (List Event × (Word × Word))) :=
  match runH code base (body modular).length s with
  | .error e => .error e
  | .ok (t, events) =>
    match returnStep code base t with
    | .error e => .error e
    | .ok (u, ret) => .ok (u, events, ret)

end SafegcdRow
