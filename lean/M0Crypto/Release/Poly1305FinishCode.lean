import M0Crypto.Release.Frame
import M0Crypto.Release.Layout
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000
namespace M0Crypto.Release.Poly1305Finish
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

def header : List Instr := [.push 0xf0 true, .lslImm 7 0 0, .movHi 12 1, .movImm 6 0]
def carry : List Instr :=
  [.memImm .ldr 0 7 0, .addImm8 0 5, .memImm .ldr 0 7 1, .dp .adcs 0 6,
   .memImm .ldr 0 7 2, .dp .adcs 0 6, .memImm .ldr 0 7 3, .dp .adcs 0 6,
   .memImm .ldr 0 7 4, .dp .adcs 0 6, .lsrImm 0 0 2, .dp .rsbs 0 0, .movImm 1 5, .dp .ands 1 0]
def reduce : List Instr :=
  [.memImm .ldr 2 7 0, .addReg 2 2 1, .memImm .ldr 3 7 1, .dp .adcs 3 6,
   .memImm .ldr 4 7 2, .dp .adcs 4 6, .memImm .ldr 5 7 3, .dp .adcs 5 6]
def pad : List Instr :=
  [.memImm .ldr 0 7 12, .addReg 2 2 0, .memImm .ldr 0 7 13, .dp .adcs 3 0,
   .memImm .ldr 0 7 14, .dp .adcs 4 0, .memImm .ldr 0 7 15, .dp .adcs 5 0]
def stle (v : LowReg) (off : Nat) : List Instr :=
  [.memImm .strb v 1 (BitVec.ofNat 5 off), .lsrImm v v 8,
   .memImm .strb v 1 (BitVec.ofNat 5 (off+1)), .lsrImm v v 8,
   .memImm .strb v 1 (BitVec.ofNat 5 (off+2)), .lsrImm v v 8,
   .memImm .strb v 1 (BitVec.ofNat 5 (off+3))]
def emit : List Instr := [.movHi 1 12] ++ stle 2 0 ++ stle 3 4 ++ stle 4 8 ++ stle 5 12
def clear : List Instr := [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .movHi 12 0]
def arithmetic : List Instr := carry ++ reduce ++ pad

/-! ### Layout of `m0c_poly1305_finish`

Derived, as in `Poly1305BlocksCode`: the function starts at `Artifacts.Release.poly1305_finish`,
and each piece starts where the one before it ends, at `seqSize` bytes per list piece.
`Poly1305FinishCheck` checks each list piece at its offset in the artifact bytes. -/

/-- Function entry: `push {r4-r7, lr}` and the context and tag registers (`header`). -/
def entryAt : Nat := Artifacts.Release.poly1305_finish
/-- Carry, reduce and pad the accumulator. -/
def arithAt : Nat := entryAt + seqSize header
/-- Store the four tag words, byte by byte. -/
def emitAt : Nat := arithAt + seqSize arithmetic
/-- Zero the working registers. -/
def clearAt : Nat := emitAt + seqSize emit
/-- `pop {r4-r7, pc}`: the return. It is not in `clear`. -/
def popAt : Nat := clearAt + seqSize clear

end M0Crypto.Release.Poly1305Finish
