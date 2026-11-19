import SafegcdTermination.LoopCounter
import M0Crypto.Release.Field25519Canon

namespace SafegcdTermination.InitCode

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.LoopCounter (initialCount)
open M0Crypto.Thumb

def returnAt : Nat := frameBytes - 4

def copyBlock : List Instr := [.ldm 1 60, .stm 0 60]

def copyWords : List Instr := copyBlock ++ copyBlock

def copyPrefix : List Instr := copyWords ++ [.subImm8 0 32]

def canonBody : List Instr := copyPrefix ++ M0Crypto.Release.Field25519Canon.body

def saveAndCall : List Instr := [.movHi 3 14, storeSp 3 returnAt, storeSp 0 outputAt, withSp 0 temp]

def clearIterations : Nat := 4*vectorBytes / 16

def clearSetup : List Instr :=
  [.movHi 0 13, .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0,
   .movImm 5 (BitVec.ofNat 8 clearIterations)]

def clearBlock : List Instr := [.stm 0 30, .subImm8 5 1]

def clearCode : List Instr := clearSetup ++ clearBlock ++ [.bcond 1 (BitVec.ofInt 8 (-4))]

def putInitialWords : List Instr :=
  [.movImm 0 1, storeSp 0 bankE, storeSp 0 deltaAt, .movImm 0 (BitVec.ofNat 8 initialCount), storeSp 0 counterAt]

def splitColumn (i : Nat) : List Instr :=
  [loadSp 0 (temp+4*i), .uxth 1 0, .lsrImm 0 0 16, storeSp 1 (bankG+8*i), storeSp 0 (bankG+8*i+4)]

def putInput : List Instr := (List.range 8).flatMap splitColumn

def putPrime : List Instr :=
  [.movHi 7 13, .movImm 0 0, .dp .mvns 0 0, .uxth 0 0, .lslImm 1 0 0, .lslImm 2 0 0, .lslImm 3 0 0,
   .subImm8 0 18, .stm 7 15, .lslImm 0 1 0, .stm 7 15, .stm 7 15, .lsrImm 3 3 1, .stm 7 15]

def tail : List Instr := putInitialWords ++ putInput ++ putPrime

def initCode (entry canon : Nat) : List Instr :=
  saveAndCall ++ [callTo (entry + seqSize saveAndCall) canon] ++ clearCode ++ tail

end SafegcdTermination.InitCode
