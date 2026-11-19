import SafegcdTermination.InitCode
import SafegcdTermination.Run43
import M0Crypto.Release.Field25519AddSub
import M0Crypto.Release.Field25519Select

namespace SafegcdTermination.FinalCode

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.InitCode (returnAt)
open M0Crypto.Thumb

def finalRow : RowCall := ⟨bankF, bankF, bankF, 0, true⟩

def packColumn (i : Nat) : List Instr :=
  [loadSp 0 (bankF+8*i), loadSp 1 (bankF+8*i+4), .lslImm 1 1 16,
   .dp .orrs 0 1, storeSp 0 (bankF+4*i)]

def pack : List Instr := (List.range 8).flatMap packColumn

def clearZero : List Instr :=
  [withSp 0 bankG, .movImm 1 0] ++ (List.range 8).map (fun i => .memImm .str 1 0 (BitVec.ofNat 5 i))

def subArgs : List Instr := [withSp 0 bankE, withSp 1 bankG, .movHi 2 13]

def selectArgs : List Instr :=
  [loadSp 3 (temp+vectorBytes-4), .asrImm 3 3 31,
   loadSp 0 outputAt, .movHi 1 13, withSp 2 bankE]

def ret : List Instr := [loadSp 3 returnAt, .bx 3]

def subBody := M0Crypto.Release.Field25519AddSub.feSubBody

def selectBody : List Instr := [.movHi 7 3] ++ M0Crypto.Release.Field25519Select.selBody

def tail (q : Targets) (off sub select : Nat) : List Instr :=
  let p := prepareFold finalRow
  let foldOff := off+seqSize p
  let s := pack ++ clearZero ++ subArgs
  let subOff := foldOff+4+seqSize s
  let selOff := subOff+4+seqSize selectArgs
  p ++ [callTo foldOff q.fold] ++ s ++ [callTo subOff sub] ++ selectArgs ++ [callTo selOff select] ++ ret

end SafegcdTermination.FinalCode
