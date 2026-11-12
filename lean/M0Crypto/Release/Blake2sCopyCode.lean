import M0Crypto.Release.Layout
import M0Crypto.Thumb.SeqScan
import M0Crypto.Artifacts.Release

set_option maxRecDepth 100000

/-!
`m0c_blake2s_copy` as instruction lists. Every offset is derived from the generated entry
offset and `seqSize`; every piece is checked against the artifact bytes (`seqAt`, `instrAt`).
-/

namespace M0Crypto.Release.Blake2sCopyCode

open M0Crypto.Thumb
open M0Crypto.Release (brSize brImm8 brImm11)

abbrev B := Artifacts.Release.bytes

def cStart : Nat := Artifacts.Release.blake2s_copy

/-- `push {r4-r7,lr}; movs r4,#3`. -/
def proL : List Instr := [.push 0xF0 true, .movImm 4 3]
/-- Destination alignment test. -/
def tstD : List Instr := [.dp .tst 0 4]
/-- One byte of the alignment loop and of the tail loop. -/
def byteB : List Instr := [.memImm .ldrb 3 1 0, .memImm .strb 3 0 0, .addImm8 1 1, .addImm8 0 1, .subImm8 2 1]
def cmp4 : List Instr := [.cmpImm 2 4]
def tstS : List Instr := [.dp .tst 1 4]
def cmp16 : List Instr := [.cmpImm 2 16]
def w16B : List Instr := [.ldm 1 0x78, .stm 0 0x78, .subImm8 2 16]
def w4B : List Instr := [.memImm .ldr 3 1 0, .memImm .str 3 0 0, .addImm8 1 4, .addImm8 0 4, .subImm8 2 4]
def unalS : List Instr := [.lsrImm 5 2 2, .dp .ands 2 4, .movImm 3 1, .dp .tst 1 3]
def pbB : List Instr :=
  [.memImm .ldrb 3 1 0, .addImm3 7 1 1, .memImm .ldrh 6 7 0, .lslImm 6 6 8, .dp .orrs 3 6,
   .memImm .ldrb 6 1 3, .lslImm 6 6 24, .dp .orrs 3 6, .stm 0 8, .addImm8 1 4, .subImm8 5 1]
def phB : List Instr :=
  [.memImm .ldrh 3 1 0, .memImm .ldrh 6 1 1, .lslImm 6 6 16, .dp .orrs 3 6, .stm 0 8,
   .addImm8 1 4, .subImm8 5 1]
def cmp0 : List Instr := [.cmpImm 2 0]
def popL : Instr := .pop 0xF0 true

/-! ## Offsets (labels of `blake2s_copy.S`) -/

def oTst : Nat := cStart + seqSize proL
def oAlBr : Nat := oTst + seqSize tstD
def oAlBody : Nat := oAlBr + brSize
def oAlDone : Nat := oAlBody + seqSize byteB
def oAlBack : Nat := oAlDone + brSize
def oSel : Nat := oAlBack + brSize
def oSelBlo : Nat := oSel + seqSize cmp4
def oSelTst : Nat := oSelBlo + brSize
def oSelBne : Nat := oSelTst + seqSize tstS
def oW16 : Nat := oSelBne + brSize
def oW16Blo : Nat := oW16 + seqSize cmp16
def oW16Body : Nat := oW16Blo + brSize
def oW16Back : Nat := oW16Body + seqSize w16B
def oW4 : Nat := oW16Back + brSize
def oW4Blo : Nat := oW4 + seqSize cmp4
def oW4Body : Nat := oW4Blo + brSize
def oW4Back : Nat := oW4Body + seqSize w4B
def oUnal : Nat := oW4Back + brSize
def oUnalBeq : Nat := oUnal + seqSize unalS
def oPB : Nat := oUnalBeq + brSize
def oPBBne : Nat := oPB + seqSize pbB
def oPBBack : Nat := oPBBne + brSize
def oPH : Nat := oPBBack + brSize
def oPHBne : Nat := oPH + seqSize phB
def oBytes : Nat := oPHBne + brSize
def oBytesBeq : Nat := oBytes + seqSize cmp0
def oBL : Nat := oBytesBeq + brSize
def oBLBne : Nat := oBL + seqSize byteB
def oDone : Nat := oBLBne + brSize

theorem layout_end : oDone + 2 = cStart + 128 := by decide

theorem pro_at : seqAt B cStart proL = true := by rw [seqAt_eq_scan]; decide +kernel
theorem tstD_at : seqAt B oTst tstD = true := by rw [seqAt_eq_scan]; decide +kernel
theorem alBr_at : instrAt B oAlBr = some (.bcond 0 (brImm8 oAlBr oSel)) := by rw [instrAt_eq_scan]; decide +kernel
theorem alBody_at : seqAt B oAlBody byteB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem alDone_at : instrAt B oAlDone = some (.bcond 0 (brImm8 oAlDone oDone)) := by rw [instrAt_eq_scan]; decide +kernel
theorem alBack_at : instrAt B oAlBack = some (.b (brImm11 oAlBack oTst)) := by rw [instrAt_eq_scan]; decide +kernel
theorem sel_at : seqAt B oSel cmp4 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem selBlo_at : instrAt B oSelBlo = some (.bcond 3 (brImm8 oSelBlo oBytes)) := by rw [instrAt_eq_scan]; decide +kernel
theorem selTst_at : seqAt B oSelTst tstS = true := by rw [seqAt_eq_scan]; decide +kernel
theorem selBne_at : instrAt B oSelBne = some (.bcond 1 (brImm8 oSelBne oUnal)) := by rw [instrAt_eq_scan]; decide +kernel
theorem w16_at : seqAt B oW16 cmp16 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem w16Blo_at : instrAt B oW16Blo = some (.bcond 3 (brImm8 oW16Blo oW4)) := by rw [instrAt_eq_scan]; decide +kernel
theorem w16Body_at : seqAt B oW16Body w16B = true := by rw [seqAt_eq_scan]; decide +kernel
theorem w16Back_at : instrAt B oW16Back = some (.b (brImm11 oW16Back oW16)) := by rw [instrAt_eq_scan]; decide +kernel
theorem w4_at : seqAt B oW4 cmp4 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem w4Blo_at : instrAt B oW4Blo = some (.bcond 3 (brImm8 oW4Blo oBytes)) := by rw [instrAt_eq_scan]; decide +kernel
theorem w4Body_at : seqAt B oW4Body w4B = true := by rw [seqAt_eq_scan]; decide +kernel
theorem w4Back_at : instrAt B oW4Back = some (.b (brImm11 oW4Back oW4)) := by rw [instrAt_eq_scan]; decide +kernel
theorem unal_at : seqAt B oUnal unalS = true := by rw [seqAt_eq_scan]; decide +kernel
theorem unalBeq_at : instrAt B oUnalBeq = some (.bcond 0 (brImm8 oUnalBeq oPH)) := by rw [instrAt_eq_scan]; decide +kernel
theorem pb_at : seqAt B oPB pbB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem pbBne_at : instrAt B oPBBne = some (.bcond 1 (brImm8 oPBBne oPB)) := by rw [instrAt_eq_scan]; decide +kernel
theorem pbBack_at : instrAt B oPBBack = some (.b (brImm11 oPBBack oBytes)) := by rw [instrAt_eq_scan]; decide +kernel
theorem ph_at : seqAt B oPH phB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem phBne_at : instrAt B oPHBne = some (.bcond 1 (brImm8 oPHBne oPH)) := by rw [instrAt_eq_scan]; decide +kernel
theorem bytes_at : seqAt B oBytes cmp0 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem bytesBeq_at : instrAt B oBytesBeq = some (.bcond 0 (brImm8 oBytesBeq oDone)) := by rw [instrAt_eq_scan]; decide +kernel
theorem bl_at : seqAt B oBL byteB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem blBne_at : instrAt B oBLBne = some (.bcond 1 (brImm8 oBLBne oBL)) := by rw [instrAt_eq_scan]; decide +kernel
theorem done_at : instrAt B oDone = some popL := by rw [instrAt_eq_scan]; decide +kernel

end M0Crypto.Release.Blake2sCopyCode
