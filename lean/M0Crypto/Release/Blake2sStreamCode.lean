import M0Crypto.Release.Blake2sCopyCode

set_option maxRecDepth 100000

/-!
`m0c_blake2s_init`, `_update` and `_final` as instruction lists. Every offset is derived from
the generated entry offset and `seqSize`; every piece is checked against the artifact bytes.
-/

namespace M0Crypto.Release.Blake2sStreamCode

open M0Crypto.Thumb
open M0Crypto.Release (brSize blSize brImm8 brImm11 blImm)
open M0Crypto.Release.Blake2sCopyCode (B)

/-! ## `update` -/

def uStart : Nat := Artifacts.Release.blake2s_update
def cmpStart : Nat := Artifacts.Release.blake2s_compress
def copyStart : Nat := Artifacts.Release.blake2s_copy

/-- `push {r4-r7,lr}; sub sp,#4; c,p,n = r0..r2; used = ctx.used`. -/
def uPro : List Instr :=
  [.push 0xF0 true, .subSp 1, .lslImm 4 0 0, .lslImm 5 1 0, .lslImm 6 2 0, .memImm .ldr 7 4 26]
def cmpN0 : List Instr := [.cmpImm 6 0]
def cmpU64 : List Instr := [.cmpImm 7 0x40]
/-- `count += 64; f0 = 0; r0 = h` (the body of `NONFINAL_BLOCK` after `r1` is set). -/
def nfBody : List Instr :=
  [.memImm .ldr 2 4 8, .memImm .ldr 3 4 9, .movImm 0 0, .addImm8 2 0x40, .dp .adcs 3 0,
   .memImm .str 2 4 8, .memImm .str 3 4 9, .strSp 0 0, .addImm3 0 4 0]
def flushPre : List Instr := [.movImm 1 0x28, .addReg 1 1 4] ++ nfBody
def clrUsed : List Instr := [.movImm 7 0]
def cmpU0 : List Instr := [.cmpImm 7 0]
def cmpN64 : List Instr := [.cmpImm 6 0x40]
def tstP : List Instr := [.lslImm 0 5 30]
def dirPre : List Instr := [.lslImm 1 5 0] ++ nfBody
def dirAdv : List Instr := [.addImm8 5 0x40, .subImm8 6 0x40, .cmpImm 6 0x40]
def takeA : List Instr := [.movImm 2 0x40, .subReg 2 2 7, .dp .cmp 2 6]
def takeB : List Instr := [.lslImm 2 6 0]
def setupC : List Instr :=
  [.movImm 0 0x28, .addReg 0 0 4, .addReg 0 0 7, .lslImm 1 5 0, .addReg 7 7 2, .addReg 5 5 2,
   .subReg 6 6 2, .cmpImm 2 8]
def byteLoop : List Instr :=
  [.memImm .ldrb 3 1 0, .memImm .strb 3 0 0, .addImm8 1 1, .addImm8 0 1, .subImm8 2 1]
/-- `movs r0..r3, #0`: the single exit of `update` and of `final` leaves no message byte or
digest word in the scratch registers. -/
def zeroScratch : List Instr := [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0]
def storeUsed : List Instr := [.memImm .str 7 4 26] ++ zeroScratch ++ [.addSp 1]
def uPop : Instr := .pop 0xF0 true

def oUCmp0 : Nat := uStart + seqSize uPro
def oUBeqOut : Nat := oUCmp0 + seqSize cmpN0
def oLoop : Nat := oUBeqOut + brSize
def oLoopBne : Nat := oLoop + seqSize cmpU64
def oFlush : Nat := oLoopBne + brSize
def oFlushBl : Nat := oFlush + seqSize flushPre
def oClrUsed : Nat := oFlushBl + blSize
def oDT : Nat := oClrUsed + seqSize clrUsed
def oDTBne1 : Nat := oDT + seqSize cmpU0
def oDTCmp : Nat := oDTBne1 + brSize
def oDTBls : Nat := oDTCmp + seqSize cmpN64
def oDTTst : Nat := oDTBls + brSize
def oDTBne2 : Nat := oDTTst + seqSize tstP
def oDirect : Nat := oDTBne2 + brSize
def oDirectBl : Nat := oDirect + seqSize dirPre
def oDirectAdv : Nat := oDirectBl + blSize
def oDirectBhi : Nat := oDirectAdv + seqSize dirAdv
def oBuf : Nat := oDirectBhi + brSize
def oBufBls : Nat := oBuf + seqSize takeA
def oTakeB : Nat := oBufBls + brSize
def oHave : Nat := oTakeB + seqSize takeB
def oHaveBlo : Nat := oHave + seqSize setupC
def oCopyBl : Nat := oHaveBlo + brSize
def oCopyB : Nat := oCopyBl + blSize
def oBytesL : Nat := oCopyB + brSize
def oBytesBne : Nat := oBytesL + seqSize byteLoop
def oNext : Nat := oBytesBne + brSize
def oNextBne : Nat := oNext + seqSize cmpN0
def oOut : Nat := oNextBne + brSize
def oUPop : Nat := oOut + seqSize storeUsed


/-! ## `final` -/

def fStart : Nat := Artifacts.Release.blake2s_final

def fPro : List Instr :=
  [.push 0xF0 true, .subSp 1, .lslImm 4 0 0, .lslImm 5 1 0, .memImm .ldr 6 4 26, .memImm .ldr 2 4 8,
   .memImm .ldr 3 4 9, .movImm 0 0, .addReg 2 2 6, .dp .adcs 3 0, .movImm 1 0x28, .addReg 1 1 4]
def tstW : List Instr := [.lslImm 7 6 30]
def padB : List Instr := [.memReg .strb 0 1 6, .addImm8 6 1]
def cmp64 : List Instr := [.cmpImm 6 0x40]
def padW : List Instr := [.memReg .str 0 1 6, .addImm8 6 4]
def fCall : List Instr := [.dp .mvns 0 0, .strSp 0 0, .addImm3 0 4 0]
def tstO : List Instr := [.lslImm 0 5 30]
def outW : List Instr := [.ldm 4 0xF, .stm 5 0xF, .ldm 4 0xF, .stm 5 0xF]
def outB0 : List Instr := [.movImm 6 0]
def outB : List Instr := [.memReg .ldrb 0 4 6, .memReg .strb 0 5 6, .addImm8 6 1, .cmpImm 6 0x20]
def fRet : List Instr := zeroScratch ++ [.addSp 1]

def oPadB : Nat := fStart + seqSize fPro
def oPadBBeq : Nat := oPadB + seqSize tstW
def oPadBBody : Nat := oPadBBeq + brSize
def oPadBBack : Nat := oPadBBody + seqSize padB
def oPadW : Nat := oPadBBack + brSize
def oPadWBeq : Nat := oPadW + seqSize cmp64
def oPadWBody : Nat := oPadWBeq + brSize
def oPadWBack : Nat := oPadWBody + seqSize padW
def oFComp : Nat := oPadWBack + brSize
def oFBl : Nat := oFComp + seqSize fCall
def oTstO : Nat := oFBl + blSize
def oTstOBne : Nat := oTstO + seqSize tstO
def oOutW : Nat := oTstOBne + brSize
def oOutWB : Nat := oOutW + seqSize outW
def oOutB0 : Nat := oOutWB + brSize
def oOutB : Nat := oOutB0 + seqSize outB0
def oOutBBne : Nat := oOutB + seqSize outB
def oFRet : Nat := oOutBBne + brSize
def oFPop : Nat := oFRet + seqSize fRet

/-- `update` ends where `final` starts, and `final` ends the artifact: the two returns are the
last instructions of their functions. -/
theorem u_end : oUPop + 2 = fStart := by decide

theorem f_end : oFPop + 2 = Artifacts.Release.size := by decide

/-! ## `init` -/

def iStart : Nat := Artifacts.Release.blake2s_init

def iA : List Instr :=
  [.push 0 true, .ldrLit 1 7, .ldrLit 2 7, .ldrLit 3 8, .stm 0 0xE, .ldrLit 1 8, .ldrLit 2 8,
   .ldrLit 3 9, .stm 0 0xE, .ldrLit 1 9, .ldrLit 2 9, .movImm 3 0, .stm 0 0xE,
   .memImm .str 3 0 0, .memImm .str 3 0 17]
def iPop : Instr := .pop 0 true
def oIPop : Nat := iStart + seqSize iA

/-! ## Checks against the artifact -/

theorem uPro_at : seqAt B uStart uPro = true := by rw [seqAt_eq_scan]; decide +kernel
theorem cmpN0_at : seqAt B oUCmp0 cmpN0 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem uBeqOut_at : instrAt B oUBeqOut = some (.bcond 0 (brImm8 oUBeqOut oOut)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem cmpU64_at : seqAt B oLoop cmpU64 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem loopBne_at : instrAt B oLoopBne = some (.bcond 1 (brImm8 oLoopBne oDT)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem flush_at : seqAt B oFlush flushPre = true := by rw [seqAt_eq_scan]; decide +kernel
theorem flushBl_at : instrAt B oFlushBl = some (.bl (blImm oFlushBl cmpStart)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem clrUsed_at : seqAt B oClrUsed clrUsed = true := by rw [seqAt_eq_scan]; decide +kernel
theorem cmpU0_at : seqAt B oDT cmpU0 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem dtBne1_at : instrAt B oDTBne1 = some (.bcond 1 (brImm8 oDTBne1 oBuf)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem cmpN64_at : seqAt B oDTCmp cmpN64 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem dtBls_at : instrAt B oDTBls = some (.bcond 9 (brImm8 oDTBls oBuf)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem tstP_at : seqAt B oDTTst tstP = true := by rw [seqAt_eq_scan]; decide +kernel
theorem dtBne2_at : instrAt B oDTBne2 = some (.bcond 1 (brImm8 oDTBne2 oBuf)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem direct_at : seqAt B oDirect dirPre = true := by rw [seqAt_eq_scan]; decide +kernel
theorem directBl_at : instrAt B oDirectBl = some (.bl (blImm oDirectBl cmpStart)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem dirAdv_at : seqAt B oDirectAdv dirAdv = true := by rw [seqAt_eq_scan]; decide +kernel
theorem directBhi_at : instrAt B oDirectBhi = some (.bcond 8 (brImm8 oDirectBhi oDirect)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem takeA_at : seqAt B oBuf takeA = true := by rw [seqAt_eq_scan]; decide +kernel
theorem bufBls_at : instrAt B oBufBls = some (.bcond 9 (brImm8 oBufBls oHave)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem takeB_at : seqAt B oTakeB takeB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem setupC_at : seqAt B oHave setupC = true := by rw [seqAt_eq_scan]; decide +kernel
theorem haveBlo_at : instrAt B oHaveBlo = some (.bcond 3 (brImm8 oHaveBlo oBytesL)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem copyBl_at : instrAt B oCopyBl = some (.bl (blImm oCopyBl copyStart)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem copyB_at : instrAt B oCopyB = some (.b (brImm11 oCopyB oNext)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem byteLoop_at : seqAt B oBytesL byteLoop = true := by rw [seqAt_eq_scan]; decide +kernel
theorem bytesBne_at : instrAt B oBytesBne = some (.bcond 1 (brImm8 oBytesBne oBytesL)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem next_at : seqAt B oNext cmpN0 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem nextBne_at : instrAt B oNextBne = some (.bcond 1 (brImm8 oNextBne oLoop)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem storeUsed_at : seqAt B oOut storeUsed = true := by rw [seqAt_eq_scan]; decide +kernel
theorem uPop_at : instrAt B oUPop = some uPop := by rw [instrAt_eq_scan]; decide +kernel

theorem fPro_at : seqAt B fStart fPro = true := by rw [seqAt_eq_scan]; decide +kernel
theorem tstW_at : seqAt B oPadB tstW = true := by rw [seqAt_eq_scan]; decide +kernel
theorem padBBeq_at : instrAt B oPadBBeq = some (.bcond 0 (brImm8 oPadBBeq oPadW)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem padB_at : seqAt B oPadBBody padB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem padBBack_at : instrAt B oPadBBack = some (.b (brImm11 oPadBBack oPadB)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem cmp64_at : seqAt B oPadW cmp64 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem padWBeq_at : instrAt B oPadWBeq = some (.bcond 0 (brImm8 oPadWBeq oFComp)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem padW_at : seqAt B oPadWBody padW = true := by rw [seqAt_eq_scan]; decide +kernel
theorem padWBack_at : instrAt B oPadWBack = some (.b (brImm11 oPadWBack oPadW)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem fCall_at : seqAt B oFComp fCall = true := by rw [seqAt_eq_scan]; decide +kernel
theorem fBl_at : instrAt B oFBl = some (.bl (blImm oFBl cmpStart)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem tstO_at : seqAt B oTstO tstO = true := by rw [seqAt_eq_scan]; decide +kernel
theorem tstOBne_at : instrAt B oTstOBne = some (.bcond 1 (brImm8 oTstOBne oOutB0)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem outW_at : seqAt B oOutW outW = true := by rw [seqAt_eq_scan]; decide +kernel
theorem outWB_at : instrAt B oOutWB = some (.b (brImm11 oOutWB oFRet)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem outB0_at : seqAt B oOutB0 outB0 = true := by rw [seqAt_eq_scan]; decide +kernel
theorem outB_at : seqAt B oOutB outB = true := by rw [seqAt_eq_scan]; decide +kernel
theorem outBBne_at : instrAt B oOutBBne = some (.bcond 1 (brImm8 oOutBBne oOutB)) := by
  rw [instrAt_eq_scan]; decide +kernel
theorem fRet_at : seqAt B oFRet fRet = true := by rw [seqAt_eq_scan]; decide +kernel
theorem fPop_at : instrAt B oFPop = some uPop := by rw [instrAt_eq_scan]; decide +kernel

theorem iA_at : seqAt B iStart iA = true := by rw [seqAt_eq_scan]; decide +kernel
theorem iPop_at : instrAt B oIPop = some iPop := by rw [instrAt_eq_scan]; decide +kernel

end M0Crypto.Release.Blake2sStreamCode
