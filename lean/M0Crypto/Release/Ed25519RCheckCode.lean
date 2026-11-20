import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.RoutinePieces
import M0Crypto.Release.Ed25519VerifyEncode

/-! The endpoint tests and descending middle-byte loop of the early R check. -/

namespace M0Crypto.Release.Ed25519RCheck

open M0Crypto.Thumb
open M0Crypto.Armv6M (LowReg Mem State Word)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg (Iface CalleeS calleeAt)
open M0Crypto.Release.Ed25519VerifyEncode (earlyMask earlyScan earlyScan_iff scan_earlyReject earlyReject)
open M0Crypto.Release.Footprint (bytesAt bytesAt_length)
open M0Crypto.Artifacts.Ed25519Compact
  (r_encoding_check r_check_high r_check_high_middle r_check_middle r_check_scan r_check_pass)

def io : Iface :=
  { ins := [(0, 0, .raw (.k 32))], outs := [], wr := [], rd := [⟨0, 0, .k 32⟩], al := [] }

def checkS : CalleeS := calleeAt r_encoding_check io [0]

def branch (cc : BitVec 4) (site target : Nat) : Instr :=
  .bcond cc (BitVec.ofInt 8 (((target : Int) - (site + 4)) / 2))

def jump (site target : Nat) : Instr :=
  .b (BitVec.ofInt 11 (((target : Int) - (site + 4)) / 2))

def endpoints : List Instr :=
  [.memImm .ldrb 2 0 31, .memImm .ldrb 3 0 0]

def chooseMask : List Instr :=
  let o := r_encoding_check + seqSize endpoints
  [.cmpImm 2 255, branch 0 (o + 2) r_check_high,
   .cmpImm 2 127, branch 0 (o + 6) r_check_high,
   .cmpImm 2 128, branch 1 (o + 10) r_check_pass,
   .cmpImm 3 1, branch 1 (o + 14) r_check_pass,
   .movImm 4 0, jump (o + 18) r_check_middle]

def chooseHigh : List Instr :=
  [.cmpImm 3 237, branch 2 (r_check_high + 2) r_check_high_middle,
   .cmpImm 2 255, branch 1 (r_check_high + 6) r_check_pass,
   .cmpImm 3 236, branch 1 (r_check_high + 10) r_check_pass]

def scanTest : List Instr := [.memReg .ldrb 5 0 1, .dp .cmp 5 4]

def scanByte : List Instr :=
  scanTest ++ [branch 1 (r_check_scan + 4) r_check_pass, .subImm8 1 1,
    branch 1 (r_check_scan + 8) r_check_scan]

def instructions : List Instr :=
  endpoints ++ chooseMask ++ chooseHigh ++ [.movImm 4 255, .movImm 1 30] ++
    scanByte ++ [.movImm 0 1, .bx 14, .movImm 0 0, .bx 14]

theorem linked (b : Build) : seqAt b.bytes r_encoding_check instructions = true := by
  rw [seqAt_eq_scan]
  cases b <;> decide +kernel

def readByte (m : Mem) (a : Word) (i : Nat) : BitVec 8 :=
  m (a + BitVec.ofNat 32 i)

theorem endpoints_value (s : State) :
    (execAll endpoints s).regs 2 = (readByte s.mem (s.regs 0) 31).zeroExtend 32 ∧
    (execAll endpoints s).regs 3 = (readByte s.mem (s.regs 0) 0).zeroExtend 32 := by
  have r0 : LowReg.toReg 0 = 0 := rfl
  have r2 : LowReg.toReg 2 = 2 := rfl
  have r3 : LowReg.toReg 3 = 3 := rfl
  simp (config := {decide := true}) [endpoints, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    State.setReg, State.reg, MemOp.width, read8, readByte, r0,r2,r3,BitVec.zeroExtend]

theorem scan_equal (s : State) (i : Nat) (hm : s.regs 1 = BitVec.ofNat 32 i)
    (byte : BitVec 8) (hb : s.regs 4 = byte.zeroExtend 32) :
    condPassed 1 (execAll scanTest s) = !(readByte s.mem (s.regs 0) i == byte) := by
  have r0 : LowReg.toReg 0 = 0 := rfl
  have r1 : LowReg.toReg 1 = 1 := rfl
  have r4 : LowReg.toReg 4 = 4 := rfl
  have r5 : LowReg.toReg 5 = 5 := rfl
  simp (config := {decide := true}) [scanTest, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    addFlags, State.setNZCV, State.setNZ, State.setReg, State.reg, condPassed, read8, readByte,
    r0,r1,r4,r5,hm,hb,sub_flags,BitVec.zeroExtend]
  generalize s.mem (s.regs 0 + BitVec.ofNat 32 i) = value
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have he : value.setWidth 32 - byte.setWidth 32 + byte.setWidth 32 = byte.setWidth 32 := by
      rw [h,BitVec.zero_add]
    rw [BitVec.sub_add_cancel] at he
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32)] using congrArg BitVec.toNat he
  · rintro rfl
    exact BitVec.sub_self _

def rejected (read : Nat → BitVec 8) : Bool :=
  match earlyMask (read 0) (read 31) with
  | some byte => earlyScan read byte 30
  | none => false

def rejectedBytes (bs : List (BitVec 8)) : Bool :=
  rejected (fun i => bs[i]?.getD 0)

theorem rejected_congr {read other : Nat → BitVec 8}
    (h : ∀ i < 32, read i = other i) : rejected read = rejected other := by
  unfold rejected
  rw [h 0 (by decide),h 31 (by decide)]
  split
  · rename_i byte _
    apply Bool.eq_iff_iff.mpr
    rw [earlyScan_iff,earlyScan_iff]
    constructor <;> intro hScan i hPos hi
    · rw [← h i (by omega)]
      exact hScan i hPos hi
    · rw [h i (by omega)]
      exact hScan i hPos hi
  · rfl

theorem rejectedBytes_mem (m : Mem) (a : Word) :
    rejectedBytes (bytesAt m a 32) = rejected (readByte m a) := by
  apply rejected_congr
  intro i hi
  simp [bytesAt,hi,readByte]

theorem rejected_sound (m : Mem) (a : Word) (h : rejected (readByte m a) = true) :
    earlyReject (bytesAt m a 32) := by
  unfold rejected at h
  split at h
  · rename_i byte hMask
    have hScan := (earlyScan_iff _ _ _).mp h
    have last : bytesAt m (a + 1#32 + 30#32) 1 = [readByte m a 31] := by
      change [m (a + 1#32 + 30#32 + 0#32)] = [m (a + 31#32)]
      rw [BitVec.add_zero, BitVec.add_assoc]
      rfl
    have splitBytes : bytesAt m a 32 =
        readByte m a 0 :: (bytesAt m (a + 1#32) 30 ++ [readByte m a 31]) :=
      (Ed25519CallProg.bytesAt_split m a 1 31).trans
        (congrArg (fun bs => readByte m a 0 :: bs)
          ((Ed25519CallProg.bytesAt_split m (a + 1#32) 30 1).trans
            (congrArg (bytesAt m (a + 1#32) 30 ++ ·) last)))
    rw [splitBytes]
    apply scan_earlyReject hMask (bytesAt_length _ _ _)
    intro i hi
    have hBound : i < 30 := by simpa only [bytesAt_length] using hi
    simp only [bytesAt,List.getElem_map,List.getElem_range,ofNat_add_assoc]
    exact hScan (1+i) (by omega) (by omega)
  · cases h

end M0Crypto.Release.Ed25519RCheck
