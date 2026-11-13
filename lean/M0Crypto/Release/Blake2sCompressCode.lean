import M0Crypto.Release.Blake2sG
import M0Crypto.Release.Layout
import M0Crypto.Thumb.SeqScan
import M0Crypto.Artifacts.Release
import M0Crypto.Release.Blake2sFrames

set_option maxRecDepth 100000

/-!
`m0c_blake2s_compress` as instruction lists, placed at offsets derived from the generated
entry offset and `seqSize` (no literal offsets). Each piece is checked against the artifact
bytes with `seqAt`.
-/

namespace M0Crypto.Release.Blake2sCode

open M0Crypto.Thumb
open M0Crypto.Release (brSize brImm11)
open M0Crypto.Release.Blake2s (b2g)

abbrev B := Artifacts.Release.bytes

/-- Prologue up to the `b` over the literal pool. -/
def pre : List Instr :=
  [ .push 0xF0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11, .push 0xF0 false,
    .subSp LOCALS_WORDS, .strSp 0 HPTR_WORDS,
    .ldrLit 0 20, .dp .eors 0 2, .movHi 9 0,
    .ldrLit 5 20, .dp .eors 5 3, .movHi 10 5,
    .ldrSp 0 SLOTW_9, .ldrLit 6 19, .dp .eors 6 0, .movHi 11 6,
    .ldrLit 0 18, .movHi 12 0,
    .addRdSp 4 8,
    .ldm 1 0x4d, .stm 4 0x4d, .ldm 1 0x4d, .stm 4 0x4d,
    .ldm 1 0x4d, .stm 4 0x4d, .ldm 1 0x4d, .stm 4 0x4d,
    .ldrSp 1 24, .ldm 1 0x4d, .movHi 8 0,
    .addRdSp 4 1, .stm 4 0x4c,
    .ldm 1 0x4d, .stm 4 0x4d,
    .ldrLit 2 2, .ldrLit 5 3, .ldrLit 6 3, .ldrLit 7 4 ]

def padList : List Instr := [.movHi 8 8]
def poolBytes : Nat := 8 * 4

/-- Message-word schedule entry. -/
def sg (r i : Nat) : Nat := ((M0Crypto.Spec.Blake2s.SIGMA.toList.map Array.toList).getD r []).getD i 0

theorem sg_eq : ∀ r : Fin 10, ∀ i : Fin 16, sg r i = (M0Crypto.Spec.Blake2s.SIGMA[(r : Nat)]!)[(i : Nat)]! := by
  decide

/-- The `k`-th `G` of a round in `B2_ROUND` order for the message schedule `sch`; the first round
does not carry v2 in r0. -/
def gListS (sch : Nat → Nat) (first : Bool) (k : Nat) : List Instr :=
  match k with
  | 0 => b2g 2 6 6 11 (sch 4) (sch 5) (!first) false
  | 1 => b2g 0 4 2 9 (sch 0) (sch 1) false false
  | 2 => b2g 1 5 5 10 (sch 2) (sch 3) false false
  | 3 => b2g 3 7 7 12 (sch 6) (sch 7) false true
  | 4 => b2g 3 4 5 11 (sch 14) (sch 15) true false
  | 5 => b2g 0 5 6 12 (sch 8) (sch 9) false false
  | 6 => b2g 1 6 7 9 (sch 10) (sch 11) false false
  | _ => b2g 2 7 2 10 (sch 12) (sch 13) false true

/-- `B2_ROUND` for a schedule. -/
def roundS (sch : Nat → Nat) (first : Bool) : List Instr := (List.range 8).flatMap (gListS sch first)

/-- `B2_ROUND` of round `r`. -/
def roundInstrs (r : Nat) : List Instr := roundS (sg r) (r == 0)

/-- Five-word batches of the frame clear (`LOCALS/20` in the assembly). -/
def clearBatches : Nat := M0Crypto.Release.Blake2s.compressLocalsBytes / 20

/-- The frame clear: zero r0-r4, point r5 at the frame, store `clearBatches` five-word batches of
zeros, zero r12. -/
def clearI : List Instr :=
  [ .movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0, .addRdSp 5 0 ] ++
  List.replicate clearBatches (.stm 5 0x1f) ++ [ .movHi 12 0 ]

/-- Feed-forward, frame clear and return. -/
def tail : List Instr :=
  [ .dp .eors 0 6, .movHi 6 8, .dp .eors 2 6, .ldrSp 6 1, .dp .eors 5 6, .ldrSp 6 3, .dp .eors 7 6,
    .ldrSp 4 24,
    .memImm .ldr 1 4 0, .dp .eors 1 2, .memImm .ldr 2 4 1, .dp .eors 2 5,
    .memImm .ldr 3 4 2, .dp .eors 3 0, .memImm .ldr 5 4 3, .dp .eors 5 7,
    .stm 4 0x2e, .ldm 4 0x0f ] ++
  [ .ldrSp 6 4, .dp .eors 0 6, .movHi 6 9, .dp .eors 0 6,
    .ldrSp 6 5, .dp .eors 1 6, .movHi 6 10, .dp .eors 1 6,
    .ldrSp 6 6, .dp .eors 2 6, .movHi 6 11, .dp .eors 2 6,
    .ldrSp 6 7, .dp .eors 3 6, .movHi 6 12, .dp .eors 3 6,
    .subImm8 4 16, .stm 4 0x0f ] ++ clearI ++
  [ .addSp LOCALS_WORDS, .pop 0xF0 false, .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7, .pop 0xF0 true ]


/-! ## Offsets -/

def fnStart : Nat := Artifacts.Release.blake2s_compress
def bOff : Nat := fnStart + seqSize pre
def padOff : Nat := bOff + brSize
def poolOff : Nat := padOff + seqSize padList
def roundsOff : Nat := poolOff + poolBytes
/-- The ten rounds. -/
def allRounds : List (List Instr) := (List.range 10).map roundInstrs
/-- Offset of round `r`. -/
def roundOff (r : Nat) : Nat := roundsOff + ((allRounds.take r).map seqSize).sum
def tailOff : Nat := roundOff 10

/-- Consecutive blocks, checked on the artifact cut at the first block (linear time, see
`SeqScan`). -/
def checkBlocks : List (BitVec 8) → List (List Instr) → Bool
  | _, [] => true
  | bs, g :: gs => seqScan bs g && checkBlocks (bs.drop (seqSize g)) gs

theorem checkBlocks_get : ∀ (gs : List (List Instr)) (bs : List (BitVec 8)) (off : Nat),
    checkBlocks (bs.drop off) gs = true → ∀ i (h : i < gs.length),
      seqAt bs (off + ((gs.take i).map seqSize).sum) (gs[i]) = true
  | [], _, _, _, i, h => by simp at h
  | g :: gs, bs, off, hc, 0, _ => by
    simp only [checkBlocks, Bool.and_eq_true] at hc
    simpa [seqAt_eq_scan] using hc.1
  | g :: gs, bs, off, hc, i + 1, h => by
    simp only [checkBlocks, Bool.and_eq_true, List.drop_drop] at hc
    have := checkBlocks_get gs bs (off + seqSize g) hc.2 i (by simpa using h)
    simpa [Nat.add_assoc, Nat.add_comm (seqSize g), seqSize, List.take_succ_cons] using this

theorem b_at : instrAt B bOff = some (.b (brImm11 bOff roundsOff)) := by decide +kernel
theorem rounds_check : checkBlocks (B.drop roundsOff) allRounds = true := by decide +kernel

end M0Crypto.Release.Blake2sCode
