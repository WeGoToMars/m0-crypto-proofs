import M0Crypto.Release.Poly1305MacDefs
import M0Crypto.Release.ChaCha20Frame
import M0Crypto.Release.Layout

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
set_option cbv.maxSteps 10000000

/-!
Instruction lists of the release-byte Poly1305 block loop. Their correspondence to
the frozen artifact is proved in `Poly1305BlocksCheck`, rather than assumed in an ISA.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Mac (mac narrow colend)

/-! ### Stack frame of `m0c_poly1305_blocks`

Word slots of the frame at `sp`, named once for the instruction lists here and for the
proofs. `ldr`/`str` SP-relative immediates are word indices (`Exec`: `imm8 * 4`), so slot
`k` is the immediate `BitVec.ofNat 8 k` at byte offset `4 * k`. `sub sp`/`add sp` take a
word count. Layout of `PB_FRAME` (28 bytes) in `src/chacha20poly1305.S`: T0..T3 at
sp+0..12, message pointer at sp+16, block count at sp+20, zeroed padding at sp+24. -/
def slotT0 : Nat := 0
def slotT1 : Nat := 1
def slotT2 : Nat := 2
def slotT3 : Nat := 3
/-- Message pointer, advanced by each block. -/
def slotMsg : Nat := 4
/-- Remaining block count. -/
def slotCount : Nat := 5
/-- Zeroed padding word. -/
def slotPad : Nat := 6
/-- Frame bytes below the count slot. The body's writes all lie here (`body_frame`). -/
def bodyBytes : Nat := 4 * slotCount
/-- Frame bytes below the padding slot. The writes of the blocks path (body, decrement,
setup) all lie here (`frameWB slotPad`). -/
def belowPadBytes : Nat := 4 * slotPad
theorem bodyBytes_le_belowPad : bodyBytes ≤ belowPadBytes := by decide

/-- Instructions with accesses aligned whenever SP and r7 are word aligned.
Byte loads may use any base; other loads must use r7. SP and r7 are stable. -/
def stableInstr (i : Instr) : Bool :=
  !(i.dsts.contains 13) && !(i.dsts.contains 7) && match i with
  | .memImm op _ n _ => op.isLoad && (op.width == 1 || n.val == 7)
  | .ldrSp _ _ | .strSp _ _ => true
  | _ => match i.spRel with | some [] => true | _ => false

def stable (is : List Instr) : Bool := is.all stableInstr

theorem stable_head {i : Instr} {is : List Instr} (h : stable (i :: is) = true) :
    13 ∉ i.dsts ∧ 7 ∉ i.dsts ∧ stableInstr i = true ∧ stable is = true := by
  simp only [stable, List.all_cons, Bool.and_eq_true] at h
  have hn := h.1
  simp only [stableInstr, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hn
  exact ⟨hn.1.1, hn.1.2, h.1, h.2⟩

theorem stable_aligned_one {i : Instr} (h : stableInstr i = true) (s : State)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0) :
    (i.accesses s).all Access.aligned = true := by
  cases i with
  | memImm op t n k =>
    simp only [stableInstr, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    simp only [Instr.accesses, List.all_cons, List.all_nil, Bool.and_true, Access.aligned,
      M0Crypto.Armv6M.State.reg, BitVec.toNat_add, BitVec.toNat_ofNat, beq_iff_eq]
    rcases h.2.2 with hw | hn
    · rw [hw]; omega
    · have hr : n.toReg = (7 : Reg) := by apply Fin.ext; change n.val = 7; exact hn
      rw [hr]
      cases op <;> simp_all [MemOp.width, MemOp.isLoad] <;> omega
  | strSp t k =>
    simp [Instr.accesses, Access.aligned, M0Crypto.Armv6M.State.sp, BitVec.toNat_add]; omega
  | ldrSp t k =>
    simp [Instr.accesses, Access.aligned, M0Crypto.Armv6M.State.sp, BitVec.toNat_add]; omega
  | _ => simp_all [stableInstr, Instr.spRel, Instr.accesses]

theorem stable_aligned : ∀ (is : List Instr) (s : State), stable is = true →
    (s.regs 13).toNat % 4 = 0 → (s.regs 7).toNat % 4 = 0 → alignedAll is s = true
  | [], _, _, _, _ => rfl
  | i :: is, s, h, hs, hc => by
    obtain ⟨h13, h7, hi, ht⟩ := stable_head h
    simp only [alignedAll, Bool.and_eq_true]
    exact ⟨stable_aligned_one hi s hs hc, stable_aligned is _ ht
      (by rw [next_regs_other s 13 (by cbv) h13]; exact hs)
      (by rw [next_regs_other s 7 (by cbv) h7]; exact hc)⟩

/-- Unaligned little-endian word load, matching LDLE in the source. -/
def ldle (d : LowReg) (o : Nat) : List Instr :=
  [.memImm .ldrb d 6 (BitVec.ofNat 5 o),
   .memImm .ldrb 4 6 (BitVec.ofNat 5 (o+1)), .lslImm 4 4 8, .dp .orrs d 4,
   .memImm .ldrb 4 6 (BitVec.ofNat 5 (o+2)), .lslImm 4 4 16, .dp .orrs d 4,
   .memImm .ldrb 4 6 (BitVec.ofNat 5 (o+3)), .lslImm 4 4 24, .dp .orrs d 4]

def loadU : List Instr := ldle 0 0 ++ ldle 1 4 ++ ldle 2 8 ++ ldle 3 12 ++ [.addImm8 6 16]
def loadA : List Instr := [.ldm 6 0x0f]
def testAlign : List Instr :=
  [.ldrSp 6 (BitVec.ofNat 8 slotMsg), .movImm 4 3, .dp .tst 6 4]
def addMsg : List Instr :=
  [.strSp 6 (BitVec.ofNat 8 slotMsg), .movHi 4 8, .addReg 0 0 4, .movHi 4 9, .dp .adcs 1 4,
   .movHi 4 10, .dp .adcs 2 4, .movHi 4 11, .dp .adcs 3 4,
   .movHi 4 14, .movHi 5 12, .dp .adcs 4 5,
   .movHi 8 0, .movHi 9 1, .movHi 10 2, .movHi 11 3, .movHi 14 4]
def columns : List Instr :=
  [.movImm 0 0, .movImm 1 0] ++
  mac 8 10 ++ mac 9 22 ++ mac 10 20 ++ mac 11 18 ++ colend 0 ++
  mac 8 12 ++ mac 9 10 ++ mac 10 22 ++ mac 11 20 ++ narrow 9 ++ colend 1 ++
  mac 8 14 ++ mac 9 12 ++ mac 10 10 ++ mac 11 22 ++ narrow 10 ++ colend 2 ++
  mac 8 16 ++ mac 9 14 ++ mac 10 12 ++ mac 11 10 ++ narrow 11

def fold : List Instr :=
  [.strSp 0 (BitVec.ofNat 8 slotT3), .movHi 2 14, .memImm .ldr 3 7 5, .dp .muls 2 3, .addReg 4 1 2,
   .lsrImm 5 4 2, .movImm 2 3, .dp .ands 2 4, .subReg 4 4 2, .addReg 5 5 4,
   .movImm 6 0, .ldrSp 0 (BitVec.ofNat 8 slotT0), .addReg 0 0 5,
   .ldrSp 1 (BitVec.ofNat 8 slotT1), .dp .adcs 1 6,
   .ldrSp 3 (BitVec.ofNat 8 slotT2), .dp .adcs 3 6,
   .ldrSp 4 (BitVec.ofNat 8 slotT3), .dp .adcs 4 6, .dp .adcs 2 6,
   .movHi 8 0, .movHi 9 1, .movHi 10 3, .movHi 11 4, .movHi 14 2]

def body : List Instr := addMsg ++ columns ++ fold
def dec : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 slotCount), .subImm8 0 1, .strSp 0 (BitVec.ofNat 8 slotCount)]
/-- Zeroes the whole frame: word `k` of the frame is stored from `r0`, which is zero
at this point. The stores are in slot order, so the list is the same as one store per
named slot. -/
def publish : List Instr :=
  [.movHi 0 8, .movHi 1 9, .movHi 2 10, .movHi 3 11,
   .memImm .str 0 7 0, .memImm .str 1 7 1, .memImm .str 2 7 2, .memImm .str 3 7 3,
   .movHi 0 14, .memImm .str 0 7 4,
   .movImm 0 0, .movHi 14 0] ++
  (List.range frameWords).map (fun k => Instr.strSp 0 (BitVec.ofNat 8 k)) ++
  [.movHi 12 0, .movImm 1 0, .movImm 2 0, .movImm 3 0]

def prologue : List Instr :=
  [.push 0xf0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11,
   .push 0xf0 false, .subSp (BitVec.ofNat 7 frameWords), .cmpImm 2 0]
def setup : List Instr :=
  [.lslImm 7 0 0, .strSp 1 (BitVec.ofNat 8 slotMsg), .strSp 2 (BitVec.ofNat 8 slotCount),
   .movHi 12 3,
   .memImm .ldr 4 7 0, .memImm .ldr 5 7 1, .memImm .ldr 6 7 2, .memImm .ldr 0 7 3,
   .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 0,
   .memImm .ldr 0 7 4, .movHi 14 0]
def epilogue : List Instr :=
  [.addSp (BitVec.ofNat 7 frameWords), .pop 0xf0 false, .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7]

/-! ### Layout of `m0c_poly1305_blocks`

Derived, not tabulated. The function starts at `Artifacts.Release.poly1305_blocks`, and each
piece starts where the one before it ends: a list piece occupies `seqSize` bytes, a short
branch occupies `brSize`. Branch displacements are computed by `brImm8`/`brImm11` from the
offsets here, so moving a piece moves its branches with it. `Poly1305BlocksCheck` checks each
list piece at its offset in the artifact bytes; each branch is checked by the `instrAt`
side goal of its `Reach` step.

Two families of names: the `From` names are distances from `testAlign`, the entry of
`loadState`; the `At` names are offsets from the start of the artifact. -/

/-- Function entry: `push`, `cmp r2, #0`. -/
def entryAt : Nat := Artifacts.Release.poly1305_blocks
/-- `bne` to `setupAt`: taken when the block count is nonzero. -/
def enterBrAt : Nat := entryAt + seqSize prologue
/-- `b` to `epilogueAt`: the zero-count return. -/
def retBrAt : Nat := enterBrAt + brSize
def setupAt : Nat := retBrAt + brSize
def testAt : Nat := setupAt + seqSize setup

/-- Distances from `testAt` (the `loadState` entry) to each later piece. -/
def alignBrFrom : Nat := seqSize testAlign
def loadAFrom : Nat := alignBrFrom + brSize
def skipBrFrom : Nat := loadAFrom + seqSize loadA
def loadUFrom : Nat := skipBrFrom + brSize
def bodyFrom : Nat := loadUFrom + seqSize loadU
def decFrom : Nat := bodyFrom + seqSize body
def countBrFrom : Nat := decFrom + seqSize dec
def backBrFrom : Nat := countBrFrom + brSize
def publishFrom : Nat := backBrFrom + brSize
def epilogueFrom : Nat := publishFrom + seqSize publish
def popFrom : Nat := epilogueFrom + seqSize epilogue

/-- `bcond` (NE) to `loadUAt` when the message is unaligned. -/
def alignBrAt : Nat := testAt + alignBrFrom
/-- Aligned path: `ldm` of the message words. -/
def loadAAt : Nat := testAt + loadAFrom
/-- `b` past the unaligned path, to `bodyAt`. -/
def skipBrAt : Nat := testAt + skipBrFrom
/-- Unaligned path: byte-wise little-endian loads. -/
def loadUAt : Nat := testAt + loadUFrom
def bodyAt : Nat := testAt + bodyFrom
def decAt : Nat := testAt + decFrom
/-- `beq` to `publishAt` when the count reaches zero. -/
def countBrAt : Nat := testAt + countBrFrom
/-- `b` back to `testAt`: the next block. -/
def backBrAt : Nat := testAt + backBrFrom
def publishAt : Nat := testAt + publishFrom
def epilogueAt : Nat := testAt + epilogueFrom
/-- `pop {r4-r7, pc}`: the return. It is not in `epilogue`. -/
def popAt : Nat := testAt + popFrom

end M0Crypto.Release.Poly1305Blocks
