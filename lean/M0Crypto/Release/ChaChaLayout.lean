import M0Crypto.Release.Layout
import M0Crypto.Release.ChaChaRoundDefs
import M0Crypto.Artifacts.Release

/-!
# Release ChaCha20 layout: piece lists and derived offsets

The pieces of `m0c_chacha20_xor` and the chain of offsets that places each piece. A piece's
offset depends on the sizes of pieces that other proof modules name, so the lists and the
chain live here, below every proof module. Each list keeps the namespace and name it had in
its proof module, so the proofs refer to it unchanged. The chain ends with the `seqSize` of
each piece, so no offset in a proof is a literal.
-/

/-! ### Frame slots of `m0c_chacha20_xor`

Slot `i` is the word at `sp + 4*i` after the prologue. `src/chacha20.S` gives the byte layout:
`X` 0 (working state), `J` 64 (slot 16), `LEN` 128 (slot 32), `OUTP` 132 (slot 33), `INP` 136
(slot 34), `FRAME` 140 (35 words), `SAVED` 36 (r4-r11 and lr, slots 35 to 43), `ARG_NONCE` 176
(slot 44), `ARG_COUNTER` 180 (slot 45). The values match the assembly frame layout. -/

namespace M0Crypto.Release.ChaChaLayout

/-- First word of the working state `x[0..15]` (`X`, byte 0). -/
def slotX : Nat := 0
/-- First word of the input state `j[0..15]` (`J`, byte 64). -/
def slotJ : Nat := 16
/-- Block counter, `j[12]`. -/
def slotCtr : Nat := slotJ + 12
/-- Key words `j[4..11]` (`slotKey + k` for key word `k`). -/
def slotKey : Nat := slotJ + 4
/-- Nonce words `j[13..15]` (`slotNon + k` for nonce word `k`). -/
def slotNon : Nat := slotJ + 13
/-- Bytes still to process (`LEN`). -/
def slotLen : Nat := 32
/-- Output pointer (`OUTP`). -/
def slotOutp : Nat := 33
/-- Input pointer (`INP`). -/
def slotInp : Nat := 34
/-- Words of the frame (`FRAME`). -/
def chFrameWords : Nat := 35
/-- The one central value of `chFrameWords`. Proofs that need the exact size use this lemma. -/
theorem chFrameWords_eq : chFrameWords = 35 := by decide
/-- Frame bytes (`FRAME`). -/
def chFrameBytes : Nat := 4 * chFrameWords
/-- The one central value of `chFrameBytes`. -/
theorem chFrameBytes_eq : chFrameBytes = 140 := by decide
/-- First saved-register word: r4-r11, then lr (`SAVED`). -/
def slotSaved : Nat := chFrameWords
/-- Words of the frame plus saved registers: the stack words of the call. -/
def chStackWords : Nat := 44
/-- The one central value of `chStackWords`. -/
theorem chStackWords_eq : chStackWords = 44 := by decide
/-- Stack bytes of the call: `sp0 - fp`, that is `FRAME` plus `SAVED`. -/
def chStackBytes : Nat := 4 * chStackWords
/-- The one central value of `chStackBytes`; the caller's `Valid` window uses the same 176. -/
theorem chStackBytes_eq : chStackBytes = 176 := by decide
/-- Caller's nonce argument word (`ARG_NONCE`). -/
def slotArgNonce : Nat := chStackWords
/-- Caller's counter argument word (`ARG_COUNTER`). -/
def slotArgCtr : Nat := slotArgNonce + 1
/-- Words the call's `fw` view covers: the stack words plus both argument words. -/
def chCallWords : Nat := slotArgCtr + 1
/-- The one central value of `chCallWords`; its byte end is the caller's `outF` window. -/
theorem chCallWords_eq : chCallWords = 46 := by decide

/-! Bounds between the layout sizes. Proofs use these (or the sizes themselves), not literals. -/

/-- The double round's stack window (`droundBytes`, slots `0..11`) lies inside the frame. -/
theorem droundBytes_le_chFrameBytes :
    M0Crypto.Release.ChaChaRound.droundBytes ≤ chFrameBytes := by decide

/-- The double round writes only the spilled words `0..11` (`ChaChaRound.view`'s `k < 12`), so
its window ends below word 12, the first row-d word. -/
theorem droundBytes_le_spilled : M0Crypto.Release.ChaChaRound.droundBytes ≤ 4 * 12 := by decide

/-- The frame lies inside the call's stack. -/
theorem chFrameBytes_le_chStackBytes : chFrameBytes ≤ chStackBytes := by decide

end M0Crypto.Release.ChaChaLayout

namespace M0Crypto.Release.ChaChaSetup

open M0Crypto.Thumb
open M0Crypto.Release.ChaChaLayout (chFrameWords slotArgCtr)

def pro : List Instr :=
  [.push 0xf0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11, .push 0xf0 false,
   .subSp (BitVec.ofNat 7 chFrameWords)]

def chk : List Instr := [.ldrSp 4 (BitVec.ofNat 8 slotArgCtr), .subImm3 5 2 1, .lsrImm 5 5 6, .addReg 5 4 5]

/-- `LOAD_LE32 r3, off`: r0 = little-endian word at `r3 + off`; clobbers r1. -/
def le32 (off : Nat) : List Instr :=
  [.memImm .ldrb 0 3 (BitVec.ofNat 5 off), .memImm .ldrb 1 3 (BitVec.ofNat 5 (off + 1)),
   .lslImm 1 1 8, .dp .orrs 0 1,
   .memImm .ldrb 1 3 (BitVec.ofNat 5 (off + 2)), .lslImm 1 1 16, .dp .orrs 0 1,
   .memImm .ldrb 1 3 (BitVec.ofNat 5 (off + 3)), .lslImm 1 1 24, .dp .orrs 0 1]

end M0Crypto.Release.ChaChaSetup

namespace M0Crypto.Release.ChaChaRet

open M0Crypto.Thumb

open M0Crypto.Release.ChaChaLayout (chFrameWords)

def epi : List Instr :=
  [.addSp (BitVec.ofNat 7 chFrameWords), .pop 0xf0 false, .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7]

end M0Crypto.Release.ChaChaRet

namespace M0Crypto.Release.ChaChaInit

open M0Crypto.Thumb

def kch (off k : Nat) : List Instr := M0Crypto.Release.ChaChaSetup.le32 off ++ [.strSp 0 (BitVec.ofNat 8 k)]

end M0Crypto.Release.ChaChaInit

namespace M0Crypto.Release.ChaChaBlock

open M0Crypto.Thumb

open M0Crypto.Release.ChaChaLayout (slotX slotJ)

def bpre : List Instr := [.addRdSp 4 (BitVec.ofNat 8 slotJ), .addRdSp 5 (BitVec.ofNat 8 slotX)]
def ptr : List Instr := [.ldm 4 0x0f, .stm 5 0x0f]
def btail : List Instr :=
  [.ldm 4 0x0f, .movHi 8 0, .movHi 9 1, .movHi 10 2, .movHi 11 3, .ldrSp 0 (BitVec.ofNat 8 (slotX + 2)),
   .movImm 4 16, .movImm 5 20,
   .movImm 6 24, .movImm 7 25, .movImm 1 10, .movHi 12 1]
def bset : List Instr := bpre ++ ptr ++ ptr ++ ptr ++ btail

end M0Crypto.Release.ChaChaBlock

namespace M0Crypto.Release.ChaChaLoop

open M0Crypto.Thumb
open M0Crypto.Release.ChaChaRound (dround)

/-- Loop-count decrement after each double round. -/
def dec : List Instr := [.movHi 1 12, .subImm8 1 1, .movHi 12 1]

/-- Loop body: double round then decrement. -/
def body : List Instr := dround ++ dec

end M0Crypto.Release.ChaChaLoop

namespace M0Crypto.Release.ChaChaOut

open M0Crypto.Thumb

open M0Crypto.Release.ChaChaLayout (slotX slotJ slotInp slotOutp slotLen)

def post : List Instr :=
  [.ldrSp 2 (BitVec.ofNat 8 slotInp), .ldrSp 3 (BitVec.ofNat 8 slotOutp), .ldrSp 4 (BitVec.ofNat 8 slotLen),
   .strSp 0 (BitVec.ofNat 8 (slotX + 2)), .movHi 0 8, .strSp 0 (BitVec.ofNat 8 (slotX + 12)), .movHi 0 9,
   .strSp 0 (BitVec.ofNat 8 (slotX + 13)), .movHi 0 10, .strSp 0 (BitVec.ofNat 8 (slotX + 14)), .movHi 0 11,
   .strSp 0 (BitVec.ofNat 8 (slotX + 15))]

def ach (i : Nat) : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 (slotX + i)), .ldrSp 1 (BitVec.ofNat 8 (slotJ + i)), .addReg 0 0 1,
   .memImm .ldr 1 2 (BitVec.ofNat 5 i), .dp .eors 0 1, .memImm .str 0 3 (BitVec.ofNat 5 i)]

def bch (i : Nat) : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 (slotX + i)), .ldrSp 1 (BitVec.ofNat 8 (slotJ + i)), .addReg 0 0 1,
   .strSp 0 (BitVec.ofNat 8 (slotX + i))]

def bl : List Instr :=
  [.memReg .ldrb 1 2 0, .memReg .ldrb 6 5 0, .dp .eors 1 6, .memReg .strb 1 3 0, .addImm8 0 1, .dp .cmp 0 4]

def disp : List Instr := [.movImm 4 64, .lslImm 0 2 0, .dp .orrs 0 3, .lslImm 0 0 30]

end M0Crypto.Release.ChaChaOut

namespace M0Crypto.Release.ChaChaXor

open M0Crypto.Thumb

open M0Crypto.Release.ChaChaLayout (slotCtr slotLen slotInp slotOutp chFrameWords slotArgNonce)

/-- The `ldr` of `LEN` and the compare against one block (`.Lnext`, and the loop test). -/
def lenTest : List Instr := [.ldrSp 4 (BitVec.ofNat 8 slotLen), .cmpImm 4 64]

def nxt : List Instr :=
  [.subImm8 4 64, .strSp 4 (BitVec.ofNat 8 slotLen), .addImm8 2 64, .strSp 2 (BitVec.ofNat 8 slotInp),
   .addImm8 3 64, .strSp 3 (BitVec.ofNat 8 slotOutp),
   .ldrSp 0 (BitVec.ofNat 8 slotCtr), .addImm8 0 1, .strSp 0 (BitVec.ofNat 8 slotCtr)]

def stores (n : Nat) : List Instr := (List.range n).map fun i => .strSp 0 (BitVec.ofNat 8 i)

def clr : List Instr :=
  [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0, .addRdSp 5 0] ++
  List.replicate 7 (.stm 5 0x1f) ++ [.movHi 12 0]

theorem clr_size : seqSize clr = 28 := by decide

end M0Crypto.Release.ChaChaXor

/-!
## Offsets of `m0c_chacha20_xor`

Each offset is the previous piece's offset plus the `seqSize` of that piece. The constant pool
(`poolBytes` bytes of data) is the only gap that is not a list.
-/

namespace M0Crypto.Release.ChaChaLayout

open M0Crypto.Thumb

/-- Entry of `m0c_chacha20_xor`. -/
def fnStart : Nat := Artifacts.Release.chacha20_xor

/-! ### Prologue and counter check -/

def cmpOff : Nat := fnStart + seqSize M0Crypto.Release.ChaChaSetup.pro
def bneOff : Nat := cmpOff + seqSize [.cmpImm 2 0]
def b0Off : Nat := bneOff + brSize
def chkOff : Nat := b0Off + brSize
def bccOff : Nat := chkOff + seqSize M0Crypto.Release.ChaChaSetup.chk
def berrOff : Nat := bccOff + brSize
def accOff : Nat := berrOff + brSize

/-! ### Accumulator stores, constant pool and key/nonce loads -/

def strSize : Nat := seqSize [.strSp 0 0]
/-- A literal-pool load followed by its `str`. -/
def litBlkSize : Nat := seqSize [.ldrLit 0 4, .strSp 0 0]
def poolBytes : Nat := 4 * 4

def stOutpOff : Nat := accOff
def stInpOff : Nat := stOutpOff + strSize
def stLenOff : Nat := stInpOff + strSize
def litJ0Off : Nat := stLenOff + strSize
def litJ1Off : Nat := litJ0Off + litBlkSize
def litJ2Off : Nat := litJ1Off + litBlkSize
def litJ3Off : Nat := litJ2Off + litBlkSize
def b7Off : Nat := litJ3Off + litBlkSize
def poolOff : Nat := b7Off + brSize
def keyOff : Nat := poolOff + poolBytes

def kchSize : Nat := seqSize (M0Crypto.Release.ChaChaInit.kch 0 0)
def stCtrOff : Nat := keyOff + 8 * kchSize
def ldrNonceOff : Nat := stCtrOff + strSize
def nonOff : Nat := ldrNonceOff + seqSize [.ldrSp 3 (BitVec.ofNat 8 slotArgNonce)]

/-! ### `.Lblock` and the double-round loop -/

def bpreOff : Nat := nonOff + 3 * kchSize
def ptr1Off : Nat := bpreOff + seqSize M0Crypto.Release.ChaChaBlock.bpre
def ptr2Off : Nat := ptr1Off + seqSize M0Crypto.Release.ChaChaBlock.ptr
def ptr3Off : Nat := ptr2Off + seqSize M0Crypto.Release.ChaChaBlock.ptr
def btailOff : Nat := ptr3Off + seqSize M0Crypto.Release.ChaChaBlock.ptr
def droundOff : Nat := btailOff + seqSize M0Crypto.Release.ChaChaBlock.btail
def decOff : Nat := droundOff + seqSize M0Crypto.Release.ChaChaRound.dround
def beqOff : Nat := decOff + seqSize M0Crypto.Release.ChaChaLoop.dec
def loopBOff : Nat := beqOff + brSize

/-! ### After the rounds and the output phases -/

def postOff : Nat := loopBOff + brSize
def cmpEOff : Nat := postOff + seqSize M0Crypto.Release.ChaChaOut.post
def blo2Off : Nat := cmpEOff + seqSize [.cmpImm 4 64]
def dispOff : Nat := blo2Off + brSize
def bne2Off : Nat := dispOff + seqSize M0Crypto.Release.ChaChaOut.disp
def achOff : Nat := bne2Off + brSize
def achSize : Nat := seqSize (M0Crypto.Release.ChaChaOut.ach 0)
def b38eOff : Nat := achOff + 16 * achSize
def bchOff : Nat := b38eOff + brSize
def bchSize : Nat := seqSize (M0Crypto.Release.ChaChaOut.bch 0)
def bmidOff : Nat := bchOff + 16 * bchSize
def blOff : Nat := bmidOff + seqSize [.addRdSp 5 0, .movImm 0 0]
def bloOff : Nat := blOff + seqSize M0Crypto.Release.ChaChaOut.bl
def n1Off : Nat := bloOff + brSize
def blsOff : Nat := n1Off + seqSize M0Crypto.Release.ChaChaXor.lenTest
def nxtOff : Nat := blsOff + brSize
def bbackOff : Nat := nxtOff + seqSize M0Crypto.Release.ChaChaXor.nxt

/-! ### Clearing, epilogue and error return -/

def clrOff : Nat := bbackOff + brSize
def zOff : Nat := clrOff + seqSize M0Crypto.Release.ChaChaXor.clr
def epiOff : Nat := zOff + seqSize [.movImm 0 0]
def popOff : Nat := epiOff + seqSize M0Crypto.Release.ChaChaRet.epi
def errOff : Nat := popOff + seqSize [.pop 0xf0 true]
def berrOff2 : Nat := errOff + seqSize [.movImm 0 0, .dp .mvns 0 0]

end M0Crypto.Release.ChaChaLayout
