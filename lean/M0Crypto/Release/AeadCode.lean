import M0Crypto.Release.Reach
import M0Crypto.Release.Layout
import M0Crypto.Release.AeadContract
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000

/-!
AEAD code layer: the release-byte instruction lists of
`m0c_chacha20poly1305_encrypt` (offset `0x970`) and `m0c_chacha20poly1305_decrypt`
(offset `0xa90`). Their byte correspondence to the frozen artifact is proved in
`AeadCheck`.

Both functions share one frame (offsets from SP after `sub sp, #124`):
`0` nonce pointer and `4` counter (outgoing stack arguments of `m0c_chacha20_xor`),
`8` the 64-byte Poly1305 context `CTX`, `72` the 32-byte scratch block `BLK`,
`104/108/112/116` the saved `out`, `tag`, `in`, `len`. The caller's stack arguments
`aad`, `aad_len`, `key`, `nonce` are at `144..160`.

`MAC_PADDED` is the same 60-byte sequence at four offsets, so its pieces are
lists parameterised only by the `bl` immediates.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- Size of the AEAD frame: `ACall.A = sp0 - aeadFrame`. -/
def aeadFrame : Nat := 144

def xorOff : Nat := Artifacts.Release.chacha20_xor
def initOff : Nat := Artifacts.Release.poly1305_init
def blocksOff : Nat := Artifacts.Release.poly1305_blocks
def finishOff : Nat := Artifacts.Release.poly1305_finish

/-- The ChaCha20 entry is the first function of the image, so a `bl xorOff` lands on the base
address. The chacha20 proofs use this as the entry point of the XOR routine; it is the one
layout fact they need, and it is proved from the artifact symbol, not from a pin. -/
theorem xorOff_base : xorOff = 0 := by decide

/-- Byte offset reached by `bl imm` placed at `off`. -/
def blTarget (off : Nat) (imm : BitVec 25) : Word := BitVec.ofNat 32 off + 4#32 + imm.signExtend 32

/-! ## Shared prologue and setup -/

def zeroCtx : List Instr := (List.range 16).map fun i => .strSp 0 (BitVec.ofNat 8 (2 + i))

/-- `push`, `sub sp`, `SAVE_ARGS`, zero `CTX` and the counter, nonce argument, xor arguments. -/
def pro : List Instr :=
  [.push 0xf0 true, .subSp 0x1f, .strSp 0 0x1a, .strSp 1 0x1b, .strSp 2 0x1c, .strSp 3 0x1d,
   .movImm 0 0] ++ zeroCtx ++
  [.strSp 0 0x01, .ldrSp 0 0x27, .strSp 0 0x00, .addRdSp 0 0x02, .lslImm 1 0 0, .movImm 2 0x40,
   .ldrSp 3 0x26]

/-- Copy the one-time key (first 32 bytes of block 0) from `CTX` to `BLK`; init arguments. -/
def copy : List Instr :=
  [.addRdSp 0 0x02, .addRdSp 1 0x12, .ldm 0 0x3c, .stm 1 0x3c, .ldm 0 0x3c, .stm 1 0x3c,
   .addRdSp 0 0x02, .addRdSp 1 0x12]

/-- `CRYPT`: counter 1, then `out, in, len, key`. -/
def crypt : List Instr :=
  [.movImm 0 1, .strSp 0 0x01, .ldrSp 0 0x1a, .ldrSp 1 0x1c, .ldrSp 2 0x1d, .ldrSp 3 0x26]

/-! ## Relative offsets of the shared prologue and setup, from the entry `e` -/

/-- `bl` to `xorOff` ends `pro`. -/
def proXorOff : Nat := seqSize pro
/-- Start of `copy`, after the xor call. -/
def copyOff : Nat := proXorOff + blSize
/-- `bl` to `initOff`, at the end of `copy`. -/
def initCallOff : Nat := copyOff + seqSize copy
/-- The first offset after the `init` call. -/
def setupEnd : Nat := initCallOff + blSize

theorem proXorOff_even : proXorOff % 2 = 0 := by decide
theorem copyOff_even : copyOff % 2 = 0 := by decide
theorem initCallOff_even : initCallOff % 2 = 0 := by decide
/-- Each `bl` returns to the next piece: its width is `4`, so its return address is the next offset. -/
theorem proXorOff_ret : proXorOff + 4 = copyOff := by decide
theorem copyOff_end : copyOff + seqSize copy = initCallOff := by decide
theorem initCallOff_ret : initCallOff + 4 = setupEnd := by decide

/-! ## Relative offsets of `CRYPT`, from its start `off` -/

/-- The `bl` to `chacha20_xor` (block-keystream call) ends `CRYPT`. -/
def cryptXorOff : Nat := seqSize crypt
def cryptEnd : Nat := cryptXorOff + blSize
theorem cryptXorOff_even : cryptXorOff % 2 = 0 := by decide
theorem cryptXorOff_ret : cryptXorOff + 4 = cryptEnd := by decide

/-- Load `r4 = aad`, `r5 = aad_len`. -/
def loadAad : List Instr := [.ldrSp 4 0x24, .ldrSp 5 0x25]
/-- Encrypt MACs the ciphertext as written: `r4 = out`, `r5 = len`. -/
def loadOut : List Instr := [.ldrSp 4 0x1a, .ldrSp 5 0x1d]
/-- Decrypt MACs the received ciphertext: `r4 = in`, `r5 = len`. -/
def loadIn : List Instr := [.ldrSp 4 0x1c, .ldrSp 5 0x1d]
/-- Any two-load setup `ldr r4; ldr r5` is one 4-byte body, whatever its immediates. -/
theorem loadPair_size (u v : BitVec 8) : seqSize [.ldrSp 4 u, .ldrSp 5 v] = 4 := rfl

/-! ## `MAC_PADDED` at offset `m`, ending at `m + macSize` -/

def macA : List Instr := [.lsrImm 2 5 4]
def macB : List Instr := [.addRdSp 0 0x02, .lslImm 1 4 0, .movImm 3 1]
def macC : List Instr := [.movImm 6 0x0f, .dp .ands 6 5]
def macD : List Instr :=
  [.lsrImm 0 5 4, .lslImm 0 0 4, .addReg 4 4 0, .movImm 0 0,
   .strSp 0 0x12, .strSp 0 0x13, .strSp 0 0x14, .strSp 0 0x15, .addRdSp 1 0x12, .movImm 2 0]
def macL : List Instr := [.memReg .ldrb 0 4 2, .memReg .strb 0 1 2, .addImm8 2 1, .dp .cmp 2 6]
def macE : List Instr := [.addRdSp 0 0x02, .movImm 2 1, .movImm 3 1]

/-- Offsets inside `MAC_PADDED`, each the end of the piece before it. -/
def macBr0Off : Nat := seqSize macA                 -- `beq` to `macCOff`
def macBOff : Nat := macBr0Off + brSize
def macBlOff : Nat := macBOff + seqSize macB        -- `bl` to `blocks`
def macCOff : Nat := macBlOff + blSize
def macBr1Off : Nat := macCOff + seqSize macC       -- `beq` to `macSize`
def macDOff : Nat := macBr1Off + brSize
def macLOff : Nat := macDOff + seqSize macD         -- loop head; `bne` back to it
def macBr2Off : Nat := macLOff + seqSize macL
def macEOff : Nat := macBr2Off + brSize
def macBl2Off : Nat := macEOff + seqSize macE       -- `bl` to `blocks`
def macSize : Nat := macBl2Off + blSize

theorem macBr0Off_even : macBr0Off % 2 = 0 := by decide
theorem macBr0Off_fall : macBr0Off + 2 = macBOff := by decide
theorem macBr0Off_le : macBr0Off ≤ macCOff := by decide
/-- The `bcond` at `macBr0Off` reaches `macCOff`: the PC (`+4`) plus the sign-extended
displacement is the target. Closed, so checked from the definitions. -/
theorem macBr0_disp :
    4#32 + ((brImm8 macBr0Off macCOff ++ 0#1).signExtend 32 : BitVec 32) =
      BitVec.ofNat 32 (macCOff - macBr0Off) := by decide +kernel
theorem macBr0Off_fits : macBr0Off + 2 ≤ macSize := by decide
theorem macBOff_even : macBOff % 2 = 0 := by decide
theorem macBlOff_even : macBlOff % 2 = 0 := by decide
theorem macBlOff_ret : macBlOff + 4 = macCOff := by decide
theorem macBlOff_fits : macBlOff + 4 ≤ macSize := by decide
theorem macLOff_even : macLOff % 2 = 0 := by decide
theorem macBr2Off_even : macBr2Off % 2 = 0 := by decide
theorem macBr2Off_back : macBr2Off = macLOff + seqSize macL := by decide
theorem macBr2Off_fall : macBr2Off + 2 = macEOff := by decide
theorem macBr2Off_fits : macBr2Off + 2 ≤ macSize := by decide
theorem macCOff_even : macCOff % 2 = 0 := by decide
theorem macBr1Off_even : macBr1Off % 2 = 0 := by decide
theorem macBr1Off_fall : macBr1Off + 2 = macDOff := by decide
theorem macBr1Off_le : macBr1Off ≤ macSize := by decide
/-- The `bcond` at `macBr1Off` reaches `macSize`; see `macBr0_disp`. -/
theorem macBr1_disp :
    4#32 + ((brImm8 macBr1Off macSize ++ 0#1).signExtend 32 : BitVec 32) =
      BitVec.ofNat 32 (macSize - macBr1Off) := by decide +kernel
theorem macBr1Off_fits : macBr1Off + 2 ≤ macSize := by decide
theorem macDOff_even : macDOff % 2 = 0 := by decide
theorem macEOff_even : macEOff % 2 = 0 := by decide
theorem macBl2Off_even : macBl2Off % 2 = 0 := by decide
theorem macBl2Off_fits : macBl2Off + 4 ≤ macSize := by decide
theorem macBl2Off_end : macBl2Off + 4 = macSize := by decide
theorem macSize_le : macSize ≤ 60 := by decide

/-- All of `MAC_PADDED` at `m`, given the two `bl` immediates. The `bcond`/`bl` immediates are
computed from the layout offsets (`brImm8`, `blImm`). -/
def MacAt (m : Nat) (i1 i2 : BitVec 25) : Prop :=
  seqAt B m macA = true ∧ instrAt B (m + macBr0Off) = some (.bcond 0 (brImm8 (m + macBr0Off) (m + macCOff))) ∧
  seqAt B (m + macBOff) macB = true ∧ instrAt B (m + macBlOff) = some (.bl i1) ∧
  seqAt B (m + macCOff) macC = true ∧ instrAt B (m + macBr1Off) = some (.bcond 0 (brImm8 (m + macBr1Off) (m + macSize))) ∧
  seqAt B (m + macDOff) macD = true ∧
  seqAt B (m + macLOff) macL = true ∧ instrAt B (m + macBr2Off) = some (.bcond 1 (brImm8 (m + macBr2Off) (m + macLOff))) ∧
  seqAt B (m + macEOff) macE = true ∧ instrAt B (m + macBl2Off) = some (.bl i2) ∧
  blTarget (m + macBlOff) i1 = BitVec.ofNat 32 blocksOff ∧
  blTarget (m + macBl2Off) i2 = BitVec.ofNat 32 blocksOff

/-- `MAC_LENGTHS`: `le64(aad_len) || le64(len)` into `BLK`, blocks arguments. -/
def lengths : List Instr :=
  [.ldrSp 0 0x25, .strSp 0 0x12, .ldrSp 0 0x1d, .strSp 0 0x14, .movImm 0 0, .strSp 0 0x13,
   .strSp 0 0x15, .addRdSp 0 0x02, .addRdSp 1 0x12, .movImm 2 1, .movImm 3 1]

/-- Finish arguments: encrypt writes the caller's tag, decrypt the expected tag into `BLK`. -/
def finE : List Instr := [.addRdSp 0 0x02, .ldrSp 1 0x1b]
def finD : List Instr := [.addRdSp 0 0x02, .addRdSp 1 0x12]

/-! ## `CLEAR_FRAME`: 24 words from `CTX` -/

def clrA : List Instr := [.addRdSp 1 0x02, .movImm 2 0x18, .movImm 0 0]
def clrL : List Instr := [.memImm .str 0 1 0, .addImm8 1 4, .subImm8 2 1] -- then `bne` back

def epiE : List Instr := [.movImm 0 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .addSp 0x1f]
def epiD : List Instr := [.lslImm 0 4 0, .movImm 1 0, .movImm 2 0, .movImm 3 0, .addSp 0x1f]

/-! ## Decrypt: full 16-byte tag comparison and verdict -/

def cmpA : List Instr := [.ldrSp 1 0x1b, .addRdSp 2 0x12, .movImm 3 0, .movImm 4 0]
def cmpL : List Instr :=
  [.memReg .ldrb 0 1 4, .memReg .ldrb 5 2 4, .dp .eors 0 5, .dp .orrs 3 0, .addImm8 4 1, .cmpImm 4 0x10]
def verdict : List Instr := [.movImm 5 0, .movImm 0 0, .cmpImm 3 0]
def accept : List Instr := [.movImm 4 0]
def reject : List Instr := [.movImm 4 2, .dp .rsbs 4 4]

/-! ## Piece starts of the two entry functions, each the end of the piece before it -/

/-- `m0c_chacha20poly1305_encrypt`: the shared prefix, then the MAC and output. -/
def encXorAt : Nat := encOff + seqSize pro                  -- `bl` xor
def encCopyAt : Nat := encXorAt + blSize
def encInitAt : Nat := encCopyAt + seqSize copy             -- `bl` init
def encCryptAt : Nat := encInitAt + blSize
def encXor1At : Nat := encCryptAt + seqSize crypt           -- `bl` xor
def encLoadAadAt : Nat := encXor1At + blSize
def encMac0At : Nat := encLoadAadAt + seqSize loadAad       -- `MacAt`
def encLoadOutAt : Nat := encMac0At + macSize
def encMac1At : Nat := encLoadOutAt + seqSize loadOut       -- `MacAt`
def encLengthsAt : Nat := encMac1At + macSize
def encBlocksAt : Nat := encLengthsAt + seqSize lengths     -- `bl` blocks
def encFinEAt : Nat := encBlocksAt + blSize
def encFinishAt : Nat := encFinEAt + seqSize finE           -- `bl` finish
def encClrAAt : Nat := encFinishAt + blSize
def encClrLAt : Nat := encClrAAt + seqSize clrA
def encLoopBrAt : Nat := encClrLAt + seqSize clrL            -- `bcond` back to `clrL`
def encEpiAt : Nat := encLoopBrAt + brSize
def encPopAt : Nat := encEpiAt + seqSize epiE
def encEnd : Nat := encPopAt + seqSize [.pop 0xf0 true]

/-- `m0c_chacha20poly1305_decrypt`: the shared prefix, the two MACs, the tag compare, output. -/
def decXorAt : Nat := decOff + seqSize pro                  -- `bl` xor
def decCopyAt : Nat := decXorAt + blSize
def decInitAt : Nat := decCopyAt + seqSize copy             -- `bl` init
def decLoadAadAt : Nat := decInitAt + blSize
def decMac0At : Nat := decLoadAadAt + seqSize loadAad       -- `MacAt`
def decLoadInAt : Nat := decMac0At + macSize
def decMac1At : Nat := decLoadInAt + seqSize loadIn         -- `MacAt`
def decLengthsAt : Nat := decMac1At + macSize
def decBlocksAt : Nat := decLengthsAt + seqSize lengths     -- `bl` blocks
def decFinDAt : Nat := decBlocksAt + blSize
def decFinishAt : Nat := decFinDAt + seqSize finD           -- `bl` finish
def decCmpAAt : Nat := decFinishAt + blSize
def decCmpLAt : Nat := decCmpAAt + seqSize cmpA
def decCmpBrAt : Nat := decCmpLAt + seqSize cmpL            -- `bcond` back to `cmpL`
def decVerdictAt : Nat := decCmpBrAt + brSize
def decRejectBrAt : Nat := decVerdictAt + seqSize verdict   -- `bcond` to `reject`
def decCryptAt : Nat := decRejectBrAt + brSize
def decXor1At : Nat := decCryptAt + seqSize crypt           -- `bl` xor
def decAcceptAt : Nat := decXor1At + blSize
def decSkipAt : Nat := decAcceptAt + seqSize accept         -- `b` to `clrA`
def decRejectAt : Nat := decSkipAt + brSize
def decClrAAt : Nat := decRejectAt + seqSize reject
def decClrLAt : Nat := decClrAAt + seqSize clrA
def decLoopBrAt : Nat := decClrLAt + seqSize clrL            -- `bcond` back to `clrL`
def decEpiAt : Nat := decLoopBrAt + brSize
def decPopAt : Nat := decEpiAt + seqSize epiD
def decEnd : Nat := decPopAt + seqSize [.pop 0xf0 true]

end M0Crypto.Release.Aead
