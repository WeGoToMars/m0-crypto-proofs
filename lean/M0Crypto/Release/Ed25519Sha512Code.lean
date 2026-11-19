import M0Crypto.Release.RoutineBranch
import M0Crypto.Release.Ed25519Build

/-!
# `m0c_sha512_block` as instruction lists

The block function of `tools/ed25519/gen_sha512.py` (`emit_block`), macro by macro: `sigmaI` is
macro `sigma`, `roundBody` is `round_body`, `schedBody` is one pass of `schedule`. Registers are
the generator's; frame offsets and masks are its constants, stated once below. A round names its
variables through a slot map `σ` (variable `x`, `a = 0 … h = 7`, lives in frame pair `σ x`); round
`r` of a group uses `slot r` (`Ed25519Sha512Rounds`).

`pieces o pool` is the whole function at offset `o`, with the literal pool that the generator
flushes inside the group body at `pool` (the data range inside the function): the group body is cut there by a
`b` over the pool word. Every offset is a sum of piece sizes; `blockAt` checks the pieces against
each build's bytes at the generated symbols.
-/

namespace M0Crypto.Release.Ed25519Sha512Code

open M0Crypto.Armv6M (Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.RoutinePieces

/-! ## Constants of the generator -/

/-- Block frame, in bytes from `sp`: the variables `V`, the schedule `W`, the saved `H` pointer,
the group counter and the `K` pointer (`VOFF, WOFF, HP, GRP, KP, BFRAME`). -/
def VOFF : Nat := 0
def WOFF : Nat := 64
def HP : Nat := 192
def GRP : Nat := 196
def KP : Nat := 200
def BFRAME : Nat := 204
/-- Bytes of the eight variables `V` (and of a group's `K` and `W` words). -/
def VB : Nat := 8 * 8

/-- The schedule buffer holds 16 eight-byte words; `MASK` wraps a byte index (`0x78`). -/
def MASK : Nat := 8 * 16 - 8
/-- A group uses one half of the buffer: `HALF = 2 ^ HALF_SHIFT` bytes. -/
def HALF_SHIFT : Nat := 6
def HALF : Nat := 2 ^ HALF_SHIFT
/-- Ten groups of eight rounds; the schedule is refreshed before even groups from 2 on. -/
def GROUPS : Nat := 10

/-- The `imm8` of a frame word at byte offset `n`. -/
abbrev wd (n : Nat) : BitVec 8 := BitVec.ofNat 8 (n / 4)

/-! ## Macro `sigma` -/

/-- A shift of macro `sigma`: into the high (`dHi`) or low result word, left or right, of the
high (`sHi`) or low input word, by `amt`. -/
structure STerm where
  dHi : Bool
  left : Bool
  sHi : Bool
  amt : Nat

/-- The four shifts of `ROTR n`. -/
def rotTerms (n : Nat) : List STerm :=
  if n < 32 then [⟨false, false, false, n⟩, ⟨false, true, true, 32 - n⟩, ⟨true, false, true, n⟩,
    ⟨true, true, false, 32 - n⟩]
  else [⟨false, false, true, n - 32⟩, ⟨false, true, false, 64 - n⟩, ⟨true, false, false, n - 32⟩,
    ⟨true, true, true, 64 - n⟩]

/-- The three shifts of `SHR k`. -/
def shrTerms (k : Nat) : List STerm := [⟨false, false, false, k⟩, ⟨false, true, true, 32 - k⟩,
  ⟨true, false, true, k⟩]

def sTerms (rots : List Nat) (shr : Option Nat) : List STerm :=
  rots.flatMap rotTerms ++ (shr.map shrTerms).getD []

/-- One shift into `d` from `s`. -/
def shI (left : Bool) (d s : LowReg) (a : Nat) : Instr :=
  if left then .lslImm d s (BitVec.ofNat 5 a) else .lsrImm d s (BitVec.ofNat 5 a)

/-- Macro `sigma` with `xl, xh, dl, dh, t = r0, r1, r2, r3, r4` (all four uses): the first shift
into a result word writes it, each later one goes through `t` and `eors`. `sl`, `sh`: the low
and high result words are started. -/
def emitS : List STerm → Bool → Bool → List Instr
  | [], _, _ => []
  | t :: ts, sl, sh =>
    if (if t.dHi then sh else sl) then
      shI t.left 4 (if t.sHi then 1 else 0) t.amt :: .dp .eors (if t.dHi then 3 else 2) 4 ::
        emitS ts sl sh
    else shI t.left (if t.dHi then 3 else 2) (if t.sHi then 1 else 0) t.amt ::
      emitS ts (sl || !t.dHi) (sh || t.dHi)

def sigmaI (rots : List Nat) (shr : Option Nat) : List Instr := emitS (sTerms rots shr) false false

/-! ## Macro `round_body` -/

/-- The frame word of the low or high half of pair `i` of `V` (generator `v`, with `i = σ x`). -/
def vw (i : Nat) (hi : Bool) : Nat := (VOFF + 8 * i) / 4 + (if hi then 1 else 0)

def ldV (t : LowReg) (σ : Nat → Nat) (x : Nat) (hi : Bool) : Instr := .ldrSp t (BitVec.ofNat 8 (vw (σ x) hi))
def stV (t : LowReg) (σ : Nat → Nat) (x : Nat) (hi : Bool) : Instr := .strSp t (BitVec.ofNat 8 (vw (σ x) hi))

/-- `adds dl, xl; adcs dh, xh`. -/
def addP (dl dh xl xh : LowReg) : List Instr := [.addReg dl dl xl, .dp .adcs dh xh]

/-- `round_body` up to `T1 = Σ1(e) + Ch + h + K + W` in `r2:r3`; `W` is word `j` of `r6`. -/
def roundT1 (σ : Nat → Nat) (j : Nat) : List Instr :=
  [ldV 0 σ 4 false, ldV 1 σ 4 true] ++ sigmaI [14, 18, 41] none ++
  [ldV 4 σ 5 false, ldV 5 σ 6 false, .dp .eors 4 5, .dp .ands 4 0, .dp .eors 4 5,
   ldV 5 σ 5 true, ldV 0 σ 6 true, .dp .eors 5 0, .dp .ands 5 1, .dp .eors 5 0] ++ addP 2 3 4 5 ++
  [ldV 4 σ 7 false, ldV 5 σ 7 true] ++ addP 2 3 4 5 ++ [.ldm 7 0x30] ++ addP 2 3 4 5 ++
  [.memImm .ldr 4 6 (BitVec.ofNat 5 (2 * j)), .memImm .ldr 5 6 (BitVec.ofNat 5 (2 * j + 1))] ++
  addP 2 3 4 5

/-- `e' = d + T1` into `d`'s slot; `T1` saved in `r8:r9`. -/
def roundD (σ : Nat → Nat) : List Instr :=
  [ldV 4 σ 3 false, ldV 5 σ 3 true] ++ addP 4 5 2 3 ++ [stV 4 σ 3 false, stV 5 σ 3 true, .movHi 8 2, .movHi 9 3]

/-- `a' = Σ0(a) + Maj + T1` into `h`'s slot. -/
def roundA (σ : Nat → Nat) : List Instr :=
  [ldV 0 σ 0 false, ldV 1 σ 0 true] ++ sigmaI [28, 34, 39] none ++
  [ldV 4 σ 1 false, ldV 5 σ 2 false, .dp .eors 5 4, .dp .eors 0 4, .dp .ands 0 5, .dp .eors 0 4,
   ldV 4 σ 1 true, ldV 5 σ 2 true, .dp .eors 5 4, .dp .eors 1 4, .dp .ands 1 5, .dp .eors 1 4] ++
  addP 2 3 0 1 ++ [.movHi 4 8, .movHi 5 9] ++ addP 2 3 4 5 ++ [stV 2 σ 7 false, stV 3 σ 7 true]

def roundBody (σ : Nat → Nat) (j : Nat) : List Instr := roundT1 σ j ++ roundD σ ++ roundA σ

/-- `(x − r) mod 8`: the slot of variable `x` in round `r` (`Ed25519Sha512Rounds.slot`). -/
def rslot (r x : Nat) : Nat := (x + 8 - r % 8) % 8

/-- The eight unrolled rounds of a group. -/
def groupI : List Instr := (List.range 8).flatMap fun r => roundBody (rslot r) r

/-! ## Macro `schedule` -/

/-- `r5 = (r7 + 8a) & MASK`: the byte offset of `W[j + a]` with `r7 = 8j`. -/
def schedIdx (a : Nat) : List Instr :=
  if a = 0 then [.movImm 5 (BitVec.ofNat 8 MASK), .dp .ands 5 7]
  else [.movHi 5 7, .addImm8 5 (BitVec.ofNat 8 (8 * a)), .movImm 4 (BitVec.ofNat 8 MASK), .dp .ands 5 4]

/-- `W[j + a]` into `rl:rh`. -/
def ldW (a : Nat) (rl rh : LowReg) : List Instr :=
  schedIdx a ++ [.memReg .ldr rl 6 5, .addImm8 5 4, .memReg .ldr rh 6 5]

/-- One pass `W[j] += σ0(W[j+1]) + W[j+9] + σ1(W[j+14])`, then `r7 += 8; cmp r7, #128`. -/
def schedBody : List Instr :=
  ldW 1 0 1 ++ sigmaI [1, 8] (some 7) ++ ldW 0 0 1 ++ addP 0 1 2 3 ++ ldW 9 2 3 ++ addP 0 1 2 3 ++
  [.movHi 8 0, .movHi 9 1] ++ ldW 14 0 1 ++ sigmaI [19, 61] (some 6) ++ [.movHi 0 8, .movHi 1 9] ++
  addP 0 1 2 3 ++ schedIdx 0 ++ [.memReg .str 0 6 5, .addImm8 5 4, .memReg .str 1 6 5,
  .addImm8 7 8, .cmpImm 7 (BitVec.ofNat 8 (8 * 16))]

/-! ## The function -/

def pre : List Instr := [.push 0 true, .subSp (BitVec.ofNat 7 (BFRAME / 4)), .strSp 0 (wd HP),
  .addRdSp 2 (wd WOFF), .movImm 3 16]

/-- One pass of the big-endian load of the block into `W`. -/
def wload : List Instr := [.ldm 1 0x30, .rev 6 4, .rev 4 5, .stm 2 0x50, .subImm8 3 1]

/-- `V = H`. -/
def vcopy : List Instr := [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] ++
  (List.replicate 4 [.ldm 0 0x3c, .stm 1 0x3c]).flatten

/-- After `ldr r7, =lit`: `r7 = K`, the pointer and the counter stored. -/
def kinit : List Instr := [.addPc 7, .strSp 7 (wd KP), .movImm 0 0, .strSp 0 (wd GRP)]

def gHead : List Instr := [.ldrSp 0 (wd GRP), .cmpImm 0 2]
def gOdd : List Instr := [.lsrImm 1 0 1]
def sPre : List Instr := [.addRdSp 6 (wd WOFF), .movImm 7 0]
/-- `r6 = W + HALF (g mod 2)`, `r7 = K` pointer. -/
def gSel : List Instr := [.ldrSp 0 (wd GRP), .lslImm 0 0 (BitVec.ofNat 5 HALF_SHIFT),
  .movImm 1 (BitVec.ofNat 8 HALF), .dp .ands 0 1, .addRdSp 6 (wd WOFF), .addReg 6 6 0, .ldrSp 7 (wd KP)]
def gTail : List Instr := [.strSp 7 (wd KP), .ldrSp 0 (wd GRP), .addImm8 0 1, .strSp 0 (wd GRP),
  .cmpImm 0 (BitVec.ofNat 8 GROUPS)]

/-- One word of `H += V`. -/
def hAddW : List Instr := [.ldm 1 0x0c, .memImm .ldr 4 0 0, .memImm .ldr 5 0 1, .addReg 2 2 4,
  .dp .adcs 3 5, .stm 0 0x0c]
def hAdd : List Instr := [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] ++ (List.replicate 8 hAddW).flatten
def post : List Instr := [.addSp (BitVec.ofNat 7 (BFRAME / 4)), .pop 0 true]

/-! ## Offsets: each piece after the one before -/

def oWL (o : Nat) : Nat := o + seqSize pre
def oCopy (o : Nat) : Nat := oWL o + seqSize wload + brSize
def oLit (o : Nat) : Nat := oCopy o + seqSize vcopy
/-- The `imm8` of `ldr r7, =lit` loading the word at `pool`. -/
def litImm (o pool : Nat) : BitVec 8 := BitVec.ofNat 8 ((pool - (oLit o + 4) / 4 * 4) / 4)
def oG (o : Nat) : Nat := oLit o + 2 + seqSize kinit
def oOdd (o : Nat) : Nat := oG o + seqSize gHead + brSize
def oS (o : Nat) : Nat := oOdd o + seqSize gOdd + brSize + seqSize sPre
def oSkip (o : Nat) : Nat := oS o + seqSize schedBody + brSize
def oR (o : Nat) : Nat := oSkip o + seqSize gSel
/-- The rounds before the pool: their instructions up to the `b` at `pool − 2`. -/
def kPool (o pool : Nat) : Nat := (pool - brSize - oR o) / 2
def oR2 (pool : Nat) : Nat := pool + 4
def oT (o pool : Nat) : Nat := oR2 pool + seqSize (groupI.drop (kPool o pool))
def oEnd (o pool : Nat) : Nat := oT o pool + seqSize gTail + 2 * brSize
def oPost (o pool : Nat) : Nat := oEnd o pool + seqSize hAdd

/-- The code before the pool. -/
def piecesA (o pool : Nat) : List Piece :=
  [.seq pre, .seq wload, .bcond 1 (oWL o), .seq vcopy, .seq [.ldrLit 7 (litImm o pool)], .seq kinit,
   .seq gHead, .bcond 3 (oSkip o), .seq gOdd, .bcond 2 (oSkip o), .seq sPre, .seq schedBody,
   .bcond 1 (oS o), .seq gSel, .seq (groupI.take (kPool o pool)), .b (oR2 pool)]

/-- The code after the pool. -/
def piecesB (o pool : Nat) : List Piece :=
  [.seq (groupI.drop (kPool o pool)), .seq gTail, .bcond 0 (oEnd o pool), .b (oG o), .seq hAdd,
   .seq post]

/-- The checks of the layout: the pieces at `o` and after the pool, the pool word right after
the `b`, the function ending at `o + size`. -/
def blockAt (o pool : Nat) (bytes : List (BitVec 8)) (size : Nat) : Bool :=
  piecesAt bytes o (piecesA o pool) && piecesAt bytes (oR2 pool) (piecesB o pool) &&
  (o + piecesSize (piecesA o pool) == pool) && (oPost o pool + seqSize post == o + size)

open M0Crypto.Artifacts M0Crypto.Release.Ed25519

/-- The size of `m0c_sha512_block`: up to the next function. -/
def size : Nat := Ed25519Compact.sha512_init - Ed25519Compact.sha512_block

/-- The data range inside `m0c_sha512_block`'s own bytes. -/
def poolRange : Option (Nat × Nat) := Ed25519Compact.dataRanges.find? fun r =>
  Ed25519Compact.sha512_block ≤ r.1 && r.2 ≤ Ed25519Compact.sha512_block + size

/-- The pool of `m0c_sha512_block`: the start of its data range. -/
def pool : Nat := (poolRange.getD (0, 0)).1

/-- The function's data range is one word, the literal. -/
theorem pool_word : poolRange = some (pool, pool + 4) := by decide

theorem compact_at : blockAt Ed25519Compact.sha512_block pool Build.compact.bytes size = true := by
  simp only [blockAt, piecesAt_eq_scan]; decide +kernel

theorem fast_at : blockAt Ed25519Compact.sha512_block pool Build.fast.bytes size = true := by
  simp only [blockAt, piecesAt_eq_scan]; decide +kernel

end M0Crypto.Release.Ed25519Sha512Code
