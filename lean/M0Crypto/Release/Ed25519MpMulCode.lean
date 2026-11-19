import M0Crypto.Release.RoutineSegs
import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.RoutinePieces
import M0Crypto.Release.Field25519Mul

/-!
# `m0c_mp_mul` as instruction lists

`emit_mp_mul` of `tools/gen_ed25519.py`: `dst[0 … 2n) = a[0 … n) · b[0 … n)` with `n = r3`. The
frame holds the four arguments and the row counter. A zero loop clears `dst`; row `i` loads
`a[i]` into `r8`, then the inner loop (`mac`) adds `a[i] · b[j]`, the word `dst[i + j]` and the
carry `r12` into `dst[i + j]` and the new carry; the row's carry goes to `dst[i + n]`. The
pointers `b + 4 j` and `dst + 4 (i + j)` live in `r10`, `r11`, the count in `r9`. `mpAt` checks
the pieces against each build's bytes; every offset is a sum of piece sizes.
-/

namespace M0Crypto.Release.Ed25519MpMulCode

open M0Crypto.Thumb
open M0Crypto.Release.RoutinePieces

/-- Frame words, in bytes from `sp`: `dst`, `a`, `b`, `n`, the row. -/
def SD : Nat := 0
def SA : Nat := 4
def SB : Nat := 8
def SN : Nat := 12
def ROW : Nat := 16
def FRAME : Nat := 20

abbrev wd (n : Nat) : BitVec 8 := BitVec.ofNat 8 (n / 4)

def enter : List Instr := [.push 0 true, .subSp (BitVec.ofNat 7 (FRAME / 4))]
/-- The arguments to the frame, `r4 = 2 n`, `r5 = 0`. -/
def pre : List Instr := [.strSp 0 (wd SD), .strSp 1 (wd SA), .strSp 2 (wd SB), .strSp 3 (wd SN),
  .lslImm 4 3 1, .movImm 5 0]
/-- A pass of the zero loop: `stm r0!, {r5}; subs r4, #1`. -/
def zbody : List Instr := [.stm 0 0x20, .subImm8 4 1]
def zpost : List Instr := [.strSp 4 (wd ROW)]
/-- The start of row `i`: `r8 = a[i]`, `r11 = dst + 4 i`, `r10 = b`, `r9 = n`, `r12 = 0`. -/
def head : List Instr := [.ldrSp 1 (wd SA), .ldrSp 4 (wd ROW), .lslImm 5 4 2, .memReg .ldr 0 1 5,
  .movHi 8 0, .ldrSp 0 (wd SD), .addReg 0 0 5, .movHi 11 0, .ldrSp 2 (wd SB), .movHi 10 2,
  .ldrSp 3 (wd SN), .movHi 9 3, .movImm 0 0, .movHi 12 0]
/-- One inner step: `r1:r0 = a[i] · b[j] + dst[i + j] + r12`, stored and carried. -/
def macA : List Instr := [.movHi 4 10, .ldm 4 0x04, .movHi 10 4, .movHi 0 8]
def macC : List Instr := [.movHi 4 11, .memImm .ldr 2 4 0, .movImm 3 0, .addReg 0 0 2, .dp .adcs 1 3,
  .movHi 2 12, .addReg 0 0 2, .dp .adcs 1 3, .stm 4 0x01, .movHi 11 4, .movHi 12 1, .movHi 2 9,
  .subImm8 2 1, .movHi 9 2]
def mac : List Instr := macA ++ M0Crypto.Release.Field25519Mul.mul32 0 1 2 3 5 ++ macC
/-- The end of row `i`: the carry to `dst[i + n]`, the row counter up, compared with `n`. -/
def tail : List Instr := [.movHi 4 11, .movHi 1 12, .memImm .str 1 4 0, .ldrSp 4 (wd ROW),
  .addImm8 4 1, .strSp 4 (wd ROW), .ldrSp 3 (wd SN), .dp .cmp 4 3]
def post : List Instr := [.addSp (BitVec.ofNat 7 (FRAME / 4)), .pop 0 true]

/-! ## Segments: footprints and trace atoms as expressions of each block's entry state -/

open M0Crypto.Release.Routine (Seg segPieces segsSize)
open M0Crypto.Sym (SExpr SMem)

/-- Frame word `n` bytes from `sp`, and the word stored there. -/
def spA (n : Nat) : SExpr := .add (.reg0 13) (.const (BitVec.ofNat 32 n))
def ldS (n : Nat) : SExpr := .ld32 .mem0 (spA n)
/-- `a + 4 · row`, the address of `a[i]`. -/
def aiA : SExpr := .add (ldS SA) (.lsl (ldS ROW) 2)

/-- The arguments to the frame, the zero loop, the row counter. -/
def top : List Seg :=
  [{ g := pre, al := [(.reg0 13, 4)], wg := [(.reg0 13, 16)], As := [.reg0 13] },
   { g := zbody, al := [(.reg0 0, 4)], wg := [(.reg0 0, 4)], As := [.reg0 0], br := some 1 },
   { g := zpost, al := [(.reg0 13, 4)], wg := [(spA ROW, 4)], As := [.reg0 13] }]

/-- A row: its start, the inner loop, its end. -/
def row : List Seg :=
  [{ g := head, al := [(.reg0 13, 4), (aiA, 4)], rg := [(.reg0 13, 20), (aiA, 4)],
     As := [.reg0 13, aiA] },
   { g := mac, al := [(.reg0 10, 4), (.reg0 11, 4)], wg := [(.reg0 11, 4)],
     rg := [(.reg0 10, 4), (.reg0 11, 4)], As := [.reg0 10, .reg0 11], br := some 1 },
   { g := tail, al := [(.reg0 13, 4), (.reg0 11, 4)], wg := [(.reg0 11, 4), (spA ROW, 4)],
     rg := [(spA ROW, 4), (spA SN, 4)], As := [.reg0 13, .reg0 11] }]

def oP (o : Nat) : Nat := o + seqSize enter
def oH (o : Nat) : Nat := oP o + segsSize top
def oE (o : Nat) : Nat := oH o + segsSize row + brSize

/-- `push; sub sp`, the top segments, the rows closed by `bne`, `add sp; pop`. -/
def pieces (o : Nat) : List Piece :=
  .seq enter :: (segPieces (oP o) top ++ (segPieces (oH o) row ++ .bcond 1 (oH o) :: [.seq post]))

def mpAt (o : Nat) (bytes : List (BitVec 8)) : Bool := piecesAt bytes o (pieces o)

open M0Crypto.Artifacts M0Crypto.Release.Ed25519

def O : Nat := Ed25519Compact.mp_mul

theorem compact_at : mpAt O Build.compact.bytes = true := by
  simp only [mpAt, piecesAt_eq_scan]; decide +kernel

theorem fast_at : mpAt O Build.fast.bytes = true := by
  simp only [mpAt, piecesAt_eq_scan]; decide +kernel

end M0Crypto.Release.Ed25519MpMulCode
