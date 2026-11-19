import M0Crypto.Release.RoutineLoopFar
import M0Crypto.Release.Ed25519Build

/-!
# `m0c_sc_recode_comb` as instruction lists

`emit_recode_comb` of `tools/gen_ed25519.py` for `n` combs (`compact` 2, `fast` 16). The frame
holds `U` (32 bytes), the digits' address `E` and the index `Q`. The first loop stores the bytes
of `U = (e >> 1) | 2^255`; pass `q` of the second gathers the four teeth of digit `q` from `U` and
stores the signed digit plus 8 at `E + q`. It is closed by `beq +0; b back`.
-/

namespace M0Crypto.Release.Ed25519RecodeCode

open M0Crypto.Thumb
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Routine (Seg segPieces segsSize)
open M0Crypto.Sym (SExpr SMem)

def enter : List Instr := [.push 0 true, .subSp 10]
def pre : List Instr := [.strSp 0 8, .addRdSp 3 0, .movImm 2 31]
def l1 : List Instr := [.memImm .ldrb 4 1 0, .memImm .ldrb 5 1 1, .lsrImm 4 4 1, .lslImm 5 5 7, .dp .orrs 4 5,
  .memImm .strb 4 3 0, .addImm8 1 1, .addImm8 3 1, .subImm8 2 1]
def mid : List Instr := [.memImm .ldrb 4 1 0, .lsrImm 4 4 1, .movImm 5 128, .dp .orrs 4 5, .memImm .strb 4 3 0,
  .movImm 2 0, .strSp 2 9]

/-- `log2 n`, and the shift of the comb row (`256 / n = 2 ^ sh`). -/
def lg (n : Nat) : Nat := if n = 2 then 1 else 4
def sh (n : Nat) : Nat := if n = 2 then 7 else 4

/-- Tooth `k`: bit `r3 + k (64 / n)` of `U` into bit `k` of `r6`. -/
def tooth (n k : Nat) : List Instr :=
  [.addImm3 4 3 0] ++ (if k = 0 then [] else [.addImm8 4 (BitVec.ofNat 8 (k * (64 / n)))]) ++
  [.lsrImm 5 4 3, .movImm 0 31, .dp .ands 5 0, .memReg .ldrb 5 7 5, .movImm 0 7, .dp .ands 4 0, .dp .lsrs 5 4,
   .movImm 0 1, .dp .ands 5 0] ++ (if k = 0 then [] else [.lslImm 5 5 (BitVec.ofNat 5 k)]) ++ [.dp .orrs 6 5]

def hd (n : Nat) : List Instr :=
  [.ldrSp 2 9, .lsrImm 3 2 (BitVec.ofNat 5 (lg n)), .movImm 4 (BitVec.ofNat 8 (n - 1)), .dp .ands 4 2,
   .movImm 5 (BitVec.ofNat 8 (n - 1)), .subReg 5 5 4, .lslImm 5 5 (BitVec.ofNat 5 (sh n)), .addReg 3 3 5,
   .addRdSp 7 0, .movImm 6 0]
def tl : List Instr :=
  [.lsrImm 4 6 3, .subImm8 4 1, .dp .eors 6 4, .movImm 0 7, .dp .ands 6 0, .addImm8 6 1, .dp .eors 6 4,
   .subReg 6 6 4, .addImm8 6 8, .ldrSp 0 8, .movImm 1 63, .dp .ands 2 1, .memReg .strb 6 0 2, .addImm8 2 1,
   .strSp 2 9, .cmpImm 2 64]
def body (n : Nat) : List Instr := hd n ++ tooth n 0 ++ tooth n 1 ++ tooth n 2 ++ tooth n 3 ++ tl
def post : List Instr := [.addSp 10, .pop 0 true]

/-! ## Segments -/

def spA (n : Nat) : SExpr := .add (.reg0 13) (.const (BitVec.ofNat 32 n))
def ldS (n : Nat) : SExpr := .ld32 .mem0 (spA n)
/-- `r3` of pass `q = ldS 36`, and the bit position of tooth `k`. -/
def rowE (n : Nat) : SExpr :=
  .add (.lsr (ldS 36) (lg n)) (.lsl (.sub (.const (BitVec.ofNat 32 (n - 1)))
    (.and (.const (BitVec.ofNat 32 (n - 1))) (ldS 36))) (sh n))
def posE (n k : Nat) : SExpr := if k = 0 then rowE n else .add (rowE n) (.const (BitVec.ofNat 32 (k * (64 / n))))
/-- The byte of `U` tooth `k` reads, and the digit's byte. -/
def toothA (n k : Nat) : SExpr := .add (.reg0 13) (.and (.lsr (posE n k) 3) (.const 31#32))
def digA : SExpr := .add (ldS 32) (.and (ldS 36) (.const 63#32))

def top : List Seg :=
  [{ g := pre, al := [(.reg0 13, 4)], wg := [(spA 32, 4)], As := [.reg0 13] },
   { g := l1, al := [(.reg0 1, 1), (.reg0 3, 1)], wg := [(.reg0 3, 1)], rg := [(.reg0 1, 2)],
     As := [.reg0 1, .reg0 3], br := some 1 },
   { g := mid, al := [(.reg0 1, 1), (.reg0 3, 1), (.reg0 13, 4)], wg := [(.reg0 3, 1), (spA 36, 4)],
     rg := [(.reg0 1, 1)], As := [.reg0 1, .reg0 3, .reg0 13] }]

def loop (n : Nat) : List Seg :=
  [{ g := body n, al := [(.reg0 13, 4), (digA, 1), (toothA n 0, 1), (toothA n 1, 1), (toothA n 2, 1), (toothA n 3, 1)],
     wg := [(digA, 1), (spA 36, 4)],
     rg := [(spA 32, 8), (toothA n 0, 1), (toothA n 1, 1), (toothA n 2, 1), (toothA n 3, 1)],
     As := [.reg0 13, digA, toothA n 0, toothA n 1, toothA n 2, toothA n 3] }]

def oP (o : Nat) : Nat := o + seqSize enter
def oL (o : Nat) : Nat := oP o + segsSize top
def oB (n o : Nat) : Nat := oL o + segsSize (loop n)
def oE (n o : Nat) : Nat := oB n o + 4

def pieces (n o : Nat) : List Piece :=
  .seq enter :: (segPieces (oP o) top ++ (segPieces (oL o) (loop n) ++ .bcond 0 (oE n o) :: .b (oL o) ::
    [.seq post]))

def rcAt (n o : Nat) (bytes : List (BitVec 8)) : Bool := piecesAt bytes o (pieces n o)

open M0Crypto.Artifacts M0Crypto.Release.Ed25519

def O : Nat := Ed25519Compact.sc_recode_comb

theorem rc_at : ∀ b : Build, rcAt b.combs O b.bytes = true := by
  intro b; cases b <;> (simp only [rcAt, piecesAt_eq_scan]; decide +kernel)

end M0Crypto.Release.Ed25519RecodeCode
