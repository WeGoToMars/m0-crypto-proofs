import M0Crypto.Release.RoutineSegs
import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.Ed25519ScalarChain

/-!
# `m0c_sc_reduce` as instruction lists

`emit_sc_reduce` of `tools/gen_ed25519.py`, Barrett reduction (HAC 14.42, `b = 2^32`, `k = 8`).
Its intended contract: from the 64-byte input `in` at `r1` (16 words, read in place), the 32-byte
output `out` at `r0` (8 words) is `< L` and equal to the input mod `L`; the output is copied from
the frame after the last read of the input, so `out` may overlap `in`.

The frame holds `out`, `in`, `Q2 = q1 · mu` (18 words), `Q4 = q3 · L` (18 words), `R` and `T`
(9 words each). The blocks between the calls are `a1` (`Q2 = in[7 …] · mu`), `a2`
(`Q4 = Q2[9 …] · L`), `s0` (`R = in − Q4` over 9 words), twice `sel` (`T = R − L`, the select
mask, `cmov(R, T)`), and `fin` (`copy(out, R)`). `scAt` checks the pieces against each build's
bytes; every offset, the `adr` sites included, is a sum of piece sizes, and the pool of four
literal words follows `pop`.
-/

namespace M0Crypto.Release.Ed25519ScReduceCode

open M0Crypto.Thumb
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519ScalarChain (chainI selMask)

/-- Frame words, in bytes from `sp`. -/
def OUT : Nat := 0
def IN : Nat := 4
def Q2 : Nat := 8
def Q4 : Nat := 80
def R : Nat := 152
def T : Nat := 188
def FRAME : Nat := 224

abbrev wd (n : Nat) : BitVec 8 := BitVec.ofNat 8 (n / 4)

/-- `ldr rd, =lit` at `o` loading the pool word at `p` (`Layout.litImm`), then `add rd, pc`. -/
def adr (rd : M0Crypto.Armv6M.LowReg) (o p : Nat) : List Instr :=
  [.ldrLit rd (BitVec.ofNat 8 (litImm o p)), .addPc rd]

/-- `[rd] = [ra] − [rb]` over 9 words (`sub_words`), `r4`, `r5` the scratch. -/
def sub9 (ra rb rd : M0Crypto.Armv6M.LowReg) : List Instr := chainI true false true ra rb rd 4 5 0 9

def enter : List Instr := [.push 0 true, .subSp (BitVec.ofNat 7 (FRAME / 4))]
def post : List Instr := [.addSp (BitVec.ofNat 7 (FRAME / 4)), .pop 0 true]

/-- The arguments to the frame; `mp_mul(Q2, in + 28, mu, 9)`, its `adr` at `x` for the pool word
at `p`. -/
def a1P : List Instr := [.strSp 0 (wd OUT), .strSp 1 (wd IN), .addRdSp 0 (wd Q2), .addImm8 1 28]
def a1 (x p : Nat) : List Instr := a1P ++ adr 2 x p ++ [.movImm 3 9]
/-- `mp_mul(Q4, Q2 + 36, L, 9)`. -/
def a2P : List Instr := [.addRdSp 0 (wd Q4), .addRdSp 1 (wd (Q2 + 36))]
def a2 (x p : Nat) : List Instr := a2P ++ adr 2 x p ++ [.movImm 3 9]
/-- `R = in − Q4` over 9 words. -/
def s0H : List Instr := [.ldrSp 1 (wd IN), .addRdSp 2 (wd Q4), .addRdSp 3 (wd R)]
def s0 : List Instr := s0H ++ sub9 1 2 3
/-- A round: `T = R − L` (its `adr` at `x`, the pool word at `p`), the mask `r3`, `cmov(R, T, 8)`. -/
def selP : List Instr := [.addRdSp 1 (wd R)]
def selH (x p : Nat) : List Instr := selP ++ adr 2 x p ++ [.addRdSp 3 (wd T)]
def selT : List Instr := [.addRdSp 0 (wd R), .addRdSp 1 (wd T), .movImm 2 8]
def sel (x p : Nat) : List Instr := selH x p ++ sub9 1 2 3 ++ selMask 3 ++ selT
/-- `copy(out, R, 8)`. -/
def fin : List Instr := [.ldrSp 0 (wd OUT), .addRdSp 1 (wd R), .movImm 2 8]

/-- Offsets, each a sum of piece sizes (a block's size does not depend on its literal, so it is
taken at `0`): the blocks from `o`, the two rounds at `oD`, `oD2`, the pool at `pl`. -/
def oA (o : Nat) : Nat := o + seqSize enter
def oB (o : Nat) : Nat := oA o + seqSize (a1 0 0) + blSize
def oC (o : Nat) : Nat := oB o + seqSize (a2 0 0) + blSize
def oD (o : Nat) : Nat := oC o + seqSize s0
def oD2 (o : Nat) : Nat := oD o + seqSize (sel 0 0) + blSize
def oF (o : Nat) : Nat := oD2 o + seqSize (sel 0 0) + blSize
def pl (o : Nat) : Nat := oF o + seqSize fin + blSize + seqSize post
/-- The `adr` of each block. -/
def a1L (o : Nat) : Nat := oA o + seqSize a1P
def a2L (o : Nat) : Nat := oB o + seqSize a2P
def selL (x : Nat) : Nat := x + seqSize selP

open M0Crypto.Artifacts M0Crypto.Release.Ed25519

/-- `push; sub sp`, the blocks and calls, `add sp; pop`. -/
def pieces (o : Nat) : List Piece :=
  [.seq enter, .seq (a1 (a1L o) (pl o)), .call Ed25519Compact.mp_mul, .seq (a2 (a2L o) (pl o + 4)),
   .call Ed25519Compact.mp_mul, .seq s0, .seq (sel (selL (oD o)) (pl o + 8)), .call Ed25519Compact.cmov,
   .seq (sel (selL (oD2 o)) (pl o + 12)), .call Ed25519Compact.cmov, .seq fin, .call Ed25519Compact.copy,
   .seq post]

def scAt (o : Nat) (bytes : List (BitVec 8)) : Bool := piecesAt bytes o (pieces o)

def O : Nat := Ed25519Compact.sc_reduce

theorem compact_at : scAt O Build.compact.bytes = true := by
  simp only [scAt, piecesAt_eq_scan]; decide +kernel

theorem fast_at : scAt O Build.fast.bytes = true := by
  simp only [scAt, piecesAt_eq_scan]; decide +kernel

end M0Crypto.Release.Ed25519ScReduceCode
