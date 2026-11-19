import M0Crypto.Release.Ed25519GeProg
import M0Crypto.Release.Ed25519LookupTE
import M0Crypto.Release.Ed25519RecodeAd

/-!
# `m0c_ge_mul_base` as a call program

The frame, the callees (`m0c_sc_recode_comb`, `m0c_zero`, `m0c_ge_lookup`, the field operations,
`m0c_cmov`, `m0c_copy`), the blocks and the program of the signed comb for `nc` combs: `2` in
`compact`, `16` in `fast`. The outer loop runs a round of `nc` digits and doubles; the inner loop
looks up the digit's entry of the comb's row and adds it. The digit index `Q` counts down from
`63`, so every branch decision is public.
-/

namespace M0Crypto.Release.Ed25519MulBaseProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Artifacts.Ed25519Compact (ge_mul_base zero cmov copy)

/-! ## The frame -/

def OUT : Nat := 0
def SC : Nat := 4
def Q : Nat := 8
def CC : Nat := 12
def ROW : Nat := 16
def E : Nat := 24
def H : Nat := 88
def T : Nat := 216
def N : Nat := 344
def oA : Nat := 472
def oB : Nat := 504
def oC : Nat := 536
def oD : Nat := 568
def TOP : Nat := 600

/-! ## Callees and blocks -/

/-- `zero` of `n` field elements: `n` 32-byte views of zero bytes. -/
def ioZeroN (n : Nat) : Iface :=
  { ins := [], outs := (List.range n).map fun j => (0, 32 * j, .bytes 32), wr := [⟨0, 0, .k (32 * n)⟩], rd := [],
    al := [0], kreq := [(1, 8 * n)] }

/-- `cmov` of three 32-byte elements from a code buffer, under the mask in `r3`: field values out. -/
def ioCmov3 : Iface :=
  { ins := ((List.range 3).map fun j => (0, 32 * j, In.view (.bytes 32))) ++ [(1, 0, .raw (.k 96)), (3, 0, .view .rw)],
    outs := (List.range 3).map fun j => (0, 32 * j, .fe), wr := [⟨0, 0, .k 96⟩], rd := [⟨0, 0, .k 96⟩, ⟨1, 0, .k 96⟩],
    al := [0, 1], eqd := [(0, 1, 96)], kreq := [(2, 24)] }

/-- `copy` of a point's four field elements to one point view. -/
def ioCopyPt : Iface :=
  { ins := (List.range 4).map fun j => (1, 32 * j, .view .fe), outs := [(0, 0, .fe4)],
    wr := [⟨0, 0, .k 128⟩], rd := [⟨1, 0, .k 128⟩], al := [0, 1], eqd := [(0, 1, 128)], kreq := [(2, 32)] }

inductive MA where
  | recode | zero4 | zero3 | look | f (a : FA) | cmov3 | copyPt
  deriving DecidableEq

def maS : MA → CalleeS
  | .recode => Ed25519Recode.rcS
  | .zero4 => calleeAt zero (ioZeroN 4) [0, 1]
  | .zero3 => calleeAt zero (ioZeroN 3) [0, 1]
  | .look => Ed25519LookupTE.lookS
  | .f a => faS a
  | .cmov3 => calleeAt cmov ioCmov3 [0, 1, 2]
  | .copyPt => calleeAt copy ioCopyPt [0, 1, 2]

/-- `set_identity`'s stores after `zero`: `1` in the low words of `Y` and `Z`. -/
def identG : List Instr := [.movImm 1 1, .memImm .str 1 0 8, .memImm .str 1 0 16]

/-- A point of zero bytes in, its field values out. -/
def ioIdent : Iface :=
  { ins := (List.range 4).map fun j => (0, 32 * j, .view (.bytes 32)), outs := (List.range 4).map fun j => (0, 32 * j, .fe),
    wr := [⟨0, 32, .k 4⟩, ⟨0, 64, .k 4⟩], rd := [], al := [0] }

/-- The Niels identity's stores after `zero`: `1` in the low words of `y+x` and `y−x`. -/
def nsetG : List Instr := [.movImm 1 1, .memImm .str 1 0 0, .memImm .str 1 0 8]

def ioNset : Iface :=
  { ins := (List.range 3).map fun j => (0, 32 * j, .view (.bytes 32)), outs := (List.range 3).map fun j => (0, 32 * j, .bytes 32),
    wr := [⟨0, 0, .k 4⟩, ⟨0, 32, .k 4⟩], rd := [], al := [0] }

/-- `ldrb r3, [r1]; movs r2, #1; ands r3, r2; subs r3, #1`: the mask of an even scalar. -/
def maskG : List Instr := [.memImm .ldrb 3 1 0, .movImm 2 1, .dp .ands 3 2, .subImm8 3 1]

def ioMask : Iface := { ins := [(1, 0, .view .cl)], outs := [], wr := [], rd := [⟨1, 0, .k 1⟩], ro := [3] }

/-- `subs r2, #8`: the digit from its stored byte. -/
def sub8G : List Instr := [.subImm8 2 8]

def ioSub8 : Iface := { ins := [(2, 0, .view .rw)], outs := [], wr := [], rd := [], ro := [2] }

inductive MB where
  | ident | nset | mask | sub8
  deriving DecidableEq

def mbS : MB → BlockS
  | .ident => ⟨ioIdent, identG, [0]⟩
  | .nset => ⟨ioNset, nsetG, [0]⟩
  | .mask => ⟨ioMask, maskG, [1]⟩
  | .sub8 => ⟨ioSub8, sub8G, []⟩

/-! ## The program -/

section
open Op Ld

/-- The field values at `o`, `o + 32`, … as loaders. -/
def fs (o : Nat) (j : Nat) : Ld := S (o + 32 * j)

/-- The views that live across the passes: the digit index, the pointers, the digits, `H`. -/
def keepO : List Loc := [.fr Q, .fr OUT, .fr SC, .fr E, .fr H, .fr (H + 32), .fr (H + 64), .fr (H + 96)]

/-- The same with the row pointer and the comb counter. -/
def keepI : List Loc := .fr CC :: .fr ROW :: keepO

/-- `ge_add` of `H` and the Niels entry at `N` into `T` (`H − N` for `neg`). -/
def addF (neg : Bool) : List FOp :=
  addOps false neg oA oB oC oD (fs H 0) (fs H 1) (fs H 2) (fs H 3) (fs N 0) (fs N 1) (fs N 2) (.K 0)
    (fs T 0) (fs T 1) (fs T 2) (fs T 3)

/-- `ge_p1p1_to_p3` of `T` into `H`, with `T` or without. -/
def p3F (withT : Bool) : List FOp :=
  p3Ops withT (fs T 0) (fs T 1) (fs T 2) (fs T 3) (fs H 0) (fs H 1) (fs H 2) (fs H 3)

/-- `ge_dbl` of `H` into `T`. -/
def dblF : List FOp := dblOps oA oB oC oD (fs H 0) (fs H 1) (fs H 2) (fs T 0) (fs T 1) (fs T 2) (fs T 3)

/-- One digit: the lookup of its entry in the comb's row, `H + entry` into `T`, `T` to `H` with or
without `T` (without when a doubling follows), the next row, digit and comb. -/
def innerP : Prog MA MB :=
  Prog.ofList [ld 0 (S N), ld 1 (W ROW 0),
    pub [.ldrSp 2 (BitVec.ofNat 8 (Q / 4))], ld 3 (S E), pub [.movImm 4 63, .dp .ands 2 4],
    ldb 2 3 2, blk .sub8 [], call .look []] |>.seq <|
  fragP MA.f (addF false) <|
  .hd (.xit [.ldrSp 0 (BitVec.ofNat 8 (CC / 4)), .cmpImm 0 1] none NE false 0 <|
        .xit [.ldrSp 0 (BitVec.ofNat 8 (Q / 4)), .cmpImm 0 0] none EQ false 0 <|
        fragP MA.f (p3F false) .nil)
    (fragP MA.f (p3F true) .nil) <|
  Prog.ofList [pub [.ldrSp 0 (BitVec.ofNat 8 (ROW / 4)), .movImm 1 3, .lslImm 1 1 8, .addReg 0 0 1], spill 0 ROW,
    pub [.ldrSp 0 (BitVec.ofNat 8 (Q / 4)), .subImm8 0 1], spill 0 Q] |>.seq <|
  .xit [.ldrSp 0 (BitVec.ofNat 8 (CC / 4)), .subImm8 0 1] (some (0, CC)) EQ true 0 (.op (keep keepI) .nil)

/-- `b<cc>` on a signed `<`. -/
def LT : BitVec 4 := 11

/-- A round: the first row, `nc` digits, then (unless the last digit was `0`) the doubling. -/
def outerP (nc : Nat) : Prog MA MB :=
  Prog.ofList [ld 0 (C 2 0 0x90), spill 0 ROW, ld 0 (K nc), spill 0 CC] |>.seq <|
  .wh nc innerP <|
  .xit [.ldrSp 0 (BitVec.ofNat 8 (Q / 4)), .cmpImm 0 0] none LT false 0 <|
  fragP MA.f dblF <| fragP MA.f (p3F true) <| .op (keep keepO) .nil

/-- The prologue: the digits, `H` the identity, `Q = 63`. -/
def proP : Prog MA MB :=
  Prog.ofList [spill 0 OUT, spill 1 SC, call .recode [(0, S E)], call .zero4 [(0, S H), (1, K 32)],
    blk .ident [(0, S H)], ld 0 (K 63), spill 0 Q, keep keepO]

/-- The epilogue: for an even scalar subtract `B` (the Niels identity, or `odd_b[0]` under the mask),
then `H` to `out`. -/
def epiP : Prog MA MB :=
  Prog.ofList [call .zero3 [(0, S N), (1, K 24)], blk .nset [(0, S N)], ld 1 (W SC 0), blk .mask [],
    ld 0 (S N), ld 1 (C 3 0 0x2a), call .cmov3 [(2, K 24)]] |>.seq <|
  fragP MA.f (addF true) <| fragP MA.f (p3F true) <|
  .op (call .copyPt [(0, W OUT 0), (1, S H), (2, K 32)]) .nil

/-- The program: `64 / nc` rounds. -/
def mbP (nc : Nat) : Prog MA MB := proP.seq (.wh (64 / nc) (outerP nc) epiP)

end

/-- `m0c_ge_mul_base` for `nc` combs: `out` written, the scalar read (a clamped view), the comb
table and `odd_b` code buffers. -/
def mbQ (nc : Nat) : CalleeP MA MB :=
  { s := eaS .mulBase, P := mbP nc, top := TOP,
    xr := [(0, ⟨.k 128, true, false, true⟩), (1, ⟨.k 32, false, true, true⟩)], pr := [],
    cb := [(Artifacts.Ed25519Compact.ed_comb, 768 * nc), (Artifacts.Ed25519Compact.ed_odd_b, 768)], sc := [(1, .cl)] }

/-! ## The decided checks

Each check is one closed `decide` per build: the typing of all 64 digit passes evaluates in about
10 s and 3 GB of kernel memory. -/

theorem mb_ok (b : Build) : (mbQ b.combs).ok maS mbS = true := by
  cases b <;> decide +kernel

open M0Crypto.Thumb M0Crypto.Release.RoutinePieces in
theorem mb_code (b : Build) :
    @CalleeP.codeOk _ _ maS mbS (mbQ b.combs) b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]; cases b <;> decide +kernel

end M0Crypto.Release.Ed25519MulBaseProg
