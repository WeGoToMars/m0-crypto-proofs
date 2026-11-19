import M0Crypto.Release.Ed25519DecompressOut
import M0Crypto.Release.Ed25519CallProgStitchGood

/-!
# `m0c_ge_decompress` as stitched sites

`m0c_ge_decompress`'s body between its prologue and its epilogue, as straight lines, status
sites and tests:

* `p0` (the spill of `out`), then the block `bL`: the load and the `y ≥ p` test, exit to `fail`;
* `q1` (`F1`, the power, `F2`), then the status call `e1` (`fe_eq`), exit to `ok1` when equal;
* `q2` (`F3`), the status call `e2`, exit to `fail`; `seg3` (`F4`), into `ok1`;
* `ok1`: `seg4` (`x` canonical), the test `x = 0` (exit to `okz`), the sign test (exit to
  `fail`);
* `okz`: the parity test, a short branch to `same`; `seg5` (`x = −x`), into `same`;
* `same`: `seg6` (the output), `movs r0, #0; b done`; `fail`: `movs r0, #1`; `done`: the
  epilogue.

The two candidate paths join at `ok1` (`tJ`), the two parity paths at `same` (`tK`).
-/

namespace M0Crypto.Release.Ed25519DecompressStitch

open M0Crypto.Armv6M (Word Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519FragC
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519 (Build)

/-! ## The load block with the `y ≥ p` test -/

inductive DX where
  | loadT
  deriving DecidableEq

/-- The load block, then the carry chain of `y + 19`; its exit is `Z` clear. -/
def dxS : DX → BlockS
  | .loadT => ⟨ioLoad, loadG ++ ypG, [1, 13]⟩

/-! ## The sites -/

section
open Op Ld

def p0 : Prog DA DB := Prog.ofList [spill 0 OUT]
def bL : Op DA DX := blk .loadT []
def q1 : Prog DA DB := fragC .f F1 (.op (call .pow [(0, S T), (1, S T), (2, K 1)]) (fragC .f F2 .nil))
def e1 : Op DA DB := eqP U
def q2 : Prog DA DB := fragC .f F3 .nil
def e2 : Op DA DB := eqP X2
end

/-- The tests' glue: `x = 0`, the sign, the parity. -/
def sG : List Instr := [.cmpImm 2 0]

/-! ## The layout -/

def oP0 : Nat := 0x2040
def oL : Nat := 0x2042
def oQ1 : Nat := 0x212a
def oE1 : Nat := 0x21b4
def oQ2 : Nat := 0x21c4
def oE2 : Nat := 0x21d0
def oS3 : Nat := 0x21e0
def oOk1 : Nat := 0x21ec
def oZ : Nat := 0x21f2
def oSg : Nat := 0x220e
def oOkz : Nat := 0x2214
def oS5 : Nat := 0x2220
def oSame : Nat := 0x2232
def oOk : Nat := 0x2262
def oFail : Nat := 0x2266
def oDone : Nat := 0x2268

/-- **The sites follow each other.** -/
theorem sites_at :
    oP0 + p0.size daS dbS = oL ∧
    oL + (bL : Op DA DX).size daS dxS + seqSize [] + 4 = oQ1 ∧
    oQ1 + q1.size daS dbS = oE1 ∧
    oE1 + e1.size daS dbS + seqSize [.cmpImm 0 0] + 4 = oQ2 ∧
    oQ2 + q2.size daS dbS = oE2 ∧
    oE2 + e2.size daS dbS + seqSize [.cmpImm 0 0] + 4 = oS3 ∧
    oS3 + seg3.size daS dbS = oOk1 ∧
    oOk1 + seg4.size daS dbS = oZ ∧
    oZ + seqSize zG + 4 = oSg ∧
    oSg + seqSize sG + 4 = oOkz ∧
    oOkz + seqSize pG + 2 = oS5 ∧
    oS5 + seg5.size daS dbS = oSame ∧
    oSame + seg6.size daS dbS = oOk ∧
    oOk + seqSize [.movImm 0 0] + 2 = oFail ∧ oFail + seqSize [.movImm 0 1] = oDone := by
  decide +kernel

/-! ## The static states -/

def t0 : St := (p0.ty daS dbS dcGeo stE).getD stE
def t1 : St := (bL.ty daS dxS dcGeo t0).getD stE
def t2 : St := (q1.ty daS dbS dcGeo (addViews t1 [])).getD stE
def t3 : St := (e1.ty daS dbS dcGeo t2).getD stE
def t4 : St := (q2.ty daS dbS dcGeo (addViews t3 [])).getD stE
def t5 : St := (e2.ty daS dbS dcGeo t4).getD stE
def t6 : St := (seg3.ty daS dbS dcGeo (addViews t5 [])).getD stE
/-- The two candidates join at `ok1`. -/
def tJ : St := joinSt { t3 with σ := σsp, ρ := [] } t6
def t7 : St := (seg4.ty daS dbS dcGeo tJ).getD stE
/-- After the tests, only `sp` known. -/
def tT : St := { t7 with σ := σsp, ρ := [] }
def t8 : St := (seg5.ty daS dbS dcGeo tT).getD stE
/-- The two parities join at `same`. -/
def tK : St := joinSt tT t8
def t9 : St := (seg6.ty daS dbS dcGeo tK).getD stE

/-- **The sites type** from the body's start along both paths of each test, and their effects
are decided. -/
theorem sites_ty :
    p0.ty daS dbS dcGeo stE = some t0 ∧ t0.ex = none ∧ p0.eok daS dbS dcGeo stE = true ∧
    bL.ty daS dxS dcGeo t0 = some t1 ∧ bL.eok daS dxS dcGeo t0 = true ∧ coCov t1.Γ [] = true ∧
    q1.ty daS dbS dcGeo (addViews t1 []) = some t2 ∧ t2.ex = none ∧ q1.eok daS dbS dcGeo (addViews t1 []) = true ∧
    e1.ty daS dbS dcGeo t2 = some t3 ∧ e1.eok daS dbS dcGeo t2 = true ∧
    q2.ty daS dbS dcGeo (addViews t3 []) = some t4 ∧ t4.ex = none ∧ q2.eok daS dbS dcGeo (addViews t3 []) = true ∧
    e2.ty daS dbS dcGeo t4 = some t5 ∧ e2.eok daS dbS dcGeo t4 = true ∧
    seg3.ty daS dbS dcGeo (addViews t5 []) = some t6 ∧ t6.ex = none ∧
    seg3.eok daS dbS dcGeo (addViews t5 []) = true ∧
    seg4.ty daS dbS dcGeo tJ = some t7 ∧ t7.ex = none ∧ seg4.eok daS dbS dcGeo tJ = true ∧
    seg5.ty daS dbS dcGeo tT = some t8 ∧ t8.ex = none ∧ seg5.eok daS dbS dcGeo tT = true ∧
    seg6.ty daS dbS dcGeo tK = some t9 ∧ t9.ex = none ∧ seg6.eok daS dbS dcGeo tK = true := by
  decide +kernel

/-! ## The code checks, both builds -/

section
variable (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS]

/-- A straight line `P` at `o`. -/
def lnChk (P : Prog DA DB) (o : Nat) : Prop :=
  P.bok (B := B) daS dbS dcGeo [] o = true ∧ piecesAt B o (Prog.emit daS dbS [] o P ++ []) = true

/-- A status call `x` at `o`, `cmp r0, #0` and the exit on `cc` to `T`. -/
def zChk (x : Op DA DB) (o : Nat) (cc : BitVec 4) (T : Nat) : Prop :=
  x.bok (B := B) daS dbS dcGeo o = true ∧
  (Op.pub [.cmpImm 0 0] : Op DA DB).bok (B := B) daS dbS dcGeo (o + x.size daS dbS) = true ∧
  Ed25519CallProg.brOk (B := B) dcGeo false (o + x.size daS dbS + seqSize [.cmpImm 0 0]) T = true ∧
  piecesAt B o (x.pieces daS dbS ++ (.seq [.cmpImm 0 0] ::
    xitBr cc false (o + x.size daS dbS + seqSize [.cmpImm 0 0]) T ++ [])) = true

/-- A test: the glue `g` at `o` and the exit on `cc` to `T`, short (`sh`) or not. -/
def tChk (g : List Instr) (o : Nat) (cc : BitVec 4) (sh : Bool) (T : Nat) : Prop :=
  (Op.pub g : Op DA DB).bok (B := B) daS dbS dcGeo o = true ∧ Ed25519CallProg.brOk (B := B) dcGeo sh (o + seqSize g) T = true ∧
  piecesAt B o (.seq g :: xitBr cc sh (o + seqSize g) T ++ []) = true

/-- The load block at `oL`, its test and the exit to `fail`. -/
def ldChk : Prop :=
  bL.bok (B := B) daS dxS dcGeo oL = true ∧
  (Op.pub [] : Op DA DX).bok (B := B) daS dxS dcGeo (oL + bL.size daS dxS) = true ∧
  Ed25519CallProg.brOk (B := B) dcGeo false (oL + bL.size daS dxS + seqSize []) oFail = true ∧
  piecesAt B oL (bL.pieces daS dxS ++ (.seq [] :: xitBr NE false (oL + bL.size daS dxS + seqSize []) oFail ++ [])) = true

/-- `movs r0, #0; b done` at `ok`, `movs r0, #1` at `fail`. -/
def tlChk : Prop :=
  (Op.pub [.movImm 0 0] : Op DA DB).bok (B := B) daS dbS dcGeo oOk = true ∧
  piecesAt B oOk [.seq [.movImm 0 0]] = true ∧
  bOk (B := B) dcGeo.cs (oOk + seqSize [.movImm 0 0]) oDone = true ∧
  seqAt B (oOk + seqSize [.movImm 0 0]) [.b (brImm11 (oOk + seqSize [.movImm 0 0]) oDone)] = true ∧
  (Op.pub [.movImm 0 1] : Op DA DB).bok (B := B) daS dbS dcGeo oFail = true ∧
  piecesAt B oFail [.seq [.movImm 0 1]] = true

end

section
variable (b : Build)

theorem lines_code : @lnChk b.bytes b.size b.codeBytes p0 oP0 ∧ @lnChk b.bytes b.size b.codeBytes q1 oQ1 ∧
    @lnChk b.bytes b.size b.codeBytes q2 oQ2 ∧ @lnChk b.bytes b.size b.codeBytes seg3 oS3 ∧
    @lnChk b.bytes b.size b.codeBytes seg4 oOk1 ∧ @lnChk b.bytes b.size b.codeBytes seg5 oS5 ∧
    @lnChk b.bytes b.size b.codeBytes seg6 oSame := by
  cases b <;> (simp only [lnChk, piecesAt_eq_scan]; decide +kernel)

theorem load_code : @ldChk b.bytes b.size b.codeBytes := by
  cases b <;> (simp only [ldChk, piecesAt_eq_scan]; decide +kernel)

theorem sites_code : @zChk b.bytes b.size b.codeBytes e1 oE1 EQ oOk1 ∧ @zChk b.bytes b.size b.codeBytes e2 oE2 NE oFail := by
  cases b <;> (simp only [zChk, piecesAt_eq_scan]; decide +kernel)

theorem tests_code : @tChk b.bytes b.size b.codeBytes zG oZ NE false oOkz ∧
    @tChk b.bytes b.size b.codeBytes sG oSg NE false oFail ∧ @tChk b.bytes b.size b.codeBytes pG oOkz EQ true oSame := by
  cases b <;> (simp only [tChk, piecesAt_eq_scan]; decide +kernel)

theorem tail_code : @tlChk b.bytes b.size b.codeBytes := by
  cases b <;> (simp only [tlChk, piecesAt_eq_scan, seqAt_eq_scan]; decide +kernel)

end

end M0Crypto.Release.Ed25519DecompressStitch
