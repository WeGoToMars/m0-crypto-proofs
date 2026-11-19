import M0Crypto.Release.Ed25519VerifyProg
import M0Crypto.Release.Ed25519VerifyBlocks
import M0Crypto.Release.Ed25519CallProgStitchGood
import M0Crypto.Release.Ed25519CallProgEntryP

/-!
# `m0c_ed25519_verify` as stitched sites

`m0c_ed25519_verify`'s body is straight lines between stitched sites:

* `p0` (the spills), then the status calls `c0` (`A` from `pk`) and `c1` (`R` from `sig`);
* `p2` (`s` into `SS` and the operands of `lt`), then the block `b2` (`lt`) with its carry test;
* `p3` (`h`), the calls `w5` and `w3` (`sc_wnaf`) and `dm` (`ge_dsm`), whose traces depend on
  memory, `m3` (`x_R Z`), then the status call `e3` (`fe_eq`);
* `m4` (`y_R Z`), then the status call `e4`;
* the verdict blocks `okG` and `failG` and the leave.

The straight lines call only `vpS`'s callees; the stitched sites call `vxS`'s, where
`ge_decompress` has no unconditional outputs: its point is the status call's outputs `decCo`.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg (FA faS)
open M0Crypto.Release.Ed25519FeEq (eqS)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ge_decompress)

/-! ## Callees -/

/-- The callees of the straight lines: sign's SHA-512 and reduction, and the field ones. -/
inductive VP where
  | e (a : EA) | f (a : FA)
  deriving DecidableEq

def vpS : VP → CalleeS
  | .e a => eaS a
  | .f a => faS a

/-- `ge_decompress` with its point only on success: no unconditional outputs. -/
def ioDecZ : Iface := { ioDec with outs := [] }

/-- The point of `ge_decompress`, four field elements at `r0`, on success. -/
def decCo : List (Reg × Nat × Kd) := (List.range 4).map fun j => (0, 32 * j, .fe)

/-- The callees of the stitched sites. -/
inductive VX where
  | dec | wnaf (w : Nat) | dsm | eq
  deriving DecidableEq

def vxS : VX → CalleeS
  | .dec => calleeAt ge_decompress ioDecZ [0, 1]
  | .wnaf w => vaS (.wnaf w)
  | .dsm => vaS .dsm
  | .eq => eqS

/-! ## The sites -/

section
open Op Ld

/-- `hash_parts(out, parts)` with the context at `CTX`. -/
def hashP (out : Nat) (parts : List (Ld × Ld × SV)) : List (Op VP VB) :=
  call (.e .init) [(0, S CTX)] :: go [] parts
where
  go (n : List SV) : List (Ld × Ld × SV) → List (Op VP VB)
    | [] => [call (.e (.final n)) [(0, S CTX), (1, S out)]]
    | (src, len, ℓ) :: ps => call (.e (.update n ℓ)) [(1, src), (2, len), (0, S CTX)] :: go (n ++ [ℓ]) ps

def aC0 : List (LowReg × Ld) := [(0, S PA), (1, W PK 0)]
def aC1 : List (LowReg × Ld) := [(0, S PR), (1, W SIG 0)]
def aW5 : List (LowReg × Ld) := [(0, S DS), (1, S SS), (2, K 5)]
def aW3 : List (LowReg × Ld) := [(0, S DH), (1, S HH), (2, K 3)]
def aDm : List (LowReg × Ld) := [(0, S SB), (1, S DS), (2, S DH), (3, S PA)]
def aE3 : List (LowReg × Ld) := [(0, S TMP), (1, S SB), (2, S T2)]
def aE4 : List (LowReg × Ld) := [(0, S TMP), (1, S (SB + 32)), (2, S T2)]

def p0 : Prog VP VB := Prog.ofList [spill 0 SIG, spill 1 MSG, spill 2 LEN, spill 3 PK]
def c0 : Op VX VB := call .dec aC0
def c1 : Op VX VB := call .dec aC1
def p2 : Prog VP VB := Prog.ofList [blk .loadS [(2, W SIG 32)], ld 1 (S SS), ld 2 (C 3 0 59), ld 3 (S TMP)]
def b2 : Op VX VB := blk .lt []
def p3 : Prog VP VB := Prog.ofList <|
  hashP HD [(W SIG 0, K 32, .k 32), (W PK 0, K 32, .k 32), (W MSG 0, W LEN 0, .prm 0)] ++
  [call (.e .reduce) [(0, S HH), (1, S HD)]]
def w5 : Op VX VB := call (.wnaf 5) aW5
def w3 : Op VX VB := call (.wnaf 3) aW3
def dm : Op VX VB := call .dsm aDm
def m3 : Prog VP VB := Prog.ofList [call (.f .mul) [(0, S T2), (1, S PR), (2, S (SB + 64))]]
def e3 : Op VX VB := call .eq aE3
def m4 : Prog VP VB := Prog.ofList [call (.f .mul) [(0, S T2), (1, S (PR + 32)), (2, S (SB + 64))]]
def e4 : Op VX VB := call .eq aE4
end

/-! ## The layout -/

/-- The offsets of the sites, the verdict blocks and the leave. -/
def oP0 : Nat := 0x2f90
def oC0 : Nat := 0x2f98
def oC1 : Nat := 0x2fa6
def oP2 : Nat := 0x2fb4
def oB2 : Nat := 0x3070
def oP3 : Nat := 0x30b4
def oW5 : Nat := 0x30e8
def oW3 : Nat := 0x30f2
def oDm : Nat := 0x30fc
def oM3 : Nat := 0x3108
def oE3 : Nat := 0x3112
def oM4 : Nat := 0x3122
def oE4 : Nat := 0x312c
def oOk : Nat := 0x313c
def oFail : Nat := 0x3140
def oLeave : Nat := 0x3144

/-- The scalar at `r1` below `L` after the `lt` test passes. -/
def ltCo : List (Reg × Nat × Kd) := [(1, 0, .sc)]

/-! ## The static states -/

def v0 : St := (p0.ty vpS vbS verifyGeo stE).getD stE
def v1 : St := (c0.ty vxS vbS verifyGeo v0).getD stE
def l0 : List (Loc × Kd) := (coRes (regsOf v0.Γ v0.σ aC0) decCo).getD []
def v2 : St := (c1.ty vxS vbS verifyGeo (addViews v1 l0)).getD stE
def l1 : List (Loc × Kd) := (coRes (regsOf (addViews v1 l0).Γ (addViews v1 l0).σ aC1) decCo).getD []
def v3 : St := (p2.ty vpS vbS verifyGeo (addViews v2 l1)).getD stE
def v4 : St := (b2.ty vxS vbS verifyGeo v3).getD stE
def l2 : List (Loc × Kd) := (coRes (regsOf v3.Γ v3.σ []) ltCo).getD []
def v5 : St := (p3.ty vpS vbS verifyGeo (addViews v4 l2)).getD stE
def v6 : St := (w5.ty vxS vbS verifyGeo v5).getD stE
def v7 : St := (w3.ty vxS vbS verifyGeo v6).getD stE
def v8 : St := (dm.ty vxS vbS verifyGeo v7).getD stE
def v9 : St := (m3.ty vpS vbS verifyGeo v8).getD stE
def v10 : St := (e3.ty vxS vbS verifyGeo v9).getD stE
def v11 : St := (m4.ty vpS vbS verifyGeo (addViews v10 [])).getD stE
def v12 : St := (e4.ty vxS vbS verifyGeo v11).getD stE

/-- **The sites type** from the body's start, each status site's views joining on its passing
edge, and the decided checks of the outputs and the effects hold. -/
theorem sites_ty :
    p0.ty vpS vbS verifyGeo stE = some v0 ∧ v0.ex = none ∧ p0.eok vpS vbS verifyGeo stE = true ∧
    c0.ty vxS vbS verifyGeo v0 = some v1 ∧ c0.eok vxS vbS verifyGeo v0 = true ∧
    coRes (regsOf v0.Γ v0.σ aC0) decCo = some l0 ∧ coOk verifyGeo l0 = true ∧ coEok (vxS .dec) decCo = true ∧
    c1.ty vxS vbS verifyGeo (addViews v1 l0) = some v2 ∧ c1.eok vxS vbS verifyGeo (addViews v1 l0) = true ∧
    coRes (regsOf (addViews v1 l0).Γ (addViews v1 l0).σ aC1) decCo = some l1 ∧ coOk verifyGeo l1 = true ∧
    p2.ty vpS vbS verifyGeo (addViews v2 l1) = some v3 ∧ v3.ex = none ∧
    p2.eok vpS vbS verifyGeo (addViews v2 l1) = true ∧
    b2.ty vxS vbS verifyGeo v3 = some v4 ∧ b2.eok vxS vbS verifyGeo v3 = true ∧
    coRes (regsOf v3.Γ v3.σ []) ltCo = some l2 ∧ coOk verifyGeo l2 = true ∧ coCov v4.Γ l2 = true ∧
    p3.ty vpS vbS verifyGeo (addViews v4 l2) = some v5 ∧ v5.ex = none ∧
    p3.eok vpS vbS verifyGeo (addViews v4 l2) = true ∧
    w5.ty vxS vbS verifyGeo v5 = some v6 ∧ w5.eok vxS vbS verifyGeo v5 = true ∧
    w3.ty vxS vbS verifyGeo v6 = some v7 ∧ w3.eok vxS vbS verifyGeo v6 = true ∧
    dm.ty vxS vbS verifyGeo v7 = some v8 ∧ dm.eok vxS vbS verifyGeo v7 = true ∧
    m3.ty vpS vbS verifyGeo v8 = some v9 ∧ v9.ex = none ∧ m3.eok vpS vbS verifyGeo v8 = true ∧
    e3.ty vxS vbS verifyGeo v9 = some v10 ∧ e3.eok vxS vbS verifyGeo v9 = true ∧
    m4.ty vpS vbS verifyGeo (addViews v10 []) = some v11 ∧ v11.ex = none ∧
    m4.eok vpS vbS verifyGeo (addViews v10 []) = true ∧
    e4.ty vxS vbS verifyGeo v11 = some v12 ∧ e4.eok vxS vbS verifyGeo v11 = true := by
  decide +kernel

end M0Crypto.Release.Ed25519VerifyProg
