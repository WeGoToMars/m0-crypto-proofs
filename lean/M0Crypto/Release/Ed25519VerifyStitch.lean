import M0Crypto.Release.Ed25519VerifyProg
import M0Crypto.Release.Ed25519VerifyBlocks
import M0Crypto.Release.Ed25519CompressP2
import M0Crypto.Release.Ed25519BytesDiff
import M0Crypto.Release.Ed25519RCheckCode
import M0Crypto.Release.Ed25519CallProgStitchGood
import M0Crypto.Release.Ed25519CallProgEntryP

/-!
# `m0c_ed25519_verify` as stitched sites

The verifier spills the arguments, decodes A, checks the endpoints of R and
scans the middle bytes when needed, then checks that S is canonical.
It hashes the raw R bytes, recodes S and the reduced hash, and computes the
projective double-scalar result. Compression produces the canonical encoding,
and the final status call compares it with all 32 bytes of R.

The successful decompression edge introduces A's four field views via `decCo`.

-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519CompressP2 (cp2S)
open M0Crypto.Release.Ed25519BytesDiff (diffS)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ge_decompress)
open M0Crypto.Artifacts.Ed25519Compact (vf_body vf_decode_a vf_done vf_dsm vf_fail vf_hash
  vf_l9_load vf_l9_literal vf_scalar vf_scalar_sub vf_success vf_wnaf_h vf_wnaf_s vf_compress vf_compare
  vf_check_r)

/-! ## Callees -/

/-- The callees of the straight lines: sign's SHA-512 and reduction, and point compression. -/
inductive VP where
  | e (a : EA) | compress
  deriving DecidableEq

def vpS : VP → CalleeS
  | .e a => eaS a
  | .compress => cp2S

/-- `ge_decompress` with its point only on success: no unconditional outputs. -/
def ioDecZ : Iface := { ioDec with outs := [] }

/-- The point of `ge_decompress`, four field elements at `r0`, on success. -/
def decCo : List (Reg × Nat × Kd) := (List.range 4).map fun j => (0, 32 * j, .fe)

/-- The callees of the stitched sites. -/
inductive VX where
  | dec | checkR | wnaf (w : Nat) | dsm | compare
  deriving DecidableEq

def vxS : VX → CalleeS
  | .dec => calleeAt ge_decompress ioDecZ [0, 1]
  | .checkR => Ed25519RCheck.checkS
  | .wnaf w => vaS (.wnaf w)
  | .dsm => vaS .dsm
  | .compare => diffS

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
def aR : List (LowReg × Ld) := [(0, W SIG 0)]
def aW5 : List (LowReg × Ld) := [(0, S DS), (1, S SS), (2, K 5)]
def aW3 : List (LowReg × Ld) := [(0, S DH), (1, S HH), (2, K 3)]
def aDm : List (LowReg × Ld) := [(0, S SB), (1, S DS), (2, S DH), (3, S PA)]
def aEncode : List (LowReg × Ld) := [(0, S ENC), (1, S SB)]
def aCompare : List (LowReg × Ld) := [(0, S ENC), (1, W SIG 0)]

def p0 : Prog VP VB := Prog.ofList [spill 0 SIG, spill 1 MSG, spill 2 LEN, spill 3 PK]
def c0 : Op VX VB := call .dec aC0
def checkR : Op VX VB := call .checkR aR
def l9Disp : Nat := (vf_l9_literal - ((vf_l9_load + 4) / 4) * 4) / 4

def p2 : Prog VP VB := Prog.ofList
  [blk .loadS [(2, W SIG 32)], ld 1 (S SS), ld 2 (C 3 0 l9Disp), ld 3 (S TMP)]
def b2 : Op VX VB := blk .lt []
def p3 : Prog VP VB := Prog.ofList <|
  hashP HD [(W SIG 0, K 32, .k 32), (W PK 0, K 32, .k 32), (W MSG 0, W LEN 0, .prm 0)] ++
  [call (.e .reduce) [(0, S HH), (1, S HD)]]
def w5 : Op VX VB := call (.wnaf 5) aW5
def w3 : Op VX VB := call (.wnaf 3) aW3
def dm : Op VX VB := call .dsm aDm
def encode : Prog VP VB := Prog.ofList [call .compress aEncode]
def compare : Op VX VB := call .compare aCompare
end

/-! ## The layout -/

/-- The offsets of the sites, the verdict blocks and the leave. -/
def oP0 : Nat := vf_body
def oC0 : Nat := vf_decode_a
def oR : Nat := vf_check_r
def oP2 : Nat := vf_scalar
def oB2 : Nat := vf_scalar_sub
def oP3 : Nat := vf_hash
def oW5 : Nat := vf_wnaf_s
def oW3 : Nat := vf_wnaf_h
def oDm : Nat := vf_dsm
def oEncode : Nat := vf_compress
def oCompare : Nat := vf_compare
def oOk : Nat := vf_success
def oFail : Nat := vf_fail
def oLeave : Nat := vf_done

/-- The scalar at `r1` below `L` after the `lt` test passes. -/
def ltCo : List (Reg × Nat × Kd) := [(1, 0, .sc)]

/-! ## The static states -/

def v0 : St := (p0.ty vpS vbS verifyGeo stE).getD stE
def v1 : St := (c0.ty vxS vbS verifyGeo v0).getD stE
def l0 : List (Loc × Kd) := (coRes (regsOf v0.Γ v0.σ aC0) decCo).getD []
def vRCall : St := (checkR.ty vxS vbS verifyGeo (addViews v1 l0)).getD stE
def vR : St := addViews vRCall []
def v3 : St := (p2.ty vpS vbS verifyGeo vR).getD stE
def v4 : St := (b2.ty vxS vbS verifyGeo v3).getD stE
def l2 : List (Loc × Kd) := (coRes (regsOf v3.Γ v3.σ []) ltCo).getD []
def v5 : St := (p3.ty vpS vbS verifyGeo (addViews v4 l2)).getD stE
def v6 : St := (w5.ty vxS vbS verifyGeo v5).getD stE
def v7 : St := (w3.ty vxS vbS verifyGeo v6).getD stE
def v8 : St := (dm.ty vxS vbS verifyGeo v7).getD stE
def v9 : St := (encode.ty vpS vbS verifyGeo v8).getD stE
def v10 : St := (compare.ty vxS vbS verifyGeo v9).getD stE

theorem checkR_ty :
    checkR.ty vxS vbS verifyGeo (addViews v1 l0) = some vRCall ∧
    checkR.eok vxS vbS verifyGeo (addViews v1 l0) = true := by
  decide +kernel

/-- **The sites type** from the body's start, each status site's views joining on its passing
edge, and the decided checks of the outputs and the effects hold. -/
theorem sites_ty :
    p0.ty vpS vbS verifyGeo stE = some v0 ∧ v0.ex = none ∧ p0.eok vpS vbS verifyGeo stE = true ∧
    c0.ty vxS vbS verifyGeo v0 = some v1 ∧ c0.eok vxS vbS verifyGeo v0 = true ∧
    coRes (regsOf v0.Γ v0.σ aC0) decCo = some l0 ∧ coOk verifyGeo l0 = true ∧ coEok (vxS .dec) decCo = true ∧
    p2.ty vpS vbS verifyGeo vR = some v3 ∧ v3.ex = none ∧
    p2.eok vpS vbS verifyGeo vR = true ∧
    b2.ty vxS vbS verifyGeo v3 = some v4 ∧ b2.eok vxS vbS verifyGeo v3 = true ∧
    coRes (regsOf v3.Γ v3.σ []) ltCo = some l2 ∧ coOk verifyGeo l2 = true ∧ coCov v4.Γ l2 = true ∧
    p3.ty vpS vbS verifyGeo (addViews v4 l2) = some v5 ∧ v5.ex = none ∧
    p3.eok vpS vbS verifyGeo (addViews v4 l2) = true ∧
    w5.ty vxS vbS verifyGeo v5 = some v6 ∧ w5.eok vxS vbS verifyGeo v5 = true ∧
    w3.ty vxS vbS verifyGeo v6 = some v7 ∧ w3.eok vxS vbS verifyGeo v6 = true ∧
    dm.ty vxS vbS verifyGeo v7 = some v8 ∧ dm.eok vxS vbS verifyGeo v7 = true ∧
    encode.ty vpS vbS verifyGeo v8 = some v9 ∧ v9.ex = none ∧ encode.eok vpS vbS verifyGeo v8 = true ∧
    compare.ty vxS vbS verifyGeo v9 = some v10 ∧ compare.eok vxS vbS verifyGeo v9 = true := by
  decide +kernel

end M0Crypto.Release.Ed25519VerifyProg
