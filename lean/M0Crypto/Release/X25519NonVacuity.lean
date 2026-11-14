import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.X25519Correct
import M0Crypto.Spec.X25519Vectors
import M0Crypto.Release.X25519TraceSpec

/-!
# Non-vacuity of the X25519 entry contract

`x25519_pre_nonvacuous`: `out` is `point`, at an odd address, and `scalar` is unaligned, on
RFC 7748 vector 1; passed to `x25519_correct`. `x25519_constant_time_nonvacuous`: that call and
the same call with the scalar of vector 2, the two calls `x25519_constant_time` assumes.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)

/-! ## X25519: `out` = `point`, both at odd addresses, `scalar` unaligned (RFC 7748 vector 1) -/

def xMem : Mem := memOf
  [(0x20000401, M0Crypto.Spec.X25519.ofHex
      "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4" ++
    M0Crypto.Spec.X25519.ofHex
      "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c")]

def xCtx : X25519.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000421#32, 0x20000401#32, 0x20000421#32, xMem,
   regsOf Artifacts.Release.x25519 0x20000421 0x20000401 0x20000421 0⟩

local macro "x25519_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩,
    by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (simp only [Disj, X25519.Ctx.fp, xCtx, X25519.stackBytes, sp0, Artifacts.Release.size]; decide +kernel) | (simp only [Disj]; decide +kernel)))

theorem x25519_pre_nonvacuous : X25519.Pre xCtx (stOf xMem xCtx.regs0) := by
  x25519_witness

example := X25519.x25519_correct _ _ x25519_pre_nonvacuous

/-! ## Constant time: the same call with the scalar of RFC 7748 vector 2 -/

def xMem2 : Mem := memOf
  [(0x20000401, M0Crypto.Spec.X25519.ofHex
      "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d" ++
    M0Crypto.Spec.X25519.ofHex
      "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c")]

/-- `xCtx` with another scalar. -/
def xCtx2 : X25519.Ctx := { xCtx with m0 := xMem2 }

/-- Two valid calls with equal public inputs and different scalars, as `x25519_constant_time`
assumes them. -/
theorem x25519_constant_time_nonvacuous :
    X25519.Pre xCtx (stOf xMem xCtx.regs0) ∧ X25519.Pre xCtx2 (stOf xMem2 xCtx2.regs0) ∧
      xCtx.pub = xCtx2.pub ∧ xCtx.scalarB ≠ xCtx2.scalarB :=
  ⟨x25519_pre_nonvacuous, by x25519_witness, by simp only [X25519.Ctx.pub, xCtx2],
    by decide +kernel⟩

end M0Crypto.Release.NonVacuity
