import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.X25519Correct
import M0Crypto.Spec.X25519Vectors

/-!
# Non-vacuity of the X25519 entry contract

`x25519_pre_nonvacuous`: `out` is `point`, at an odd address, and `scalar` is unaligned, on
RFC 7748 vector 1; passed to `x25519_correct`.
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

theorem x25519_pre_nonvacuous : X25519.Pre xCtx (stOf xMem xCtx.regs0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩,
    by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (simp only [Disj, X25519.Ctx.fp, xCtx, X25519.stackBytes, sp0, Artifacts.Release.size]; decide +kernel)

example := X25519.x25519_correct _ _ x25519_pre_nonvacuous

end M0Crypto.Release.NonVacuity
