import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt

/-!
# Non-vacuity of the ChaCha20 and ChaCha20-Poly1305 entry contracts

For each function, one concrete call that meets the hypothesis shared by all of the
function's top-level theorems (`ChaCha20Xor.Pre`, `Aead.APre`), passed to its correctness
theorem (`example`s at the end). The calls exercise the cases where an over-strong
precondition would hide: in-place operation, unaligned buffers and a non-empty message.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj Ctx Valid)
open M0Crypto.Release.Aead (ACall AValid ABuf AEntry)

/-! ## ChaCha20: in place, 100 bytes at an odd address, counter 1 -/

def chMem : Mem := memOf [(sp0, le32 0x20000340 ++ le32 1)]

def chCtx : Frame.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000401#32, 100#32, 0x20000300#32, 0x20000340#32,
   1#32, chMem, regsOf 0 0x20000401 0x20000401 100 0x20000300⟩

theorem xor_correct_nonvacuous : ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, Frame.Ctx.fp, chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, Artifacts.Release.size]; decide +kernel)

/-! ## AEAD: in place, 100 bytes at an odd address, 13-byte AAD, unaligned tag -/

def aMem : Mem :=
  memOf [(sp0, le32 0x20000500 ++ le32 13 ++ le32 0x20000300 ++ le32 0x20000340)]

def aCall (off : Nat) : ACall :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000483#32, 0x20000401#32, 100#32, 0x20000500#32,
   13#32, 0x20000300#32, 0x20000340#32, aMem, regsOf off 0x20000401 0x20000483 0x20000401 100⟩

local macro "aead_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide +kernel, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, aCall, Artifacts.Release.size]; decide +kernel)))

theorem encrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) := by
  aead_witness

theorem decrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.decOff) Aead.decOff (stOf aMem (aCall Aead.decOff).regs0) := by
  aead_witness

/-! ## Each witness fits its theorem -/

example := ChaCha20Xor.xor_correct _ _ xor_correct_nonvacuous
example := Aead.encrypt_correct _ _ encrypt_correct_nonvacuous
example := Aead.decrypt_correct _ _ decrypt_correct_nonvacuous

end M0Crypto.Release.NonVacuity
