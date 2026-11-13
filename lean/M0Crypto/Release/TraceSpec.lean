import M0Crypto.Release.Contract

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb

namespace M0Crypto.Release.TraceSpec

/-!
# Shared vocabulary of the trace specifications

Statement file: definitions only. The read model (`ReadsFrom`) and the stack window
(`InStackWindow`) used by the per-function trace specifications: `ChaCha20TraceSpec`
(`m0c_chacha20_xor` and the AEAD entry points) and `X25519TraceSpec` (`m0c_x25519`).
-/

/-! ## Read access model -/

/-- Every read of the trace lies in `Rd`. -/
def ReadsFrom (Rd : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y

/-! ## Stack window containment -/

/-- SP lies in the entry's stack window `[sp0 - stackBytes, sp0]`. -/
def InStackWindow (sp0 : Word) (stackBytes : Nat) (sp : Word) : Prop :=
  ∃ o ≤ stackBytes, sp = sp0 - BitVec.ofNat 32 o

end M0Crypto.Release.TraceSpec
