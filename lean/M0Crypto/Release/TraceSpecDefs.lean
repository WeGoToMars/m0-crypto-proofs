import M0Crypto.Release.ChaCha20Layout

/-!
# Stack bound constants of the trace specifications

Split out of `TraceSpec` so that the constant-time certificates can use them without
importing the functional proofs.
-/

namespace M0Crypto.Release.TraceSpec

/-- Stack bytes allocated by the AEAD entry points (`m0c_chacha20poly1305_encrypt`
and `m0c_chacha20poly1305_decrypt`), matching `AValid.spLo`. -/
def aeadStackBytes : Nat := 320

theorem aeadStackBytes_eq : aeadStackBytes = 320 := by decide

/-- Stack bytes allocated by `m0c_chacha20_xor`, matching `ChaCha20Layout.chStackBytes`. -/
def chacha20StackBytes : Nat := ChaCha20Layout.chStackBytes

theorem chacha20StackBytes_eq : chacha20StackBytes = 176 := ChaCha20Layout.chStackBytes_eq

end M0Crypto.Release.TraceSpec
