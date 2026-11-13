import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.ChaCha20TraceSpec

/-!
# Values of the stack bound constants of the trace specifications

`aeadStackBytes` itself is defined in `TraceSpec`.
-/

namespace M0Crypto.Release.TraceSpec

theorem aeadStackBytes_eq : aeadStackBytes = 320 := by decide

/-- Stack bytes allocated by `m0c_chacha20_xor`, matching `ChaCha20Layout.chStackBytes`. -/
def chacha20StackBytes : Nat := ChaCha20Layout.chStackBytes

theorem chacha20StackBytes_eq : chacha20StackBytes = 176 := ChaCha20Layout.chStackBytes_eq

end M0Crypto.Release.TraceSpec
