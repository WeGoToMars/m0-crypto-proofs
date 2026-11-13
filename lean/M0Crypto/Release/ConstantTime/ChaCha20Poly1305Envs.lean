import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.AeadCode
import M0Crypto.Release.ChaCha20TraceSpecDefs

/-!
Certificate environments of `m0c_chacha20_xor` and AEAD decryption.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts M0Crypto.Release

def chacha20Env : Env := ⟨⟨TraceSpec.chacha20StackBytes, 4 * chacha20ArgWords⟩, Release.size, none, [], false⟩

def encryptEnv : Env := ⟨⟨TraceSpec.aeadStackBytes, 4 * aeadArgWords⟩, Release.size, none, [], false⟩

def decryptEnv : Env :=
  ⟨⟨TraceSpec.aeadStackBytes, 4 * aeadArgWords⟩, Release.size, some Aead.decRejectBrAt, [], false⟩

end M0Crypto.Release.ConstantTime
