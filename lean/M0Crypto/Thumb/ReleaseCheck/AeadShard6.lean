import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard6 : Fin aeadShardCount := ⟨6, by decide⟩

#eval runAeadShard aeadShard6

end M0Crypto.Thumb.ReleaseCheck
