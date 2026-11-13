import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard0 : Fin aeadShardCount := ⟨0, by decide⟩

#eval runAeadShard aeadShard0

end M0Crypto.Thumb.ReleaseCheck
