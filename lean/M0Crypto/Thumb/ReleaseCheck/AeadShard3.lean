import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard3 : Fin aeadShardCount := ⟨3, by decide⟩

#eval runAeadShard aeadShard3

end M0Crypto.Thumb.ReleaseCheck
