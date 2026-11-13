import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard7 : Fin aeadShardCount := ⟨7, by decide⟩

#eval runAeadShard aeadShard7

end M0Crypto.Thumb.ReleaseCheck
