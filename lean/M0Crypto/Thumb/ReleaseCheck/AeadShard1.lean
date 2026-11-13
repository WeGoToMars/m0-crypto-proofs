import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard1 : Fin aeadShardCount := ⟨1, by decide⟩

#eval runAeadShard aeadShard1

end M0Crypto.Thumb.ReleaseCheck
