import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard4 : Fin aeadShardCount := ⟨4, by decide⟩

#eval runAeadShard aeadShard4

end M0Crypto.Thumb.ReleaseCheck
