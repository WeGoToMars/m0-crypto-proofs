import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard2 : Fin aeadShardCount := ⟨2, by decide⟩

#eval runAeadShard aeadShard2

end M0Crypto.Thumb.ReleaseCheck
