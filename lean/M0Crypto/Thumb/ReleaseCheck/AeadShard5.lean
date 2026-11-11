import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def aeadShard5 : Fin aeadShardCount := ⟨5, by decide⟩

#eval runAeadShard aeadShard5

end M0Crypto.Thumb.ReleaseCheck
