import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead7 : Fin aeadShardCount := ⟨7, by decide⟩

#eval runAeadShard checkedAead7

end M0Crypto.Thumb.ReleaseCheck
