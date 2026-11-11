import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead4 : Fin aeadShardCount := ⟨4, by decide⟩

#eval runAeadShard checkedAead4

end M0Crypto.Thumb.ReleaseCheck
