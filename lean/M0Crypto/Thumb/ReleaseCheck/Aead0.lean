import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead0 : Fin aeadShardCount := ⟨0, by decide⟩

#eval runAeadShard checkedAead0

end M0Crypto.Thumb.ReleaseCheck
