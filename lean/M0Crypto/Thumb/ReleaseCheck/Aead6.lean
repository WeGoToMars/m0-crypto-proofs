import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead6 : Fin aeadShardCount := ⟨6, by decide⟩

#eval runAeadShard checkedAead6

end M0Crypto.Thumb.ReleaseCheck
