import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead5 : Fin aeadShardCount := ⟨5, by decide⟩

#eval runAeadShard checkedAead5

end M0Crypto.Thumb.ReleaseCheck
