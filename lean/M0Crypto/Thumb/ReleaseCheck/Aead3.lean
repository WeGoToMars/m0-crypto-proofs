import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead3 : Fin aeadShardCount := ⟨3, by decide⟩

#eval runAeadShard checkedAead3

end M0Crypto.Thumb.ReleaseCheck
