import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead2 : Fin aeadShardCount := ⟨2, by decide⟩

#eval runAeadShard checkedAead2

end M0Crypto.Thumb.ReleaseCheck
