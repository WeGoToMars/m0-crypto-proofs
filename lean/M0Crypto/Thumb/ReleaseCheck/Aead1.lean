import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedAead1 : Fin aeadShardCount := ⟨1, by decide⟩

#eval runAeadShard checkedAead1

end M0Crypto.Thumb.ReleaseCheck
