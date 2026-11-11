import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedChaCha0 : Fin chachaShardCount := ⟨0, by decide⟩

#eval runChaChaShard checkedChaCha0

end M0Crypto.Thumb.ReleaseCheck
