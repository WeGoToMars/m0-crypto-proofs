import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedChaCha3 : Fin chachaShardCount := ⟨3, by decide⟩

#eval runChaChaShard checkedChaCha3

end M0Crypto.Thumb.ReleaseCheck
