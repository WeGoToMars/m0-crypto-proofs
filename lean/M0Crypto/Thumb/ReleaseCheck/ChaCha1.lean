import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedChaCha1 : Fin chachaShardCount := ⟨1, by decide⟩

#eval runChaChaShard checkedChaCha1

end M0Crypto.Thumb.ReleaseCheck
