import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def checkedChaCha2 : Fin chachaShardCount := ⟨2, by decide⟩

#eval runChaChaShard checkedChaCha2

end M0Crypto.Thumb.ReleaseCheck
