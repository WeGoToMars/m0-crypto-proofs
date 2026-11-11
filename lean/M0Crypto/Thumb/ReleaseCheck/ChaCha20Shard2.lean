import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def chacha20Shard2 : Fin chacha20ShardCount := ⟨2, by decide⟩

#eval runChaCha20Shard chacha20Shard2

end M0Crypto.Thumb.ReleaseCheck
