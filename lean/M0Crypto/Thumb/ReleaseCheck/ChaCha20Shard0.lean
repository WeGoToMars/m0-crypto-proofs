import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def chacha20Shard0 : Fin chacha20ShardCount := ⟨0, by decide⟩

#eval runChaCha20Shard chacha20Shard0

end M0Crypto.Thumb.ReleaseCheck
