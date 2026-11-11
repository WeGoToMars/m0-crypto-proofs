import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck

def chacha20Shard3 : Fin chacha20ShardCount := ⟨3, by decide⟩

#eval runChaCha20Shard chacha20Shard3

end M0Crypto.Thumb.ReleaseCheck
