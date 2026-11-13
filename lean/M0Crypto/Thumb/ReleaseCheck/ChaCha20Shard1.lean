import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

def chacha20Shard1 : Fin chacha20ShardCount := ⟨1, by decide⟩

#eval runChaCha20Shard chacha20Shard1

end M0Crypto.Thumb.ReleaseCheck
