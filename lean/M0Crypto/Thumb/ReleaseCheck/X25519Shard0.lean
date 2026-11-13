import M0Crypto.Thumb.ReleaseCheck.X25519Cases

namespace M0Crypto.Thumb.ReleaseCheck.X25519

def x25519Shard0 : Fin entryShardCount := ⟨0, by decide⟩

#eval runEntryShard x25519Shard0

end M0Crypto.Thumb.ReleaseCheck.X25519
