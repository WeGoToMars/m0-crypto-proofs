import M0Crypto.Thumb.ReleaseCheck.X25519Cases

namespace M0Crypto.Thumb.ReleaseCheck.X25519

def x25519Shard1 : Fin entryShardCount := ⟨1, by decide⟩

#eval runEntryShard x25519Shard1

end M0Crypto.Thumb.ReleaseCheck.X25519
