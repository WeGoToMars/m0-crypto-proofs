import M0Crypto.Thumb.ReleaseCheck.X25519Cases

namespace M0Crypto.Thumb.ReleaseCheck.X25519

def x25519Shard2 : Fin entryShardCount := ⟨2, by decide⟩

#eval runEntryShard x25519Shard2

end M0Crypto.Thumb.ReleaseCheck.X25519
