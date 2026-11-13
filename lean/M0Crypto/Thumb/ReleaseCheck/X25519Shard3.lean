import M0Crypto.Thumb.ReleaseCheck.X25519Cases

namespace M0Crypto.Thumb.ReleaseCheck.X25519

def x25519Shard3 : Fin entryShardCount := ⟨3, by decide⟩

#eval runEntryShard x25519Shard3

-- Non-vacuity: the audit rejects a write range one byte short of `out`.
#guard (entryCase "short out" bufO bufS bufP vk1 vu1 31).isSome

end M0Crypto.Thumb.ReleaseCheck.X25519
