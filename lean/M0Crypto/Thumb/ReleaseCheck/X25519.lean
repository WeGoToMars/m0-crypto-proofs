import M0Crypto.Thumb.ReleaseCheck.X25519Routines
import M0Crypto.Thumb.ReleaseCheck.X25519Shard0
import M0Crypto.Thumb.ReleaseCheck.X25519Shard1
import M0Crypto.Thumb.ReleaseCheck.X25519Shard2
import M0Crypto.Thumb.ReleaseCheck.X25519Shard3

/-! Complete executable release checks of the X25519 asset. Lake builds the imported shards
in parallel; the guard below checks that this root schedules every entry shard exactly once.
Use `lake build +M0Crypto.Thumb.ReleaseCheck.X25519` to rebuild affected evaluations. -/

namespace M0Crypto.Thumb.ReleaseCheck

#guard [X25519.x25519Shard0.val, X25519.x25519Shard1.val, X25519.x25519Shard2.val, X25519.x25519Shard3.val] == List.range X25519.entryShardCount

end M0Crypto.Thumb.ReleaseCheck
