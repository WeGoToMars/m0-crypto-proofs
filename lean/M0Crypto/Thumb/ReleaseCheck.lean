import M0Crypto.Thumb.ReleaseCheck.ChaCha20Shard0
import M0Crypto.Thumb.ReleaseCheck.ChaCha20Shard1
import M0Crypto.Thumb.ReleaseCheck.ChaCha20Shard2
import M0Crypto.Thumb.ReleaseCheck.ChaCha20Shard3
import M0Crypto.Thumb.ReleaseCheck.AeadShard0
import M0Crypto.Thumb.ReleaseCheck.AeadShard1
import M0Crypto.Thumb.ReleaseCheck.AeadShard2
import M0Crypto.Thumb.ReleaseCheck.AeadShard3
import M0Crypto.Thumb.ReleaseCheck.AeadShard4
import M0Crypto.Thumb.ReleaseCheck.AeadShard5
import M0Crypto.Thumb.ReleaseCheck.AeadShard6
import M0Crypto.Thumb.ReleaseCheck.AeadShard7
import M0Crypto.Thumb.ReleaseCheck.Pairwise

/-! Complete executable release checks. Lake builds the imported shards in
parallel. Each shard runs the same case evaluator; Cases checks the partition,
and the guards below check that this root schedules every shard exactly once.
Use `lake build +M0Crypto.Thumb.ReleaseCheck` to rebuild affected evaluations;
running this import root with `lake env lean` alone does not rebuild imports. -/

namespace M0Crypto.Thumb.ReleaseCheck

#guard [chacha20Shard0.val, chacha20Shard1.val, chacha20Shard2.val, chacha20Shard3.val] == List.range chacha20ShardCount
#guard [aeadShard0.val, aeadShard1.val, aeadShard2.val, aeadShard3.val, aeadShard4.val, aeadShard5.val, aeadShard6.val, aeadShard7.val] == List.range aeadShardCount

end M0Crypto.Thumb.ReleaseCheck
