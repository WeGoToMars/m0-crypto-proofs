import M0Crypto.Thumb.ReleaseCheck.ChaCha0
import M0Crypto.Thumb.ReleaseCheck.ChaCha1
import M0Crypto.Thumb.ReleaseCheck.ChaCha2
import M0Crypto.Thumb.ReleaseCheck.ChaCha3
import M0Crypto.Thumb.ReleaseCheck.Aead0
import M0Crypto.Thumb.ReleaseCheck.Aead1
import M0Crypto.Thumb.ReleaseCheck.Aead2
import M0Crypto.Thumb.ReleaseCheck.Aead3
import M0Crypto.Thumb.ReleaseCheck.Aead4
import M0Crypto.Thumb.ReleaseCheck.Aead5
import M0Crypto.Thumb.ReleaseCheck.Aead6
import M0Crypto.Thumb.ReleaseCheck.Aead7
import M0Crypto.Thumb.ReleaseCheck.Pairwise

/-! Complete executable release checks. Lake builds the imported shards in
parallel. Each shard runs the same case evaluator; Cases checks the partition,
and the guards below check that this root schedules every shard exactly once.
Use `lake build +M0Crypto.Thumb.ReleaseCheck` to rebuild affected evaluations;
running this import root with `lake env lean` alone does not rebuild imports. -/

namespace M0Crypto.Thumb.ReleaseCheck

#guard [checkedChaCha0.val, checkedChaCha1.val, checkedChaCha2.val, checkedChaCha3.val] == List.range chachaShardCount
#guard [checkedAead0.val, checkedAead1.val, checkedAead2.val, checkedAead3.val, checkedAead4.val, checkedAead5.val, checkedAead6.val, checkedAead7.val] == List.range aeadShardCount

end M0Crypto.Thumb.ReleaseCheck
