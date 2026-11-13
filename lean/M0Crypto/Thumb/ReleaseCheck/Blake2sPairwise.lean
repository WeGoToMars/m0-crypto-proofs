import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck
open M0Crypto.Artifacts

/-! ## Pairwise constant-time checks for BLAKE2s

Same pointers and same sequence of lengths; different message bytes, different context
garbage, different caller registers. -/

#eval runB2sPairwise

-- Non-vacuity: different lengths give different traces; so do different partitions.
#guard
  match b2sSeqTrace 64 0 0 [64] 1 2 sentinel, b2sSeqTrace 65 0 0 [65] 1 2 sentinel with
  | .ok a, .ok b => a != b
  | _, _ => false

#guard
  match b2sSeqTrace 100 0 0 [100] 1 2 sentinel, b2sSeqTrace 100 0 0 [50, 50] 1 2 sentinel with
  | .ok a, .ok b => a != b
  | _, _ => false

end M0Crypto.Thumb.ReleaseCheck
