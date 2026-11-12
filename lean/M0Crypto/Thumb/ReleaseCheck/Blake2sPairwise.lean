import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck
open M0Crypto.Artifacts

/-! ## Pairwise constant-time checks for BLAKE2s

Same pointers and same sequence of lengths; different message bytes, different context
garbage, different caller registers. -/

private def same (len inOff outOff : Nat) (parts : List Nat) : Bool :=
  match b2sSeqTrace len inOff outOff parts 1 2 sentinel,
        b2sSeqTrace len inOff outOff parts 101 202 sentinel2 with
  | .ok a, .ok b => a == b
  | _, _ => false

#guard same 0 0 0 [0]
#guard same 1 1 2 [1]
#guard same 63 0 0 [63]
#guard same 64 3 1 [64]
#guard same 65 2 2 [65]
#guard same 200 1 3 [200]
#guard same 200 0 0 [63, 1, 64, 72]
#guard same 130 3 1 [17, 17, 17, 17, 17, 17, 17, 11]
#guard same 1025 1 1 [1025]
#guard same 1025 2 3 [500, 525]
#guard same 129 0 0 [64, 1, 64]

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
