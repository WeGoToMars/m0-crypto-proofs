import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck
open M0Crypto

-- The specification is RFC 7693's BLAKE2s-256: the empty-message digest starts 69 21 7a 30.
#guard (M0Crypto.Spec.Blake2s.blake2s []).take 4 == [0x69#8, 0x21#8, 0x7a#8, 0x30#8]

#eval runB2sShard0

-- Non-vacuity: the audit rejects a narrower write range, and the spec comparison a wrong digest.
#guard
  let mem := mkMem [(ctxA, gen ctxSize 1), (0x20001000, gen 10 2)]
  match stepCheck "init" mem Artifacts.Release.blake2s_init [ctxA] [] [(ctxA, 100)] b2sInitStack with
  | .error _ => true
  | .ok _ => false

#guard
  let mem := mkMem [(ctxA, gen ctxSize 1), (0x20001000, gen 10 2)]
  match stepCheck "init" mem Artifacts.Release.blake2s_init [ctxA] [] [(ctxA, ctxSize)] 0 with
  | .error _ => true
  | .ok _ => false

#guard (b2sStreamCase 10 0 0 [3, 4] 1).isSome

end M0Crypto.Thumb.ReleaseCheck
