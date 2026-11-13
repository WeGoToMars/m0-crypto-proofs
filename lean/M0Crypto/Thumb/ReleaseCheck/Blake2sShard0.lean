import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck
open M0Crypto

private def check (r : Option String) : IO Unit :=
  match r with | some e => throw (IO.userError e) | none => pure ()

-- The specification is RFC 7693's BLAKE2s-256: the empty-message digest starts 69 21 7a 30.
#guard (M0Crypto.Spec.Blake2s.blake2s []).take 4 == [0x69#8, 0x21#8, 0x7a#8, 0x30#8]

-- compress: chosen counters and finalization words, including carries
#eval do
  for (t0, t1) in [(0, 0), (64, 0), (0xffffffc0, 0), (0xffffffc0, 1), (0xffffffff, 0xffffffff), (128, 5)] do
    for f0 in [0, 0xffffffff] do
      check (b2sCompressCase t0 t1 f0 (t0 + f0))

-- hash: one-shot lengths 0-70 at input/output offsets 0-3
#eval do
  for len in List.range 71 do
    for off in [0, 1, 2, 3] do
      check (b2sStreamCase len off ((off + 1) % 4) [len] (len + off))

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
