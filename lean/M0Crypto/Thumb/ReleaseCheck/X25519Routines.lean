import M0Crypto.Thumb.ReleaseCheck.X25519Cases

/-! The three field routines on 409 operand pairs each (17 edge values squared, 120
pseudo-random pairs), over five aliasing layouts, and guards that the checks reject a wrong
function, a smaller stack and a narrower write range. -/

namespace M0Crypto.Thumb.ReleaseCheck.X25519

#eval runRoutines

-- Non-vacuity: a wrong function, a smaller frame and a narrower `dst` are rejected.
#guard (routineCase "mul+1" feMul feMulSize 148 true (fun x y => x * y + 1) rd ra rb
  (rnd 32 1) (rnd 32 2)).isSome
#guard (routineCase "mul frame" feMul feMulSize 144 true mulF rd ra rb (rnd 32 1) (rnd 32 2)).isSome
#guard (routineCase "sqr as mul" feSqr feSqrSize 148 false mulF rd ra rb (rnd 32 1) (rnd 32 2)).isSome
#guard (routineCase "mulc" feMulcAdd feMulcAddSize 4 true (fun x y => 121665 * x + y) rd ra rb
  (rnd 32 1) (rnd 32 2)).isSome
#guard (routineCase "ok" feMul feMulSize 148 true mulF rd ra rb (rnd 32 1) (rnd 32 2)).isNone

end M0Crypto.Thumb.ReleaseCheck.X25519
