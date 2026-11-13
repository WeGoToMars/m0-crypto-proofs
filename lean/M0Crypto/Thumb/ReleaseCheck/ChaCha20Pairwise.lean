import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

namespace M0Crypto.Thumb.ReleaseCheck

/-! Pairwise constant-time checks (`pairwiseCases` in `ChaCha20Cases`): equal traces for
different secrets, and different traces for the two decryption verdicts. -/

#eval run "pairwise" (pairwiseCases ())

end M0Crypto.Thumb.ReleaseCheck
