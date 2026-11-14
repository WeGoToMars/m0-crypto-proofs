import M0Crypto.Release.ConstantTime.HoleElab
import M0Crypto.Release.ConstantTime.AeadDecryptEntry
import M0Crypto.Release.AeadReadSites

/-! The hole map of `m0c_chacha20poly1305_decrypt` (`Holes.lean`), generated at build time and
checked by the kernel with the stack ranges `Aead.siteRange` at its load sites. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts

def decryptHoles : HoleMap :=
  hole_map% genHoles decryptEnv Release.chacha20poly1305_decrypt decryptCert 200

theorem decrypt_holes : certHoleFailure decryptEnv Aead.siteRange decryptHoles decryptCert = none := by
  decide +kernel

end M0Crypto.Release.ConstantTime
