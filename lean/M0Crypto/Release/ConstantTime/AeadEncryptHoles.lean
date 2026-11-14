import M0Crypto.Release.ConstantTime.HoleElab
import M0Crypto.Release.ConstantTime.AeadEncryptEntry
import M0Crypto.Release.AeadReadSites

/-! The hole map of `m0c_chacha20poly1305_encrypt` (`Holes.lean`), generated at build time and
checked by the kernel with the stack ranges `Aead.siteRange` at its load sites. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts

def encryptHoles : HoleMap :=
  hole_map% genHoles encryptEnv Release.chacha20poly1305_encrypt encryptCert 200

theorem encrypt_holes : certHoleFailure encryptEnv Aead.siteRange encryptHoles encryptCert = none := by
  decide +kernel

end M0Crypto.Release.ConstantTime
