import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates

/-! # Certificate for `m0c_chacha20poly1305_decrypt` -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

def decryptCert : Cert :=
  ct_cert% gen decryptEnv Release.bytes Release.chacha20poly1305_decrypt
    (entryState aeadArgWords) genFuel

theorem decrypt_certOk :
    certOk decryptEnv Release.bytes Release.chacha20poly1305_decrypt (entryState aeadArgWords)
      decryptCert = true := by
  decide +kernel

theorem decrypt_certFailure_eq_none :
    certFailure decryptEnv Release.bytes Release.chacha20poly1305_decrypt
      (entryState aeadArgWords) decryptCert = none :=
  (certOk_iff _ _ _ _ _).mp decrypt_certOk

theorem decrypt_slotsCheck : certSlotsCheck decryptEnv decryptCert = true := by
  decide +kernel

theorem decrypt_indicesCheck : certIndicesCheck decryptCert decryptEnv = true := by
  decide +kernel

theorem decrypt_indicesFailure_eq_none : certIndicesFailure decryptCert decryptEnv = none :=
  (certIndicesFailure_eq_none_iff decryptCert decryptEnv).mpr decrypt_indicesCheck

theorem decrypt_certAligned : certAligned decryptCert = true := by decide +kernel

end M0Crypto.Release.ConstantTime
