import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Envs

/-! # Certificate for `m0c_chacha20poly1305_encrypt` -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

def encryptCert : Cert :=
  ct_cert% gen encryptEnv Release.bytes Release.chacha20poly1305_encrypt
    (entryState aeadArgWords) genFuel

theorem encrypt_certOk :
    certOk encryptEnv Release.bytes Release.chacha20poly1305_encrypt (entryState aeadArgWords)
      encryptCert = true := by
  decide +kernel

theorem encrypt_certFailure_eq_none :
    certFailure encryptEnv Release.bytes Release.chacha20poly1305_encrypt
      (entryState aeadArgWords) encryptCert = none :=
  (certOk_iff _ _ _ _ _).mp encrypt_certOk

theorem encrypt_slotsCheck : certSlotsCheck encryptEnv encryptCert = true := by
  decide +kernel

theorem encrypt_indicesCheck : certIndicesCheck encryptCert encryptEnv = true := by
  decide +kernel

theorem encrypt_indicesFailure_eq_none : certIndicesFailure encryptCert encryptEnv = none :=
  (certIndicesFailure_eq_none_iff encryptCert encryptEnv).mpr encrypt_indicesCheck

theorem encrypt_certAligned : certAligned encryptCert = true := by decide +kernel

end M0Crypto.Release.ConstantTime
