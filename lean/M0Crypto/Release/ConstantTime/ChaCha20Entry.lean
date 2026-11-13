import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Envs

/-! # Certificate for `m0c_chacha20_xor` -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

def chacha20Cert : Cert :=
  ct_cert% gen chacha20Env Release.bytes Release.chacha20_xor (entryState chacha20ArgWords) genFuel

theorem chacha20_certOk :
    certOk chacha20Env Release.bytes Release.chacha20_xor (entryState chacha20ArgWords)
      chacha20Cert = true := by
  decide +kernel

theorem chacha20_certFailure_eq_none :
    certFailure chacha20Env Release.bytes Release.chacha20_xor
      (entryState chacha20ArgWords) chacha20Cert = none :=
  (certOk_iff _ _ _ _ _).mp chacha20_certOk

theorem chacha20_slotsCheck : certSlotsCheck chacha20Env chacha20Cert = true := by
  decide +kernel

theorem chacha20_indicesCheck : certIndicesCheck chacha20Cert chacha20Env = true := by
  decide +kernel

theorem chacha20_indicesFailure_eq_none : certIndicesFailure chacha20Cert chacha20Env = none :=
  (certIndicesFailure_eq_none_iff chacha20Cert chacha20Env).mpr chacha20_indicesCheck

theorem chacha20_certAligned : certAligned chacha20Cert = true := by decide +kernel

end M0Crypto.Release.ConstantTime
