import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.Blake2sFrames

/-! # Certificate for `m0c_blake2s_compress` -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

/-- Stack argument of `m0c_blake2s_compress`: `f0`. -/
def b2cArgWords : Nat := 1

/-- Stack window of the compression: 136 bytes below the entry `sp`, the `f0` word above. -/
def b2cEnv : Env := ⟨⟨COMPRESS_FRAME, 4 * b2cArgWords⟩, Release.size, none, []⟩

def b2cCert : Cert :=
  ct_cert% gen b2cEnv Release.bytes Release.blake2s_compress (entryState b2cArgWords) genFuel

theorem b2c_certOk :
    certOk b2cEnv Release.bytes Release.blake2s_compress (entryState b2cArgWords) b2cCert = true := by
  decide +kernel

theorem b2c_indicesCheck : certIndicesCheck b2cCert b2cEnv = true := by decide +kernel

theorem b2c_indicesFailure_eq_none : certIndicesFailure b2cCert b2cEnv = none :=
  (certIndicesFailure_eq_none_iff b2cCert b2cEnv).mpr b2c_indicesCheck

theorem b2c_slotsCheck : certSlotsCheck b2cEnv b2cCert = true := by decide +kernel

theorem b2c_certAligned : certAligned b2cCert = true := by decide +kernel

theorem b2c_sites : certSites b2cEnv Blake2sCode.compressSites b2cCert = true := by decide +kernel

end M0Crypto.Release.ConstantTime
