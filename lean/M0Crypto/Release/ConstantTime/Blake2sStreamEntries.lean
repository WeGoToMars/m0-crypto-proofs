import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.Blake2sStreamCode
import M0Crypto.Release.Blake2sStreamSites
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.ReadBounds
import M0Crypto.Release.Blake2sFrames

/-!
# Certificates for the BLAKE2s streaming entries

`m0c_blake2s_init`, `_copy`, `_update` and `_final` take only register arguments. `update`
and `final` branch on `ctx.used`, a public value held in memory; the environment declares the
two loads of it (`updateUsedLoad`, `finalUsedLoad`) as public (`Env.pubLoads`). The soundness
obligation is `PubLoadOk`: the two runs load the same word there.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release M0Crypto.Thumb M0Crypto.Release.Blake2sStreamCode

/-- The `ldr r7, [r4, #CTX_USED]` of `update`: the last instruction of its prologue. -/
def updateUsedLoad : Nat := uStart + seqSize uPro.dropLast

/-- The `ldr r6, [r4, #CTX_USED]` of `final`: the fifth instruction. -/
def finalUsedLoad : Nat := fStart + seqSize (fPro.take 4)

def b2iEnv : Env := ⟨⟨4, 0⟩, Artifacts.Release.size, none, [], false⟩
def b2kEnv : Env := ⟨⟨20, 0⟩, Artifacts.Release.size, none, [], false⟩
def b2uEnv : Env := ⟨⟨STREAM_FRAME, 0⟩, Artifacts.Release.size, none, [updateUsedLoad], false⟩
def b2fEnv : Env := ⟨⟨STREAM_FRAME, 0⟩, Artifacts.Release.size, none, [finalUsedLoad], false⟩


def b2uCert : Cert :=
  ct_cert% gen b2uEnv Artifacts.Release.bytes Artifacts.Release.blake2s_update (entryStateP 3 0) genFuel

def b2fCert : Cert :=
  ct_cert% gen b2fEnv Artifacts.Release.bytes Artifacts.Release.blake2s_final (entryStateP 2 0) genFuel


def b2iCert : Cert :=
  ct_cert% gen b2iEnv Artifacts.Release.bytes Artifacts.Release.blake2s_init (entryStateP 1 0) genFuel

def b2kCert : Cert :=
  ct_cert% gen b2kEnv Artifacts.Release.bytes Artifacts.Release.blake2s_copy (entryStateP 3 0) genFuel

theorem b2i_certOk :
    certOk b2iEnv Artifacts.Release.bytes Artifacts.Release.blake2s_init (entryStateP 1 0) b2iCert = true := by
  decide +kernel

theorem b2i_indicesCheck : certIndicesCheck b2iCert b2iEnv = true := by decide +kernel

theorem b2i_indicesFailure_eq_none : certIndicesFailure b2iCert b2iEnv = none :=
  (certIndicesFailure_eq_none_iff b2iCert b2iEnv).mpr b2i_indicesCheck

theorem b2i_slotsCheck : certSlotsCheck b2iEnv b2iCert = true := by decide +kernel

theorem b2i_certAligned : certAligned b2iCert = true := by decide +kernel

theorem b2i_sites : certSites b2iEnv initSites b2iCert = true := by decide +kernel

theorem b2i_loadFailure : certLoadFailure (fun _ => false) b2iEnv b2iCert = none := by decide +kernel

theorem b2k_certOk :
    certOk b2kEnv Artifacts.Release.bytes Artifacts.Release.blake2s_copy (entryStateP 3 0) b2kCert = true := by
  decide +kernel

theorem b2k_indicesCheck : certIndicesCheck b2kCert b2kEnv = true := by decide +kernel

theorem b2k_indicesFailure_eq_none : certIndicesFailure b2kCert b2kEnv = none :=
  (certIndicesFailure_eq_none_iff b2kCert b2kEnv).mpr b2k_indicesCheck

theorem b2k_slotsCheck : certSlotsCheck b2kEnv b2kCert = true := by decide +kernel

theorem b2k_certAligned : certAligned b2kCert = true := by decide +kernel

theorem b2k_sites : certSites b2kEnv copySites b2kCert = true := by decide +kernel

theorem b2u_certOk :
    certOk b2uEnv Artifacts.Release.bytes Artifacts.Release.blake2s_update (entryStateP 3 0) b2uCert = true := by
  decide +kernel

theorem b2u_indicesCheck : certIndicesCheck b2uCert b2uEnv = true := by decide +kernel

theorem b2u_indicesFailure_eq_none : certIndicesFailure b2uCert b2uEnv = none :=
  (certIndicesFailure_eq_none_iff b2uCert b2uEnv).mpr b2u_indicesCheck

theorem b2u_slotsCheck : certSlotsCheck b2uEnv b2uCert = true := by decide +kernel

theorem b2u_certAligned : certAligned b2uCert = true := by decide +kernel

theorem b2f_certOk :
    certOk b2fEnv Artifacts.Release.bytes Artifacts.Release.blake2s_final (entryStateP 2 0) b2fCert = true := by
  decide +kernel

theorem b2f_indicesCheck : certIndicesCheck b2fCert b2fEnv = true := by decide +kernel

theorem b2f_indicesFailure_eq_none : certIndicesFailure b2fCert b2fEnv = none :=
  (certIndicesFailure_eq_none_iff b2fCert b2fEnv).mpr b2f_indicesCheck

theorem b2f_slotsCheck : certSlotsCheck b2fEnv b2fCert = true := by decide +kernel

theorem b2f_certAligned : certAligned b2fCert = true := by decide +kernel

/-! ## Negative controls

Without the declaration, or with it one instruction off, generation fails on the branch that
tests `ctx.used`. -/

def genFails (env : Env) (entry : Nat) (np : Nat) : Bool :=
  match gen env Artifacts.Release.bytes entry (entryStateP np 0) genFuel with
  | .error _ => true
  | .ok _ => false

#guard genFails { b2uEnv with pubLoads := [] } Artifacts.Release.blake2s_update 3
#guard genFails { b2uEnv with pubLoads := [updateUsedLoad + 2] } Artifacts.Release.blake2s_update 3
#guard genFails { b2uEnv with pubLoads := [updateUsedLoad - 2] } Artifacts.Release.blake2s_update 3
#guard genFails { b2fEnv with pubLoads := [] } Artifacts.Release.blake2s_final 2
#guard genFails { b2fEnv with pubLoads := [finalUsedLoad + 2] } Artifacts.Release.blake2s_final 2
#guard genFails { b2fEnv with pubLoads := [finalUsedLoad - 2] } Artifacts.Release.blake2s_final 2

end M0Crypto.Release.ConstantTime
