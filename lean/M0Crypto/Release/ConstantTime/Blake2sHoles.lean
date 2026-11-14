import M0Crypto.Release.ConstantTime.HoleElab
import M0Crypto.Release.ConstantTime.Blake2sStreamEntries

/-! The hole maps of `m0c_blake2s_init`, `m0c_blake2s_update` and `m0c_blake2s_final`
(`Holes.lean`), generated at build time and checked by the kernel. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts

def b2iHoles : HoleMap := hole_map% genHoles b2iEnv Release.blake2s_init b2iCert 200
def b2uHoles : HoleMap := hole_map% genHoles b2uEnv Release.blake2s_update b2uCert 200
def b2fHoles : HoleMap := hole_map% genHoles b2fEnv Release.blake2s_final b2fCert 200

theorem b2i_holes : certHoleFailure b2iEnv (fun _ => none) b2iHoles b2iCert = none := by decide +kernel
theorem b2u_holes : certHoleFailure b2uEnv (fun _ => none) b2uHoles b2uCert = none := by decide +kernel
theorem b2f_holes : certHoleFailure b2fEnv (fun _ => none) b2fHoles b2fCert = none := by decide +kernel

end M0Crypto.Release.ConstantTime
