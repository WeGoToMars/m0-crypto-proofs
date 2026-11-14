import M0Crypto.Release.ConstantTime.HoleElab
import M0Crypto.Release.ConstantTime.X25519Entry

/-! The hole map of `m0c_x25519` (`Holes.lean`), generated at build time and checked by the
kernel. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts

def x25519Holes : HoleMap := hole_map% genHoles x25519Env Release.x25519 x25519Cert 200

theorem x25519_holes : certHoleFailure x25519Env (fun _ => none) x25519Holes x25519Cert = none := by
  decide +kernel

end M0Crypto.Release.ConstantTime
