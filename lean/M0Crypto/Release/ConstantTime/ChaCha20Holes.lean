import M0Crypto.Release.ConstantTime.HoleElab
import M0Crypto.Release.ConstantTime.ChaCha20Entry

/-! The hole map of `m0c_chacha20_xor` (`Holes.lean`), generated at build time and checked by the
kernel. -/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Artifacts

def chacha20Holes : HoleMap := hole_map% genHoles chacha20Env Release.chacha20_xor chacha20Cert 200

theorem chacha20_holes :
    certHoleFailure chacha20Env (fun _ => none) chacha20Holes chacha20Cert = none := by
  decide +kernel

end M0Crypto.Release.ConstantTime
