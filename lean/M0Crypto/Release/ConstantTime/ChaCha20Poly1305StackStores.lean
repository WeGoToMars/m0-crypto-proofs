import M0Crypto.Release.ConstantTime.StackStoreSound
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Envs

/-!
Code and stack disjointness of the ChaCha20 and AEAD calls.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg write32)
open M0Crypto.Thumb

/-- The ChaCha entry contract separates the artifact and analysis stack window. -/
theorem chacha20_code_stack_disj (c : M0Crypto.Release.Frame.Ctx)
    (hv : M0Crypto.Release.Frame.Valid c) :
    M0Crypto.Release.Frame.Disj c.base M0Crypto.Artifacts.Release.size
      (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) := by
  simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes,
    M0Crypto.Release.Frame.Ctx.fp, M0Crypto.Release.ChaCha20Layout.chStackBytes_eq] using hv.codeF

/-- The AEAD entry contract separates the artifact and analysis stack window. -/
theorem aead_code_stack_disj (c : M0Crypto.Release.Aead.ACall)
    (hv : M0Crypto.Release.Aead.AValid c) :
    M0Crypto.Release.Frame.Disj c.base M0Crypto.Artifacts.Release.size
      (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) := by
  simpa [encryptEnv, aeadArgWords, TraceSpec.aeadStackBytes] using hv.codeS

end M0Crypto.Release.ConstantTime
