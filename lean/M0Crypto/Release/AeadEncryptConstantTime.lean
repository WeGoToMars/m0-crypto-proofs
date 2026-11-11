import M0Crypto.Release.AeadEncryptStack
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates

set_option linter.unusedSimpArgs false
-- the kernel `decide` on the stack-window width needs a deeper recursion limit
set_option maxRecDepth 100000

/-!
# Constant-time trace of AEAD encryption

The certificate relation pairs two executions of `m0c_chacha20poly1305_encrypt` with equal public inputs
and takes a matching step at every position, provided each untracked store of the first run
is separated from the code and the analysis stack window (`PositionObligations`). That
separation is `encrypt_hbuffer`, the same fact the Stack proof uses. The encrypt environment
declassifies no branch, so the second obligation is vacuous.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- **`m0c_chacha20poly1305_encrypt` runs with a trace independent of its secret inputs.** Two calls
satisfying the entry contract with equal public inputs have equal traces, for every fuel. -/
theorem _root_.M0Crypto.Release.Aead.encrypt_constant_time : TraceSpec.AeadEncryptConstantTime := by
  intro c₁ c₂ s₁ s₂ hv₁ hb₁ he₁ hlr₁ hret₁ hv₂ hb₂ he₂ hlr₂ hret₂ hpub fuel
  have hlr := pub_lr hpub
  obtain ⟨n, hn⟩ := encrypt_correct c₁ hv₁ hb₁ s₁ he₁ hlr₁ hret₁
  obtain ⟨t, tr, ht, -, -⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  obtain ⟨hdisj, hnowrap⟩ := encrypt_frame c₁ hv₁
  have hbuffer := encrypt_hbuffer c₁ hv₁ hb₁ s₁ he₁ hlr₁ hret₁ hrun
  have hlocal : ∀ u₁ u₂, BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₂ u₂ →
      CertAt encryptEnv encryptCert
        ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u₁ u₂ →
      PositionObligations encryptEnv encryptCert
        ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u₁ u₂ := by
    intro u₁ u₂ hs₁ _ _ b off st i is hm hp hrel
    refine ⟨hbuffer u₁ (hs₁.mem_runStates hrun) u₂ b off st i is hm hp hrel, ?_⟩
    intro cond imm _ hd
    simp [encryptEnv] at hd
  have key := certificate_reachable_trace_eq (env := encryptEnv)
    (bytes := M0Crypto.Artifacts.Release.bytes)
    (entry := M0Crypto.Artifacts.Release.chacha20poly1305_encrypt) (init := entryState aeadArgWords)
    (cert := encryptCert)
    (p := ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩)
    encrypt_certOk encrypt_indicesFailure_eq_none encrypt_certAligned encrypt_slotsCheck
    (by decide) hdisj (by decide) hv₁.base4 hnowrap hlr₁ hlocal fuel
    (encrypt_entry_reachable hv₁ he₁ hv₂ he₂ hpub)
  simpa [ACall.ret, hlr] using key

end M0Crypto.Release.ConstantTime
