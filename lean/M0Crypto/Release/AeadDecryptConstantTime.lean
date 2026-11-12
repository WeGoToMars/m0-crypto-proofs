import M0Crypto.Release.AeadDecryptStack
import M0Crypto.Release.ConstantTime.AfterBranchCert
import M0Crypto.Release.ConstantTime.DecryptVerdict
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates

set_option linter.unusedSimpArgs false
-- the kernel `decide` on the stack-window width needs a deeper recursion limit
set_option maxRecDepth 100000

/-!
# Constant-time trace of AEAD decryption

Same shape as `M0Crypto.Release.Aead.encrypt_constant_time`: `certificate_reachable_trace_eq` with the decrypt
certificate. The store-separation obligation is `decrypt_hbuffer` for the first run. The
decrypt environment declassifies one branch, the rejection branch `decRejectBrAt`. There the
obligation is `decrypt_declass_agrees`, which needs the zero flag of each run to equal that
run's authentication decision. `decrypt_branch_flag` supplies it for every recorded state at
that PC (`decrypt_recorded_branch_flag_of_cert`), and equal verdicts make the two flags agree.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- At each recorded state at the rejection branch, Z is the functional authentication decision. -/
theorem decrypt_branch_flag (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ v ∈ states, v.pc = c.base + BitVec.ofNat 32 decRejectBrAt →
      v.z = decide (c.expected = c.tagB) := by
  intro v hmem hpc
  obtain ⟨hdisj, hnowrap⟩ := decrypt_frame c hv
  have hbr : decRejectBrAt < M0Crypto.Artifacts.Release.size := by decide
  exact decrypt_recorded_branch_flag_of_cert c hv hb s he
    ⟨c.base, c.sp0, c.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩ rfl
    (fun i hi => hret i (by rwa [B_len] at hi)) hrun
    (fun u hu hpc' => decrypt_certAt_states c hv hb s he hlr hret hrun u hu
      (by rw [hpc']; exact Ne.symm (hret decRejectBrAt hbr)))
    (fun x hx b off st i is hm =>
      decrypt_hbuffer c hv hb s he hlr hret hrun x hx x b off st i is (List.mem_filter.mp hm).1)
    hdisj hv.base4 hnowrap hlr hmem hpc

/-- **`m0c_chacha20poly1305_decrypt` runs with a trace independent of its secret inputs, given the same
authentication verdict.** Two calls satisfying the entry contract with equal public inputs and
equal verdicts have equal traces, for every fuel. -/
theorem _root_.M0Crypto.Release.Aead.decrypt_constant_time : TraceSpec.AeadDecryptConstantTime := by
  intro c₁ c₂ s₁ s₂ ⟨hv₁, hb₁, he₁, hlr₁, hret₁⟩ ⟨hv₂, hb₂, he₂, hlr₂, hret₂⟩ hpub hver fuel
  replace hret₁ := Region.ne hret₁
  replace hret₂ := Region.ne hret₂
  have hlr := pub_lr hpub
  have hbase := pub_base hpub
  obtain ⟨n₁, hn₁⟩ := decrypt_correct c₁ s₁ ⟨hv₁, hb₁, he₁, hlr₁, Region.not hret₁⟩
  obtain ⟨t₁, tr₁, ht₁, -, -⟩ := hn₁ n₁ (Nat.le_refl n₁)
  obtain ⟨states₁, hrun₁, -, -⟩ := runStates_of_runUntil ht₁
  obtain ⟨n₂, hn₂⟩ := decrypt_correct c₂ s₂ ⟨hv₂, hb₂, he₂, hlr₂, Region.not hret₂⟩
  obtain ⟨t₂, tr₂, ht₂, -, -⟩ := hn₂ n₂ (Nat.le_refl n₂)
  obtain ⟨states₂, hrun₂, -, -⟩ := runStates_of_runUntil ht₂
  obtain ⟨hdisj, hnowrap⟩ := decrypt_frame c₁ hv₁
  have hbuffer := decrypt_hbuffer c₁ hv₁ hb₁ s₁ he₁ hlr₁ hret₁ hrun₁
  have hflag₁ := decrypt_branch_flag c₁ hv₁ hb₁ s₁ he₁ hlr₁ hret₁ hrun₁
  have hflag₂ := decrypt_branch_flag c₂ hv₂ hb₂ s₂ he₂ hlr₂ hret₂ hrun₂
  have hlocal : ∀ u₁ u₂, BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (c₁.regs0 14 &&& ~~~1#32) s₂ u₂ →
      CertAt decryptEnv decryptCert
        ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u₁ u₂ →
      PositionObligations decryptEnv decryptCert
        ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩
        M0Crypto.Artifacts.Release.bytes u₁ u₂ := by
    intro u₁ u₂ hs₁ hs₂ _ b off st i is hm hp hrel
    refine ⟨hbuffer u₁ (hs₁.mem_runStates hrun₁) u₂ b off st i is hm hp hrel, ?_⟩
    intro cond imm hi hd
    have hoff : off = decRejectBrAt := by simpa [decryptEnv] using hd.symm
    subst hoff
    have hs₂' : BeforeStop (c₂.regs0 14 &&& ~~~1#32) s₂ u₂ := hlr ▸ hs₂
    exact decrypt_declass_agrees c₁ c₂ u₁ u₂ cond imm hm (hi ▸ hp) hd
      (hflag₁ u₁ (hs₁.mem_runStates hrun₁) hrel.pc)
      (hflag₂ u₂ (hs₂'.mem_runStates hrun₂) (by rw [hrel.pc_eq, hrel.pc, hbase]))
      hver
  have key := certificate_reachable_trace_eq (env := decryptEnv)
    (bytes := M0Crypto.Artifacts.Release.bytes)
    (entry := M0Crypto.Artifacts.Release.chacha20poly1305_decrypt)
    (init := entryState aeadArgWords) (cert := decryptCert)
    (p := ⟨c₁.base, c₁.sp0, c₁.regs0 14, M0Crypto.Artifacts.Release.bytes.length⟩)
    decrypt_certOk decrypt_indicesFailure_eq_none decrypt_certAligned decrypt_slotsCheck
    (by decide) hdisj (by decide) hv₁.base4 hnowrap hlr₁ hlocal fuel
    (decrypt_entry_reachable hv₁ he₁ hv₂ he₂ hpub)
  simpa [ACall.ret, hlr] using key

end M0Crypto.Release.ConstantTime
