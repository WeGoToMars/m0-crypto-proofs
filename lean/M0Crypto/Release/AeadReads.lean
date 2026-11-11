import M0Crypto.Release.AeadEncryptStack
import M0Crypto.Release.AeadDecryptReads
import M0Crypto.Release.AeadEncryptReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read bounds of AEAD encryption and decryption

The write-policy run (`*_reach_p`) and the read-policy run (`*_reach_r`) are combined into one
judgment, so the recorded run satisfies both at every visited state. Each event sits at a position
of the certificate (the certificate relates the recorded run to itself). A load through a
non-stack address is at a read site (`certLoadFailure`), where the read policy bounds the address;
every other read is a stack or code read bounded by the certificate's window check.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead
open M0Crypto.Release.ChaCha20XorReads

theorem encrypt_loadFailure : certLoadFailure rdSiteB encryptEnv encryptCert = none := by
  decide +kernel

theorem decrypt_loadFailure : certLoadFailure rdSiteB decryptEnv decryptCert = none := by
  decide +kernel

theorem readOk_encryptRd (c : ACall) {y : Word}
    (h : ReadOk ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ encryptEnv y) :
    TraceSpec.AeadEncryptReadRegion c y := by
  rcases h with ⟨o, ho, e⟩ | ⟨o, ho, e⟩
  · refine .stack (o := o) ?_ ?_
    · simp [encryptEnv, TraceSpec.aeadStackBytes_eq, aeadArgWords] at ho; have := TraceSpec.aeadStackBytes_eq; omega
    · simpa [encryptEnv, TraceSpec.aeadStackBytes] using e
  · exact .code (by simpa [encryptEnv, Artifacts.Release.bytes_length] using ho) e

theorem readOk_decryptRd (c : ACall) {y : Word}
    (h : ReadOk ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ decryptEnv y) :
    TraceSpec.AeadDecryptReadRegion c y := by
  rcases h with ⟨o, ho, e⟩ | ⟨o, ho, e⟩
  · refine .enc (.stack (o := o) ?_ ?_)
    · simp [decryptEnv, TraceSpec.aeadStackBytes_eq, aeadArgWords] at ho; have := TraceSpec.aeadStackBytes_eq; omega
    · simpa [decryptEnv, TraceSpec.aeadStackBytes] using e
  · exact .enc (.code (by simpa [decryptEnv, Artifacts.Release.bytes_length] using ho) e)

/-- **The read bound of a recorded run.** At every visited state the certificate relates the state
to itself. A load through a non-stack address is at a read site (`certLoadFailure`), where the read
policy bounds the address; every other read is a stack or code read bounded by the certificate's
window check. -/
theorem reads_of_recorded {env : Env} {cert : Cert} {entry : Nat} {init : AbsState}
    (c : ACall) (hv : AValid c) {Rd : Word → Prop}
    (hok : certOk env Artifacts.Release.bytes entry init cert = true)
    (hal : certAligned cert = true)
    (hlf : certLoadFailure rdSiteB env cert = none)
    (hsize : env.size = Artifacts.Release.bytes.length)
    (hbridge : ∀ y, ReadOk ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ env y → Rd y)
    {s : State} {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events))
    (hcert : ∀ u ∈ states, u.pc ≠ c.regs0 14 &&& ~~~1#32 →
      CertAt env cert ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes u u)
    (hrd : ∀ x ∈ states, x.pc ≠ c.regs0 14 &&& ~~~1#32 →
      ∃ t e, step x = .ok (t, e) ∧ RdP c.base Rd x e) :
    ∀ e ∈ events, ∀ y, Reads e.accesses y → Rd y := by
  have hnowrap : c.base.toNat + Artifacts.Release.bytes.length ≤ 2 ^ 32 := by
    simpa [Artifacts.Release.bytes_length] using hv.codeS.1
  have hq := runStates_events_invariant (fun u => BeforeStop (c.regs0 14 &&& ~~~1#32) s u)
    (fun ev => ∀ y, Reads ev.accesses y → Rd y)
    (c.regs0 14 &&& ~~~1#32) ?_ fuel BeforeStop.initial hrun
  · exact hq
  · intro u t ev hu hne hst
    refine ⟨BeforeStop.next hu hne hst, ?_⟩
    have hmem := hu.mem_runStates hrun
    obtain ⟨t', e', hst', hrd'⟩ := hrd u hmem hne
    rw [hst] at hst'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hst')
    obtain ⟨b, off, st, code, hm, hp, hnil, hlow⟩ := hcert u hmem hne
    cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      have hev := certPoint_step_event i hok hal
        (by show c.base.toNat % 2 = 0; have := hv.base4; omega) hm hp hlow hst
      subst hev
      intro y hy
      obtain ⟨a, ha, hk, q, hq, rfl⟩ := hy
      obtain ⟨out, hx⟩ := certPoint_xfer hok hm hp
      by_cases hl : loadSite st i = true
      · have hoff := certPoint_loadSite hlf hm hp hl
        have hsite : SiteRd c.base u.pc := ⟨off, hoff, by simpa using hlow.pc⟩
        exact hrd' hsite _ ⟨a, ha, hk, q, hq, rfl⟩
      · have hl' : loadSite st i = false := by simpa using hl
        exact hbridge _ (xfer_reads i hlow hx hsize hv.base4 hnowrap hl' a ha hk q hq)

theorem encrypt_rd_recorded (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c encOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, x.pc ≠ c.regs0 14 &&& ~~~1#32 →
      ∃ t e, step x = .ok (t, e) ∧ RdP c.base (TraceSpec.AeadEncryptReadRegion c) x e := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have h1 : ReachS c.base (PolE c c.tag (EncAllPc c.base) (AWr c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ EncryptResult c t) :=
    (encrypt_reach_p (Pc := EncAllPc c.base) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.toRetPost.pc, h⟩)
  have h2 : ReachS c.base (RdP c.base (TraceSpec.AeadEncryptReadRegion c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ EncryptResult c t) :=
    (encrypt_reach_r (Rd := TraceSpec.AeadEncryptReadRegion c) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.toRetPost.pc, h⟩)
  have h := ReachS.and (fun i hi => by rw [B_len] at hi; exact hret i hi) h1 h2
  have := ReachS.recorded (stop := c.regs0 14 &&& ~~~1#32) ?_ hc h hrun
  · intro x hx hne
    obtain ⟨t, e, hs, hp⟩ := this x hx hne
    exact ⟨t, e, hs, hp.2⟩
  · intro x e hh i hi hw
    rw [B_len] at hi
    have h := hh.1
    rcases h.1.1.2 _ hw with hs | ho | ht
    · exact hv.code_not_swr hi hs
    · exact not_out hb.codeO hi ho
    · exact not_tag hb.codeT hi ht

/-- **Every read of AEAD encryption is inside its permitted regions.** -/
theorem _root_.M0Crypto.Release.Aead.encrypt_reads : TraceSpec.AeadEncryptReads := by
  intro c s hv hb he hlr hret
  obtain ⟨n, hcorrect⟩ := encrypt_correct c hv hb s he hlr hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  refine ⟨t, tr, ht, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  exact reads_of_recorded c hv encrypt_certOk encrypt_certAligned encrypt_loadFailure
    (by simp [encryptEnv, Artifacts.Release.bytes_length]) (fun _ => readOk_encryptRd c) hrun
    (encrypt_certAt_states c hv hb s he hlr hret hrun)
    (encrypt_rd_recorded c hv hb s he hlr hret hrun)

theorem decrypt_rd_recorded (c : ACall) (hv : AValid c) (hb : ABuf c) (s : State)
    (he : AEntry c decOff s) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < M0Crypto.Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates (c.regs0 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ x ∈ states, x.pc ≠ c.regs0 14 &&& ~~~1#32 →
      ∃ t e, step x = .ok (t, e) ∧ RdP c.base (TraceSpec.AeadDecryptReadRegion c) x e := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have h1 : ReachS c.base (PolW c (DecAllPc c.base) (DAllowed c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ DecryptResult c t) :=
    (decrypt_reach_p (Pc := DecAllPc c.base) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.abi.pc, h⟩)
  have h2 : ReachS c.base (RdP c.base (TraceSpec.AeadDecryptReadRegion c)) s
      (fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ DecryptResult c t) :=
    (decrypt_reach_r (Rd := TraceSpec.AeadDecryptReadRegion c) c hv hb s he hlr (fun _ h => h)).mono
      (fun _ _ h => h) (fun t h => ⟨h.abi.pc, h⟩)
  have h := ReachS.and (fun i hi => by rw [B_len] at hi; exact hret i hi) h1 h2
  have := ReachS.recorded (stop := c.regs0 14 &&& ~~~1#32) ?_ hc h hrun
  · intro x hx hne
    obtain ⟨t, e, hs, hp⟩ := this x hx hne
    exact ⟨t, e, hs, hp.2⟩
  · intro x e hh i hi hw
    rw [B_len] at hi
    have h := hh.1
    rcases h.1.2 _ hw with hs | ⟨_, ho⟩
    · exact hv.code_not_swr hi hs
    · exact not_out hb.codeO hi ho

/-- **Every read of AEAD decryption is inside its permitted regions.** -/
theorem _root_.M0Crypto.Release.Aead.decrypt_reads : TraceSpec.AeadDecryptReads := by
  intro c s hv hb he hlr hret
  obtain ⟨n, hcorrect⟩ := decrypt_correct c hv hb s he hlr hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  refine ⟨t, tr, ht, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  exact reads_of_recorded c hv decrypt_certOk decrypt_certAligned decrypt_loadFailure
    (by simp [decryptEnv, Artifacts.Release.bytes_length]) (fun _ => readOk_decryptRd c) hrun
    (decrypt_certAt_states c hv hb s he hlr hret hrun)
    (decrypt_rd_recorded c hv hb s he hlr hret hrun)

end M0Crypto.Release.ConstantTime
