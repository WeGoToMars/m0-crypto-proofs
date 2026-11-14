import M0Crypto.Release.AeadReads
import M0Crypto.Release.ConstantTime.HolesRun
import M0Crypto.Release.ConstantTime.AeadEncryptHoles
import M0Crypto.Release.ConstantTime.AeadDecryptHoles

set_option linter.unusedSimpArgs false

/-!
# Stack discipline and interrupts of AEAD encryption and decryption

`certificate_run_discipline_of` with the hole maps of `AeadEncryptHoles` and `AeadDecryptHoles`.
The load sites are the read sites `rdSiteB`. Under the read policy, a load at a read site reads a
caller buffer or the stack range `Aead.siteRange`, which the hole-map check proves written: the
ChaCha input copy inside the ChaCha code, the input copy and the Poly1305 block elsewhere.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- The caller buffers that the AEAD functions read at read sites. -/
def SiteBuf (c : ACall) (y : Word) : Prop :=
  Region c.inp c.len.toNat y ∨ Region c.aad c.alen.toNat y ∨ Region c.key 32 y ∨
  Region c.nonce 12 y ∨ Region c.out c.len.toNat y ∨ Region c.tag 16 y

/-- The caller buffers and the first `n` stack bytes from the ChaCha input copy. -/
def SiteBytes (c : ACall) (n : Nat) (y : Word) : Prop :=
  SiteBuf c y ∨
    Region (c.sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes + BitVec.ofNat 32 inpStackOff) n y

theorem siteBytes_of {c : ACall} {n : Nat} {y : Word} (h : AeadSiteRegion c n y) :
    SiteBytes c n y := by
  rcases h with h | h | h | h | h
  · exact .inl (.inl h)
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr (.inl h)))
  · exact .inl (.inr (.inr (.inr (.inl h))))
  · exact .inr h

theorem siteBuf_out {c : ACall} {y : Word} (h : Region c.out c.len.toNat y) : SiteBytes c siteLen y :=
  .inl (.inr (.inr (.inr (.inr (.inl h)))))

theorem siteBuf_tag {c : ACall} {y : Word} (h : Region c.tag 16 y) : SiteBytes c siteLen y :=
  .inl (.inr (.inr (.inr (.inr (.inr h)))))

/-- The caller buffers lie outside the stack window. -/
theorem siteBuf_not_below (c : ACall) (hv : AValid c) (hb : ABuf c) (y : Word) (h : SiteBuf c y) :
    ¬ TraceSpec.BelowEntry c.sp0 TraceSpec.aeadStackBytes y := by
  intro hw
  have e : BitVec.ofNat 32 TraceSpec.aeadStackBytes = 320#32 := by
    rw [TraceSpec.aeadStackBytes_eq]
  have hw' : Region (c.sp0 - 320#32) 320 y := by
    simpa only [TraceSpec.BelowEntry, e, TraceSpec.aeadStackBytes_eq] using hw
  have hw336 : Region (c.sp0 - 320#32) 336 y := by unfold Region at hw' ⊢; omega
  rcases h with h | h | h | h | h | h
  · exact not_region_of_disj hb.inS h hw'
  · exact not_region_of_disj hb.aadS h hw'
  · exact not_region_of_disj hv.keyS h hw'
  · exact not_region_of_disj hv.nonceS h hw'
  · exact not_region_of_disj hb.outS h hw336
  · exact not_region_of_disj hb.tagS h hw336

/-- A read of `SiteBytes c n` is a caller-buffer read or lies in the checked stack range. -/
theorem site_cases {c : ACall} {n off : Nat} {y : Word}
    (hr : siteRange off = some ((inpStackOff : Int) - TraceSpec.aeadStackBytes,
      ((inpStackOff + n : Nat) : Int) - TraceSpec.aeadStackBytes))
    (h : SiteBytes c n y) : SiteBuf c y ∨ ∃ a b, siteRange off = some (a, b) ∧
      ∃ q : Int, a ≤ q ∧ q < b ∧ y = c.sp0 + BitVec.ofInt 32 q := by
  rcases h with h | h
  · exact .inl h
  · obtain ⟨o, ho, rfl⟩ := Region.exists h
    refine .inr ⟨_, _, hr, ((inpStackOff + o : Nat) : Int) - TraceSpec.aeadStackBytes,
      by omega, by omega, ?_⟩
    rw [stack_offset_rebase c.sp0 TraceSpec.aeadStackBytes _ (by omega)]
    have : (((inpStackOff + o : Nat) : Int) - TraceSpec.aeadStackBytes +
        (TraceSpec.aeadStackBytes : Int)).toNat = inpStackOff + o := by omega
    rw [this, ofNat_add_assoc]

/-- The read policy at a read site of the recorded run places its reads in `SiteBuf` or in the
checked stack range of the site. -/
theorem rdP_site {c : ACall} {u : State} {ev : Event} {off : Nat} {y : Word}
    (hrd : RdP c.base (SiteBytes c siteLen) (SiteBytes c copyLen) u ev)
    (hpe : ev.pc = c.base + BitVec.ofNat 32 off) (hok : rdSiteB off = true)
    (hy : Reads ev.accesses y) : SiteBuf c y ∨ ∃ a b, siteRange off = some (a, b) ∧
      ∃ q : Int, a ≤ q ∧ q < b ∧ y = c.sp0 + BitVec.ofInt 32 q := by
  obtain ⟨h1, h2⟩ := hrd ⟨off, hok, hpe⟩ y hy
  by_cases hc : off < ChaCha20Policy.chaEnd
  · exact site_cases (by simp only [siteRange, hc, ↓reduceIte]) (h2 ⟨off, Nat.zero_le _, hc, hpe⟩)
  · exact site_cases (by simp only [siteRange, hc, ↓reduceIte]) h1

/-- Every run of a valid encryption keeps the stack discipline, and each of its states before
the return is at an instruction of the artifact. -/
theorem encrypt_run_discipline {c : ACall} {s : State} (hp : APre c encOff s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 TraceSpec.aeadStackBytes states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ c.ret →
        Interrupt.CodePos c.base Artifacts.Release.bytes u := by
  obtain ⟨hv, hb, he, hlr, hret⟩ := hp
  replace hret := Region.ne hret
  obtain ⟨n, hcorrect⟩ := encrypt_returns c s ⟨hv, hb, he, hlr, Region.not hret⟩
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, ?_⟩
  have hrd := encrypt_rd_recorded (Rd := SiteBytes c siteLen) (Kn := SiteBytes c copyLen)
    c hv hb s he hlr hret (fun _ h => h.elim siteBytes_of siteBuf_out) (fun _ h => siteBytes_of h)
    hrun
  have hsite : ∀ u t ev, BeforeStop (c.regs0 14 &&& ~~~1#32) s u →
      u.pc ≠ c.regs0 14 &&& ~~~1#32 → step u = .ok (t, ev) →
      ∀ off, u.pc = c.base + BitVec.ofNat 32 off → rdSiteB off = true →
      ∀ i, instrAt Artifacts.Release.bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → SiteBuf c y ∨ ∃ a b, siteRange off = some (a, b) ∧
        ∃ q : Int, a ≤ q ∧ q < b ∧ y = c.sp0 + BitVec.ofInt 32 q := by
    intro u t ev hu hne hst off hpc hok _ _ _ y hy
    obtain ⟨t', e', hst', hp'⟩ := hrd u (hu.mem_runStates hrun) hne
    rw [hst] at hst'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hst')
    exact rdP_site hp' (by rw [step_ev_pc hst]; exact hpc) hok hy
  have hpos : ∀ u ∈ states, u.pc ≠ c.regs0 14 &&& ~~~1#32 → ∃ b off st i is, b ∈ encryptCert ∧
      BlockPoint encryptEnv b off st (i :: is) ∧
      LowEq ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes
        off st u u ∧
      BufferStoreOk encryptEnv ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes st u i := by
    intro u hu hne
    obtain ⟨b, off, st, code, hm, hp, hnil, hlow⟩ := encrypt_certAt_states c hv hb s he hlr hret hrun u hu hne
    cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      exact ⟨b, off, st, i, is, hm, hp, hlow,
        encrypt_hbuffer c hv hb s he hlr hret hrun u hu u b off st i is hm hp hlow⟩
  have h := certificate_run_discipline_of (env := encryptEnv) (cert := encryptCert)
    (p := ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩)
    encrypt_certOk encrypt_indicesFailure_eq_none encrypt_certAligned (by decide)
    (encrypt_frame c hv).1 (by simp [encryptEnv, Artifacts.Release.bytes_length]) hv.base4
    (encrypt_frame c hv).2 (by rw [he.regs]; exact he.sp) encrypt_loadFailure (SiteBuf c) hsite
    (fun y h => by simpa [encryptEnv] using siteBuf_not_below c hv hb y h) encrypt_holes hrun hpos
  simpa [encryptEnv, ACall.ret] using h

/-- Every run of a valid decryption keeps the stack discipline, and each of its states before
the return is at an instruction of the artifact. -/
theorem decrypt_run_discipline {c : ACall} {s : State} (hp : APre c decOff s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 TraceSpec.aeadStackBytes states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ c.ret →
        Interrupt.CodePos c.base Artifacts.Release.bytes u := by
  obtain ⟨hv, hb, he, hlr, hret⟩ := hp
  replace hret := Region.ne hret
  obtain ⟨n, hcorrect⟩ := decrypt_returns c s ⟨hv, hb, he, hlr, Region.not hret⟩
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hcorrect fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, ?_⟩
  have hrd := decrypt_rd_recorded (Rd := SiteBytes c siteLen) (Kn := SiteBytes c copyLen)
    c hv hb s he hlr hret (fun _ h => h.elim siteBytes_of siteBuf_tag) (fun _ h => siteBytes_of h)
    hrun
  have hsite : ∀ u t ev, BeforeStop (c.regs0 14 &&& ~~~1#32) s u →
      u.pc ≠ c.regs0 14 &&& ~~~1#32 → step u = .ok (t, ev) →
      ∀ off, u.pc = c.base + BitVec.ofNat 32 off → rdSiteB off = true →
      ∀ i, instrAt Artifacts.Release.bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → SiteBuf c y ∨ ∃ a b, siteRange off = some (a, b) ∧
        ∃ q : Int, a ≤ q ∧ q < b ∧ y = c.sp0 + BitVec.ofInt 32 q := by
    intro u t ev hu hne hst off hpc hok _ _ _ y hy
    obtain ⟨t', e', hst', hp'⟩ := hrd u (hu.mem_runStates hrun) hne
    rw [hst] at hst'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hst')
    exact rdP_site hp' (by rw [step_ev_pc hst]; exact hpc) hok hy
  have hpos : ∀ u ∈ states, u.pc ≠ c.regs0 14 &&& ~~~1#32 → ∃ b off st i is, b ∈ decryptCert ∧
      BlockPoint decryptEnv b off st (i :: is) ∧
      LowEq ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes
        off st u u ∧
      BufferStoreOk decryptEnv ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes st u i := by
    intro u hu hne
    obtain ⟨b, off, st, code, hm, hp, hnil, hlow⟩ := decrypt_certAt_states c hv hb s he hlr hret hrun u hu hne
    cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      exact ⟨b, off, st, i, is, hm, hp, hlow,
        decrypt_hbuffer c hv hb s he hlr hret hrun u hu u b off st i is hm hp hlow⟩
  have h := certificate_run_discipline_of (env := decryptEnv) (cert := decryptCert)
    (p := ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩)
    decrypt_certOk decrypt_indicesFailure_eq_none decrypt_certAligned (by decide)
    (decrypt_frame c hv).1 (by simp [decryptEnv, Artifacts.Release.bytes_length]) hv.base4
    (decrypt_frame c hv).2 (by rw [he.regs]; exact he.sp) decrypt_loadFailure (SiteBuf c) hsite
    (fun y h => by simpa [decryptEnv] using siteBuf_not_below c hv hb y h) decrypt_holes hrun hpos
  simpa [decryptEnv, ACall.ret] using h

/-- The code lies in the read region and outside the stack window. -/
theorem aead_code (c : ACall) (hv : AValid c) {y : Word}
    (hy : Region c.base Artifacts.Release.bytes.length y) :
    AeadCommonReadRegion c y ∧ ¬ TraceSpec.BelowEntry c.sp0 TraceSpec.aeadStackBytes y := by
  rw [Artifacts.Release.bytes_length] at hy
  obtain ⟨o, ho, e⟩ := Region.exists hy
  refine ⟨.code ho e, fun hw => ?_⟩
  have e' : BitVec.ofNat 32 TraceSpec.aeadStackBytes = 320#32 := by
    rw [TraceSpec.aeadStackBytes_eq]
  have hw' : Region (c.sp0 - 320#32) 336 y := by
    have := hw
    simp only [TraceSpec.BelowEntry, e', TraceSpec.aeadStackBytes_eq] at this
    unfold Region at this ⊢; omega
  exact not_region_of_disj hv.codeS hy hw'

/-- **`m0c_chacha20poly1305_encrypt` keeps the stack discipline below its entry SP.** -/
theorem _root_.M0Crypto.Release.Aead.encrypt_stack_discipline :
    TraceSpec.AeadEncryptStackDiscipline := by
  intro c s hp
  obtain ⟨n, hn⟩ := encrypt_run_discipline hp
  exact ⟨n, fun fuel hf => by
    obtain ⟨states, tr, hr, hd, -⟩ := hn fuel hf
    exact ⟨states, tr, hr, hd⟩⟩

/-- **`m0c_chacha20poly1305_encrypt` with interrupts.** -/
theorem _root_.M0Crypto.Release.Aead.encrypt_interrupted : TraceSpec.AeadEncryptInterrupted := by
  intro K c s hp
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (Aead.encrypt_reads c s hp)
    (Aead.encrypt_stack c s hp) (encrypt_run_discipline hp)
  · obtain ⟨h1, h2⟩ := aead_code c hp.1 hy
    exact ⟨TraceSpec.AeadEncryptReadRegion.common h1, h2⟩
  · obtain ⟨n, hn⟩ := encrypt_returns c s hp
    exact ⟨n, fun fuel hf => by
      obtain ⟨t, tr, ht, hr, -⟩ := hn fuel hf
      exact ⟨t, tr, ht, hr⟩⟩

/-- **`m0c_chacha20poly1305_decrypt` keeps the stack discipline below its entry SP.** -/
theorem _root_.M0Crypto.Release.Aead.decrypt_stack_discipline :
    TraceSpec.AeadDecryptStackDiscipline := by
  intro c s hp
  obtain ⟨n, hn⟩ := decrypt_run_discipline hp
  exact ⟨n, fun fuel hf => by
    obtain ⟨states, tr, hr, hd, -⟩ := hn fuel hf
    exact ⟨states, tr, hr, hd⟩⟩

/-- **`m0c_chacha20poly1305_decrypt` with interrupts.** -/
theorem _root_.M0Crypto.Release.Aead.decrypt_interrupted : TraceSpec.AeadDecryptInterrupted := by
  intro K c s hp
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (Aead.decrypt_reads c s hp)
    (Aead.decrypt_stack c s hp) (decrypt_run_discipline hp)
  · obtain ⟨h1, h2⟩ := aead_code c hp.1 hy
    exact ⟨TraceSpec.AeadDecryptReadRegion.common h1, h2⟩
  · obtain ⟨n, hn⟩ := decrypt_returns c s hp
    exact ⟨n, fun fuel hf => by
      obtain ⟨t, tr, ht, hr, -⟩ := hn fuel hf
      exact ⟨t, tr, ht, hr⟩⟩

end M0Crypto.Release.ConstantTime
