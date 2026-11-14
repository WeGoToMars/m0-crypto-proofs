import M0Crypto.Release.ChaCha20XorReads
import M0Crypto.Release.ChaCha20XorStack
import M0Crypto.Release.ConstantTime.HolesRun
import M0Crypto.Release.ConstantTime.ChaCha20Holes

set_option linter.unusedSimpArgs false

/-!
# Stack discipline and interrupts of `m0c_chacha20_xor`

`certificate_run_discipline` with the hole map of `ChaCha20Holes`. The load sites are the key and
nonce loads and the input loads. The whole-call access events of `ChaCha20StoreEvents` place their
reads in the key, nonce and input, which the contract separates from the stack window.
-/

namespace M0Crypto.Release.ChaCha20XorDiscipline
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.ChaCha20StoreEvents

/-- Offsets of the key, nonce and input loads. -/
def loadB (off : Nat) : Bool := decide (ChaCha20Policy.KNOff off) || inputLoadOff off

theorem chacha20_loadFailure : certLoadFailure loadB chacha20Env chacha20Cert = none := by
  decide +kernel

/-- Every run of a valid call keeps the stack discipline, and each of its states before the
return is at an instruction of the artifact. -/
theorem xor_run_discipline {c : Frame.Ctx} {s : State} (hp : ChaCha20Xor.Pre c s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline c.sp0 ChaCha20Layout.chStackBytes states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ c.ret →
        Interrupt.CodePos c.base Artifacts.Release.bytes u := by
  obtain ⟨hv, he, hlr, hret⟩ := hp
  replace hret := Region.ne hret
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  obtain ⟨n, hn⟩ := reachEvents_runUntil hc
    (fun pc y hw i hi => by
      rcases hw.1 with h | ⟨h, _⟩
      · cases h
      · exact chacha20_write_misses_code c hv h hi)
    (fun i hi => hret i (by rwa [B_len] at hi))
    (xor_reach_events_rd c hv s he hlr)
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨s', tr, hru, hpol⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hpolS : EventAccessesTo (StorePolicy c) tr := fun e he a ha k hk => (hpol e he a ha k hk).1
  have hlocal : ∀ u₁ u₂, BeforeStop (c.regs0 14 &&& ~~~1#32) s u₁ →
      BeforeStop (c.regs0 14 &&& ~~~1#32) s u₂ →
      CertAt chacha20Env chacha20Cert ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes u₁ u₂ →
      PositionObligations chacha20Env chacha20Cert
        ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes u₁ u₂ := by
    intro u₁ u₂ hb₁ _ _ b off st i is hm hp hrel
    refine ⟨ChaCha20XorConstantTime.bufferStoreOk c hv hret hrun hpolS hm hp hrel
      (hb₁.mem_runStates hrun), pubLoadOk_nil rfl _ _ _ _, ?_⟩
    intro cond imm _ hd
    simp [chacha20Env] at hd
  have hsite : ∀ u t ev, BeforeStop (c.regs0 14 &&& ~~~1#32) s u →
      u.pc ≠ c.regs0 14 &&& ~~~1#32 → step u = .ok (t, ev) →
      ∀ off, u.pc = c.base + BitVec.ofNat 32 off → loadB off = true →
      ∀ i, instrAt Artifacts.Release.bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → ChaCha20Init.KNRd c y ∨ Region c.inp c.len.toNat y := by
    intro u t ev hu hne hst off hpc hok _ _ _ y hy
    obtain ⟨t', e', hst', hmem⟩ := runStates_member_event hrun (hu.mem_runStates hrun) hne
    rw [hst] at hst'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hst')
    obtain ⟨a, ha, hk, q, hq, rfl⟩ := hy
    have hpe : ev.pc = c.base + BitVec.ofNat 32 off := by rw [step_ev_pc hst]; exact hpc
    have hr := (hpol ev hmem a ha q hq).2 hk
    simp only [loadB, Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with hkn | hin
    · have hs : ChaCha20Policy.SiteOff off := by
        unfold ChaCha20Policy.KNOff at hkn
        unfold ChaCha20Policy.SiteOff
        omega
      exact Or.inl ((hr ⟨off, hs, hpe⟩).2.1 ⟨off, hkn, hpe⟩)
    · have hb := inputLoadOff_bounds off hin
      have hs : ChaCha20Policy.SiteOff off := by unfold ChaCha20Policy.SiteOff; omega
      exact Or.inr ((hr ⟨off, hs, hpe⟩).2.2 ⟨off, hin, hpe⟩)
  have hsb := ChaCha20Layout.chStackBytes_eq
  have hR : ∀ y, (ChaCha20Init.KNRd c y ∨ Region c.inp c.len.toNat y) →
      ¬ TraceSpec.BelowEntry c.sp0 chacha20Env.win.below y := by
    intro y hy hb
    have hb' : Region c.fp ChaCha20Layout.chStackBytes y := by
      simpa [TraceSpec.BelowEntry, chacha20Env, TraceSpec.chacha20StackBytes, Frame.Ctx.fp] using hb
    rcases hy with (⟨o, ho, e⟩ | ⟨o, ho, e⟩) | hi
    · exact not_region_of_disj hv.keyF (Region.mk ho e) hb'
    · exact not_region_of_disj hv.nonceF (Region.mk ho e) hb'
    · exact not_region_of_disj hv.inF hi (by rw [← hsb]; exact hb')
  have h := certificate_run_discipline (env := chacha20Env) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.chacha20_xor) (init := entryState chacha20ArgWords)
    (cert := chacha20Cert) (p := ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩)
    chacha20_certOk chacha20_indicesFailure_eq_none chacha20_certAligned chacha20_slotsCheck
    (by decide)
    (by simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes, Frame.Ctx.fp,
        ChaCha20Layout.chStackBytes_eq, Artifacts.Release.bytes_length] using hv.codeF)
    (by simp [chacha20Env, Artifacts.Release.bytes_length]) hv.base4
    (by simpa [Artifacts.Release.bytes_length] using hv.codeF.1) hlr hlocal
    (chacha20_entry_reachable hv he hv he rfl) (by rw [he.regs]; exact he.sp)
    chacha20_loadFailure _ (ls := fun _ => none)
    (fun u t ev hu hne hst off hpc hok i hi hei y hy =>
      Or.inl (hsite u t ev hu hne hst off hpc hok i hi hei y hy)) hR chacha20_holes hrun
  simpa [chacha20Env, TraceSpec.chacha20StackBytes, Frame.Ctx.ret] using h

/-- **`m0c_chacha20_xor` keeps the stack discipline below its entry SP.** -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_stack_discipline :
    TraceSpec.ChaCha20XorStackDiscipline := by
  intro c s hp
  obtain ⟨n, hn⟩ := xor_run_discipline hp
  exact ⟨n, fun fuel hf => by
    obtain ⟨states, tr, hr, hd, -⟩ := hn fuel hf
    exact ⟨states, tr, hr, hd⟩⟩

/-- **`m0c_chacha20_xor` with interrupts.** -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_interrupted : TraceSpec.ChaCha20XorInterrupted := by
  intro K c s hp
  have hv := hp.valid
  refine Interrupt.interruptedCall_of (fun y hy => ?_) ?_ (ChaCha20Xor.xor_reads c s hp)
    (ChaCha20Xor.xor_stack c s hp) (xor_run_discipline hp)
  · rw [Artifacts.Release.bytes_length] at hy
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl hy))), fun hb => ?_⟩
    obtain ⟨o, ho, e⟩ := Region.exists hb
    refine not_region_of_disj hv.codeF hy (Region.mk (o := o) (by have := ChaCha20Layout.chStackBytes_eq; omega) ?_)
    rw [e]; rfl
  · obtain ⟨n, hn⟩ := ChaCha20Xor.xor_correct c s hp
    exact ⟨n, fun fuel hf => by
      obtain ⟨t, tr, ht, hr, -⟩ := hn fuel hf
      exact ⟨t, tr, ht, hr⟩⟩

end M0Crypto.Release.ChaCha20XorDiscipline
