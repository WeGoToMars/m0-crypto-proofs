import M0Crypto.Release.X25519Correct
import M0Crypto.Release.X25519Bridge
import M0Crypto.Release.ConstantTime.EntryReads
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.RegionStores
import M0Crypto.Release.ChaCha20XorStack

set_option linter.unusedSimpArgs false

/-!
Claims X4-X6 for `m0c_x25519` (plan `x25519-proofs.md`, phase 10): `x25519_constant_time`,
`x25519_reads`, `x25519_stack`, each from `X25519.Pre` alone.

The certificate (`ConstantTime/X25519Entry.lean`) tracks every access except the 64 byte loads
of `scalar` and `point` and the 32 byte stores to `out` (`X25519Code.loadSites`,
`storeSites`). `x25519_run` proves `X25519Ev.Ev` for every event of a call; `ev_recorded`
moves it to every non-final state of a recorded run. From there:

* stores (`store_site`): at a store site the event writes only `out`, which is separated from
  the code and the certificate's window (`bufferStoreOk_of_site`, `bufferStoreOk_of_region`);
* loads (`load_site`): at a load site the event reads only `scalar` or `point`
  (`certificate_run_reads`).

The certificate's run theorems then give equal traces for equal public inputs, the read bound
and the stack window at every non-final state; the final state has SP restored (`Result.sp`).
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.X25519Code (AtSite loadSites storeSites)
open M0Crypto.Release.X25519Ev (Ev)
open M0Crypto.Release.X25519Prologue (InpR)

/-- The event of a step is at the PC of its pre-state. -/
theorem step_ev_pc {s t : State} {e : Event} (h : step s = .ok (t, e)) : e.pc = s.pc := by
  unfold step at h; simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]
    · cases h
  · cases h

section
variable {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s) {fuel : Nat} {states : List State}
  {events : List Event} (hrun : runStates c.ret fuel s = .ok (states, events))
include hp hrun

/-- Every non-final state of a recorded run satisfies `Ev` with the event of its step. -/
theorem x25519_ev_recorded :
    ∀ x ∈ states, x.pc ≠ c.ret → ∃ t e, step x = .ok (t, e) ∧ Ev c x e := by
  have hv := hp.valid
  have hc : CodeAt s.mem c.base B := by rw [hp.entry.mem]; exact hv.code
  refine ReachS.recorded (P := Ev c) (stop := c.ret) ?_ hc (X25519Correct.x25519_run hp) hrun
  intro x e h i hi hw
  rw [B_len] at hi
  rcases h.2.1 _ hw with hy | hy
  · exact X25519MulcFacts.region_ne hv.codeS hy i hi rfl
  · exact X25519MulcFacts.region_ne hv.codeO hy i hi rfl

/-- **Store sites**: every untracked store of a certified state writes only `out`. -/
theorem x25519_store_site :
    ∀ x ∈ states, ∀ y b off st i is, b ∈ x25519Cert →
      BlockPoint x25519Env b off st (i :: is) →
      LowEq (x25519Params c) Artifacts.Release.bytes off st x y →
      BufferStoreOk x25519Env (x25519Params c) Artifacts.Release.bytes st x i := by
  intro x hx y b off st i is hm hpt hlow
  have hv := hp.valid
  have hne : x.pc ≠ c.ret := by
    have hf := (certPoint_instrAt x25519_certOk hm hpt).2
    have hpos := instr_size_pos i
    have hoff : off < Artifacts.Release.size := by
      simpa [B_len] using (show off < Artifacts.Release.bytes.length by omega)
    rw [hlow.pc]
    exact Ne.symm (x25519_ret_not_code hp off hoff)
  obtain ⟨t, e, hst, hev⟩ := x25519_ev_recorded hp hrun x hx hne
  have he := certPoint_step_event i x25519_certOk x25519_certAligned (x25519_base2 hv) hm hpt hlow hst
  refine bufferStoreOk_of_site x25519_sites hm hpt fun hoff hstm => ?_
  refine bufferStoreOk_of_region (x25519_out_code hv) (x25519_out_window hv) (by decide)
    (fun a ha => ?_) hstm
  have hat : AtSite storeSites c.base e.pc := ⟨off, hoff, by rw [he]; exact hlow.pc⟩
  have hr : Region c.out 32 a := hev.2.2.2 hat a (by rw [he]; exact ha)
  exact ⟨(a - c.out).toNat, hr, by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩

/-- The certificate's per-position obligations along a recorded run from `s`. -/
theorem x25519_hlocal (s₂ : State) :
    ∀ u₁ u₂, BeforeStop ((x25519Params c).lr0 &&& ~~~1#32) s u₁ →
      BeforeStop ((x25519Params c).lr0 &&& ~~~1#32) s₂ u₂ →
      CertAt x25519Env x25519Cert (x25519Params c) Artifacts.Release.bytes u₁ u₂ →
      PositionObligations x25519Env x25519Cert (x25519Params c) Artifacts.Release.bytes u₁ u₂ := by
  intro u₁ u₂ hb₁ _ _ b off st i is hm hpt hrel
  refine ⟨x25519_store_site hp hrun u₁ (hb₁.mem_runStates hrun) u₂ b off st i is hm hpt hrel,
    pubLoadOk_nil rfl _ _ _ _, ?_⟩
  intro cond imm _ hd
  simp [x25519Env] at hd

/-- **Load sites**: at a load site a step reads only `scalar` or `point`. -/
theorem x25519_load_site :
    ∀ u t ev, BeforeStop ((x25519Params c).lr0 &&& ~~~1#32) s u →
      u.pc ≠ (x25519Params c).lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → ∀ off, u.pc = (x25519Params c).base + BitVec.ofNat 32 off →
      loadSites.contains off = true →
      ∀ i, instrAt Artifacts.Release.bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → InpR c y := by
  intro u t ev hu hne hst off hpc hok _ _ _ y hy
  obtain ⟨t', e', hst', hev⟩ := x25519_ev_recorded hp hrun u (hu.mem_runStates hrun) hne
  rw [hst] at hst'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hst')
  exact hev.2.2.1 ⟨off, List.contains_iff_mem.mp hok, by rw [step_ev_pc hst]; exact hpc⟩ y hy

end

/-- **`m0c_x25519` runs with a trace independent of its secret inputs.** Two valid calls with
equal public inputs have equal traces, for every fuel. -/
theorem _root_.M0Crypto.Release.X25519.x25519_constant_time : TraceSpec.X25519ConstantTime := by
  intro c₁ c₂ s₁ s₂ hp₁ hp₂ hpub fuel
  have hv := hp₁.valid
  obtain ⟨n, hn⟩ := X25519.x25519_correct c₁ s₁ hp₁
  obtain ⟨t, tr, ht, -, -⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  have key := certificate_reachable_trace_eq x25519_certOk x25519_indicesFailure_eq_none
    x25519_certAligned x25519_slotsCheck x25519_win_width (x25519_code_stack_disjoint hv)
    x25519_env_size (x25519_base4 hv) (x25519_code_no_wrap hv) (x25519_lr hp₁)
    (x25519_hlocal hp₁ hrun s₂) fuel (x25519_entry_reachable hp₁ hp₂ hpub)
  have hret : c₂.ret = c₁.ret := by
    simp only [X25519.Ctx.pub, Prod.mk.injEq] at hpub
    unfold X25519.Ctx.ret; rw [hpub.2.2.1]
  rw [hret]
  exact key

/-- **Every byte `m0c_x25519` reads is in `scalar`, `point`, the artifact or its stack
window.** -/
theorem _root_.M0Crypto.Release.X25519.x25519_reads : TraceSpec.X25519Reads := by
  intro c s hp
  have hv := hp.valid
  obtain ⟨n, hn⟩ := X25519.x25519_correct c s hp
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, -, -⟩ := hn fuel hf
  refine ⟨t, tr, ht, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  have h := certificate_run_reads x25519_certOk x25519_indicesFailure_eq_none x25519_certAligned
    x25519_slotsCheck x25519_win_width (x25519_code_stack_disjoint hv) x25519_env_size
    (x25519_base4 hv) (x25519_code_no_wrap hv) (x25519_lr hp) (x25519_hlocal hp hrun s)
    (x25519_entry_reachable hp hp rfl) x25519_loadFailure (InpR c) (x25519_load_site hp hrun) hrun
  intro e he y hy
  rcases h e he y hy with (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩) | hr | hr
  · refine Or.inr (Or.inr (Or.inr ?_))
    show ((c.fp + BitVec.ofNat 32 o) - c.fp).toNat < X25519.stackBytes
    have : o < X25519.stackBytes := ho
    rw [Frame.sub_ofNat_toNat _ _ (by simp only [X25519.stackBytes] at this; omega)]; exact this
  · refine Or.inr (Or.inr (Or.inl ?_))
    have : o < Artifacts.Release.size := ho
    show ((c.base + BitVec.ofNat 32 o) - c.base).toNat < Artifacts.Release.size
    have hs : Artifacts.Release.size < 2 ^ 32 := by decide
    rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact this
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)

/-- **Every state of `m0c_x25519` keeps SP within `stackBytes` below its entry value.** -/
theorem _root_.M0Crypto.Release.X25519.x25519_stack : TraceSpec.X25519Stack := by
  intro c s hp
  have hv := hp.valid
  obtain ⟨n, hn⟩ := X25519.x25519_correct c s hp
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, hres, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, fun u hu => ?_⟩
  by_cases hpc : u.pc = c.ret
  · have hl := ChaCha20XorStack.runStates_stop_last hrun u hu hpc
    obtain ⟨last, hlast, hrun'⟩ := runStates_final hrun
    have ht' := (runUntil_success_unique ht hrun').1
    rw [hlast] at hl
    cases hl
    subst ht'
    exact restored_sp_in_stack_window hres.sp _
  · exact certificate_reachable_window x25519_certOk x25519_indicesFailure_eq_none
      x25519_certAligned x25519_slotsCheck x25519_win_width (x25519_code_stack_disjoint hv)
      x25519_env_size (x25519_base4 hv) (x25519_code_no_wrap hv) (x25519_lr hp)
      (x25519_hlocal hp hrun s) (x25519_entry_reachable hp hp rfl) (runStates_beforeStop hrun u hu) hpc

end M0Crypto.Release.ConstantTime
