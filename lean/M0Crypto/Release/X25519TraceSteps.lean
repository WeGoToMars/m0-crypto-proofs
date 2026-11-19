import M0Crypto.Release.X25519Correct
import M0Crypto.Release.X25519Bridge
import M0Crypto.Release.X25519SafegcdCall
import M0Crypto.Release.ConstantTime.EntryReads
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.RegionStores

set_option linter.unusedSimpArgs false

/-!
The trace, read and stack claims for `m0c_x25519`: `x25519_constant_time`,
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
open M0Crypto.Release.X25519Layout (SAVED LFRAME E)
open M0Crypto.Release.X25519SafegcdCode (borrowed)

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
  · exact Field25519Facts.region_ne hv.codeS hy i hi rfl
  · exact Field25519Facts.region_ne hv.codeO hy i hi rfl

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


abbrev X25519RunRel (c : X25519.Ctx) :=
  FragmentRel c.ret (X25519SummaryStep c)
    (RunRel x25519Env x25519Cert (x25519Params c) Artifacts.Release.bytes c.ret)

theorem x25519_plain_position {c : X25519.Ctx} {u : State}
    (hpc : u.pc ≠ c.base + BitVec.ofNat 32 x25519CallSite)
    {off : Nat} (hOff : u.pc = c.base + BitVec.ofNat 32 off) :
    x25519Env.frameCallAt off = none := by
  have hn : x25519CallSite ≠ off := by
    intro he
    apply hpc
    rwa [he]
  simp [Env.frameCallAt,x25519Env,x25519InversionCall,hn]

theorem x25519_plain_step {c : X25519.Ctx} {s₁ s₂ u v : State} (hp : X25519.Pre c s₁)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates c.ret fuel s₁ = .ok (states,events))
    (hU : BeforeStop c.ret s₁ u) (hV : BeforeStop c.ret s₂ v)
    (hcert : CertAt x25519Env x25519Cert (x25519Params c) B u v)
    (hpc : u.pc ≠ c.base + BitVec.ofNat 32 x25519CallSite) :
    PairedStep (RunRel x25519Env x25519Cert (x25519Params c) B c.ret) u v := by
  have hv := hp.valid
  exact certAt_run_paired x25519_certOk x25519_indicesFailure_eq_none x25519_certAligned
    x25519_slotsCheck x25519_win_width (x25519_code_stack_disjoint hv) x25519_env_size
    (x25519_base4 hv) (x25519_code_no_wrap hv) (x25519_lr hp) hcert
    (x25519_hlocal hp hrun s₂ u v hU hV hcert) (fun _ => x25519_plain_position hpc)

theorem x25519_pair_step {c : X25519.Ctx} {s₁ s₂ u v : State} (hp : X25519.Pre c s₁)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates c.ret fuel s₁ = .ok (states,events))
    (hU : BeforeStop c.ret s₁ u) (hV : BeforeStop c.ret s₂ v)
    (h : X25519RunRel c u v) (hne : u.pc ≠ c.ret) :
    PairedStep (X25519RunRel c) u v := by
  rcases h with (hcert | ⟨hret,_⟩) | ⟨tr,a,b,htr,ha,hb,hnext⟩
  · by_cases hpc : u.pc = c.base + BitVec.ofNat 32 x25519CallSite
    · obtain ⟨t₁,t₂,h₁,h₂,hAfter,_,_,_⟩ := x25519_enter_summary hp hcert hpc
      exact FragmentRel.step (show x25519CallTrace _ _ ≠ [] from List.cons_ne_nil _ _) h₁ h₂ (.inl hAfter)
    · exact (x25519_plain_step hp hrun hU hV hcert hpc).mono (fun _ _ h => .inl h)
  · exact absurd hret hne
  · exact FragmentRel.step htr ha hb hnext

/-- Every state of a recorded run has a related partner, at a certificate
point or in the verified call. -/
theorem x25519_summary_reachable {c : X25519.Ctx} {s u : State} (hp : X25519.Pre c s)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : runStates c.ret fuel s = .ok (states,events)) (hu : BeforeStop c.ret s u) :
    ∃ v, X25519RunRel c u v ∧ BeforeStop c.ret s v := by
  induction hu with
  | initial => exact ⟨s,.inl (.inl (x25519_entry_reachable hp hp rfl)),.initial⟩
  | @next x t e hReach hStop hStep ih =>
    obtain ⟨v,h,hV⟩ := ih
    have hs := x25519_pair_step hp hrun hReach hV h hStop
    have hpc := FragmentRel.pc_eq (fun _ _ hr => hr.pc_eq) h
    unfold PairedStep at hs
    rw [hStep] at hs
    cases hv : step v with
    | error f => simp [hv] at hs
    | ok p =>
      obtain ⟨v',ev⟩ := p
      simp only [hv] at hs
      exact ⟨v',hs.2,.next hV (hpc ▸ hStop) hv⟩

/-- **`m0c_x25519` runs with a trace independent of its secret inputs.** Two valid calls with
equal public inputs have equal traces, for every fuel. -/
theorem _root_.M0Crypto.Release.X25519.x25519_constant_time : TraceSpec.X25519ConstantTime := by
  intro c₁ c₂ s₁ s₂ hp₁ hp₂ hpub fuel
  obtain ⟨n, hn⟩ := X25519.x25519_correct c₁ s₁ hp₁
  obtain ⟨t, tr, ht, -, -⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  let R : State → State → Prop := fun u v =>
    X25519RunRel c₁ u v ∧ BeforeStop c₁.ret s₁ u ∧ BeforeStop c₁.ret s₂ v
  have hret : c₂.ret = c₁.ret := by
    simp only [X25519.Ctx.pub, Prod.mk.injEq] at hpub
    unfold X25519.Ctx.ret
    rw [hpub.2.2.1]
  rw [hret]
  apply runUntil_trace_eq R c₁.ret
  · intro u v h
    exact FragmentRel.pc_eq (fun _ _ h => h.pc_eq) h.1
  · intro u v h hn
    exact (x25519_pair_step hp₁ hrun h.2.1 h.2.2 h.1 hn).with_reach
      (FragmentRel.pc_eq (fun _ _ h => h.pc_eq) h.1) hn h.2.1 h.2.2
  · exact ⟨.inl (.inl (x25519_entry_reachable hp₁ hp₂ hpub)),.initial,.initial⟩

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
  apply runStates_events_invariant (BeforeStop c.ret s)
    (fun e => ∀ y, Reads e.accesses y → TraceSpec.X25519ReadRegion c y) c.ret ?_ fuel .initial hrun
  intro u v e hU hne hStep
  refine ⟨.next hU hne hStep,?_⟩
  obtain ⟨w,h,_⟩ := x25519_summary_reachable hp hrun hU
  rcases h with (hcert | ⟨hret,_⟩) | ⟨tr,j,k,ht,hj,hk,_⟩
  · obtain ⟨b,off,st,is,hm,hpt,hni,hlow⟩ := hcert
    cases is with
    | nil => exact absurd rfl hni
    | cons i is =>
      have hev := certPoint_step_event i x25519_certOk x25519_certAligned (x25519_base2 hv)
        hm hpt hlow hStep
      obtain ⟨out,hx⟩ := certPoint_xfer x25519_certOk hm hpt
      by_cases hLoad : loadSite st i = true
      · have hoff := certPoint_loadSite x25519_loadFailure hm hpt hLoad
        intro y hy
        exact Or.imp id Or.inl (x25519_load_site hp hrun u v e hU hne hStep off hlow.pc hoff i
          (certPoint_instrAt x25519_certOk hm hpt).1 (by rw [hev]) y hy)
      · have hLoad' : loadSite st i = false := by simpa using hLoad
        subst e
        intro y hy
        obtain ⟨a,ha,hk,j,hj,hy⟩ := hy
        subst y
        rcases xfer_reads i hlow hx x25519_env_size (x25519_base4 hv) (x25519_code_no_wrap hv)
            hLoad' a ha hk j hj with ⟨n,hn,he⟩ | ⟨n,hn,he⟩
        · exact .inr (.inr (.inr (Region.mk hn he)))
        · exact .inr (.inr (.inl (Region.mk hn he)))
  · exact absurd hret hne
  · cases hj with
    | nil => exact absurd rfl ht
    | cons _ hst hObs _ =>
      have hh := Except.ok.inj (hStep.symm.trans hst)
      have he := (Prod.mk.inj hh).2
      subst e
      exact hObs.reads

/-- **Every state of `m0c_x25519` keeps SP within `stackBytes` below its entry value.** -/
theorem _root_.M0Crypto.Release.X25519.x25519_stack : TraceSpec.X25519Stack := by
  intro c s hp
  obtain ⟨n, hn⟩ := X25519.x25519_correct c s hp
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, ht, hres, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil ht
  refine ⟨states, tr, hrun, fun u hu => ?_⟩
  by_cases hpc : u.pc = c.ret
  · have hl := Release.runStates_stop_last hrun u hu hpc
    obtain ⟨last, hlast, hrun'⟩ := runStates_final hrun
    have ht' := (runUntil_success_unique ht hrun').1
    rw [hlast] at hl
    cases hl
    subst ht'
    exact restored_sp_in_stack_window hres.sp _
  · obtain ⟨v,h,_⟩ := x25519_summary_reachable hp hrun (runStates_beforeStop hrun u hu)
    rcases h with (hcert | ⟨hret,_⟩) | ⟨tr,j,k,ht,hj,hk,_⟩
    · obtain ⟨b,off,st,is,hm,hpt,hni,hlow⟩ := hcert
      cases is with
      | nil => exact absurd rfl hni
      | cons i is =>
        obtain ⟨out,hx⟩ := certPoint_xfer x25519_certOk hm hpt
        exact (xfer_stack_window hlow hx).1
    · exact absurd hret hpc
    · cases hj with
      | nil => exact absurd rfl ht
      | cons _ _ hObs _ =>
        refine ⟨SAVED+LFRAME+borrowed,by decide,?_⟩
        change u.sp = _
        rw [hObs.sp,X25519SafegcdFrame.workSp,E,BitVec.ofNat_add]
        bv_omega

end M0Crypto.Release.ConstantTime
