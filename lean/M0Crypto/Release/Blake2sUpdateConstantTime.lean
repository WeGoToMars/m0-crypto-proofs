import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sCtCommon
import M0Crypto.Release.ConstantTime.Blake2sStreamEntries
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ChaCha20XorStack
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ConstantTime.EntryReads
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# Constant-time trace of `m0c_blake2s_update`

Two calls with the same `r0`-`r3` (context pointer, input pointer, length and `r3`), `sp` and
`lr`, whose contexts hold the same `used` word, execute identical traces: the input bytes, the
buffered bytes and the context's other words may differ. The certificate relation steps both runs together. Two obligations remain:

* the stores through untracked bases (the sites of `update`, `copy` and `compress`) write only
  the context, which misses the code and the frame (`update_reachS`, `WU`);
* the declared public load of `ctx.used` reads the same word in both runs: the run's first-visit
  invariant (`UF`) gives the pre-prologue memory and `r4 = r0` there.
-/

namespace M0Crypto.Release.Blake2sUpdate
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sCode (SiteAt siteAt_of_update siteAt_of_copy siteAt_of_compress compressSites)

/-- The parameters of a call entered in state `s`. -/
def params (base : Word) (s : State) : Params :=
  ⟨base, s.regs 13, s.regs 14, Artifacts.Release.bytes.length⟩

/-- The untracked store sites reachable from `update`: its own, `copy`'s and `compress`'s. -/
def uSites : List Nat := updateSites ++ copySites ++ compressSites

theorem uSites_store : uSites.all (fun off => isStoreSite (instrAt B off)) = true := by
  decide +kernel

theorem b2u_sites : certSites b2uEnv uSites b2uCert = true := by decide +kernel

theorem siteAt_of_uSites {base pc : Word} {off : Nat} (h : off ∈ uSites)
    (hpc : pc = base + BitVec.ofNat 32 off) : SiteAt base pc := by
  simp only [uSites, List.mem_append] at h
  rcases h with (h | h) | h
  · exact siteAt_of_update h hpc
  · exact siteAt_of_copy h hpc
  · exact siteAt_of_compress h hpc

theorem instrAt_usedLoad : instrAt B updateUsedLoad = some ldrU1 := by
  decide +kernel

theorem wrU_misses_code {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    ∀ y, WrU s y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i := by
  intro y hy i hi
  rw [B_len] at hi
  rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · exact Blake2sHash.wr_disj e.codeF ho hi
  · exact Blake2sHash.wr_disj e.codeC ho hi

/-- The recorded run satisfies the pc-dependent write bound and the first-visit invariant of the
declared load at every non-final state. -/
theorem update_hP {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PL (WU base s) (UF s) z ev :=
  ReachS.recorded (P := PL (WU base s) (UF s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrU_misses_code e _ (hz.1 _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code ((update_reachS e).mono (P' := PL (WU base s) (UF s)) (fun _ _ h => h)
      (fun t ht => ⟨ht.pc, ht⟩)) hrun

/-- A state of the recorded run at a checked position is not the stop address. -/
theorem not_stop {base : Word} {s : State}
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {z w : State}
    (hm : b ∈ b2uCert) (hp : BlockPoint b2uEnv b off st (i :: is))
    (h : LowEq (params base s) Artifacts.Release.bytes off st z w) :
    z.pc ≠ s.regs 14 &&& ~~~1#32 := by
  have hf := (certPoint_instrAt b2u_certOk hm hp).2
  have hpos := instr_size_pos i
  have hoff : off < Artifacts.Release.size := by
    simpa [B_len] using (show off < Artifacts.Release.bytes.length by omega)
  rw [h.1]
  exact Ne.symm (hret off hoff)

/-- Every checked store of the recorded run satisfies the certificate's separation premise. -/
theorem bufferStoreOk {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events))
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {z w : State}
    (hm : b ∈ b2uCert) (hp : BlockPoint b2uEnv b off st (i :: is))
    (h : LowEq (params base s) Artifacts.Release.bytes off st z w) (hmem : z ∈ states) :
    BufferStoreOk b2uEnv (params base s) Artifacts.Release.bytes st z i := by
  obtain ⟨t, ev, hstep, hpl⟩ := update_hP e hrun z hmem (not_stop hret hm hp h)
  have hbase : (params base s).base.toNat % 2 = 0 := by
    have := e.base4; show base.toNat % 2 = 0; omega
  have hev := certPoint_step_event i b2u_certOk b2u_certAligned hbase hm hp h hstep
  have hdec := (certPoint_instrAt b2u_certOk hm hp).1
  refine bufferStoreOk_of_site b2u_sites hm hp ?_
  intro hoff hstm
  have hsite : SiteAt base z.pc := siteAt_of_uSites hoff h.1
  subst hev
  refine bufferStoreOk_of_region (buf := s.regs 0) (len := 112) ?_ ?_ (by omega) ?_ ?_
  · simpa [params, Artifacts.Release.bytes_length] using e.codeC
  · simpa [params, b2uEnv] using disj_symm e.cF
  · intro a ha
    exact (hpl.1 a ha).2 hsite
  · intro n l hi'
    rcases store_decode (List.all_eq_true.mp uSites_store off hoff) hdec with ⟨n', l', h', hl'⟩ | ⟨op, t, n', k, h', -⟩
    · rw [h'] at hi'; cases hi'; exact hl'
    · rw [h'] at hi'; cases hi'

/-- The declared load of `ctx.used` reads the same word in both runs. -/
theorem update_pubLoad {base : Word} {s₁ s₂ : State} {st₁ st₂ : SState}
    (e₁ : UpdateEntry base s₁ st₁) (e₂ : UpdateEntry base s₂ st₂)
    (hret₁ : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hlr : s₂.regs 14 = s₁.regs 14) (hr0 : s₂.regs 0 = s₁.regs 0)
    (hused : read32 s₁.mem (s₁.regs 0 + 104#32) = read32 s₂.mem (s₁.regs 0 + 104#32))
    {f₁ f₂ : Nat} {states₁ states₂ : List State} {events₁ events₂ : List Event}
    (hrun₁ : M0Crypto.Release.runStates (s₁.regs 14 &&& ~~~1#32) f₁ s₁ = .ok (states₁, events₁))
    (hrun₂ : M0Crypto.Release.runStates (s₂.regs 14 &&& ~~~1#32) f₂ s₂ = .ok (states₂, events₂))
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {z w : State}
    (hm : b ∈ b2uCert) (hp : BlockPoint b2uEnv b off st (i :: is))
    (h : LowEq (params base s₁) Artifacts.Release.bytes off st z w)
    (hz : z ∈ states₁) (hw : w ∈ states₂) :
    PubLoadOk b2uEnv off z w i := by
  by_cases hoff : off = updateUsedLoad
  case neg =>
    apply pubLoadOk_of_notin
    simp [b2uEnv, hoff]
  subst hoff
  have hdec := (certPoint_instrAt b2u_certOk hm hp).1
  rw [instrAt_usedLoad] at hdec
  cases hdec
  have hbase : (params base s₁).base.toNat % 2 = 0 := by
    have := e₁.base4; show base.toNat % 2 = 0; omega
  have hwstop : w.pc ≠ s₂.regs 14 &&& ~~~1#32 := by
    rw [h.pc_eq, hlr]; exact not_stop hret₁ hm hp h
  obtain ⟨t₁, ev₁, hstep₁, hpl₁⟩ := update_hP e₁ hrun₁ z hz (not_stop hret₁ hm hp h)
  obtain ⟨t₂, ev₂, hstep₂, hpl₂⟩ := update_hP e₂ hrun₂ w hw hwstop
  have hev₁ := certPoint_step_event ldrU1 b2u_certOk b2u_certAligned hbase hm hp h hstep₁
  have hev₂ := certPoint_step_event₂ ldrU1 b2u_certOk b2u_certAligned hbase hm hp h hstep₂
  have u₁ : UF s₁ z := hpl₁.2.2 (by rw [hev₁])
  have u₂ : UF s₂ w := hpl₂.2.2 (by rw [hev₂])
  have m₁ := pm_ctx e₁ 104 (by omega)
  have m₂ := pm_ctx e₂ 104 (by omega)
  rw [hr0] at m₂
  show PubLoadOk b2uEnv _ z w (.memImm .ldr 7 4 26)
  refine pubLoadOk_used _ _ _ (a := s₁.regs 0) u₁.1 (u₂.1.trans hr0) ?_
  rw [u₁.2, u₂.2]
  exact m₁.trans (hused.trans m₂.symm)

/-- The certificate's per-position obligations hold along two recorded runs. -/
theorem update_hlocal {base : Word} {s₁ s₂ : State} {st₁ st₂ : SState}
    (e₁ : UpdateEntry base s₁ st₁) (e₂ : UpdateEntry base s₂ st₂)
    (hret₁ : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hlr : s₂.regs 14 = s₁.regs 14) (hr0 : s₂.regs 0 = s₁.regs 0)
    (hused : read32 s₁.mem (s₁.regs 0 + 104#32) = read32 s₂.mem (s₁.regs 0 + 104#32))
    {f₁ f₂ : Nat} {states₁ states₂ : List State} {events₁ events₂ : List Event}
    (hrun₁ : M0Crypto.Release.runStates (s₁.regs 14 &&& ~~~1#32) f₁ s₁ = .ok (states₁, events₁))
    (hrun₂ : M0Crypto.Release.runStates (s₂.regs 14 &&& ~~~1#32) f₂ s₂ = .ok (states₂, events₂)) :
    ∀ u₁ u₂, BeforeStop (s₁.regs 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (s₁.regs 14 &&& ~~~1#32) s₂ u₂ →
      CertAt b2uEnv b2uCert (params base s₁) Artifacts.Release.bytes u₁ u₂ →
      PositionObligations b2uEnv b2uCert (params base s₁) Artifacts.Release.bytes u₁ u₂ := by
  intro u₁ u₂ hb₁ hb₂ _ b off st i is hm hp hrel
  have hrun₂' : M0Crypto.Release.runStates (s₁.regs 14 &&& ~~~1#32) f₂ s₂ = .ok (states₂, events₂) := by
    rw [← hlr]; exact hrun₂
  refine ⟨bufferStoreOk e₁ hret₁ hrun₁ hm hp hrel (hb₁.mem_runStates hrun₁),
    update_pubLoad e₁ e₂ hret₁ hlr hr0 hused hrun₁ hrun₂ hm hp hrel (hb₁.mem_runStates hrun₁)
      (hb₂.mem_runStates hrun₂'), ?_⟩
  intro cond imm _ hd
  simp [b2uEnv] at hd

/-- **`m0c_blake2s_update` runs with a trace independent of the data it absorbs.** Two calls
satisfying the entry contract, agreeing on `r0`-`r3` (context pointer, input pointer, length and
the unused `r3`), `sp`, `lr` and the context's `used` word, have equal event traces for every
fuel. The input bytes, the other context words and `r4`-`r12` may differ. -/
theorem update_constant_time {base : Word} {s₁ s₂ : State} {st₁ st₂ : SState}
    (e₁ : UpdateEntry base s₁ st₁) (e₂ : UpdateEntry base s₂ st₂)
    (hret : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hpc : s₂.pc = s₁.pc) (hsp : s₂.regs 13 = s₁.regs 13) (hlr : s₂.regs 14 = s₁.regs 14)
    (hpub : ∀ r : Reg, r.val < 3 → s₂.regs r = s₁.regs r)
    (hused : read32 s₁.mem (s₁.regs 0 + 104#32) = read32 s₂.mem (s₁.regs 0 + 104#32))
    (fuel : Nat) :
    (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₁).map Prod.snd =
      (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₂).map Prod.snd := by
  have hLow : LowEq (params base s₁) Artifacts.Release.bytes Artifacts.Release.blake2s_update
      (entryStateP 3 0) s₁ s₂ := by
    apply entryStateP_sound (np := 3) (by decide)
    · exact e₁.pc
    · exact hpc
    · rfl
    · exact hsp
    · intro i hi
      exact (hpub ⟨i % 16, Nat.mod_lt _ (by decide)⟩ (by simp only; omega)).symm
    · rfl
    · exact hlr
    · intro k hk; omega
    · rfl
    · exact e₁.code
    · exact e₂.code
  have hcert := certAt_initial b2u_certOk b2u_indicesFailure_eq_none hLow
  have hret₂ : ∀ i < Artifacts.Release.size, s₂.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i := by
    rw [hlr]; exact hret
  obtain ⟨n₁, hn₁⟩ := Blake2sHash.update_correct e₁ hret
  obtain ⟨n₂, hn₂⟩ := Blake2sHash.update_correct e₂ hret₂
  obtain ⟨t₁, tr₁, hru₁, -⟩ := hn₁ n₁ (Nat.le_refl n₁)
  obtain ⟨t₂, tr₂, hru₂, -⟩ := hn₂ n₂ (Nat.le_refl n₂)
  obtain ⟨states₁, hrun₁, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru₁
  obtain ⟨states₂, hrun₂, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru₂
  exact certificate_reachable_trace_eq (env := b2uEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_update) (init := entryStateP 3 0)
    (cert := b2uCert) (p := params base s₁)
    b2u_certOk b2u_indicesFailure_eq_none b2u_certAligned b2u_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2uEnv] using e₁.codeF)
    (by simp [b2uEnv, Artifacts.Release.bytes_length]) e₁.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e₁.codeF.1) e₁.lr
    (update_hlocal e₁ e₂ hret hlr (hpub 0 (by decide)) hused hrun₁ hrun₂) fuel hcert

/-- **`update` keeps `sp` within 160 bytes below its entry value** in every state of the call. -/
theorem update_stack {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, TraceSpec.InStackWindow (s.regs 13) STREAM_FRAME (u.regs 13) := by
  obtain ⟨n, hn⟩ := Blake2sHash.update_correct e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hpost, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hLow : LowEq (params base s) Artifacts.Release.bytes Artifacts.Release.blake2s_update
      (entryStateP 3 0) s s := by
    apply entryStateP_sound (np := 3) (by decide)
    · exact e.pc
    · rfl
    · rfl
    · rfl
    · intro i hi; rfl
    · rfl
    · rfl
    · intro k hk; rfl
    · rfl
    · exact e.code
    · exact e.code
  have hcert := certAt_initial b2u_certOk b2u_indicesFailure_eq_none hLow
  intro u hu
  by_cases hpc : u.pc = s.regs 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hrunU⟩ := runStates_final hrun
    have h1 := runUntil_success_unique hru hrunU
    have h2 := ChaCha20XorStack.runStates_stop_last hrun u hu hpc
    rw [hlast] at h2
    cases h2
    have : u = t := h1.1.symm
    subst this
    simpa [hpost.sp] using restored_sp_in_stack_window (sp0 := s.regs 13) (s := u) hpost.sp STREAM_FRAME
  · have hw := certificate_reachable_window (env := b2uEnv) (bytes := Artifacts.Release.bytes)
      (entry := Artifacts.Release.blake2s_update) (init := entryStateP 3 0)
      (cert := b2uCert) (p := params base s)
      b2u_certOk b2u_indicesFailure_eq_none b2u_certAligned b2u_slotsCheck
      (by decide)
      (by rw [Artifacts.Release.bytes_length]; simpa [params, b2uEnv] using e.codeF)
      (by simp [b2uEnv, Artifacts.Release.bytes_length]) e.base4
      (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
      (update_hlocal e e hret rfl rfl (by simp) hrun hrun) hcert (runStates_beforeStop hrun u hu) hpc
    simpa [b2uEnv, params] using hw

end M0Crypto.Release.Blake2sUpdate
