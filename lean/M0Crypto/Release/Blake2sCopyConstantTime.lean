import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sCopySites
import M0Crypto.Release.ConstantTime.Blake2sStreamEntries
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.RegionStores
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ConstantTime.EntryReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# Constant-time trace of `m0c_blake2s_copy`

Two calls with the same `r0`-`r3` (destination, source, length and `r3`), `sp` and `lr` execute
identical traces, whatever the caller's other registers and the memory (including the source and
destination bytes) hold. The certificate relation steps both runs together; the only obligation
left is the separation of the stores through the destination (`copySites`), which write the
`n` destination bytes (`copy_reachS`) and so miss the code and the frame.
-/

namespace M0Crypto.Release.Blake2sCopy
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2sStreamCode (copySites copySites_store isStoreSite)
open M0Crypto.Release.Blake2sCode (SiteAt siteAt_of_copy)

/-- The parameters of a call entered in state `s`. -/
def params (base : Word) (s : State) : Params :=
  ⟨base, s.regs 13, s.regs 14, Artifacts.Release.bytes.length⟩

theorem copy_sites_decode {off : Nat} (h : off ∈ copySites) {i : Instr}
    (hi : instrAt B off = some i) : (∃ n l, i = .stm n l ∧ 0 < bitCount l) ∨ (∃ op t n k, i = .memImm op t n k ∧ op.isLoad = false) := by
  have := List.all_eq_true.mp copySites_store off h
  rw [hi] at this
  cases i with
  | stm n l => exact Or.inl ⟨n, l, rfl, by simpa [isStoreSite] using this⟩
  | memImm op t n k =>
    exact Or.inr ⟨op, t, n, k, rfl, by simpa [isStoreSite] using this⟩
  | _ => simp [isStoreSite] at this

theorem dst_ok {base : Word} {s : State} (e : CopyEntry base s) :
    Disj base Artifacts.Release.size (s.regs 0) (s.regs 2).toNat ∧
    Disj (s.regs 13 - 20#32) 20 (s.regs 0) (s.regs 2).toNat :=
  ⟨e.codeD, M0Crypto.Release.ConstantTime.disj_symm e.dstF⟩

/-- Every checked store of the recorded run satisfies the certificate's separation premise. -/
theorem bufferStoreOk {base : Word} {s : State} (e : CopyEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events))
    (hP : ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PcWr (WC base s) z ev)
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {z w : State}
    (hm : b ∈ b2kCert) (hp : BlockPoint b2kEnv b off st (i :: is))
    (h : LowEq (params base s) Artifacts.Release.bytes off st z w) (hmem : z ∈ states) :
    BufferStoreOk b2kEnv (params base s) Artifacts.Release.bytes st z i := by
  have hstop : z.pc ≠ s.regs 14 &&& ~~~1#32 := by
    have hf := (certPoint_instrAt b2k_certOk hm hp).2
    have hpos := instr_size_pos i
    have hoff : off < Artifacts.Release.size := by
      simpa [B_len] using (show off < Artifacts.Release.bytes.length by omega)
    rw [h.1]
    exact Ne.symm (hret off hoff)
  obtain ⟨t, ev, hstep, hpw⟩ := hP z hmem hstop
  have hbase : (params base s).base.toNat % 2 = 0 := by
    have := e.base4; show base.toNat % 2 = 0; omega
  have hev := certPoint_step_event i b2k_certOk b2k_certAligned hbase hm hp h hstep
  have hdec := (certPoint_instrAt b2k_certOk hm hp).1
  refine bufferStoreOk_of_site b2k_sites hm hp ?_
  intro hoff hstm
  have hsite : SiteAt base z.pc := siteAt_of_copy hoff h.1
  subst hev
  obtain ⟨c1, c2⟩ := dst_ok e
  refine bufferStoreOk_of_region (buf := s.regs 0) (len := (s.regs 2).toNat) ?_ ?_ (by have := e.n64; omega) ?_ ?_
  · simpa [params, Artifacts.Release.bytes_length] using c1
  · simpa [params, b2kEnv] using c2
  · intro a ha
    exact ((hpw a ha).2 hsite)
  · intro n l hi'
    rcases copy_sites_decode hoff hdec with ⟨n', l', h', hl'⟩ | ⟨op, t, n', k, h', -⟩
    · rw [h'] at hi'; cases hi'; exact hl'
    · rw [h'] at hi'; cases hi'

theorem wrC_misses_code {base : Word} {s : State} (e : CopyEntry base s) :
    ∀ y, WrC s y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i := by
  intro y hy i hi
  rw [B_len] at hi
  rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · exact Blake2sHash.wr_disj e.codeF ho hi
  · exact Blake2sHash.wr_disj e.codeD ho hi

/-- The recorded run satisfies the pc-dependent write bound at every non-final state. -/
theorem copy_hP {base : Word} {s : State} (e : CopyEntry base s) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PcWr (WC base s) z ev :=
  ReachS.recorded (P := PcWr (WC base s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrC_misses_code e _ (hz _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code ((copy_reachS e).mono (P' := PcWr (WC base s)) (fun _ _ h => h.1) (fun t ht => ⟨ht.pc, ht⟩)) hrun

/-- The certificate's per-position obligations hold along a recorded run. -/
theorem copy_hlocal {base : Word} {s₁ s₂ : State} (e : CopyEntry base s₁)
    (hret : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s₁.regs 14 &&& ~~~1#32) fuel s₁ = .ok (states, events)) :
    ∀ u₁ u₂, BeforeStop (s₁.regs 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (s₁.regs 14 &&& ~~~1#32) s₂ u₂ →
      CertAt b2kEnv b2kCert (params base s₁) Artifacts.Release.bytes u₁ u₂ →
      PositionObligations b2kEnv b2kCert (params base s₁) Artifacts.Release.bytes u₁ u₂ := by
  intro u₁ u₂ hb₁ _ _ b off st i is hm hp hrel
  refine ⟨bufferStoreOk e hret hrun (copy_hP e hrun) hm hp hrel (hb₁.mem_runStates hrun),
    pubLoadOk_nil rfl _ _ _ _, ?_⟩
  intro cond imm _ hd
  simp [b2kEnv] at hd

/-- **`m0c_blake2s_copy` runs with a trace independent of the caller's secret state.** Two
calls satisfying the entry contract, agreeing on `r0`-`r3` (destination, source, length and
`r3`), `sp` and `lr`, have equal event traces for every fuel. -/
theorem copy_constant_time {base : Word} {s₁ s₂ : State}
    (e₁ : CopyEntry base s₁) (e₂ : CopyEntry base s₂)
    (hret : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hpc : s₂.pc = s₁.pc) (hsp : s₂.regs 13 = s₁.regs 13) (hlr : s₂.regs 14 = s₁.regs 14)
    (hpub : ∀ r : Reg, r.val < 3 → s₂.regs r = s₁.regs r) (fuel : Nat) :
    (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₁).map Prod.snd =
      (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₂).map Prod.snd := by
  have hLow : LowEq (params base s₁) Artifacts.Release.bytes Artifacts.Release.blake2s_copy
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
  have hcert := certAt_initial b2k_certOk b2k_indicesFailure_eq_none hLow
  obtain ⟨n, hn⟩ := copy_correct e₁ hret
  obtain ⟨s', tr, hru, -⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  exact certificate_reachable_trace_eq (env := b2kEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_copy) (init := entryStateP 3 0)
    (cert := b2kCert) (p := params base s₁)
    b2k_certOk b2k_indicesFailure_eq_none b2k_certAligned b2k_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2kEnv, fr] using e₁.codeF)
    (by simp [b2kEnv, Artifacts.Release.bytes_length]) e₁.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e₁.codeF.1) e₁.lr
    (copy_hlocal e₁ hret hrun) fuel hcert

/-- **`copy` keeps `sp` within twenty bytes below its entry value** in every state of the call. -/
theorem copy_stack {base : Word} {s : State} (e : CopyEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, TraceSpec.InStackWindow (s.regs 13) 20 (u.regs 13) := by
  obtain ⟨n, hn⟩ := copy_correct e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hpost, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hLow : LowEq (params base s) Artifacts.Release.bytes Artifacts.Release.blake2s_copy
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
  have hcert := certAt_initial b2k_certOk b2k_indicesFailure_eq_none hLow
  intro u hu
  by_cases hpc : u.pc = s.regs 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hrunU⟩ := runStates_final hrun
    have h1 := runUntil_success_unique hru hrunU
    have h2 := Release.runStates_stop_last hrun u hu hpc
    rw [hlast] at h2
    cases h2
    have : u = t := h1.1.symm
    subst this
    simpa [hpost.sp] using restored_sp_in_stack_window (sp0 := s.regs 13) (s := u) hpost.sp 20
  · have hw := certificate_reachable_window (env := b2kEnv) (bytes := Artifacts.Release.bytes)
      (entry := Artifacts.Release.blake2s_copy) (init := entryStateP 3 0)
      (cert := b2kCert) (p := params base s)
      b2k_certOk b2k_indicesFailure_eq_none b2k_certAligned b2k_slotsCheck
      (by decide)
      (by rw [Artifacts.Release.bytes_length]; simpa [params, b2kEnv, fr] using e.codeF)
      (by simp [b2kEnv, Artifacts.Release.bytes_length]) e.base4
      (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
      (copy_hlocal (s₂ := s) e hret hrun) hcert (runStates_beforeStop hrun u hu) hpc
    simpa [b2kEnv, params] using hw

end M0Crypto.Release.Blake2sCopy
