import M0Crypto.Release.ChaCha20XorConstantTime
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ConstantTime.ReadBounds
import M0Crypto.Release.ConstantTime.RunInvariant

set_option linter.unusedSimpArgs false

/-!
# Read bounds of `m0c_chacha20_xor`

Every byte read by the call lies in the input, key, nonce, artifact or stack window. Each event
sits at a position of the certificate (the certificate relates the run to itself). A load through
a non-stack address is at a caller-memory load site (`certLoadFailure`), where the whole-call
access events of `ChaCha20StoreEvents` bound the address. Every other read is a stack or literal
read, bounded by the certificate's window check.
-/

namespace M0Crypto.Release.ChaCha20XorReads
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.ChaCha20StoreEvents

/-- Offsets of the caller-memory load instructions. -/
def siteB (off : Nat) : Bool := decide (ChaCha20Policy.SiteOff off)

theorem chacha20_loadFailure : certLoadFailure siteB chacha20Env chacha20Cert = none := by
  decide +kernel

/-- The event of a step from a certificate position. -/
theorem certPoint_step_event {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s s₂ t : State} {e : Event} (i : Instr)
    (hc : certOk env bytes entry init cert = true)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (h : LowEq p bytes off st s s₂) (hstep : step s = .ok (t, e)) :
    e = ⟨s.pc, i, i.accesses s⟩ := by
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hd := decode_at h.code₁ off i hdecode hlen
  have heven := certPoint_pc_even p.base hbase ha hm hp
  have hpc := h.pc
  unfold step at hstep
  simp only [hpc] at hstep
  rw [heven, hd] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · cases hex : i.exec s <;> simp_all
  · simp at hstep

theorem readOk_chaChaRd (c : Frame.Ctx) {y : Word}
    (h : ReadOk ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ chacha20Env y) :
    TraceSpec.ChaCha20XorReadRegion c y := by
  have hsb := ChaCha20Layout.chStackBytes_eq
  rcases h with ⟨o, ho, e⟩ | ⟨o, ho, e⟩
  · right; right; right; right
    refine Region.mk (o := o) ?_ ?_
    · simp [chacha20Env, TraceSpec.chacha20StackBytes, chacha20ArgWords] at ho; omega
    · simpa [chacha20Env, TraceSpec.chacha20StackBytes, Frame.Ctx.fp, hsb] using e
  · right; right; right; left
    exact Region.mk (by simpa [chacha20Env, Artifacts.Release.bytes_length] using ho) e

/-- **Every read of `m0c_chacha20_xor` is inside its permitted regions.** -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_reads : TraceSpec.ChaCha20XorReads := by
  intro c s ⟨hv, he, hlr, hret⟩
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
  refine ⟨s', tr, hru, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil hru
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
  have hsize : chacha20Env.size = Artifacts.Release.bytes.length := by
    simp [chacha20Env, Artifacts.Release.bytes_length]
  have hnowrap : c.base.toNat + Artifacts.Release.bytes.length ≤ 2 ^ 32 := by
    simpa [Artifacts.Release.bytes_length] using hv.codeF.1
  have hpart := certificate_reachable_partner (env := chacha20Env)
    (bytes := Artifacts.Release.bytes) (entry := Artifacts.Release.chacha20_xor)
    (init := entryState chacha20ArgWords) (cert := chacha20Cert)
    (p := ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩)
    chacha20_certOk chacha20_indicesFailure_eq_none chacha20_certAligned chacha20_slotsCheck
    (by decide)
    (by simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes, Frame.Ctx.fp,
        ChaCha20Layout.chStackBytes_eq, Artifacts.Release.bytes_length] using hv.codeF)
    hsize hv.base4 hnowrap hlr hlocal (chacha20_entry_reachable hv he hv he rfl)
  have hq := runStates_events_invariant (fun u => BeforeStop (c.regs0 14 &&& ~~~1#32) s u)
    (fun ev => (∀ a ∈ ev.accesses, ∀ k < a.width,
        RdPolicy c ev.pc a.kind (a.addr + BitVec.ofNat 32 k)) →
      ∀ y, Reads ev.accesses y → TraceSpec.ChaCha20XorReadRegion c y)
    (c.regs0 14 &&& ~~~1#32) ?_ fuel BeforeStop.initial hrun
  · intro e he y hy
    exact hq e he (hpol e he) y hy
  · intro u t ev hu hne hst
    refine ⟨BeforeStop.next hu hne hst, ?_⟩
    obtain ⟨u₂, hrel, -⟩ := hpart u hu
    rcases hrel with ⟨b, off, st, code, hm, hp, hnil, hlow⟩ | ⟨hpc, _⟩
    · cases code with
      | nil => exact absurd rfl hnil
      | cons i is =>
        have hev := certPoint_step_event i chacha20_certOk chacha20_certAligned
          (by show c.base.toNat % 2 = 0; have := hv.base4; omega) hm hp hlow hst
        subst hev
        intro hallowed y hy
        obtain ⟨a, ha, hk, q, hq, rfl⟩ := hy
        obtain ⟨out, hx⟩ := certPoint_xfer chacha20_certOk hm hp
        by_cases hl : loadSite st i = true
        · have hoff := certPoint_loadSite chacha20_loadFailure hm hp hl
          have hsite : ChaCha20Policy.SitePC c.base u.pc :=
            ⟨off, by simpa [siteB] using hoff, by simpa using hlow.pc⟩
          exact (hallowed a ha q hq).2 hk hsite
        · have hl' : loadSite st i = false := by simpa using hl
          exact readOk_chaChaRd c (xfer_reads i hlow hx hsize hv.base4 hnowrap hl' a ha hk q hq)
    · exact absurd hpc hne

end M0Crypto.Release.ChaCha20XorReads
