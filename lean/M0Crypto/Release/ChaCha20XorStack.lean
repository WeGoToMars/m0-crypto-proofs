import M0Crypto.Release.ChaCha20XorConstantTime
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges

set_option linter.unusedSimpArgs false

/-!
# Stack bound of `m0c_chacha20_xor`

At every state of the call the stack pointer lies in `[sp0 - chStackBytes, sp0]`. States before the
return address come from the certificate run (the certificate relates the run to itself); the
state at the return address is the last state of the recording, whose SP the functional proof
restores.
-/

namespace M0Crypto.Release.ChaCha20XorStack
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.ChaCha20StoreEvents

/-- Only the last state of a recording can be at the stop address. -/
theorem runStates_stop_last {stop : Word} {fuel : Nat} {s : State}
    {states : List State} {events : List Event}
    (hrun : runStates stop fuel s = .ok (states, events)) :
    ∀ u ∈ states, u.pc = stop → states.getLast? = some u := by
  induction fuel generalizing s states events with
  | zero =>
    simp only [runStates] at hrun
    split at hrun
    · cases hrun; intro u hu _; simp at hu; simp [hu]
    · contradiction
  | succ fuel ih =>
    simp only [runStates] at hrun
    split at hrun
    · cases hrun; intro u hu _; simp at hu; simp [hu]
    · rename_i hp
      cases hs : step s with
      | error err => simp [hs] at hrun
      | ok pair =>
        obtain ⟨next, ev⟩ := pair
        simp only [hs] at hrun
        cases ht : runStates stop fuel next with
        | error err => simp [ht] at hrun
        | ok pair =>
          obtain ⟨rest, tr⟩ := pair
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          intro u hu hpc
          have hne : rest ≠ [] := (runStates_nonempty ht).1
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact absurd hpc hp
          · have := ih ht u hu hpc
            cases rest with
            | nil => contradiction
            | cons x xs => simpa using this

/-- **Every state of `m0c_chacha20_xor` keeps SP in the stack window.** -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_stack : TraceSpec.ChaCha20XorStack := by
  intro c s hv he hlr hret
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  obtain ⟨n, hn⟩ := reachEvents_runUntil hc
    (fun pc y hw i hi => by
      rcases hw with h | ⟨h, _⟩
      · cases h
      · exact chacha20_write_misses_code c hv h hi)
    (fun i hi => hret i (by rwa [B_len] at hi))
    (xor_reach_events c hv s he hlr)
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨s', tr, hru, hpol⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hlocal : ∀ u₁ u₂, BeforeStop (c.regs0 14 &&& ~~~1#32) s u₁ →
      BeforeStop (c.regs0 14 &&& ~~~1#32) s u₂ →
      CertAt chacha20Env chacha20Cert ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩
        Artifacts.Release.bytes u₁ u₂ →
      PositionObligations chacha20Env chacha20Cert
        ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩ Artifacts.Release.bytes u₁ u₂ := by
    intro u₁ u₂ hb₁ _ _ b off st i is hm hp hrel
    refine ⟨ChaCha20XorConstantTime.bufferStoreOk c hv hret hrun hpol hm hp hrel (hb₁.mem_runStates hrun), ?_⟩
    intro cond imm _ hd
    simp [chacha20Env] at hd
  have hsb := ChaCha20Layout.chStackBytes_eq
  intro u hu
  by_cases hpc : u.pc = c.regs0 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hw⟩ := chacha20_final_stack_window c hv s he hlr hret hrun
    have := runStates_stop_last hrun u hu hpc
    rw [hlast] at this
    cases this
    simpa [chacha20Env, TraceSpec.chacha20StackBytes] using hw
  · have hw := certificate_reachable_window (env := chacha20Env) (bytes := Artifacts.Release.bytes)
      (entry := Artifacts.Release.chacha20_xor) (init := entryState chacha20ArgWords)
      (cert := chacha20Cert) (p := ⟨c.base, c.sp0, c.regs0 14, Artifacts.Release.bytes.length⟩)
      chacha20_certOk chacha20_indicesFailure_eq_none chacha20_certAligned chacha20_slotsCheck
      (by decide)
      (by simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes, Frame.Ctx.fp,
          ChaCha20Layout.chStackBytes_eq, Artifacts.Release.bytes_length] using hv.codeF)
      (by simp [chacha20Env, Artifacts.Release.bytes_length]) hv.base4
      (by simpa [Artifacts.Release.bytes_length] using hv.codeF.1) hlr hlocal
      (chacha20_entry_reachable hv he hv he rfl) (runStates_beforeStop hrun u hu) hpc
    simpa [chacha20Env, TraceSpec.chacha20StackBytes] using hw

end M0Crypto.Release.ChaCha20XorStack
