import M0Crypto.Release.ChaCha20XorConstantTime
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Bridges

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

/-- **Every state of `m0c_chacha20_xor` keeps SP in the stack window.** -/
theorem _root_.M0Crypto.Release.ChaCha20Xor.xor_stack : TraceSpec.ChaCha20XorStack := by
  intro c s ⟨hv, he, hlr, hret⟩
  replace hret := Region.ne hret
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
    refine ⟨ChaCha20XorConstantTime.bufferStoreOk c hv hret hrun hpol hm hp hrel (hb₁.mem_runStates hrun), pubLoadOk_nil rfl _ _ _ _, ?_⟩
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
