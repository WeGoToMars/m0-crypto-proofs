import M0Crypto.Release.Blake2sCompressConstantTime
import M0Crypto.Release.ConstantTime.ReachableWindow
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false

/-!
# Stack bound of `m0c_blake2s_compress`

Every state of the call keeps `sp` in `[sp0 - 136, sp0]`. States before the return address come
from the certificate run (related to itself); the state at the return address is the last state
of the recording, whose `sp` the functional proof restores.
-/

namespace M0Crypto.Release.Blake2sCompress
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ConstantTime

theorem compress_stack {base : Word} {s : State}
    (e : Entry base s) (x : CtExtra base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, TraceSpec.InStackWindow (s.regs 13) COMPRESS_FRAME (u.regs 13) := by
  obtain ⟨n, hn⟩ := compress_recorded e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hpost⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hLow : LowEq (params base s) Artifacts.Release.bytes Artifacts.Release.blake2s_compress
      (entryState b2cArgWords) s s := by
    apply entryState_sound
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
  have hcert := certAt_initial b2c_certOk b2c_indicesFailure_eq_none hLow
  have wd := window_disj e x
  intro u hu
  by_cases hpc : u.pc = s.regs 14 &&& ~~~1#32
  · obtain ⟨last, hlast, hrunU⟩ := runStates_final hrun
    have h1 := runUntil_success_unique hru hrunU
    have h2 := Release.runStates_stop_last hrun u hu hpc
    rw [hlast] at h2
    cases h2
    have : u = t := h1.1.symm
    subst this
    simpa [hpost.sp] using restored_sp_in_stack_window (sp0 := s.regs 13) (s := u) hpost.sp COMPRESS_FRAME
  · have hw := certificate_reachable_window (env := b2cEnv) (bytes := Artifacts.Release.bytes)
      (entry := Artifacts.Release.blake2s_compress) (init := entryState b2cArgWords)
      (cert := b2cCert) (p := params base s)
      b2c_certOk b2c_indicesFailure_eq_none b2c_certAligned b2c_slotsCheck
      (by decide)
      (by simpa [params, b2cEnv, b2cArgWords, Artifacts.Release.bytes_length] using wd.1)
      (by simp [b2cEnv, Artifacts.Release.bytes_length]) e.base4
      (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
      (compress_hlocal (s₂ := s) e x hret hrun) hcert (runStates_beforeStop hrun u hu) hpc
    simpa [b2cEnv, params] using hw

end M0Crypto.Release.Blake2sCompress
