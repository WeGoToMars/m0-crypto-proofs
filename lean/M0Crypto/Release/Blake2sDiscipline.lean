import M0Crypto.Release.Blake2sInitConstantTime
import M0Crypto.Release.Blake2sUpdateReads
import M0Crypto.Release.Blake2sFinalReads
import M0Crypto.Release.ConstantTime.HolesRun
import M0Crypto.Release.ConstantTime.Blake2sHoles

set_option linter.unusedSimpArgs false

/-!
# Stack discipline of the BLAKE2s entry points

From the entry-state hypotheses of the read theorems: `certificate_run_discipline` with the
hole maps of `ConstantTime/Blake2sHoles.lean`. The load sites of `update` and `final` read the
context and the input, which the entry hypotheses separate from the stack window.
-/

namespace M0Crypto.Release
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Blake2sLd (ldAll)

namespace Blake2sInit

/-- **`init` keeps the stack discipline over its 4-byte frame.** -/
theorem init_discipline_of_entry {base : Word} {s : State} (e : InitEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline (s.regs 13) 4 states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ s.regs 14 &&& ~~~1#32 →
        Interrupt.CodePos base Artifacts.Release.bytes u := by
  obtain ⟨n, hn⟩ := Blake2sHash.init_correct_of_entry e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hLow : LowEq (params base s) Artifacts.Release.bytes Artifacts.Release.blake2s_init
      (entryStateP 1 0) s s := by
    apply entryStateP_sound (np := 1) (by decide)
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
  have hcert := certAt_initial b2i_certOk b2i_indicesFailure_eq_none hLow
  exact certificate_run_discipline (env := b2iEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_init) (init := entryStateP 1 0)
    (cert := b2iCert) (p := params base s)
    b2i_certOk b2i_indicesFailure_eq_none b2i_certAligned b2i_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2iEnv] using e.codeF)
    (by simp [b2iEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (init_hlocal (s₂ := s) e hret hrun) hcert rfl b2i_loadFailure (fun _ => False)
    (fun _ _ _ _ _ _ off _ hok => by simp at hok) (fun _ h => h.elim)
    b2i_holes hrun

end Blake2sInit

namespace Blake2sUpdate

/-- **`update` keeps the stack discipline over its stack window, callee frames included.** -/
theorem update_discipline_of_entry {base : Word} {s : State} {st0 : SState}
    (e : UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline (s.regs 13) STREAM_FRAME states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ s.regs 14 &&& ~~~1#32 →
        Interrupt.CodePos base Artifacts.Release.bytes u := by
  obtain ⟨n, hn⟩ := Blake2sHash.update_correct_of_entry e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -⟩ := hn fuel hf
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
  exact certificate_run_discipline (env := b2uEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_update) (init := entryStateP 3 0)
    (cert := b2uCert) (p := params base s)
    b2u_certOk b2u_indicesFailure_eq_none b2u_certAligned b2u_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2uEnv] using e.codeF)
    (by simp [b2uEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (update_hlocal e e hret rfl rfl (by simp) hrun hrun) hcert rfl update_loadFailure (UR s)
    (fun u t ev hu hne hst off _ hok i hi hevi y hy => Or.inl <| by
      obtain ⟨t', ev', hst', hP⟩ := update_hPR e hrun u (hu.mem_runStates hrun) hne
      have hq := hst.symm.trans hst'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hq
      rw [hq.2] at hevi
      have hld : ldAll ev'.instr = true := by rw [hevi]; exact ldB_ld off hok i hi
      exact hP.2 hld y (by rw [← hq.2]; exact hy))
    (fun y hy hb => by
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact not_region_of_disj e.cF (Region.mk ho rfl) hb
      · exact not_region_of_disj e.pF (Region.mk ho rfl) hb)
    b2u_holes hrun

end Blake2sUpdate

namespace Blake2sFinal

/-- **`final` keeps the stack discipline over its stack window, callee frames included.** -/
theorem final_discipline_of_entry {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State}
    (e : FinalEntry base s st)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr,
      runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, tr) ∧
      TraceSpec.StackDiscipline (s.regs 13) STREAM_FRAME states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ s.regs 14 &&& ~~~1#32 →
        Interrupt.CodePos base Artifacts.Release.bytes u := by
  obtain ⟨n, hn⟩ := Blake2sHash.final_correct_of_entry e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -⟩ := hn fuel hf
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  refine ⟨states, tr, hrun, ?_⟩
  have hLow : LowEq (params base s) Artifacts.Release.bytes Artifacts.Release.blake2s_final
      (entryStateP 2 0) s s := by
    apply entryStateP_sound (np := 2) (by decide)
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
  have hcert := certAt_initial b2f_certOk b2f_indicesFailure_eq_none hLow
  exact certificate_run_discipline (env := b2fEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_final) (init := entryStateP 2 0)
    (cert := b2fCert) (p := params base s)
    b2f_certOk b2f_indicesFailure_eq_none b2f_certAligned b2f_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2fEnv] using e.codeF)
    (by simp [b2fEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (final_hlocal e e hret rfl rfl (by simp) hrun hrun) hcert rfl final_loadFailure (CtxRF s)
    (fun u t ev hu hne hst off _ hok i hi hevi y hy => Or.inl <| by
      obtain ⟨t', ev', hst', hP⟩ := final_hPR e hrun u (hu.mem_runStates hrun) hne
      have hq := hst.symm.trans hst'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hq
      rw [hq.2] at hevi
      have hld : ldAll ev'.instr = true := by rw [hevi]; exact ldB_ld off hok i hi
      exact hP.2 hld y (by rw [← hq.2]; exact hy))
    (fun y hy hb => by
      obtain ⟨o, ho, rfl⟩ := hy
      exact not_region_of_disj e.cF (Region.mk ho rfl) hb)
    b2f_holes hrun

end Blake2sFinal

end M0Crypto.Release
