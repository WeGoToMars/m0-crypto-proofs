import M0Crypto.Release.Blake2sFinalConstantTime
import M0Crypto.Release.Blake2sFinalReach
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.ConstantTime.EntryReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# Read bounds of `m0c_blake2s_final`

Every byte a call reads lies in its stack window, the artifact, or the 112-byte context window at
`r0`. The certificate bounds every read except those of the loads through the caller's context
pointer (its *load sites*); `final_reachSR` bounds exactly the reads of the instructions at those
sites (`ldAll`).
-/

namespace M0Crypto.Release.Blake2sFinal
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Blake2sLd (ldAll)

/-- The load sites of the certificate: every instruction `ldAll` constrains. Derived from the
artifact, so a layout change moves it. -/
def ldB (off : Nat) : Bool :=
  match instrAt B off with
  | some i => ldAll i
  | none => false

theorem final_loadFailure : certLoadFailure ldB b2fEnv b2fCert = none := by
  decide +kernel

/-- The instruction at every load site is one of the constrained loads. -/
theorem ldB_ld : ∀ off, ldB off = true → ∀ i, instrAt B off = some i → ldAll i = true := by
  intro off hoff i hi
  unfold ldB at hoff
  rw [hi] at hoff
  exact hoff

/-- The recorded run satisfies the write and read bounds at every non-final state. -/
theorem final_hPR {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State}
    (e : FinalEntry base s st) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PL2R ldAll (WF base s) (FF s) (CtxRF s) z ev :=
  ReachS.recorded (P := PL2R ldAll (WF base s) (FF s) (CtxRF s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrF_misses_code e _ (hz.1.1 _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code ((final_reachSR e).mono (fun _ _ h => h) (fun t ht => ⟨ht.pc, ht⟩)) hrun

/-- **Every byte `m0c_blake2s_final` reads is in its stack window, the artifact or the context
window.** -/
theorem final_reads_of_entry {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State}
    (e : FinalEntry base s st)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom (fun y => ReadOk (params base s) b2fEnv y ∨ CtxRF s y) tr := by
  obtain ⟨n, hn⟩ := Blake2sHash.final_correct_of_entry e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -⟩ := hn fuel hf
  refine ⟨t, tr, hru, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
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
  exact certificate_run_reads (env := b2fEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_final) (init := entryStateP 2 0)
    (cert := b2fCert) (p := params base s)
    b2f_certOk b2f_indicesFailure_eq_none b2f_certAligned b2f_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2fEnv] using e.codeF)
    (by simp [b2fEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (final_hlocal e e hret rfl rfl (by simp) hrun hrun) hcert final_loadFailure (CtxRF s)
    (fun u t ev hu hne hst off _ hok i hi hevi y hy => by
      obtain ⟨t', ev', hst', hP⟩ := final_hPR e hrun u (hu.mem_runStates hrun) hne
      have hq := hst.symm.trans hst'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hq
      rw [hq.2] at hevi
      have hld : ldAll ev'.instr = true := by rw [hevi]; exact ldB_ld off hok i hi
      exact hP.2 hld y (by rw [← hq.2]; exact hy))
    hrun

end M0Crypto.Release.Blake2sFinal
