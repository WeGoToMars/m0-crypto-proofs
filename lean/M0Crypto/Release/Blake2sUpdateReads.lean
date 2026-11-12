import M0Crypto.Release.Blake2sUpdateConstantTime
import M0Crypto.Release.Blake2sUpdateReach
import M0Crypto.Release.Blake2sLd
import M0Crypto.Release.ConstantTime.EntryReads

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# Read bounds of `m0c_blake2s_update`

Every byte a call reads lies in its stack window, the artifact, the 112-byte context window at
`r0` or the `n` input bytes at `r1`. The certificate bounds every read except those of the loads
through the caller's context and input pointers (its *load sites*); `update_reachSR` bounds
exactly the reads of the instructions at those sites (`ldAll`).
-/

namespace M0Crypto.Release.Blake2sUpdate
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

theorem update_loadFailure : certLoadFailure ldB b2uEnv b2uCert = none := by
  decide +kernel

/-- The instruction at every load site is one of the constrained loads. -/
theorem ldB_ld : ∀ off, ldB off = true → ∀ i, instrAt B off = some i → ldAll i = true := by
  intro off hoff i hi
  unfold ldB at hoff
  rw [hi] at hoff
  exact hoff

/-- The recorded run satisfies the write and read bounds at every non-final state. -/
theorem update_hPR {base : Word} {s : State} {st0 : SState}
    (e : UpdateEntry base s st0) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PLR ldAll (WU base s) (UF s) (UR s) z ev :=
  ReachS.recorded (P := PLR ldAll (WU base s) (UF s) (UR s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrU_misses_code e _ (hz.1.1 _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code ((update_reachSR e).mono (fun _ _ h => h) (fun t ht => ⟨ht.pc, ht⟩)) hrun

/-- **Every byte `m0c_blake2s_update` reads is in its stack window, the artifact, the context
window or the input.** -/
theorem update_reads {base : Word} {s : State} {st0 : SState}
    (e : UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom (fun y => ReadOk (params base s) b2uEnv y ∨ UR s y) tr := by
  obtain ⟨n, hn⟩ := Blake2sHash.update_correct e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -⟩ := hn fuel hf
  refine ⟨t, tr, hru, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
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
  exact certificate_run_reads (env := b2uEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_update) (init := entryStateP 3 0)
    (cert := b2uCert) (p := params base s)
    b2u_certOk b2u_indicesFailure_eq_none b2u_certAligned b2u_slotsCheck
    (by decide)
    (by rw [Artifacts.Release.bytes_length]; simpa [params, b2uEnv] using e.codeF)
    (by simp [b2uEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (update_hlocal e e hret rfl rfl (by simp) hrun hrun) hcert update_loadFailure (UR s)
    (fun u t ev hu hne hst off _ hok i hi hevi y hy => by
      obtain ⟨t', ev', hst', hP⟩ := update_hPR e hrun u (hu.mem_runStates hrun) hne
      have hq := hst.symm.trans hst'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hq
      rw [hq.2] at hevi
      have hld : ldAll ev'.instr = true := by rw [hevi]; exact ldB_ld off hok i hi
      exact hP.2 hld y (by rw [← hq.2]; exact hy))
    hrun

end M0Crypto.Release.Blake2sUpdate
