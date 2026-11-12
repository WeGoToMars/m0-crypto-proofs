import M0Crypto.Release.Blake2sCompressConstantTime
import M0Crypto.Release.ConstantTime.EntryReads

set_option linter.unusedSimpArgs false

/-!
# Read bounds of `m0c_blake2s_compress`

Every byte a call reads lies in its stack window, the artifact, the block it hashes (64 bytes at
`r1`) or the chain words (32 bytes at `r0`). The certificate bounds every read except those of
the loads through a caller pointer, its *load sites*. `compress_reachSR` bounds exactly the reads
of the instructions at those sites (`cLd`): the six `ldm`s of the prologue (four over the block,
two over the chain words) and the five chain-word loads of the epilogue.
-/

namespace M0Crypto.Release.Blake2sCompress
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime

/-- The load sites of the certificate: every instruction `cLd` constrains. Derived from the
artifact, so a layout change moves it. -/
def ldB (off : Nat) : Bool :=
  match instrAt B off with
  | some i => cLd i
  | none => false

theorem compress_loadFailure : certLoadFailure ldB b2cEnv b2cCert = none := by
  decide +kernel

/-- The instruction at every load site is one of the constrained loads. -/
theorem ldB_ld : ∀ off, ldB off = true → ∀ i, instrAt B off = some i → cLd i = true := by
  intro off hoff i hi
  unfold ldB at hoff
  rw [hi] at hoff
  exact hoff

/-- The recorded run satisfies the write and read bounds at every non-final state. -/
theorem compress_hPR {base : Word} {s : State} (e : Entry base s) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PNR cLd (CW base s) (RR s) z ev :=
  ReachS.recorded (P := PNR cLd (CW base s) (RR s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrOf_misses_code e _ (hz.1.1 _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code (compress_reachSR e _ (fun t ht => ⟨ht.pc, ht⟩)) hrun

/-- **Every byte `m0c_blake2s_compress` reads is in its stack window, the artifact, the block or
the chain words.** -/
theorem compress_reads {base : Word} {s : State} (e : Entry base s) (x : CtExtra base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom (fun y => ReadOk (params base s) b2cEnv y ∨ RR s y) tr := by
  obtain ⟨n, hn⟩ := compress_recorded e hret
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, -⟩ := hn fuel hf
  refine ⟨t, tr, hru, ?_⟩
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
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
    · intro k hk
      have : k = 0 := by simp [b2cArgWords] at hk; omega
      subst this
      rfl
    · rfl
    · exact e.code
    · exact e.code
  have hcert := certAt_initial b2c_certOk b2c_indicesFailure_eq_none hLow
  have wd := window_disj e x
  exact certificate_run_reads (env := b2cEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_compress) (init := entryState b2cArgWords)
    (cert := b2cCert) (p := params base s)
    b2c_certOk b2c_indicesFailure_eq_none b2c_certAligned b2c_slotsCheck
    (by decide)
    (by simpa [params, b2cEnv, b2cArgWords, Artifacts.Release.bytes_length] using wd.1)
    (by simp [b2cEnv, Artifacts.Release.bytes_length]) e.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e.codeF.1) e.lr
    (compress_hlocal e x hret hrun) hcert compress_loadFailure (RR s)
    (fun u t ev hu hne hst off _ hok i hi hevi y hy => by
      obtain ⟨t', ev', hst', hP⟩ := compress_hPR e hrun u (hu.mem_runStates hrun) hne
      have hq := hst.symm.trans hst'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hq
      rw [hq.2] at hevi
      have hld : cLd ev'.instr = true := by rw [hevi]; exact ldB_ld off hok i hi
      exact hP.2 hld y (by rw [← hq.2]; exact hy))
    hrun

end M0Crypto.Release.Blake2sCompress
