import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.ConstantTime.Blake2sCompressEntry
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.Alignment
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.Blake2sFrames

set_option linter.unusedSimpArgs false

/-!
# Constant-time trace of `m0c_blake2s_compress`

Two calls that satisfy the entry contract and agree on every public input (the pointers, the
counter words, the finalization word, `sp`, `lr`) execute identical traces, whatever the chain
words and the message block contain. The certificate relation steps both runs together; the
only obligation it leaves is the separation of the two output `stm`s, whose base register it does
not track. At those two pcs the run writes only the chain window (`compress_reachS`), which the
entry contract separates from the code and the stack window.
-/

namespace M0Crypto.Release.Blake2sCompress
open M0Crypto.Armv6M (Word State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2sCode (compressSites SiteAt siteAt_of_compress)

/-- Further separation the trace proof needs: the argument word `f0` at the stack top is outside
the code and the chain window. -/
structure CtExtra (base : Word) (s : State) : Prop where
  codeA : Disj base Artifacts.Release.size (s.regs 13) 4
  hA : Disj (s.regs 0) 32 (s.regs 13) 4

/-- The code and the chain window are each separated from the stack window (frame and `f0`). -/
theorem window_disj {base : Word} {s : State} (e : Entry base s) (x : CtExtra base s) :
    Disj base Artifacts.Release.size (s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME) (COMPRESS_FRAME + 4) ∧
    Disj (s.regs 0) 32 (s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME) (COMPRESS_FRAME + 4) := by
  have hv : (s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME).toNat = (s.regs 13).toNat - COMPRESS_FRAME := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := e.spLo; have := (s.regs 13).isLt; omega
  have hf : fpOf s = s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME := rfl
  obtain ⟨c1, c2, c3⟩ := e.codeF
  obtain ⟨d1, d2, d3⟩ := x.codeA
  obtain ⟨h1, h2, h3⟩ := e.hpF
  obtain ⟨k1, k2, k3⟩ := x.hA
  rw [hf] at c2 c3 h2 h3
  rw [hv] at c2 c3 h2 h3
  have := e.spLo
  have : 0 < Artifacts.Release.size := by decide
  refine ⟨⟨c1, by omega, ?_⟩, ⟨k1, by omega, ?_⟩⟩
  · rw [hv]; omega
  · rw [hv]; omega

/-- An instruction fetch at a site is a nonempty `stm`. -/
def isStm : Option Instr → Bool
  | some (.stm _ l) => decide (0 < bitCount l)
  | _ => false

theorem sites_stm : compressSites.all (fun off => isStm (instrAt B off)) = true := by
  decide +kernel

theorem site_instr {off : Nat} (h : off ∈ compressSites) {i : Instr} (hi : instrAt B off = some i) :
    ∃ n l, i = .stm n l ∧ 0 < bitCount l := by
  have := List.all_eq_true.mp sites_stm off h
  rw [hi] at this
  cases i <;> simp [isStm] at this
  rename_i n l
  exact ⟨n, l, rfl, this⟩

theorem bitCount_le (l : BitVec 8) : bitCount l ≤ 8 := by
  revert l; decide +kernel

/-- Every write of a `Writes`-bounded `stm` event lies in the chain window, so the store is
separated from the code and the stack window. -/
theorem stm_sep {base : Word} {s : State} (e : Entry base s) (x : CtExtra base s)
    {y : State} {n : M0Crypto.Armv6M.LowReg} {l : BitVec 8} (hl : 0 < bitCount l)
    (hw : ∀ a, Writes ((Instr.stm n l).accesses y) a → HOf s a) :
    Disj base Artifacts.Release.size (y.reg n) (4 * bitCount l) ∧
    Disj (s.regs 13 - BitVec.ofNat 32 COMPRESS_FRAME) (COMPRESS_FRAME + 4) (y.reg n) (4 * bitCount l) := by
  obtain ⟨-, hh⟩ := window_disj e x
  have hle := bitCount_le l
  have w : ∀ i k, i < bitCount l → k < 4 →
      Writes ((Instr.stm n l).accesses y) (y.reg n + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :=
    fun i k hi hk => ⟨⟨.write, y.reg n + BitVec.ofNat 32 (4 * i), 4⟩, by
      simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩,
      rfl, k, hk, rfl⟩
  have hf := hw _ (by simpa using w 0 0 hl (by omega))
  have hl' := hw _ (w (bitCount l - 1) 3 (by omega) (by omega))
  have e2 : y.reg n + BitVec.ofNat 32 (4 * (bitCount l - 1)) + BitVec.ofNat 32 3 =
      y.reg n + BitVec.ofNat 32 (4 * bitCount l - 1) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [e2] at hl'
  obtain ⟨o, ho, hfo⟩ := hf
  obtain ⟨o', ho', hlo⟩ := hl'
  have hfo' : y.reg n = s.regs 0 + BitVec.ofNat 32 o := by simpa using hfo
  have hw0 : 0 < 4 * bitCount l := by omega
  have hlen : 32 + 4 * bitCount l ≤ 2 ^ 32 := by omega
  constructor
  · exact disj_of_ends hw0 e.codeH hlen ⟨o, ho, hfo'⟩ ⟨o', ho', hlo⟩
  · exact disj_of_ends hw0 (disj_symm hh) hlen ⟨o, ho, hfo'⟩ ⟨o', ho', hlo⟩

/-- The parameters of a call entered in state `s`. -/
def params (base : Word) (s : State) : Params :=
  ⟨base, s.regs 13, s.regs 14, Artifacts.Release.bytes.length⟩

/-- The writes of a call stay inside the frame and the chain window, which miss the code. -/
theorem wrOf_misses_code {base : Word} {s : State} (e : Entry base s) :
    ∀ y, WrOf s y → ∀ i, i < B.length → y ≠ base + BitVec.ofNat 32 i := by
  intro y hy i hi
  rw [B_len] at hi
  rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := e.codeF
    intro eq
    have := congrArg BitVec.toNat eq
    rw [M0Crypto.Release.Frame.toNat_add_ofNat _ _ (by omega), M0Crypto.Release.Frame.toNat_add_ofNat _ _ (by omega)] at this
    omega
  · obtain ⟨h1, h2, h3⟩ := e.codeH
    intro eq
    have := congrArg BitVec.toNat eq
    rw [M0Crypto.Release.Frame.toNat_add_ofNat _ _ (by omega), M0Crypto.Release.Frame.toNat_add_ofNat _ _ (by omega)] at this
    omega

/-- Every checked store of the recorded run satisfies the certificate's separation premise. -/
theorem bufferStoreOk {base : Word} {s : State} (e : Entry base s) (x : CtExtra base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events))
    (hP : ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PcWr (CW base s) z ev)
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} {z w : State}
    (hm : b ∈ b2cCert) (hp : BlockPoint b2cEnv b off st (i :: is))
    (h : LowEq (params base s) Artifacts.Release.bytes off st z w) (hmem : z ∈ states) :
    BufferStoreOk b2cEnv (params base s) Artifacts.Release.bytes st z i := by
  have hstop : z.pc ≠ s.regs 14 &&& ~~~1#32 := by
    have hf := (certPoint_instrAt b2c_certOk hm hp).2
    have hpos := instr_size_pos i
    have hoff : off < Artifacts.Release.size := by
      simpa [B_len] using (show off < Artifacts.Release.bytes.length by omega)
    rw [h.1]
    exact Ne.symm (hret off hoff)
  obtain ⟨t, ev, hstep, hpw⟩ := hP z hmem hstop
  have hbase : (params base s).base.toNat % 2 = 0 := by have := e.base4; show base.toNat % 2 = 0; omega
  have hev := certPoint_step_event i b2c_certOk b2c_certAligned hbase hm hp h hstep
  have hdec := (certPoint_instrAt b2c_certOk hm hp).1
  refine bufferStoreOk_of_site b2c_sites hm hp ?_
  intro hoff _
  obtain ⟨n, l, rfl, hl⟩ := site_instr hoff hdec
  intro _
  have hsite : SiteAt base z.pc := siteAt_of_compress hoff h.1
  subst hev
  have := stm_sep e x hl (fun a ha => ((hpw a ha).2 hsite).1)
  simpa [params, b2cEnv, b2cArgWords, Artifacts.Release.bytes_length] using this

/-- The recorded run satisfies the pc-dependent write bound at every non-final state. -/
theorem compress_hP {base : Word} {s : State} (e : Entry base s) {fuel : Nat}
    {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s.regs 14 &&& ~~~1#32) fuel s = .ok (states, events)) :
    ∀ z ∈ states, z.pc ≠ s.regs 14 &&& ~~~1#32 → ∃ t ev, step z = .ok (t, ev) ∧
      PcWr (CW base s) z ev :=
  ReachS.recorded (P := PcWr (CW base s)) (stop := s.regs 14 &&& ~~~1#32)
    (fun z ev hz i hi hw => by
      obtain ⟨a, ha, hk, k, hkk, heq⟩ := hw
      exact wrOf_misses_code e _ (hz _ ⟨a, ha, hk, k, hkk, rfl⟩).1 i hi heq.symm)
    e.code (((compress_reachS e _ (fun t ht => ⟨ht.pc, ht⟩)).mono (P' := PcWr (CW base s))
      (fun _ _ h => h.1) (fun _ h => h))) hrun

/-- The certificate's per-position obligations hold along a recorded run. -/
theorem compress_hlocal {base : Word} {s₁ s₂ : State} (e : Entry base s₁) (x : CtExtra base s₁)
    (hret : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    {fuel : Nat} {states : List State} {events : List Event}
    (hrun : M0Crypto.Release.runStates (s₁.regs 14 &&& ~~~1#32) fuel s₁ = .ok (states, events)) :
    ∀ u₁ u₂, BeforeStop (s₁.regs 14 &&& ~~~1#32) s₁ u₁ →
      BeforeStop (s₁.regs 14 &&& ~~~1#32) s₂ u₂ →
      CertAt b2cEnv b2cCert (params base s₁) Artifacts.Release.bytes u₁ u₂ →
      PositionObligations b2cEnv b2cCert (params base s₁) Artifacts.Release.bytes u₁ u₂ := by
  intro u₁ u₂ hb₁ _ _ b off st i is hm hp hrel
  refine ⟨bufferStoreOk e x hret hrun (compress_hP e hrun) hm hp hrel (hb₁.mem_runStates hrun), pubLoadOk_nil rfl _ _ _ _, ?_⟩
  intro cond imm _ hd
  simp [b2cEnv] at hd

/-- Some recorded run reaches the return address. -/
theorem compress_recorded {base : Word} {s : State} (e : Entry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      Post s t := by
  obtain ⟨n, hn⟩ := Reach.runUntil (P := Post s) e.code
    (fun y hy i hi => wrOf_misses_code e y hy i hi) (fun i hi => hret i (by rwa [B_len] at hi))
    (compress_reach e _ (fun t ht => ⟨ht.pc, ht⟩))
  exact ⟨n, fun fuel hf => by
    obtain ⟨t, tr, h, hp, -⟩ := hn fuel hf
    exact ⟨t, tr, h, hp⟩⟩

/-- **`m0c_blake2s_compress` runs with a trace independent of its secret inputs.** Two calls
satisfying the entry contract, agreeing on the pointers, the counter words, the finalization
word, `sp` and `lr`, have equal event traces for every fuel. The chain words and the message
block may differ arbitrarily. -/
theorem compress_constant_time {base : Word} {s₁ s₂ : State}
    (e₁ : Entry base s₁) (e₂ : Entry base s₂) (x₁ : CtExtra base s₁)
    (hret : ∀ i < Artifacts.Release.size, s₁.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hpc : s₂.pc = s₁.pc) (hsp : s₂.regs 13 = s₁.regs 13) (hlr : s₂.regs 14 = s₁.regs 14)
    (hpub : ∀ r : Reg, r.val < 4 → s₂.regs r = s₁.regs r)
    (hf0 : read32 s₂.mem (s₁.regs 13) = read32 s₁.mem (s₁.regs 13)) (fuel : Nat) :
    (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₁).map Prod.snd =
      (runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₂).map Prod.snd := by
  have hLow : LowEq (params base s₁) Artifacts.Release.bytes Artifacts.Release.blake2s_compress
      (entryState b2cArgWords) s₁ s₂ := by
    apply entryState_sound
    · exact e₁.pc
    · exact hpc
    · rfl
    · exact hsp
    · intro i hi
      exact (hpub ⟨i % 16, Nat.mod_lt _ (by decide)⟩ (by simp only; omega)).symm
    · rfl
    · exact hlr
    · intro k hk
      have : k = 0 := by simp [b2cArgWords] at hk; omega
      subst this
      simpa [params] using hf0.symm
    · rfl
    · exact e₁.code
    · exact e₂.code
  have hcert := certAt_initial b2c_certOk b2c_indicesFailure_eq_none hLow
  obtain ⟨n, hn⟩ := compress_recorded e₁ hret
  obtain ⟨s', tr, hru, -⟩ := hn n (Nat.le_refl n)
  obtain ⟨states, hrun, -, -⟩ := M0Crypto.Release.runStates_of_runUntil hru
  have wd := window_disj e₁ x₁
  exact certificate_reachable_trace_eq (env := b2cEnv) (bytes := Artifacts.Release.bytes)
    (entry := Artifacts.Release.blake2s_compress) (init := entryState b2cArgWords)
    (cert := b2cCert) (p := params base s₁)
    b2c_certOk b2c_indicesFailure_eq_none b2c_certAligned b2c_slotsCheck
    (by decide)
    (by simpa [params, b2cEnv, b2cArgWords, Artifacts.Release.bytes_length] using wd.1)
    (by simp [b2cEnv, Artifacts.Release.bytes_length]) e₁.base4
    (by simpa [params, Artifacts.Release.bytes_length] using e₁.codeF.1) e₁.lr
    (compress_hlocal e₁ x₁ hret hrun) fuel hcert

end M0Crypto.Release.Blake2sCompress
