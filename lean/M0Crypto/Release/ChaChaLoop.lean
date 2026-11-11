import M0Crypto.Release.Reach
import M0Crypto.Release.ChaChaRound
import M0Crypto.Release.ChaChaLayout
import M0Crypto.Thumb.SeqScan

set_option linter.unusedSimpArgs false

/-!
The ChaCha20 round loop of the release artifact: ten iterations of
`DOUBLE_ROUND_REG_D` (offset `droundOff`), each followed by the public loop count in r12
(`mov r1, r12; subs r1, #1; mov r12, r1; beq; b`).
-/

namespace M0Crypto.Release.ChaChaLoop

open M0Crypto.Armv6M (Word Reg State read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.ChaChaRound
open M0Crypto.Proofs.ChaCha20DRound (innerBlockF toArr innerBlock_toArr)
open M0Crypto.Spec.ChaCha20 (innerBlocks)
open M0Crypto.Release.ChaChaLayout (droundOff decOff beqOff loopBOff postOff)

abbrev B := Artifacts.Release.bytes

set_option maxRecDepth 100000

theorem dec_at : seqAt B decOff dec = true := by decide
theorem beq_at : instrAt B beqOff = some (.bcond 0 (brImm8 beqOff postOff)) := by decide +kernel
theorem b_at : instrAt B loopBOff = some (.b (brImm11 loopBOff droundOff)) := by decide +kernel

theorem B_len : B.length < 2 ^ 32 := by rw [Artifacts.Release.bytes_length]; decide

theorem sub_flags (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).1 = x - y :=
  M0Crypto.Release.sub_flags x y

/-- The decrement: r1 = r12 = r12 - 1 and Z = (r12 - 1 = 0); r0, r2-r11, SP, LR, memory unchanged. -/
theorem dec_effect (t : State) :
    let t' := execAll dec t
    t'.regs 12 = t.regs 12 - 1 ∧ t'.z = (t.regs 12 - 1 == 0) ∧ t'.mem = t.mem ∧
    (∀ r : Reg, r.val ≠ 1 → r.val ≠ 12 → r.val ≠ 15 → t'.regs r = t.regs r) := by
  refine ⟨?_, ?_, execAll_mem dec t (by decide), fun r h1 h12 h15 =>
    execAll_regs_of_dsts dec t r h15 (fun x => x = 1 ∨ x = 12) (by simp [dec, Instr.dsts]; decide) (by omega)⟩
  · simp only [execAll, dec, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg,
      M0Crypto.Proofs.toReg_1]
    simp (config := { decide := true }) only [ite_true, ite_false, BitVec.setWidth_eq]
    rw [show (BitVec.setWidth 32 (1 : BitVec 8) : Word) = 1#32 from rfl, sub_flags]; rfl
  · simp only [execAll, dec, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg,
      M0Crypto.Proofs.toReg_1]
    simp (config := { decide := true }) only [ite_true, ite_false]
    rw [show (BitVec.setWidth 32 (1 : BitVec 8) : Word) = 1#32 from rfl, sub_flags]; rfl

theorem dec_aligned (t : State) : alignedAll dec t = true := by
  simp [alignedAll, dec, Instr.accesses]

theorem view_congr (s t : State) (inR0 : Option Nat) (h0 : t.regs 0 = s.regs 0)
    (hd : ∀ k, 12 ≤ k → k < 16 → t.regs (dregOf k) = s.regs (dregOf k))
    (h13 : t.regs 13 = s.regs 13) (hm : t.mem = s.mem) :
    ChaChaRound.view inR0 t = ChaChaRound.view inR0 s := by
  funext k
  unfold ChaChaRound.view
  split
  · split
    · exact h0
    · rw [h13, hm]
  · split
    · exact hd k (by omega) (by omega)
    · rfl

/-- `f` applied `n` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

theorem setReg15_view (t : State) (x : Word) (inR0 : Option Nat) :
    ChaChaRound.view inR0 (t.setReg 15 x) = ChaChaRound.view inR0 t :=
  view_congr t _ inR0 (setReg_regs_ne _ _ _ _ (by decide))
    (fun k h1 h2 => setReg_regs_ne _ _ _ _ (fun e => by
      have := congrArg Fin.val e; simp [dregOf] at this; omega))
    (setReg_regs_ne _ _ _ _ (by decide)) rfl

theorem body_at : seqAt B droundOff body = true := by
  rw [body, seqAt_append, dround_at]; exact dec_at

theorem body_len : body.length = 159 := by decide
theorem body_split : droundOff + seqSize body = beqOff := by decide
theorem beq_le_post : beqOff ≤ postOff := by decide
/-- The `beq` falls to `postOff`: its sign-extended displacement, from PC + 4, is the
distance `postOff - beqOff`. -/
theorem sext_beq :
    4#32 + BitVec.signExtend 32 (brImm8 beqOff postOff ++ 0#1) = BitVec.ofNat 32 (postOff - beqOff) := by
  decide +kernel
theorem body_falls : body.all Instr.falls = true := by decide

theorem body_aligned (s : State) (hsp : (s.regs 13).toNat % 4 = 0) : alignedAll body s = true := by
  rw [body, alignedAll_append, dround_aligned s hsp, dec_aligned]; rfl

theorem body_writes (s : State) : WritesIn (traceAll body s) (s.regs 13) droundBytes := by
  rw [body, traceAll_append]
  apply WritesIn.append (traceAll_writes_sp dround s droundBytes (dround_sp.mono fun _ h => .inr h.2))
  intro e he y ⟨a, ha, _⟩
  simp [traceAll, dec, Instr.accesses] at he
  rcases he with rfl | rfl | rfl <;> simp [Instr.accesses] at ha

/-- Every byte accessed by a round body lies in its stack frame. -/
theorem body_accesses (s : State) : AccessesIn (traceAll body s) (s.regs 13) droundBytes := by
  rw [body, traceAll_append]
  apply AccessesIn.append (traceAll_accesses_sp dround s droundBytes (dround_sp.mono fun _ h => h.2))
  intro e he a ha k hk
  simp [traceAll, dec, Instr.accesses] at he
  rcases he with rfl | rfl | rfl <;> simp [Instr.accesses] at ha

theorem cond_eq (t : State) : condPassed 0 t = t.z := by simp [condPassed]

theorem ofNat_sub_one (k : Nat) (hk : k + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (k + 1) - 1 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

/- **Round loop.** From offset `droundOff` with `n` (1 ≤ n) in r12, the loop runs
`161 n - 1` steps to offset `postOff` and applies `inner_block` `n` times to the view. -/
/-- Every event is before the output instructions in the release layout. -/
def TraceBeforeOutput (base : Word) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∃ off < ChaChaLayout.achOff, e.pc = base + BitVec.ofNat 32 off

/-- A double-round body stays within the pre-output instruction range. -/
theorem body_before_output (base : Word) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 droundOff) :
    TraceBeforeOutput base (traceAll body s) := by
  intro e he
  obtain ⟨off, hoff, hp⟩ := traceAll_pc_offset body s body_falls e he
  refine ⟨droundOff + off, ?_, ?_⟩
  · have hbound : droundOff + seqSize body ≤ ChaChaLayout.achOff := by decide +kernel
    omega
  · rw [hp, hpc, ofNat_add_assoc]

theorem loop_bounded {base : Word} (hb : base.toNat % 4 = 0) : ∀ (n : Nat), 1 ≤ n → n < 2 ^ 32 →
    ∀ (s : State), s.pc = base + BitVec.ofNat 32 droundOff → RotRegs s → (s.regs 13).toNat % 4 = 0 →
    s.regs 12 = BitVec.ofNat 32 n →
    ∃ s' tr, runH B base (161 * n - 1) s = .ok (s', tr) ∧
      s'.pc = base + BitVec.ofNat 32 postOff ∧
      ChaChaRound.view (some 2) s' = iter innerBlockF n (ChaChaRound.view (some 2) s) ∧
      RotRegs s' ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧ s'.regs 12 = 0 ∧
      (∀ y, (∀ o < droundBytes, y ≠ s.regs 13 + BitVec.ofNat 32 o) → s'.mem y = s.mem y) ∧
      WritesIn tr (s.regs 13) droundBytes ∧ TraceBeforeOutput base tr ∧
      AccessesIn tr (s.regs 13) droundBytes
  | 0, h, _, _, _, _, _, _ => absurd h (by decide)
  | k + 1, _, hk, s, hpc, hrot, hsp, h12 => by
    have hb2 : base.toNat % 2 = 0 := by omega
    -- the body
    generalize hs1 : execAll dround s = s1
    generalize hs2 : execAll body s = s2
    have hs2' : s2 = execAll dec s1 := by rw [← hs2, ← hs1, body, execAll_append]
    obtain ⟨d12, dz, dm, dr⟩ := dec_effect s1
    rw [← hs2'] at d12 dz dm dr
    have r1 : ∀ r : Reg, r.val ≠ 15 → 3 < r.val ∧ (r.val < 8 ∨ 11 < r.val) → s1.regs r = s.regs r :=
      fun r h15 h => hs1 ▸ dround_regs s r h15 h
    have sp2 : s2.regs 13 = s.regs 13 := by rw [dr 13 (by decide) (by decide) (by decide)]; exact r1 13 (by decide) (by decide)
    have r12' : s2.regs 12 = BitVec.ofNat 32 k := by
      rw [d12, r1 12 (by decide) (by decide), h12, ofNat_sub_one k hk]
    have z2 : s2.z = (BitVec.ofNat 32 k == 0) := by
      rw [dz, r1 12 (by decide) (by decide), h12, ofNat_sub_one k hk]
    have rot2 : RotRegs s2 := by
      have rot1 : RotRegs s1 := ⟨by rw [r1 4 (by decide) (by decide)]; exact hrot.r4,
        by rw [r1 5 (by decide) (by decide)]; exact hrot.r5,
        by rw [r1 6 (by decide) (by decide)]; exact hrot.r6,
        by rw [r1 7 (by decide) (by decide)]; exact hrot.r7⟩
      exact ⟨by rw [dr 4 (by decide) (by decide) (by decide)]; exact rot1.r4,
        by rw [dr 5 (by decide) (by decide) (by decide)]; exact rot1.r5,
        by rw [dr 6 (by decide) (by decide) (by decide)]; exact rot1.r6,
        by rw [dr 7 (by decide) (by decide) (by decide)]; exact rot1.r7⟩
    have lr2 : s2.regs 14 = s.regs 14 := by
      rw [dr 14 (by decide) (by decide) (by decide)]; exact r1 14 (by decide) (by decide)
    have view2 : ChaChaRound.view (some 2) s2 = innerBlockF (ChaChaRound.view (some 2) s) := by
      rw [view_congr s1 s2 _ (dr 0 (by decide) (by decide) (by decide))
        (fun j h1 h2 => dr _ (by simp [dregOf]; omega) (by simp [dregOf]; omega) (by simp [dregOf]; omega))
        (by rw [dr 13 (by decide) (by decide) (by decide)]) dm, ← hs1]
      exact dround_view s hrot
    have mem2 : ∀ y, (∀ o < droundBytes, y ≠ s.regs 13 + BitVec.ofNat 32 o) → s2.mem y = s.mem y := by
      intro y hy; rw [dm, ← hs1]; exact dround_mem s y hy
    have pc2 : s2.pc = base + BitVec.ofNat 32 beqOff := by
      rw [← hs2, execAll_pc body s body_falls, hpc, ofNat_add_assoc, body_split]
    have hrun := runH_block hb2 B_len body droundOff s hpc (by decide) body_at body_falls
      (body_aligned s hsp)
    rw [hs2] at hrun
    -- the beq
    have hz : (s2.z = true) ↔ k = 0 := by
      rw [z2]; constructor
      · intro h; have := beq_iff_eq.mp h; have := congrArg BitVec.toNat this
        simp at this; omega
      · intro h; subst h; rfl
    have hsz : beqOff + (Instr.bcond 0 0).size ≤ B.length := by
      rw [Artifacts.Release.bytes_length]; decide
    by_cases h0 : k = 0
    · -- exit
      subst h0
      have hz' : condPassed 0 s2 = true := by rw [cond_eq]; exact hz.mpr rfl
      have hbeq := stepH_of_instr hb2 B_len (s := s2) pc2 (by decide) beq_at hsz
        (by simp [Instr.accesses]) (by simp only [Instr.exec, hz', ite_true]; rfl)
      refine ⟨s2.setReg 15 (s2.pc + 4#32 + BitVec.signExtend 32 (brImm8 beqOff postOff ++ 0#1)),
        traceAll body s ++ [⟨s2.pc, .bcond 0 (brImm8 beqOff postOff), (Instr.bcond 0 (brImm8 beqOff postOff)).accesses s2⟩],
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show 161 * (0 + 1) - 1 = body.length + (0 + 1) by rw [body_len], hrun,
          runH_one_step 0 hbeq]; rfl
      · simp only [M0Crypto.Armv6M.State.pc, M0Crypto.Armv6M.State.setReg, ite_true]
        rw [show s2.regs 15 = s2.pc from rfl, pc2, BitVec.add_assoc, sext_beq,
          ofNat_add_assoc, Nat.add_sub_of_le beq_le_post]
      · show _ = innerBlockF _
        rw [← view2]
        exact setReg15_view s2 _ _
      · exact ⟨by simp [M0Crypto.Armv6M.State.setReg]; exact rot2.r4, by simp [M0Crypto.Armv6M.State.setReg]; exact rot2.r5,
          by simp [M0Crypto.Armv6M.State.setReg]; exact rot2.r6, by simp [M0Crypto.Armv6M.State.setReg]; exact rot2.r7⟩
      · simp [M0Crypto.Armv6M.State.setReg]; exact sp2
      · simp [M0Crypto.Armv6M.State.setReg]; exact lr2
      · simp [M0Crypto.Armv6M.State.setReg]; exact r12'
      · intro y hy; exact mem2 y hy
      · apply WritesIn.append (body_writes s)
        exact WritesIn.cons_noacc (by simp [Instr.accesses]) (WritesIn.nil _ _)
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact body_before_output base s hpc e he
        · simp only [List.mem_singleton] at he
          subst e
          exact ⟨beqOff, by decide +kernel, pc2⟩
      · apply AccessesIn.append (body_accesses s)
        exact AccessesIn.cons_noacc (by simp [Instr.accesses]) (AccessesIn.nil _ _)
    · -- continue: beq not taken, then b back to `droundOff`
      have hz' : condPassed 0 s2 = false := by
        rw [cond_eq]; cases h : s2.z
        · rfl
        · exact absurd (hz.mp h) h0
      have hbeq := stepH_of_instr hb2 B_len (s := s2) pc2 (by decide) beq_at hsz
        (by simp [Instr.accesses]) (by simp only [Instr.exec, hz', Bool.false_eq_true, ite_false]; rfl)
      generalize hs3 : s2.setReg 15 (s2.pc + BitVec.ofNat 32 (Instr.bcond 0 (brImm8 beqOff postOff)).size) = s3 at hbeq
      have pc3 : s3.pc = base + BitVec.ofNat 32 loopBOff := by
        rw [← hs3]; simp only [M0Crypto.Armv6M.State.pc, M0Crypto.Armv6M.State.setReg, ite_true]
        rw [show s2.regs 15 = s2.pc from rfl, pc2, ofNat_add_assoc]; rfl
      have hbr := stepH_of_instr hb2 B_len (s := s3) pc3 (by decide) b_at
        (by rw [Artifacts.Release.bytes_length]; decide) (by simp [Instr.accesses])
        (by simp only [Instr.exec]; rfl)
      generalize hs4 : s3.setReg 15 (s3.pc + 4#32 + BitVec.signExtend 32 (brImm11 loopBOff droundOff ++ 0#1)) = s4 at hbr
      have pc4 : s4.pc = base + BitVec.ofNat 32 droundOff := by
        rw [← hs4]; simp only [M0Crypto.Armv6M.State.pc, M0Crypto.Armv6M.State.setReg, ite_true]
        rw [show s3.regs 15 = s3.pc from rfl, pc3, BitVec.add_assoc, BitVec.add_assoc]
        congr 1
      have e4 : ∀ r : Reg, r.val ≠ 15 → s4.regs r = s2.regs r := by
        intro r h; rw [← hs4, ← hs3]
        rw [setReg_regs_ne _ _ _ _ (fun e => h (by rw [e]; rfl)),
          setReg_regs_ne _ _ _ _ (fun e => h (by rw [e]; rfl))]
      have m4 : s4.mem = s2.mem := by rw [← hs4, ← hs3]; rfl
      have rot4 : RotRegs s4 := ⟨by rw [e4 4 (by decide)]; exact rot2.r4, by rw [e4 5 (by decide)]; exact rot2.r5,
        by rw [e4 6 (by decide)]; exact rot2.r6, by rw [e4 7 (by decide)]; exact rot2.r7⟩
      have sp4 : s4.regs 13 = s.regs 13 := by rw [e4 13 (by decide), sp2]
      obtain ⟨s', tr, hr', hpc', hv', hrot', hsp', hlr', h12', hm', hw', hbound', haccess'⟩ :=
        loop_bounded hb k (by omega) (by omega) s4 pc4 rot4 (by rw [sp4]; exact hsp)
          (by rw [e4 12 (by decide), r12'])
      have view4 : ChaChaRound.view (some 2) s4 = ChaChaRound.view (some 2) s2 := by
        rw [← hs4, ← hs3, setReg15_view, setReg15_view]
      refine ⟨s', traceAll body s ++ ⟨s2.pc, .bcond 0 (brImm8 beqOff postOff), (Instr.bcond 0 (brImm8 beqOff postOff)).accesses s2⟩ ::
          ⟨s3.pc, .b (brImm11 loopBOff droundOff), (Instr.b (brImm11 loopBOff droundOff)).accesses s3⟩ :: tr, ?_, hpc', ?_, hrot', ?_, ?_, h12', ?_, ?_, ?_, ?_⟩
      · rw [show 161 * (k + 1) - 1 = body.length + ((161 * k - 1) + 1 + 1) by rw [body_len]; omega,
          hrun, runH_one_step _ hbeq, runH_one_step _ hbr, hr']
      · rw [hv', view4, view2]; rfl
      · rw [hsp', sp4]
      · rw [hlr', e4 14 (by decide), lr2]
      · intro y hy
        rw [hm' y (by rw [sp4]; exact hy), m4, mem2 y hy]
      · apply WritesIn.append (body_writes s)
        apply WritesIn.cons_noacc (by simp [Instr.accesses])
        apply WritesIn.cons_noacc (by simp [Instr.accesses])
        rw [← sp4]; exact hw'
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact body_before_output base s hpc e he
        · rcases List.mem_cons.mp he with rfl | he
          · exact ⟨beqOff, by decide +kernel, pc2⟩
          · rcases List.mem_cons.mp he with rfl | he
            · exact ⟨loopBOff, by decide +kernel, pc3⟩
            · exact hbound' e he
      · apply AccessesIn.append (body_accesses s)
        apply AccessesIn.cons_noacc (by simp [Instr.accesses])
        apply AccessesIn.cons_noacc (by simp [Instr.accesses])
        rw [← sp4]; exact haccess'


theorem loop {base : Word} (hb : base.toNat % 4 = 0) : ∀ (n : Nat), 1 ≤ n → n < 2 ^ 32 →
    ∀ (s : State), s.pc = base + BitVec.ofNat 32 droundOff → RotRegs s → (s.regs 13).toNat % 4 = 0 →
    s.regs 12 = BitVec.ofNat 32 n →
    ∃ s' tr, runH B base (161 * n - 1) s = .ok (s', tr) ∧
      s'.pc = base + BitVec.ofNat 32 postOff ∧
      ChaChaRound.view (some 2) s' = iter innerBlockF n (ChaChaRound.view (some 2) s) ∧
      RotRegs s' ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧ s'.regs 12 = 0 ∧
      (∀ y, (∀ o < droundBytes, y ≠ s.regs 13 + BitVec.ofNat 32 o) → s'.mem y = s.mem y) ∧
      WritesIn tr (s.regs 13) droundBytes := by
  intro n hn hn' s hp hr hs h12
  obtain ⟨u, tr, he, hpc, hv, hrot, hsp, hlr, hcounter, hm, hw, _, _⟩ :=
    loop_bounded hb n hn hn' s hp hr hs h12
  exact ⟨u, tr, he, hpc, hv, hrot, hsp, hlr, hcounter, hm, hw⟩

/-- `n` loop iterations are the spec's `innerBlocks n` (RFC 8439 §2.3). -/
theorem iter_toArr : ∀ (n : Nat) (f : Nat → Word),
    toArr (iter innerBlockF n f) = innerBlocks n (toArr f)
  | 0, _ => rfl
  | n + 1, f => by rw [iter, iter_toArr n, innerBlocks, innerBlock_toArr]

end M0Crypto.Release.ChaChaLoop
