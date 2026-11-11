import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305Blocks
import M0Crypto.Release.Poly1305BlocksFrame

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
/-!
Whole-function execution of `m0c_poly1305_blocks` over the release bytes.
`blocks_reach` supports internal calls; `blocks_execution` transfers the result
to the single-memory Thumb runner. `afterBlocks` is an instruction-level
execution specification. Equality to the RFC accumulator is not proved here.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local irreducible] body loadState oneBlock loopState

/-- Saved r8-r11, r4-r7 and LR in the upper 36 bytes of the stack window. -/
def Saved (c : BCtx) (m : Mem) : Prop :=
  ∀ i < 9, read32 m (slot c.fp (7+i)) = saved c.regs0 i

theorem saved_outside (c : BCtx) (i k : Nat) (hi : i < 9) (hk : k < 4) :
    ¬ InFrame c.fp 7 (slot c.fp (7+i) + BitVec.ofNat 32 k) := by
  rintro ⟨o, ho, he⟩
  have := congrArg BitVec.toNat he
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem setup_saved (c : BCtx) (s : State) (hs : s.regs 13 = c.fp) (hm : Saved c s.mem) :
    Saved c (execAll setup s).mem := by
  intro i hi
  have hc : slotCount < 7 := by decide
  have hmn : slotMsg < 7 := by decide
  rw [(setup_effect s).2.2.2, hs,
    read32_write32_slot' _ _ _ slotCount (7+i) (by decide) (by omega),
    ite_eq_right (by omega), read32_write32_slot' _ _ _ slotMsg (7+i) (by decide) (by omega), ite_eq_right (by omega)]
  exact hm i hi

theorem loop_saved (c : BCtx) (n : Nat) (s : State) (hs : s.regs 13 = c.fp) (hm : Saved c s.mem) :
    Saved c (loopState c.base n s).mem := by
  intro i hi
  have hp : slotPad ≤ frameWords := by decide
  have hfw : frameWords = 7 := by decide
  rw [read32_congr (m := s.mem)]
  · exact hm i hi
  · intro k hk
    apply loop_mem
    rw [hs]
    rintro ⟨o, ho, he⟩
    apply saved_outside c i k hi hk
    exact ⟨o, by omega, he⟩

theorem publish_saved (c : BCtx) (hv : BValid c) (s : State)
    (hs : s.regs 13 = c.fp) (hc : s.regs 7 = c.ctx) (hm : Saved c s.mem) :
    Saved c (execAll publish s).mem := by
  intro i hi
  rw [(publish_effect s).1]
  rw [read32_congr (m := s.mem)]
  · exact hm i hi
  · intro k hk
    dsimp only [publishMem]
    rw [storeWords_other]
    · rw [storeWords_other]
      intro j q hj hq he
      simp only [List.length_cons, List.length_nil] at hj
      have hdis := hv.ctxS
      have neq := ne_of_disj hdis.2.1 hdis.1 (Or.symm hdis.2.2)
        (i := 4*(7+i)+k) (j := 4*j+q) (by omega) (by omega)
      apply neq
      rw [hc, slot, ofNat_add_assoc] at he
      rw [ofNat_add_assoc] at he
      exact he
    · intro j q hj hq he
      simp only [List.length_replicate] at hj
      have hfw : frameWords = 7 := by decide
      apply saved_outside c i k hi hk
      refine ⟨4*j+q, by omega, ?_⟩
      rw [he, hs, ofNat_add_assoc]
/-- Execution-level reference state before the epilogue. `loopState` retains the
actual 32-bit/64-bit instruction arithmetic; this is deliberately separate from
RFC modular correctness, which requires refining it with `Poly1305Arith.block_arith`. -/
def afterBlocks (c : BCtx) (s : State) : State :=
  let p := execAll prologue s
  if c.count = 0#32 then p
  else execAll publish (loopState c.base c.count.toNat
    (execAll setup (p.setReg 15 (c.base + BitVec.ofNat 32 setupAt))))

structure BResult (c : BCtx) (s t : State) : Prop where
  pc : t.pc = c.regs0 14 &&& ~~~1#32
  sp : t.regs 13 = c.sp0
  regs : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  scratch : ∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → t.regs r = (afterBlocks c s).regs r
  mem : t.mem = (afterBlocks c s).mem

theorem blocks_reach_w (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachW c.base (BlkPc c.base) c.Wr s (BResult c s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ReachS.bind
  apply (prologue_run c hv s he).mono (fun _ _ h => h)
  intro p hp; subst p
  let p := execAll prologue s
  obtain ⟨pm, ps, p0, p1, p2, p3, pz⟩ := prologue_effect c s he
  have pp : p.pc = c.base + BitVec.ofNat 32 enterBrAt := by
    dsimp [p]; rw [execAll_pc _ _ (by decide)]
    change s.pc + _ = _
    have entrypc : s.pc = c.base + BitVec.ofNat 32 entryAt := by show s.regs 15 = _; rw [he.regs, he.pc]
    rw [entrypc, ofNat_add_assoc]; rfl
  change p.z = (c.count == 0#32) at pz
  have pmS : Saved c p.mem := by rw [pm]; exact mP_saved c hv
  apply ReachW.bcond hb2 enterBrAt setupAt 1 (brImm8 enterBrAt setupAt) pp (by decide) (by decide) (by decide) (by decide)
    ⟨enterBrAt, by decide +kernel, by decide +kernel, rfl⟩
  · intro hn
    have cn : c.count ≠ 0#32 := by simpa [condPassed, pz] using hn
    let q := p.setReg 15 (c.base + BitVec.ofNat 32 setupAt)
    have qs : q.regs 13 = c.fp := ps
    have q0 : q.regs 0 = c.ctx := p0
    have q2 : q.regs 2 = c.count := p2
    apply ReachS.bind
    apply (setup_run hv.base4 q rfl (by rw [qs]; exact fp4 hv) (by rw [q0]; exact hv.ctx4)
      (fun o ho => Or.inl ⟨o, Nat.lt_of_lt_of_le ho belowPadBytes_le_fp, by rw [qs]⟩)).mono (fun _ _ h => h)
    intro u hu; subst u
    let u := execAll setup q
    obtain ⟨u7, u12, us, um⟩ := setup_effect q
    have us' : u.regs 13 = c.fp := us.trans qs
    have u7' : u.regs 7 = c.ctx := u7.trans q0
    have up : u.pc = c.base + BitVec.ofNat 32 testAt := by
      dsimp [u]; rw [execAll_pc _ _ (by decide)]; change (c.base + _) + _ = _
      rw [ofNat_add_assoc]; rfl
    have uc : read32 u.mem (slot (u.regs 13) slotCount) = BitVec.ofNat 32 c.count.toNat := by
      rw [us, um, M0Crypto.Armv6M.read32_write32_same, q2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have uS : Saved c u.mem := setup_saved c q qs pmS
    apply ReachS.bind
    apply (loop_run_w hv.base4 c.count.toNat (by have := c.count.isLt; have hz := cn; bv_omega)
      c.count.isLt u up (by rw [us']; exact fp4 hv) (by rw [u7']; exact hv.ctx4) uc
      (fun o ho => Or.inl ⟨o, Nat.lt_of_lt_of_le ho belowPadBytes_le_fp, by rw [us']⟩)).mono (fun _ _ h => h)
    intro v hv'
    obtain ⟨veq, vp, v7, v12, vs, _⟩ := hv'
    have vs' : v.regs 13 = c.fp := vs.trans us'
    have v7' : v.regs 7 = c.ctx := v7.trans u7'
    have vS : Saved c v.mem := by rw [veq]; exact loop_saved c _ u us' uS
    apply ReachS.bind
    apply ((publish_run hv.base4 v vp (by rw [vs']; exact fp4 hv) (by rw [v7']; exact hv.ctx4)).monoW
      (by
        intro y hy
        have hfw : frameWords ≤ 16 := by decide
        rcases hy with ⟨o, ho, heq⟩ | h
        · exact .inl ⟨o, by omega, by rw [vs'] at heq; exact heq⟩
        · exact .inr ⟨cn, by simpa [v7'] using h⟩)).mono (fun _ _ h => h)
    intro w hw; subst w
    have wp : (execAll publish v).pc = c.base + BitVec.ofNat 32 epilogueAt := by
      rw [execAll_pc _ _ (by decide), vp, ofNat_add_assoc]; exact pc_congr (by decide +kernel)
    apply (blocks_ret_w c hv c.Wr _ wp ((publish_effect v).2.2.trans vs')
      (publish_saved c hv v vs' v7' vS) hlr).mono (fun _ _ h => h)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
    · intro r hr
      rw [ht.2.2.2.1 r hr]
      change _ = (afterBlocks c s).regs r
      rw [afterBlocks, ite_eq_right cn]
      change _ = (execAll publish (loopState c.base c.count.toNat u)).regs r
      rw [veq]
    · rw [ht.2.2.2.2, afterBlocks, ite_eq_right cn]
      change _ = (execAll publish (loopState c.base c.count.toNat u)).mem
      rw [veq]
  · intro hz
    have cz : c.count = 0#32 := by simpa [condPassed, pz] using hz
    let q := p.setReg 15 (c.base + BitVec.ofNat 32 retBrAt)
    apply ReachW.b hb2 retBrAt epilogueAt (brImm11 retBrAt epilogueAt) (by rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ⟨retBrAt, by decide +kernel, by decide +kernel, rfl⟩
    let u := q.setReg 15 (c.base + BitVec.ofNat 32 epilogueAt)
    apply (blocks_ret_w c hv c.Wr u rfl ps pmS hlr).mono (fun _ _ h => h)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
    · intro r hr
      rw [ht.2.2.2.1 r hr, afterBlocks, ite_eq_left cz]
      have hr15 : r ≠ 15 := by
        intro h
        have hv15 : r.val = 15 := congrArg Fin.val h
        omega
      change (((p.setReg 15 _).setReg 15 _).regs r) = p.regs r
      rw [setReg_regs_ne _ 15 r _ hr15, setReg_regs_ne _ 15 r _ hr15]
    · rw [ht.2.2.2.2, afterBlocks, ite_eq_left cz]
      rfl

theorem blocks_reach (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base c.Wr s (BResult c s) :=
  (blocks_reach_w c hv s he hlr).toReach

/-- Whole-function execution of the linked bytes. For every 32-bit block count,
including zero, execution returns with AAPCS registers restored. Each write is in
the 64-byte stack window or h0..h4; return must be outside the artifact for this
standalone `runUntil` statement. Use `blocks_reach` for internal AEAD calls. -/
theorem blocks_execution (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      BResult c s t ∧ WritesTo c.Wr tr := by
  apply Reach.runUntil (P := BResult c s) (by rw [he.mem]; exact hv.code)
  · intro y hy i hi
    rw [B_len] at hi
    rcases hy with ⟨o, ho, rfl⟩ | ⟨_, o, ho, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := hv.codeS
      exact ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) (by omega)
    · obtain ⟨h1, h2, h3⟩ := hv.codeC
      exact ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) (by omega)
  · intro i hi; exact hret i (by rw [B_len] at hi; exact hi)
  · exact (blocks_reach c hv s he hlr).mono (fun t h => ⟨h.pc, h⟩)

end M0Crypto.Release.Poly1305Blocks
