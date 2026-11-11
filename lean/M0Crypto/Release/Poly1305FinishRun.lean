import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305FinishReturn
import M0Crypto.Release.Poly1305FinishCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace M0Crypto.Release.Poly1305Finish
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

theorem arithmetic_regs (s : State) (r : Reg) (hr : 6 ≤ r.val) (h15 : r.val ≠ 15) :
    (execAll arithmetic s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ h15
  simp [arithmetic, carry, reduce, pad, Instr.dsts]; omega

def middle (s : State) : State := execAll clear (execAll emit (execAll arithmetic s))

theorem middle_mem (s : State) : (middle s).mem = tagMem (execAll arithmetic s) := by
  rw [middle, execAll_mem _ _ (by decide), emit_mem]

theorem middle_regs (s : State) (r : Reg) (hr : 8 ≤ r.val) (h12 : r.val ≠ 12) (h15 : r.val ≠ 15) :
    (middle s).regs r = s.regs r := by
  rw [middle, execAll_regs_other _ _ _ h15 (by simp [clear, Instr.dsts]; omega),
    execAll_regs_other _ _ _ h15 (by simp [emit, stle, Instr.dsts]; omega), arithmetic_regs _ _ (by omega) h15]

theorem middle_cleared (s : State) (r : Reg) (hr : r.val < 4 ∨ r.val = 12) : (middle s).regs r = 0#32 := by
  unfold middle
  have hs : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 12 := by
    rcases r with ⟨v, hv⟩; simp only [Fin.ext_iff, Fin.val_mk] at hr ⊢; omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [clear, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg]

theorem middle_pc (s : State) :
    (middle s).pc = s.pc + BitVec.ofNat 32 (seqSize arithmetic + seqSize emit + seqSize clear) := by
  rw [middle, execAll_pc _ _ (by decide), execAll_pc _ _ (by decide), execAll_pc _ _ calc_falls,
    ofNat_add_assoc, ofNat_add_assoc, Nat.add_assoc]

theorem header_run_p (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s) :
    ReachS c.base (FPol c) s (fun t => t = execAll header s) := by
  have hsubH := pc_sub_fin c.base entryAt (seqSize header) (by decide) (by decide)
  have hneH := pc_ne_emit c.base entryAt (seqSize header) (by decide) (by decide) (by decide)
  have hs : s.regs 13 = c.sp0 := by rw [he.regs, he.sp]
  have hp : s.pc = c.base + BitVec.ofNat 32 entryAt := by show s.regs 15 = _; rw [he.regs, he.pc]
  have hfp4 := fp4 c hv
  have bc240 : bitCount 240#8 = 4 := by decide
  have hsp : s.regs 13 - BitVec.ofNat 32 (4 * (bitCount 0xf0 + true.toNat)) = c.fp := by
    rw [hs, Frame.bitCount_f0]; rfl
  have hsp' : s.regs 13 - BitVec.ofNat 32 (4 * (bitCount 240#8 + 1)) = c.fp := by
    rw [bc240, hs]; rfl
  apply ReachS.blockW (fpol_of_region c (fun pc h => hsubH pc h) (fun pc h => hneH pc h)) (inRegion_pcBetween (by decide) (by decide)) (by have := hv.base4; omega) hp (by decide) segments_at.1 (by decide)
  · simp (config := { decide := true }) [alignedAll, header, Instr.accesses, wordAccesses,
      M0Crypto.Armv6M.State.sp, hsp, hsp', bc240, Frame.bitCount_f0, List.range_succ, Access.aligned,
      BitVec.toNat_add, hs]
    have := hv.sp8
    omega
  · intro e hev y ⟨a, ha, hw, k, hk, hy⟩
    simp only [traceAll, header, List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl | rfl | rfl <;>
      simp [Instr.accesses, wordAccesses, Frame.bitCount_f0, bc240, M0Crypto.Armv6M.State.sp, hsp, hsp'] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    left
    change k < 4 at hk
    dsimp only [Access.addr] at hy
    refine ⟨4*j+k, by omega, ?_⟩
    rw [hy, hs, ofNat_add_assoc]
    rfl
  · exact ReachS.done rfl


theorem middle_run_p (c : FCtx) (hv : FValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 arithAt) (hsp : s.regs 13 = c.fp)
    (hc : s.regs 7 = c.ctx) (ht : s.regs 12 = c.tag) :
    ReachS c.base (FPol c) s (fun t => t = middle s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply ReachS.blockW (fpol_of_region c (pc_sub_fin c.base arithAt (seqSize arithmetic) (by decide) (by decide))
      (pc_ne_emit c.base arithAt (seqSize arithmetic) (by decide) (by decide) (by decide))) (inRegion_pcBetween (by decide) (by decide))
    hb2 hp (by decide) segments_at.2.1 calc_falls
    (Poly1305Blocks.stable_aligned _ _ calc_stable (by rw [hsp]; exact fp4 c hv)
      (by rw [hc]; exact hv.ctx4)) (WritesTo.of_noWritesMem _ _ calc_noW c.Wr)
  have ap : (execAll arithmetic s).pc = c.base + BitVec.ofNat 32 emitAt := by
    rw [execAll_pc _ _ calc_falls, hp, ofNat_add_assoc]; rfl
  apply ReachS.blockW (Wr := InFrame c.tag 4) (fpol_of_emit c) (inRegion_pcBetween (by decide) (by decide))
    hb2 ap (by decide) segments_at.2.2.1 (by decide) (emit_aligned _)
  · exact WritesTo.of_writesIn (emit_writes (execAll arithmetic s)) (fun o ho => by
      rw [arithmetic_regs _ 12 (by decide) (by decide), ht]
      exact ⟨o, ho, rfl⟩)
  have ep : (execAll emit (execAll arithmetic s)).pc = c.base + BitVec.ofNat 32 clearAt := by
    rw [execAll_pc _ _ (by decide), ap, ofNat_add_assoc]; rfl
  apply ReachS.blockW (fpol_of_region c (pc_sub_fin c.base clearAt (seqSize clear) (by decide) (by decide))
      (pc_ne_emit c.base clearAt (seqSize clear) (by decide) (by decide) (by decide))) (inRegion_pcBetween (by decide) (by decide))
    hb2 ep (by decide) segments_at.2.2.2.1 (by decide)
    (by simp [alignedAll, clear, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) c.Wr)
  exact ReachS.done rfl

theorem header_run (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s) :
    ReachW c.base (FinPc c.base) c.Wr s (fun t => t = execAll header s) :=
  (header_run_p c hv s he).mono (fun _ _ h => h.1) (fun _ h => h)

theorem middle_run (c : FCtx) (hv : FValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 arithAt) (hsp : s.regs 13 = c.fp)
    (hc : s.regs 7 = c.ctx) (ht : s.regs 12 = c.tag) :
    ReachW c.base (FinPc c.base) c.Wr s (fun t => t = middle s) :=
  (middle_run_p c hv s hp hsp hc ht).mono (fun _ _ h => h.1) (fun _ h => h)

/-- The saved AAPCS words survive tag publication, including tag/context aliasing. -/
theorem middle_saved (c : FCtx) (hv : FValid c) (s : State) (hm : s.mem = c.mP) (ht : s.regs 12 = c.tag)
    (j : Nat) (hj : j < 5) : read32 (middle s).mem (slot c.fp j) =
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14].getD j 0#32 := by
  rw [middle_mem, tagMem, execAll_mem _ _ calc_noW, hm, arithmetic_regs _ 12 (by decide) (by decide), ht]
  rw [read32_congr (m := c.mP)]
  · rw [FCtx.mP]
    have h := Frame.read32_storeWords_same c.m0 c.fp
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14] j (by simp; omega) (by simp)
    change read32 _ (c.fp + BitVec.ofNat 32 (4*j)) = _
    rw [h]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro k hk
    apply storeWords_other
    intro i q hi hq heq
    have hd := hv.tagS
    apply ne_of_disj hd.2.1 hd.1 (Or.symm hd.2.2) (i := 4*j+k) (j := 4*i+q) (by omega) (by simp at hi; omega)
    rw [slot, ofNat_add_assoc, ofNat_add_assoc] at heq
    exact heq

structure FResult (c : FCtx) (s t : State) : Prop where
  ret : t.pc = c.regs0 14 &&& ~~~1#32
  sp : t.regs 13 = c.sp0
  callee : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r
  cleared : ∀ r : Reg, r.val < 4 ∨ r.val = 12 → t.regs r = 0#32
  mem : t.mem = tagMem (tagState s)

theorem header_falls : header.all Instr.falls = true := by decide
attribute [local irreducible] header arithmetic emit clear middle tagState

/-- Composable execution theorem for the complete finish function, under the tag-emit policy. -/
theorem finish_reach_p (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachS c.base (FPol c) s (fun t => FResult c s t) := by
  apply ReachS.bind
  apply (header_run_p c hv s he).mono (fun _ _ h => h)
  intro u hu
  have effect := header_effect c s he
  rw [← hu] at effect
  have up : u.pc = c.base + BitVec.ofNat 32 arithAt := by
    rw [hu, execAll_pc _ _ header_falls]
    have hp : s.pc = c.base + BitVec.ofNat 32 entryAt := by show s.regs 15 = _; rw [he.regs, he.pc]
    rw [hp, ofNat_add_assoc]; rfl
  apply ReachS.bind
  apply (middle_run_p c hv u up effect.2.2.2.1 effect.2.1 effect.2.2.1).mono (fun _ _ h => h)
  intro v hveq
  have hsum : arithAt + (seqSize arithmetic + seqSize emit + seqSize clear) = popAt := by
    simp only [popAt, clearAt, emitAt]; omega
  have vp : v.pc = c.base + BitVec.ofNat 32 popAt := by
    rw [hveq, middle_pc, up, ofNat_add_assoc, hsum]
  have vs : v.regs 13 = c.fp := by rw [hveq, middle_regs _ 13 (by decide) (by decide) (by decide), effect.2.2.2.1]
  apply (pop_ret_p c hv v vp vs (by rw [hveq]; exact middle_saved c hv u effect.1 effect.2.2.1) hlr).mono
    (fun _ _ h => h)
  intro t h
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · intro r hlo hhi
    by_cases hr : r.val < 8
    · exact h.2.2.1 r hlo hr
    · rw [h.2.2.2.1 r (Or.inr (by omega)) (by omega) (by omega), hveq,
        middle_regs _ r (by omega) (by omega) (by omega)]
      exact effect.2.2.2.2.2 r (by omega) hhi
  · intro r hr
    rw [h.2.2.2.1 r (by rcases hr with hr | hr; exact Or.inl hr; exact Or.inr (by omega))
      (by omega) (by omega), hveq]
    exact middle_cleared u r hr
  · rw [h.2.2.2.2, hveq, middle_mem, hu]
    unfold tagState
    rfl

/-- Composable execution theorem for the complete finish function. -/
theorem finish_reach_w (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachW c.base (FinPc c.base) c.Wr s (fun t => FResult c s t) :=
  (finish_reach_p c hv s he hlr).mono (fun _ _ h => h.1) (fun _ h => h)

/-- Composable execution theorem for the complete finish function. -/
theorem finish_reach (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) : Reach c.base c.Wr s (fun t => FResult c s t) :=
  (finish_reach_w c hv s he hlr).toReach
end M0Crypto.Release.Poly1305Finish
