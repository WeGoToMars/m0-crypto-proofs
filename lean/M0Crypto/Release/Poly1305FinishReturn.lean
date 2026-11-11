import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305Finish
import M0Crypto.Release.Poly1305FinishCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace M0Crypto.Release.Poly1305Finish
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7

theorem pop_ret (c : FCtx) (hv : FValid c) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 popAt) (hs : s.regs 13 = c.fp)
    (hsv : ∀ j < 5, read32 s.mem (slot c.fp j) =
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14].getD j 0#32)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base c.Wr s fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 8 → t.regs r = c.regs0 r) ∧
      (∀ r : Reg, (r.val < 4 ∨ 8 ≤ r.val) → r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) ∧ t.mem = s.mem := by
  have sv0 := hsv 0 (by decide); have sv1 := hsv 1 (by decide)
  have sv2 := hsv 2 (by decide); have sv3 := hsv 3 (by decide); have sv4 := hsv 4 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ, slot, Nat.reduceMul, BitVec.add_zero] at sv0 sv1 sv2 sv3 sv4
  have hfp4 := fp4 c hv
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hsp1 : s.regs 13 + BitVec.ofNat 32 (4 * bitCount 0xf0) = c.fp + 16#32 := by
    rw [hs, Frame.bitCount_f0]
  obtain ⟨t, hex⟩ : ∃ t, (Instr.pop 0xf0 true).exec s = .ok t := by
    simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, sv4, hlr, ite_true]
    exact ⟨_, rfl⟩
  have hex' := hex
  simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, sv4, hlr, ite_true, Except.ok.injEq] at hex'
  subst hex'
  apply Reach.step hb2 popAt _ hp (by decide) segments_at.2.2.2.2
    (by rw [B_len]; decide)
    (by simp [Instr.accesses, wordAccesses, List.range_succ, Access.aligned, Frame.bitCount_f0,
          M0Crypto.Armv6M.State.sp, hs, BitVec.toNat_add]; exact ⟨fun _ _ => by omega, by omega⟩)
    hex (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses, wordAccesses] at ha
            obtain ⟨_, _, rfl⟩ := ha; cases hw)
  apply Reach.done
  generalize hF : (((loadRegs (s.setReg 15 (s.pc + BitVec.ofNat 32 (Instr.pop 240 true).size)) (s.regs 13)
      (List.map M0Crypto.Armv6M.LowReg.toReg (listRegs 240))).setReg 13
      (s.regs 13 + BitVec.ofNat 32 (4 * (bitCount 240 + true.toNat)))).setReg
      15 (c.regs0 14 &&& ~~~1#32)) = F
  have q : ∀ r : Reg, F.regs r = (if r = 15 then c.regs0 14 &&& ~~~1#32 else if r = 13 then c.fp + 20#32
      else if r = 4 then c.regs0 4 else if r = 5 then c.regs0 5 else if r = 6 then c.regs0 6
      else if r = 7 then c.regs0 7 else s.regs r) := by
    intro r; rw [← hF]
    simp (config := { decide := true }) only [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240,
      List.map, loadRegs, M0Crypto.Armv6M.LowReg.toReg, hs, Frame.bitCount_f0, BitVec.add_assoc,
      BitVec.reduceAdd, sv0, sv1, sv2, sv3, Bool.toNat_true, Nat.reduceAdd, Nat.reduceMul,
      M0Crypto.Armv6M.State.pc]
    by_cases h15 : r = 15
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg]
    by_cases h13 : r = 13
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg]
    by_cases h4 : r = 4
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv0, BitVec.add_assoc]
    by_cases h5 : r = 5
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv1, BitVec.add_assoc]
    by_cases h6 : r = 6
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv2, BitVec.add_assoc]
    by_cases h7 : r = 7
    · subst r; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, Frame.listRegs_240, Frame.listRegs_f0, loadRegs, M0Crypto.Armv6M.LowReg.toReg, sv3, BitVec.add_assoc]
    simp only [h4, h5, h6, h7, h13, h15, ite_false]
    rw [loadRegs_regs_other _ _ _ _ (by
      simp only [Frame.listRegs_240, Frame.listRegs_f0, List.map, List.mem_cons, List.not_mem_nil, or_false]
      rcases r with ⟨v, hv⟩; simp only [Fin.ext_iff] at h4 h5 h6 h7; simp at h4 h5 h6 h7 ⊢; omega)]
    simp [h15]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact q 15
  · rw [q]; simp (config := { decide := true }) [FCtx.fp]; bv_omega
  · intro r hlo hhi
    rcases (by omega : r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7) with hr | hr | hr | hr <;>
      have er : r = ⟨r.val, r.isLt⟩ := rfl <;> rw [q] <;>
      simp (config := { decide := true }) [Fin.ext_iff, hr]
    all_goals congr 1 <;> apply Fin.ext <;> omega
  · intro r hr h13 h15
    rw [q]
    simp only [show r ≠ 15 from fun h => h15 (congrArg Fin.val h),
      show r ≠ 13 from fun h => h13 (congrArg Fin.val h), ite_false]
    have h4 : r ≠ 4 := by intro h; have := congrArg Fin.val h; omega
    have h5 : r ≠ 5 := by intro h; have := congrArg Fin.val h; omega
    have h6 : r ≠ 6 := by intro h; have := congrArg Fin.val h; omega
    have h7 : r ≠ 7 := by intro h; have := congrArg Fin.val h; omega
    simp [h4, h5, h6, h7]
  · rw [← hF]; simp [M0Crypto.Armv6M.State.setReg, loadRegs_mem]
end M0Crypto.Release.Poly1305Finish
