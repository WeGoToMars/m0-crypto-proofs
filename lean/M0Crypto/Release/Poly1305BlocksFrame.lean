import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305BlocksCode
import M0Crypto.Release.Poly1305BlocksCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-!
Call contract, stack layout, setup, context publication and return for
`m0c_poly1305_blocks`. The nonempty call writes h0..h4 only, in addition to its
64-byte stack window; the zero-block call writes only the saved-register area.
-/
namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Frame (saved listRegs_f0 listRegs_240 bitCount_f0)

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

structure BCtx where
  base : Word
  sp0 : Word
  ctx : Word
  msg : Word
  count : Word
  pad : Word
  m0 : Mem
  regs0 : Reg → Word
namespace BCtx
def fp (c : BCtx) : Word := c.sp0 - 64#32
def mP (c : BCtx) : Mem :=
  storeWords (storeWords c.m0 (c.sp0 - 20#32)
    [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])
    (c.sp0 - 36#32) [c.regs0 8, c.regs0 9, c.regs0 10, c.regs0 11]
def Wr (c : BCtx) (y : Word) : Prop := InFrame c.fp 16 y ∨ (c.count ≠ 0#32 ∧ InFrame c.ctx 5 y)
end BCtx
/-- The blocks path's writes fit in the caller's frame `BCtx.Wr` (`InFrame c.fp 16`). -/
theorem belowPadBytes_le_fp : belowPadBytes ≤ 4 * 16 := by decide
structure BValid (c : BCtx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 64 ≤ c.sp0.toNat
  ctx4 : c.ctx.toNat % 4 = 0
  codeS : Disj c.base Artifacts.Release.size c.fp 64
  codeC : Disj c.base Artifacts.Release.size c.ctx 64
  ctxS : Disj c.ctx 64 c.fp 64
  msgS : Disj c.msg (16 * c.count.toNat) c.fp 64
  code : CodeAt c.m0 c.base B
structure BEntry (c : BCtx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 entryAt
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.ctx
  r1 : c.regs0 1 = c.msg
  r2 : c.regs0 2 = c.count
  r3 : c.regs0 3 = c.pad

theorem fp_toNat {c : BCtx} (hv : BValid c) : c.fp.toNat = c.sp0.toNat - 64 := by
  have := hv.spLo; simp [BCtx.fp, BitVec.toNat_sub]; omega
theorem fp4 {c : BCtx} (hv : BValid c) : c.fp.toNat % 4 = 0 := by
  have := hv.sp8; rw [fp_toNat hv]; omega

theorem popAt_eq : popAt = epilogueAt + seqSize epilogue := by
  unfold popAt popFrom epilogueAt; omega

theorem blocks_pop_at : instrAt B popAt = some (.pop 0xf0 true) := by decide +kernel

theorem blocks_ret (c : BCtx) (hv : BValid c) (Wr : Word → Prop) (s : State)
    (hpc : s.pc = c.base + BitVec.ofNat 32 epilogueAt) (hsp : s.regs 13 = c.fp)
    (hsv : ∀ i < 9, read32 s.mem (slot c.fp (7 + i)) = saved c.regs0 i)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base Wr s fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r) ∧
      (∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → t.regs r = s.regs r) ∧ t.mem = s.mem := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hfp4 := fp4 hv
  have sv : ∀ i, i < 9 → read32 s.mem (c.fp + BitVec.ofNat 32 (frameBytes + 4 * i)) = saved c.regs0 i := by
    intro i hi; have := hsv i hi; rw [Frame.slot_eq, show 4 * (7 + i) = frameBytes + 4 * i by simp only [frameBytes, frameWords]; omega] at this; exact this
  have sv0 := sv 0 (by omega); have sv1 := sv 1 (by omega); have sv2 := sv 2 (by omega)
  have sv3 := sv 3 (by omega); have sv4 := sv 4 (by omega); have sv5 := sv 5 (by omega)
  have sv6 := sv 6 (by omega); have sv7 := sv 7 (by omega); have sv8 := sv 8 (by omega)
  simp only [saved, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8
  apply Reach.block hb2 epilogue epilogueAt hpc (by decide +kernel) epilogue_at (by decide)
  · simp [alignedAll, epilogue, Instr.next, Instr.exec, Instr.accesses, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, bitCount_f0, listRegs_f0, wordAccesses, List.range_succ, Access.aligned,
      hsp, BitVec.toNat_add, M0Crypto.Armv6M.State.pc]
    omega
  · intro e he y ⟨a, ha, hw, _⟩
    simp only [traceAll, epilogue, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Instr.accesses, wordAccesses] at ha <;> (try obtain ⟨_, _, rfl⟩ := ha) <;> simp_all
  simp only [frameBytes, frameWords, Nat.reduceMul, Nat.reduceAdd] at sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8
  have q : ∀ r : Reg, (execAll epilogue s).regs r = (if r = 13 then c.fp + 44#32 else if r = 15 then c.base + BitVec.ofNat 32 popAt
      else if r = 4 then c.regs0 8 else if r = 5 then c.regs0 9 else if r = 6 then c.regs0 10
      else if r = 7 then c.regs0 11 else if r = 8 then c.regs0 8 else if r = 9 then c.regs0 9
      else if r = 10 then c.regs0 10 else if r = 11 then c.regs0 11 else s.regs r) := by
    intro r
    by_cases h15 : r = 15
    · subst h15
      show (execAll epilogue s).pc = _
      rw [execAll_pc epilogue s (by decide), hpc, ofNat_add_assoc, ← popAt_eq]
      simp (config := { decide := true })
    simp (config := { decide := true }) [epilogue, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      bitCount_f0, listRegs_f0, listRegs_240, loadRegs, hsp, BitVec.add_assoc, sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7,
      LowReg.toReg, M0Crypto.Armv6M.State.pc, hpc, Instr.size, bitCount, frameWords]
    by_cases h4 : r = 4; · subst h4; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h5 : r = 5; · subst h5; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h6 : r = 6; · subst h6; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h7 : r = 7; · subst h7; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h8 : r = 8; · subst h8; simp (config := { decide := true })
    by_cases h9 : r = 9; · subst h9; simp (config := { decide := true })
    by_cases h10 : r = 10; · subst h10; simp (config := { decide := true })
    by_cases h11 : r = 11; · subst h11; simp (config := { decide := true })
    by_cases h13 : r = 13; · subst h13; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    simp only [h4, h5, h6, h7, h8, h9, h10, h11, h13, h15, ite_false]
    repeat' split
    all_goals first
      | rfl
      | (rename_i h; exfalso; first
          | exact h7 (h.trans (by decide)) | exact h6 (h.trans (by decide))
          | exact h5 (h.trans (by decide)) | exact h4 (h.trans (by decide)))
  have hm : (execAll epilogue s).mem = s.mem := execAll_mem epilogue s (by decide)
  generalize ht : execAll epilogue s = t at q hm
  have t13 : t.regs 13 = c.fp + 44#32 := by rw [q]; rfl
  have t15 : t.pc = c.base + BitVec.ofNat 32 popAt := by
    show t.regs 15 = _; rw [q]; rfl
  have hsp1 : t.regs 13 + BitVec.ofNat 32 (4 * bitCount 0xf0) = c.fp + 60#32 := by
    rw [t13, bitCount_f0, BitVec.add_assoc]; rfl
  obtain ⟨t', hex⟩ : ∃ t', (Instr.pop 0xf0 true).exec t = .ok t' := by
    simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, hm, sv8, hlr, ite_true]
    exact ⟨_, rfl⟩
  have hex' := hex
  simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, hm, sv8, hlr, ite_true, Except.ok.injEq] at hex'
  subst hex'
  apply Reach.step hb2 popAt _ t15 (by decide +kernel) blocks_pop_at (by rw [B_len]; decide +kernel)
    (by simp [Instr.accesses, wordAccesses, List.range_succ, Access.aligned, bitCount_f0,
          M0Crypto.Armv6M.State.sp, t13, BitVec.toNat_add]; exact ⟨fun _ _ => by omega, by omega⟩)
    hex (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses, wordAccesses] at ha
            obtain ⟨_, _, rfl⟩ := ha; cases hw)
  apply Reach.done
  generalize hF : (((loadRegs (t.setReg 15 (t.pc + BitVec.ofNat 32 (Instr.pop 240 true).size)) (t.regs 13)
      (List.map LowReg.toReg (listRegs 240))).setReg 13 (t.regs 13 + BitVec.ofNat 32 (4 * (bitCount 240 + true.toNat)))).setReg
      15 (c.regs0 14 &&& ~~~1#32)) = F
  have qF : ∀ r : Reg, F.regs r = (if r = 15 then c.regs0 14 &&& ~~~1#32 else if r = 13 then c.fp + 64#32
      else if r = 4 then c.regs0 4 else if r = 5 then c.regs0 5 else if r = 6 then c.regs0 6
      else if r = 7 then c.regs0 7 else t.regs r) := by
    intro r; rw [← hF]
    simp (config := { decide := true }) only [M0Crypto.Armv6M.State.setReg, listRegs_240, List.map, loadRegs,
      LowReg.toReg, t13, bitCount_f0, hm, BitVec.add_assoc, BitVec.reduceAdd, sv4, sv5, sv6, sv7, Bool.toNat_true,
      show bitCount 240 = 4 from bitCount_f0, Nat.reduceAdd, Nat.reduceMul, M0Crypto.Armv6M.State.pc]
    by_cases h15 : r = 15; · subst h15; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h13 : r = 13; · subst h13; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h4 : r = 4; · subst h4; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h5 : r = 5; · subst h5; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h6 : r = 6; · subst h6; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h7 : r = 7; · subst h7; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    simp only [h4, h5, h6, h7, h13, h15, ite_false]
    rw [loadRegs_regs_other _ _ _ _ (by
      simp only [listRegs_240, listRegs_f0, List.map, List.mem_cons, List.not_mem_nil, or_false]
      rcases r with ⟨v, hv⟩; simp only [Fin.ext_iff] at h4 h5 h6 h7; simp at h4 h5 h6 h7 ⊢; omega)]
    simp [h15]
  have hFm : F.mem = s.mem := by rw [← hF]; simp [M0Crypto.Armv6M.State.setReg, loadRegs_mem, hm]
  refine ⟨by show F.regs 15 = _; rw [qF]; rfl, by rw [qF]; simp only [BCtx.fp]; simp (config := { decide := true }); bv_omega,
    ?_, ?_, hFm⟩
  · intro r h1 h2
    have hr : r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 := by
      rcases r with ⟨v, hv⟩; simp only [Fin.ext_iff]; simp at h1 h2 ⊢; omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [qF] <;>
      simp (config := { decide := true }) [q]
  · intro r hr
    have : r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 13 ∧ r ≠ 15 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11 := by
      rcases r with ⟨v, hv⟩; simp only [ne_eq, Fin.ext_iff]; simp at hr ⊢; omega
    obtain ⟨n4, n5, n6, n7, n13, n15, n8, n9, n10, n11⟩ := this
    rw [qF, q]
    simp only [n4, n5, n6, n7, n8, n9, n10, n11, n13, n15, ite_false]

/-- At the call boundary only h0..h4 of the context are replaced. -/
def publishMem (s : State) : Mem :=
  storeWords (storeWords s.mem (s.regs 7)
    [s.regs 8, s.regs 9, s.regs 10, s.regs 11, s.regs 14])
    (s.regs 13) (List.replicate frameWords 0#32)

theorem publish_effect (s : State) :
    (execAll publish s).mem = publishMem s ∧
    (∀ r : Reg, r.val < 4 ∨ r.val = 12 ∨ r.val = 14 → (execAll publish s).regs r = 0#32) ∧
    (execAll publish s).regs 13 = s.regs 13 := by
  refine ⟨?_, ?_, execAll_regs_other _ _ _ (by decide) (by decide)⟩
  · simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, execAll, publish, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp,
      publishMem, storeWords, List.replicate_succ, BitVec.add_assoc,
      slotT0, slotT1, slotT2, slotT3, slotMsg, slotCount, slotPad,
      frameWords, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
  · intro r hr
    rcases (by rcases r with ⟨r, hr'⟩; simp only [Fin.ext_iff] at *; simp at *; omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 12 ∨ r = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, execAll, publish,
        frameWords, List.range_zero, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg]

theorem publish_run {base : Word} (hb : base.toNat % 4 = 0) (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 publishAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0) :
    Reach base (fun y => InFrame (s.regs 13) frameWords y ∨ InFrame (s.regs 7) 5 y) s
      (fun t => t = execAll publish s) := by
  apply Reach.block (by omega) publish publishAt hp (by decide +kernel) segments_at.2.2.2.2.2 (by decide)
  · simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, alignedAll, publish,
      frameWords, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, Access.aligned, BitVec.toNat_add]
    omega
  · intro e he y ⟨a, ha, hw, k, hk, hy⟩
    have hfw : 7 ≤ frameWords := by decide
    simp only [traceAll, publish, frameWords, List.range_succ, List.range_zero, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, Instr.accesses, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, MemOp.isLoad,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp,
        slotT0, slotT1, slotT2, slotT3, slotMsg, slotCount, slotPad] at ha
    all_goals subst ha; simp at hk hy; rw [hy]
    all_goals first
      | (left; refine ⟨0+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨4+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨8+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨12+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨16+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨20+k, by omega, ?_⟩; bv_omega)
      | (left; refine ⟨24+k, by omega, ?_⟩; bv_omega)
      | (right; refine ⟨0+k, by omega, ?_⟩; bv_omega)
      | (right; refine ⟨4+k, by omega, ?_⟩; bv_omega)
      | (right; refine ⟨8+k, by omega, ?_⟩; bv_omega)
      | (right; refine ⟨12+k, by omega, ?_⟩; bv_omega)
      | (right; refine ⟨16+k, by omega, ?_⟩; bv_omega)
  · exact Reach.done rfl

theorem mP_saved (c : BCtx) (hv : BValid c) (i : Nat) (hi : i < 9) :
    read32 c.mP (slot c.fp (7 + i)) = saved c.regs0 i := by
  have hs : c.sp0 - 36#32 = c.fp + BitVec.ofNat 32 frameBytes := by
    simp only [BCtx.fp, frameBytes, frameWords]; bv_omega
  simp only [BCtx.mP]
  by_cases h4 : i < 4
  · rw [hs, Frame.slot_eq, show 4 * (7 + i) = frameBytes + 4 * i by simp only [frameBytes, frameWords]; omega, ← ofNat_add_assoc,
      Frame.read32_storeWords_same _ _ _ i (by simp; omega) (by simp)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [Frame.read32_congr (m := storeWords c.m0 (c.sp0 - 20#32)
        [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])]
    · have h20 : c.sp0 - 20#32 = c.fp + BitVec.ofNat 32 44 := by
        simp only [BCtx.fp]; bv_omega
      rw [h20, Frame.slot_eq, show 4 * (7 + i) = 44 + 4 * (i - 4) by omega, ← ofNat_add_assoc,
        Frame.read32_storeWords_same _ _ _ (i - 4) (by simp; omega) (by simp)]
      rcases (by omega : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp only [frameBytes, frameWords] at hs
      intro k hk
      rw [hs]
      apply storeWords_other
      intro j q hj hq e
      have hfp := fp_toNat hv
      have := hv.spLo
      have := congrArg BitVec.toNat e
      simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      simp at hj
      omega


theorem setup_effect (s : State) :
    (execAll setup s).regs 7 = s.regs 0 ∧ (execAll setup s).regs 12 = s.regs 3 ∧
    (execAll setup s).regs 13 = s.regs 13 ∧
    (execAll setup s).mem = write32 (write32 s.mem (slot (s.regs 13) slotMsg) (s.regs 1))
      (slot (s.regs 13) slotCount) (s.regs 2) := by
  simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, execAll, setup, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, lslC, slot, slotMsg, slotCount]

theorem setup_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 setupAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 0).toNat % 4 = 0)
    (hw : ∀ o < belowPadBytes, Wr (s.regs 13 + BitVec.ofNat 32 o)) :
    Reach base Wr s (fun t => t = execAll setup s) := by
  apply Reach.block (by omega) setup setupAt hp (by decide) setup_at (by decide)
  · simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, alignedAll, setup, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, lslC, Access.aligned, BitVec.toNat_add]
    omega
  · intro e he y hy
    obtain ⟨o, ho, rfl⟩ := frameWB_writes setup s (show frameWB slotPad setup = true from by decide) e he y hy
    exact hw o ho
  · exact Reach.done rfl

theorem prologue_effect (c : BCtx) (s : State) (he : BEntry c s) :
    let t := execAll prologue s
    t.mem = c.mP ∧ t.regs 13 = c.fp ∧ t.regs 0 = c.ctx ∧ t.regs 1 = c.msg ∧
    t.regs 2 = c.count ∧ t.regs 3 = c.pad ∧ t.z = (c.count == 0#32) := by
  simp (config := { decide := true }) [execAll, prologue, Instr.next, Instr.exec, addFlags,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg,
    listRegs_f0, listRegs_240, bitCount_f0, bitCount, he.mem, he.regs, he.sp,
    he.r0, he.r1, he.r2, he.r3, BCtx.mP, BCtx.fp, M0Crypto.Release.sub_flags,
    BitVec.sub_sub]
  change ((M0Crypto.Armv6M.addWithCarry c.count (~~~0#32) true).1 == 0#32) = _
  rw [M0Crypto.Release.sub_flags, BitVec.sub_zero]

theorem prologue_run (c : BCtx) (hv : BValid c) (s : State) (he : BEntry c s) :
    Reach c.base c.Wr s (fun t => t = execAll prologue s) := by
  have hp : s.pc = c.base + BitVec.ofNat 32 entryAt := by show s.regs 15 = _; rw [he.regs, he.pc]
  have hs : s.regs 13 = c.sp0 := by rw [he.regs, he.sp]
  have hs4 : c.sp0.toNat % 4 = 0 := by have := hv.sp8; omega
  apply Reach.block (by have := hv.base4; omega) prologue entryAt hp (by decide) prologue_at (by decide)
  · simp (config := { decide := true }) [alignedAll, prologue, Instr.next, Instr.exec, Instr.accesses,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, wordAccesses,
      bitCount_f0, bitCount, listRegs_f0, listRegs_240, List.range_succ, Access.aligned,
      hs, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  · intro e hevent y ⟨a, ha, hw, k, hk, hy⟩
    simp only [traceAll, prologue, List.mem_cons, List.not_mem_nil, or_false] at hevent
    rcases hevent with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := { decide := true }) [Instr.accesses, wordAccesses, bitCount_f0,
        bitCount, listRegs_f0, listRegs_240, M0Crypto.Armv6M.State.sp,
        Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, hs] at ha
    all_goals
      obtain ⟨j, hj, rfl⟩ := ha
      left
      dsimp only [Access.width] at hk
      dsimp only [Access.addr] at hy
      first
      | (refine ⟨44 + 4*j + k, by omega, ?_⟩; rw [hy]; simp only [BCtx.fp]; bv_omega)
      | (refine ⟨frameBytes + 4*j + k, by simp only [frameBytes, frameWords]; omega, ?_⟩; rw [hy]; simp only [BCtx.fp, frameBytes, frameWords]; bv_omega)
  · exact Reach.done rfl

end M0Crypto.Release.Poly1305Blocks
