import M0Crypto.Release.Frame
import M0Crypto.Release.ChaCha20Layout

set_option linter.unusedSimpArgs false

/-!
The epilogue of `m0c_chacha20_xor` (offset `epiOff`): `add sp, #140; pop {r4-r7};
mov r8-r11, r4-r7; pop {r4-r7, pc}`, and the two return-value entries
`.Lreturn_ok` (`zOff`) and `.Lerr_counter` (`errOff`).
-/

namespace M0Crypto.Release.ChaCha20Return

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Layout (epiOff popOff chFrameWords chFrameBytes chStackBytes slotSaved)

set_option maxRecDepth 100000

theorem epi_at : seqAt B epiOff epi = true := by decide
theorem pop_at : instrAt B popOff = some (.pop 0xf0 true) := by decide
/-- Closed bridges from the layout names to the frame and epilogue values they determine. -/
theorem ssv35 : slotSaved = 35 := by decide
theorem epi_pop : popOff = epiOff + seqSize epi := rfl

theorem fp_toNat {c : Ctx} (hv : Valid c) : c.fp.toNat = c.sp0.toNat - chStackBytes := by
  have := hv.spLo; have := ChaCha20Layout.chStackBytes_eq
  simp only [Ctx.fp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem fp4 {c : Ctx} (hv : Valid c) : c.fp.toNat % 4 = 0 := by
  have := hv.sp8; have := ChaCha20Layout.chStackBytes_eq; rw [fp_toNat hv]; omega

/-- The epilogue from `epiOff` restores r4-r11 and SP and returns to the saved LR. -/
theorem ret (c : Ctx) (hv : Valid c) (Wr : Word → Prop) (s : State)
    (hpc : s.pc = c.base + BitVec.ofNat 32 epiOff) (hsp : s.regs 13 = c.fp)
    (hsv : ∀ i < 9, read32 s.mem (slot c.fp (slotSaved + i)) = saved c.regs0 i)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base Wr s fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = c.regs0 r) ∧
      (∀ r : Reg, r.val < 4 ∨ r.val = 12 → t.regs r = s.regs r) ∧ t.mem = s.mem := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hfp4 := fp4 hv
  have sS := ssv35; have sB := ChaCha20Layout.chFrameBytes_eq; have b4 := bitCount_f0
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sv : ∀ i, i < 9 → read32 s.mem (c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * i)) = saved c.regs0 i := by
    intro i hi; have := hsv i hi; rw [slot_eq, show 4 * (slotSaved + i) = chFrameBytes + 4 * i by omega] at this; exact this
  have sv0 := sv 0 (by omega); have sv1 := sv 1 (by omega); have sv2 := sv 2 (by omega)
  have sv3 := sv 3 (by omega); have sv4 := sv 4 (by omega); have sv5 := sv 5 (by omega)
  have sv6 := sv 6 (by omega); have sv7 := sv 7 (by omega); have sv8 := sv 8 (by omega)
  simp only [saved, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8
  apply Reach.block hb2 epi epiOff hpc (by decide) epi_at (by decide)
  · simp [alignedAll, epi, Instr.next, Instr.exec, Instr.accesses, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, bitCount_f0, listRegs_f0, wordAccesses, List.range_succ, Access.aligned,
      hsp, BitVec.toNat_add, M0Crypto.Armv6M.State.pc]
    omega
  · intro e he y ⟨a, ha, hw, _⟩
    simp only [traceAll, epi, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Instr.accesses, wordAccesses] at ha <;> (try obtain ⟨_, _, rfl⟩ := ha) <;> simp_all
  simp only [Nat.reduceMul, Nat.reduceAdd, ChaCha20Layout.chFrameBytes_eq] at sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8
  have q : ∀ r : Reg, (execAll epi s).regs r = (if r = 13 then c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * bitCount 0xf0)
      else if r = 15 then c.base + BitVec.ofNat 32 popOff
      else if r = 4 then c.regs0 8 else if r = 5 then c.regs0 9 else if r = 6 then c.regs0 10
      else if r = 7 then c.regs0 11 else if r = 8 then c.regs0 8 else if r = 9 then c.regs0 9
      else if r = 10 then c.regs0 10 else if r = 11 then c.regs0 11 else s.regs r) := by
    intro r
    simp (config := { decide := true }) [epi, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      bitCount_f0, listRegs_f0, listRegs_240, loadRegs, hsp, BitVec.add_assoc, chFrameWords, ChaCha20Layout.chFrameBytes_eq, epi_pop, BitVec.ofNat_add, seqSize, Instr.size, sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7,
      LowReg.toReg, M0Crypto.Armv6M.State.pc, hpc, Instr.size, bitCount]
    by_cases h4 : r = 4; · subst h4; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h5 : r = 5; · subst h5; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h6 : r = 6; · subst h6; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h7 : r = 7; · subst h7; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h8 : r = 8; · subst h8; simp (config := { decide := true })
    by_cases h9 : r = 9; · subst h9; simp (config := { decide := true })
    by_cases h10 : r = 10; · subst h10; simp (config := { decide := true })
    by_cases h11 : r = 11; · subst h11; simp (config := { decide := true })
    by_cases h13 : r = 13; · subst h13; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h15 : r = 15
    · subst h15; have hpc' : s.regs 15 = c.base + BitVec.ofNat 32 epiOff := hpc
      simp (config := { decide := true }) [hpc', epi_pop, BitVec.ofNat_add, seqSize, Instr.size]; bv_omega
    simp only [h4, h5, h6, h7, h8, h9, h10, h11, h13, h15, ite_false]
    repeat' split
    all_goals first
      | rfl
      | (rename_i h; exfalso; first
          | exact h7 (h.trans (by decide)) | exact h6 (h.trans (by decide))
          | exact h5 (h.trans (by decide)) | exact h4 (h.trans (by decide)))
  have hm : (execAll epi s).mem = s.mem := execAll_mem epi s (by decide)
  generalize ht : execAll epi s = t at q hm
  have t13 : t.regs 13 = c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * bitCount 0xf0) := by rw [q]; rfl
  have t15 : t.pc = c.base + BitVec.ofNat 32 popOff := by
    show t.regs 15 = _; rw [q]; rfl
  have hsp1 : t.regs 13 + BitVec.ofNat 32 (4 * bitCount 0xf0) = c.fp + BitVec.ofNat 32 (chStackBytes - 4) := by
    rw [t13, bitCount_f0, BitVec.add_assoc, ChaCha20Layout.chFrameBytes_eq, ChaCha20Layout.chStackBytes_eq]; rfl
  obtain ⟨t', hex⟩ : ∃ t', (Instr.pop 0xf0 true).exec t = .ok t' := by
    simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, hm, sv8, hlr, ite_true, ChaCha20Layout.chStackBytes_eq, Nat.reduceSub]
    exact ⟨_, rfl⟩
  have hex' := hex
  simp only [Instr.exec, M0Crypto.Armv6M.State.sp, hsp1, hm, sv8, hlr, ite_true, Except.ok.injEq, ChaCha20Layout.chStackBytes_eq, Nat.reduceSub] at hex'
  subst hex'
  apply Reach.step hb2 popOff _ t15 (by decide) pop_at (by rw [B_len]; decide)
    (by simp [Instr.accesses, wordAccesses, List.range_succ, Access.aligned, bitCount_f0,
          M0Crypto.Armv6M.State.sp, t13, BitVec.toNat_add]; exact ⟨fun _ _ => by omega, by omega⟩)
    hex (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses, wordAccesses] at ha
            obtain ⟨_, _, rfl⟩ := ha; cases hw)
  apply Reach.done
  generalize hF : (((loadRegs (t.setReg 15 (t.pc + BitVec.ofNat 32 (Instr.pop 240 true).size)) (t.regs 13)
      (List.map LowReg.toReg (listRegs 240))).setReg 13 (t.regs 13 + BitVec.ofNat 32 (4 * (bitCount 240 + true.toNat)))).setReg
      15 (c.regs0 14 &&& ~~~1#32)) = F
  have qF : ∀ r : Reg, F.regs r = (if r = 15 then c.regs0 14 &&& ~~~1#32 else if r = 13 then c.fp + BitVec.ofNat 32 chStackBytes
      else if r = 4 then c.regs0 4 else if r = 5 then c.regs0 5 else if r = 6 then c.regs0 6
      else if r = 7 then c.regs0 7 else t.regs r) := by
    intro r; rw [← hF]
    simp (config := { decide := true }) only [M0Crypto.Armv6M.State.setReg, listRegs_240, List.map, loadRegs,
      LowReg.toReg, t13, bitCount_f0, ChaCha20Layout.chFrameBytes_eq, ChaCha20Layout.chStackBytes_eq, hm, BitVec.add_assoc, BitVec.reduceAdd, sv4, sv5, sv6, sv7, Bool.toNat_true,
      show bitCount 240 = 4 from bitCount_f0, Nat.reduceAdd, Nat.reduceMul, M0Crypto.Armv6M.State.pc]
    by_cases h15 : r = 15; · subst h15; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc]
    by_cases h13 : r = 13; · subst h13; simp (config := { decide := true }) [M0Crypto.Armv6M.State.setReg, listRegs_240, loadRegs, LowReg.toReg, sv4, sv5, sv6, sv7, BitVec.add_assoc, ChaCha20Layout.chFrameBytes_eq, ChaCha20Layout.chStackBytes_eq, t13, bitCount_f0]
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
  refine ⟨by show F.regs 15 = _; rw [qF]; rfl, by rw [qF]; simp only [Ctx.fp]; simp (config := { decide := true }); bv_omega,
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

/-! ## The memory after the prologue -/

theorem read32_storeWords_same (m : Mem) : ∀ (a : Word) (vs : List Word) (i : Nat) (hi : i < vs.length),
    vs.length ≤ 2 ^ 28 → read32 (storeWords m a vs) (a + BitVec.ofNat 32 (4 * i)) = vs[i] :=
  Frame.read32_storeWords_same m

theorem mP_other (c : Ctx) (y : Word) (hy : ∀ k < 36, y ≠ c.sp0 - BitVec.ofNat 32 36 + BitVec.ofNat 32 k) :
    c.mP y = c.m0 y := by
  simp only [Ctx.mP]
  rw [storeWords_other, storeWords_other]
  · intro i k hi hk e; simp at hi
    exact hy (16 + 4 * i + k) (by omega) (by rw [e]; bv_omega)
  · intro i k hi hk e; simp at hi
    exact hy (4 * i + k) (by omega) (by rw [e]; bv_omega)

theorem mP_saved (c : Ctx) (hv : Valid c) (i : Nat) (hi : i < 9) :
    read32 c.mP (slot c.fp (slotSaved + i)) = saved c.regs0 i := by
  have sS := ssv35; have sB := ChaCha20Layout.chFrameBytes_eq; have b4 := bitCount_f0; have sSB := ChaCha20Layout.chStackBytes_eq
  have hs : c.sp0 - BitVec.ofNat 32 20 - BitVec.ofNat 32 16 = c.fp + BitVec.ofNat 32 chFrameBytes := by
    simp only [Ctx.fp]; bv_omega
  simp only [Ctx.mP]
  by_cases h4 : i < 4
  · rw [hs, slot_eq, show 4 * (slotSaved + i) = chFrameBytes + 4 * i by omega, ← ofNat_add_assoc,
      read32_storeWords_same _ _ _ i (by simp; omega) (by simp)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [Frame.read32_congr (m := storeWords c.m0 (c.sp0 - BitVec.ofNat 32 20)
        [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])]
    · have h20 : c.sp0 - BitVec.ofNat 32 20 = c.fp + BitVec.ofNat 32 (chFrameBytes + 4 * bitCount 0xf0) := by
        simp only [Ctx.fp]; bv_omega
      rw [h20, slot_eq, show 4 * (slotSaved + i) = chFrameBytes + 4 * bitCount 0xf0 + 4 * (i - 4) by omega,
        ← ofNat_add_assoc c.fp (chFrameBytes + 4 * bitCount 0xf0) (4 * (i - 4)),
        read32_storeWords_same _ _ _ (i - 4) (by simp; omega) (by simp)]
      rcases (by omega : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro k hk
      rw [hs]
      apply storeWords_other
      intro j q hj hq e
      have hfp := fp_toNat hv
      have := hv.spLo
      have := congrArg BitVec.toNat e
      simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      simp at hj
      omega

/-- Words at or above the entry SP are unchanged by the prologue. -/
theorem mP_above (c : Ctx) (hv : Valid c) (j : Nat) (hj : c.sp0.toNat + j + 4 ≤ 2 ^ 32) :
    read32 c.mP (c.sp0 + BitVec.ofNat 32 j) = read32 c.m0 (c.sp0 + BitVec.ofNat 32 j) := by
  apply Frame.read32_congr
  intro k hk
  apply mP_other
  intro q hq e
  have := hv.spLo
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at this
  omega

end M0Crypto.Release.ChaCha20Return
