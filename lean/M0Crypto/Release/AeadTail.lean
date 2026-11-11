import M0Crypto.Release.AeadWin
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
`MAC_PADDED` tail, offsets `m + 0xe` to `m + 0x3c`: when `n % 16 ≠ 0`, zero the
first 16 bytes of `BLK`, copy the `n % 16` trailing message bytes into it, and
absorb it as one block with pad 1.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.PolyBlocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK wordAt)
open M0Crypto.Spec.AEAD (p)

namespace MacEnv
variable {base A d n : Word} {M : Mem} (he : MacEnv base A d n M)
include he

theorem key_eq {m1 m2 : Mem} (hf : ∀ y, ¬ MacWr A y → m1 y = m2 y) :
    keyAt m1 (A + 8#32) = keyAt m2 (A + 8#32) := by
  unfold keyAt
  rw [he.ctx_word hf 5 (by decide) (by decide), he.ctx_word hf 6 (by decide) (by decide),
    he.ctx_word hf 7 (by decide) (by decide), he.ctx_word hf 8 (by decide) (by decide)]

theorem keyOK {m1 m2 : Mem} (hf : ∀ y, ¬ MacWr A y → m1 y = m2 y) (hk : keyAtOK m2 (A + 8#32)) :
    keyAtOK m1 (A + 8#32) := by
  unfold keyAtOK at hk ⊢
  rw [he.ctx_word hf 5 (by decide) (by decide), he.ctx_word hf 6 (by decide) (by decide),
    he.ctx_word hf 7 (by decide) (by decide), he.ctx_word hf 8 (by decide) (by decide),
    he.ctx_word hf 9 (by decide) (by decide), he.ctx_word hf 10 (by decide) (by decide),
    he.ctx_word hf 11 (by decide) (by decide)]
  exact hk

end MacEnv

/-! ## Straight-line effects -/

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5 M0Crypto.Proofs.toReg_6

theorem macC_effect (s : State) :
    (execAll macC s).regs 6 = 15#32 &&& s.regs 5 ∧ (execAll macC s).z = (15#32 &&& s.regs 5 == 0#32) ∧
    (execAll macC s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 6 → r.val ≠ 15 → (execAll macC s).regs r = s.regs r) := by
  refine ⟨?_, ?_, rfl, fun r h6 h15 => execAll_regs_other _ _ r h15 (by simp [macC, Instr.dsts, Fin.ext_iff]; omega)⟩ <;>
  simp [macC, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg]

theorem macD_effect (s : State) :
    (execAll macD s).regs 4 = s.regs 4 + ((s.regs 5 >>> 4) <<< 4) ∧
    (execAll macD s).regs 1 = s.regs 13 + 72#32 ∧ (execAll macD s).regs 2 = 0#32 ∧
    (execAll macD s).mem = write32 (write32 (write32 (write32 s.mem (s.regs 13 + 72#32) 0#32)
      (s.regs 13 + 76#32) 0#32) (s.regs 13 + 80#32) 0#32) (s.regs 13 + 84#32) 0#32 ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 4 → r.val ≠ 15 →
      (execAll macD s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, fun r h0 h1 h2 h4 h15 => execAll_regs_other _ _ r h15
    (by simp [macD, Instr.dsts, Fin.ext_iff, h0, h1, h2]; omega)⟩ <;>
  simp [macD, execAll, Instr.next, Instr.exec, lsrC, lslC, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, M0Crypto.Release.add_flags]

theorem macL_effect (s : State) :
    (execAll macL s).mem = write8 s.mem (s.regs 1 + s.regs 2) (read8 s.mem (s.regs 4 + s.regs 2)) ∧
    (execAll macL s).regs 2 = s.regs 2 + 1#32 ∧
    (execAll macL s).z = (s.regs 2 + 1#32 - s.regs 6 == 0#32) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 2 → r.val ≠ 15 → (execAll macL s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, fun r h0 h2 h15 => execAll_regs_other _ _ r h15
    (by simp [macL, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h2])⟩ <;>
  simp [macL, execAll, Instr.next, Instr.exec, Instr.exec.memOp, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Release.add_flags,
    M0Crypto.Release.sub_flags]

theorem macE_effect (s : State) :
    (execAll macE s).regs 0 = s.regs 13 + 8#32 ∧ (execAll macE s).regs 2 = 1#32 ∧
    (execAll macE s).regs 3 = 1#32 ∧ (execAll macE s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 15 → (execAll macE s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, rfl, fun r h0 h2 h3 h15 => execAll_regs_other _ _ r h15
    (by simp [macE, Instr.dsts, Fin.ext_iff, h0, h2]; omega)⟩ <;>
  simp [macE, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp]

/-! ## Memory facts -/

theorem write32_zero (m : Mem) (a x : Word) :
    write32 m a 0#32 x = if x = a ∨ x = a + 1#32 ∨ x = a + 2#32 ∨ x = a + 3#32 then 0#8 else m x := by
  by_cases h0 : x = a <;> by_cases h1 : x = a + 1#32 <;> by_cases h2 : x = a + 2#32 <;>
    by_cases h3 : x = a + 3#32 <;> simp [write32, h0, h1, h2, h3] <;> rfl

theorem write32_zero_pass (m : Mem) (a x : Word) (h : m x = 0#8) : write32 m a 0#32 x = 0#8 := by
  rw [write32_zero]; split <;> first | rfl | exact h

theorem write32_zero_hit (m : Mem) (a : Word) (k : Nat) (hk : k < 4) :
    write32 m a 0#32 (a + BitVec.ofNat 32 k) = 0#8 := by
  rw [write32_zero, if_pos]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · left; simp
  · right; left; rfl
  · right; right; left; rfl
  · right; right; right; rfl

theorem blk_addr (A : Word) (w k : Nat) :
    A + BitVec.ofNat 32 (72 + 4 * w) + BitVec.ofNat 32 k = A + 72#32 + BitVec.ofNat 32 (4 * w + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- After `macD`, the 16 bytes of `BLK` are zero and nothing else changed. -/
theorem zero16 (m : Mem) (A : Word) :
    let z := write32 (write32 (write32 (write32 m (A + 72#32) 0#32) (A + 76#32) 0#32) (A + 80#32) 0#32)
      (A + 84#32) 0#32
    (∀ j < 16, z (A + 72#32 + BitVec.ofNat 32 j) = 0#8) ∧
    (∀ y, (∀ j < 16, y ≠ A + 72#32 + BitVec.ofNat 32 j) → z y = m y) := by
  intro z
  have e : ∀ w k, A + BitVec.ofNat 32 (72 + 4 * w) + BitVec.ofNat 32 k = A + 72#32 + BitVec.ofNat 32 (4 * w + k) :=
    blk_addr A
  constructor
  · intro j hj
    have hj' : A + 72#32 + BitVec.ofNat 32 j = A + BitVec.ofNat 32 (72 + 4 * (j / 4)) + BitVec.ofNat 32 (j % 4) := by
      rw [e]; congr 2; omega
    rw [hj']
    have hk := Nat.mod_lt j (show 4 > 0 by decide)
    rcases (by omega : j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3) with h | h | h | h <;> rw [h]
    · exact write32_zero_pass _ _ _ (write32_zero_pass _ _ _ (write32_zero_pass _ _ _ (write32_zero_hit _ _ _ hk)))
    · exact write32_zero_pass _ _ _ (write32_zero_pass _ _ _ (write32_zero_hit _ _ _ hk))
    · exact write32_zero_pass _ _ _ (write32_zero_hit _ _ _ hk)
    · exact write32_zero_hit _ _ _ hk
  · intro y hy
    have w : ∀ w < 4, ∀ k < 4, y ≠ A + BitVec.ofNat 32 (72 + 4 * w) + BitVec.ofNat 32 k := fun w hw k hk => by
      rw [e]; exact hy _ (by omega)
    simp only [z]
    rw [write32_other' _ _ _ _ (w 3 (by decide)), write32_other' _ _ _ _ (w 2 (by decide)),
      write32_other' _ _ _ _ (w 1 (by decide)), write32_other' _ _ _ _ (w 0 (by decide))]

theorem byte_copy (b : BitVec 8) : (b.setWidth 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, show i < 32 by omega]

end M0Crypto.Release.Aead
