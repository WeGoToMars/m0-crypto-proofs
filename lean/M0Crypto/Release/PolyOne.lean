import M0Crypto.Release.PolyBody
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace M0Crypto.Release.PolyBlocks
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.AEAD (p)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

def mp (s : State) : Word := read32 s.mem (slot (s.regs 13) slotMsg)

theorem load_hi (s : State) (r : Reg) (hr : 7 ≤ r.val) (h15 : r.val ≠ 15) :
    (loadState s).regs r = s.regs r := by
  have hr15 : r ≠ 15 := by intro h; apply h15; rw [h]; rfl
  have ht : (execAll testAlign s).regs r = s.regs r := by
    apply execAll_regs_other _ _ _ h15; simp [testAlign, Instr.dsts]; omega
  rw [loadState]
  try dsimp only
  split
  · have hl : listRegs 15#8 = [0, 1, 2, 3] := by decide
    rw [setReg_regs_ne _ _ _ _ hr15, execAll_regs_other _ _ _ h15 (by simp [loadA, Instr.dsts, hl]; omega)]
    rw [setReg_regs_ne _ _ _ _ hr15, ht]
  · rw [execAll_regs_other _ _ _ h15]
    · rw [setReg_regs_ne _ _ _ _ hr15, ht]
    · simp [loadU, ldle, Instr.dsts]; omega

theorem load_hval (s : State) : hval (loadState s) = hval s := by
  simp only [hval, load_hi s 8 (by decide) (by decide), load_hi s 9 (by decide) (by decide),
    load_hi s 10 (by decide) (by decide), load_hi s 11 (by decide) (by decide), load_hi s 14 (by decide) (by decide)]

theorem load_cw (s : State) (j : Nat) : cw (loadState s) j = cw s j := by
  simp only [cw, (load_props s).1, (load_props s).2.2.2]

theorem load_next (s : State) : (loadState s).regs 6 = mp s + 16#32 := by
  have ht := (test_regs s).1
  rw [loadState]
  try dsimp only
  split
  · rw [setReg_regs_ne _ 15 6 _ (by decide)]
    have hl : listRegs 15#8 = [0, 1, 2, 3] := by decide
    simp (config := { decide := true }) [loadA, execAll, Instr.next, Instr.exec,
      hl, bitCount, loadRegs, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, mp, ht, slotMsg]
  · simp only [loadU, execAll_append]
    have h6 : (execAll (ldle 0 0 ++ ldle 1 4 ++ ldle 2 8 ++ ldle 3 12)
      ((execAll testAlign s).setReg 15 (s.pc + BitVec.ofNat 32 loadUFrom))).regs 6 = mp s := by
      simp only [execAll_append, ldle_r6 _ 0 (by decide), ldle_r6 _ 1 (by decide),
        ldle_r6 _ 2 (by decide), ldle_r6 _ 3 (by decide), setReg_regs_ne _ 15 6 _ (by decide), ht]; rfl
    simp (config := { decide := true }) [execAll, Instr.next, Instr.exec, addFlags,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, h6, M0Crypto.Proofs.addWithCarry_fst]
    exact h6

attribute [local irreducible] body loadState

theorem one_cw (s : State) (hs : Sep s) (j : Nat) (hj : j < 16) : cw (oneBlock s) j = cw s j := by
  rw [cw, (one_props s).1]
  congr 1
  apply read32_congr
  intro k hk
  apply one_mem
  rintro ⟨o, ho, he⟩
  unfold Sep at hs
  have hp : slotPad ≤ frameWords := by decide
  apply ne_of_disj hs.1 hs.2.1 hs.2.2 (i := 4*j+k) (j := o) (by omega) (by omega)
  rwa [slot, ofNat_add_assoc] at he

theorem one_sep (s : State) (hs : Sep s) : Sep (oneBlock s) := by
  simpa only [Sep, (one_props s).1, (one_props s).2.2.1] using hs

theorem one_key (s : State) (hs : Sep s) (hk : KeyOK s) : KeyOK (oneBlock s) := by
  unfold KeyOK
  rw [one_cw s hs 5 (by decide), one_cw s hs 6 (by decide), one_cw s hs 7 (by decide),
    one_cw s hs 8 (by decide), one_cw s hs 9 (by decide), one_cw s hs 10 (by decide), one_cw s hs 11 (by decide)]
  exact hk

theorem one_hval (s : State) : hval (oneBlock s) = hval (execAll body (loadState s)) := by
  unfold oneBlock hval
  simp only [execAll_regs_other dec _ 8 (by decide) (by decide),
    execAll_regs_other dec _ 9 (by decide) (by decide), execAll_regs_other dec _ 10 (by decide) (by decide),
    execAll_regs_other dec _ 11 (by decide) (by decide), execAll_regs_other dec _ 14 (by decide) (by decide)]

/-- One full machine loop iteration agrees with one modular message step. -/
theorem one_correct (s : State) (hs : Sep s) (hk : KeyOK s)
    (hh : (s.regs 14).toNat ≤ 4) (hp : (s.regs 12).toNat ≤ 1) :
    hval (oneBlock s) % p = PolySpec.step (rval s) (s.regs 12).toNat (hval s)
      (Ctx.bytesAt s.mem (mp s) 16) ∧ hval (oneBlock s) < 5 * 2^128 := by
  have hl : Sep (loadState s) := by
    simpa only [Sep, (load_props s).1, (load_props s).2.2.1] using hs
  have hk' : KeyOK (loadState s) := by simpa only [KeyOK, load_cw] using hk
  have h := body_correct (loadState s) hl hk'
    (by rw [load_hi s 14 (by decide) (by decide)]; exact hh)
    (by rw [(load_props s).2.1]; exact hp)
  rw [← one_hval] at h
  have l0 : (loadState s).regs 0 = read32 s.mem (slot (mp s) 0) := load_words s 0 (by decide)
  have l1 : (loadState s).regs 1 = read32 s.mem (slot (mp s) 1) := load_words s 1 (by decide)
  have l2 : (loadState s).regs 2 = read32 s.mem (slot (mp s) 2) := load_words s 2 (by decide)
  have l3 : (loadState s).regs 3 = read32 s.mem (slot (mp s) 3) := load_words s 3 (by decide)
  rw [l0, l1, l2, l3] at h
  simpa only [load_hval, (load_props s).2.1, rval, load_cw, PolySpec.step,
    PolySpec.leNat_bytesAt16, slot, Nat.mul_comm, Nat.reduceMul, BitVec.add_zero] using h

theorem body_ptr (s : State) :
    read32 (execAll body s).mem (slot (s.regs 13) slotMsg) = s.regs 6 := by
  have ht : frameWB 4 (columns ++ fold) = true := by cbv
  have hf : (columns ++ fold).all Instr.falls = true := by cbv
  have hr := (addMsg_ptrs s).2.2
  have hsm : 4 ≤ slotMsg ∧ slotMsg < 16 := by decide
  have hm : read32 (execAll (columns ++ fold) (execAll addMsg s)).mem (slot (s.regs 13) slotMsg) =
      read32 (execAll addMsg s).mem (slot (s.regs 13) slotMsg) := by
    apply read32_congr
    intro k hk
    apply frameWB_mem _ _ ht hf
    rw [hr]
    rintro ⟨o, ho, he⟩
    have := congrArg BitVec.toNat he
    simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  rw [body, List.append_assoc, execAll_append, hm, addMsg_mem,
    M0Crypto.Armv6M.read32_write32_same]

theorem one_mp (s : State) : mp (oneBlock s) = mp s + 16#32 := by
  have bsp : (execAll body (loadState s)).regs 13 = s.regs 13 :=
    (body_regs _).2.2.trans (load_props s).2.2.1
  rw [mp, (one_props s).2.2.1, oneBlock, (dec_props _).1, bsp,
    M0Crypto.Armv6M.read32_write32_slot _ _ _ slotCount slotMsg (by decide) (by decide),
    ite_eq_right (by decide : slotCount ≠ slotMsg)]
  rw [← (load_props s).2.2.1, body_ptr, load_next]

/-- Abstract one-step facts used by the loop induction, keeping the machine
state opaque to kernel conversion while its equality to execution is explicit. -/
structure StepResult (s t : State) : Prop where
  ctx : t.regs 7 = s.regs 7
  pad : t.regs 12 = s.regs 12
  sp : t.regs 13 = s.regs 13
  sep : Sep t
  key : KeyOK t
  words : ∀ j < 16, cw t j = cw s j
  ptr : mp t = mp s + 16#32
  mem : ∀ y, (¬ InFrame (s.regs 13) slotPad y) → t.mem y = s.mem y
  value : hval t % p = PolySpec.step (rval s) (s.regs 12).toNat (hval s) (Ctx.bytesAt s.mem (mp s) 16)
  bound : hval t < 5*2^128

theorem step_result (s : State) (hs : Sep s) (hk : KeyOK s)
    (hh : (s.regs 14).toNat ≤ 4) (hp : (s.regs 12).toNat ≤ 1) :
    ∃ t, oneBlock s = t ∧ StepResult s t := by
  refine ⟨oneBlock s, rfl, ?_⟩
  exact ⟨(one_props s).1, (one_props s).2.1, (one_props s).2.2.1, one_sep s hs,
    one_key s hs hk, one_cw s hs, one_mp s, one_mem s, (one_correct s hs hk hh hp).1,
    (one_correct s hs hk hh hp).2⟩

end M0Crypto.Release.PolyBlocks
