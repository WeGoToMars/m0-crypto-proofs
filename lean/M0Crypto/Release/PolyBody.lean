import M0Crypto.Release.PolyFold
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option Elab.async false
namespace M0Crypto.Release.PolyBlocks
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.PolyMac (v64)
open M0Crypto.Spec.AEAD (p)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

theorem addMsg_ptrs (s : State) :
    (execAll addMsg s).regs 7 = s.regs 7 ∧ (execAll addMsg s).regs 12 = s.regs 12 ∧
    (execAll addMsg s).regs 13 = s.regs 13 := by
  exact ⟨execAll_regs_other _ _ _ (by decide) (by decide),
    execAll_regs_other _ _ _ (by decide) (by decide), execAll_regs_other _ _ _ (by decide) (by decide)⟩

theorem addMsg_mem (s : State) :
    (execAll addMsg s).mem = write32 s.mem (slot (s.regs 13) slotMsg) (s.regs 6) := by
  simp (config := { decide := true }) [addMsg, execAll, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, slot, slotMsg]

theorem addMsg_sep (s : State) (h : Sep s) : Sep (execAll addMsg s) := by
  simpa only [Sep, (addMsg_ptrs s).1, (addMsg_ptrs s).2.2] using h

theorem addMsg_cw (s : State) (h : Sep s) (j : Nat) (hj : j < 16) :
    cw (execAll addMsg s) j = cw s j := by
  simp only [cw, (addMsg_ptrs s).1, addMsg_mem, cw_write s h slotMsg (by decide) _ j hj]

def rval (s : State) : Nat := PolyArith.val4 (cw s 5) (cw s 6) (cw s 7) (cw s 8)

def KeyOK (s : State) : Prop :=
  (cw s 5 < 2^28 ∧ cw s 6 < 2^28 ∧ cw s 7 < 2^28 ∧ cw s 8 < 2^28) ∧
  (cw s 6 % 4 = 0 ∧ cw s 7 % 4 = 0 ∧ cw s 8 % 4 = 0) ∧
  (cw s 9 = cw s 6 + cw s 6 / 4 ∧ cw s 10 = cw s 7 + cw s 7 / 4 ∧ cw s 11 = cw s 8 + cw s 8 / 4)

attribute [local irreducible] c0 c1 c2 c3 addMsg fold columns body

/-- The release block body implements one Poly1305 modular step and reestablishes
its lazy-reduction limb bound. No equations about intermediate machine values
are supplied by the caller. -/
theorem body_correct (s : State) (hs : Sep s) (hk : KeyOK s)
    (hh : (s.regs 14).toNat ≤ 4) (hp : (s.regs 12).toNat ≤ 1) :
    hval (execAll body s) % p =
      ((hval s + PolyArith.val4 (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat +
        2^128 * (s.regs 12).toNat) * rval s) % p ∧ hval (execAll body s) < 5 * 2^128 := by
  let H := execAll addMsg s
  have hS : Sep H := addMsg_sep s hs
  have hK : KeyOK H := by
    change KeyOK (execAll addMsg s)
    simp only [KeyOK]
    rw [addMsg_cw s hs 5 (by decide), addMsg_cw s hs 6 (by decide),
      addMsg_cw s hs 7 (by decide), addMsg_cw s hs 8 (by decide),
      addMsg_cw s hs 9 (by decide), addMsg_cw s hs 10 (by decide), addMsg_cw s hs 11 (by decide)]
    exact hk
  have hf := c3_cf H hS
  obtain ⟨f0, f1, f2⟩ := columns_slots H hS
  have hg : (gw (c3 H)).toNat = (v64 (c3 H) / 2^32 + (H.regs 14).toNat * cw H 5 % 2^32) % 2^32 := by
    rw [gw_nat, hf.regs 14 (by decide) (by decide), hf.words 5 (by decide)]
  have ho : hval (execAll fold (c3 H)) =
      (PolyArith.val4 (v64 (c0 H) % 2^32) (v64 (c1 H) % 2^32) (v64 (c2 H) % 2^32)
        (v64 (c3 H) % 2^32) + 2^128 * ((gw (c3 H)).toNat % 4) + (fw (c3 H)).toNat) % 2^160 := by
    rw [fold_h _ (hf.sep hS), f0, f1, f2]
  have h := PolyArith.block_arith (s.regs 8).toNat (s.regs 9).toNat (s.regs 10).toNat (s.regs 11).toNat
    (s.regs 14).toNat (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat (s.regs 12).toNat
    (cw H 5) (cw H 6) (cw H 7) (cw H 8) (cw H 9) (cw H 10) (cw H 11)
    (H.regs 8).toNat (H.regs 9).toNat (H.regs 10).toNat (H.regs 11).toNat (H.regs 14).toNat
    (v64 (c0 H)) (v64 (c1 H)) (v64 (c2 H)) (v64 (c3 H)) (gw (c3 H)).toNat (fw (c3 H)).toNat
    (hval (execAll fold (c3 H)))
    ⟨(s.regs 8).isLt, (s.regs 9).isLt, (s.regs 10).isLt, (s.regs 11).isLt, hh⟩
    ⟨(s.regs 0).isLt, (s.regs 1).isLt, (s.regs 2).isLt, (s.regs 3).isLt⟩ hp
    hK.1 hK.2.1 hK.2.2
    ⟨(H.regs 8).isLt, (H.regs 9).isLt, (H.regs 10).isLt, (H.regs 11).isLt, (H.regs 14).isLt⟩
    (addMsg_h s) (c0_v H) (c1_v H hS) (c2_v H hS) (c3_v H hS) hg (fw_nat _) ho
  change _ ∧ _ at h
  have w5 : cw H 5 = cw s 5 := addMsg_cw s hs 5 (by decide)
  have w6 : cw H 6 = cw s 6 := addMsg_cw s hs 6 (by decide)
  have w7 : cw H 7 = cw s 7 := addMsg_cw s hs 7 (by decide)
  have w8 : cw H 8 = cw s 8 := addMsg_cw s hs 8 (by decide)
  rw [w5, w6, w7, w8] at h
  simpa only [body, execAll_append, columns_eq, hval, rval] using h

end M0Crypto.Release.PolyBlocks
