import M0Crypto.Release.AeadTail
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
The `MAC_PADDED` byte-copy loop at `m + macLOff`: copies `rem` bytes from `dq` into
`BLK` (`A + 72`), whose 16 bytes start out zero.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-- `BLK` holds the first `k` source bytes followed by zeros. -/
def BlkHas (A dq : Word) (M0 : Mem) (k : Nat) (m : Mem) : Prop :=
  ∀ j < 16, m (A + 72#32 + BitVec.ofNat 32 j) = if j < k then M0 (dq + BitVec.ofNat 32 j) else 0#8

def OutBlk (A y : Word) : Prop := ∀ j < 16, y ≠ A + 72#32 + BitVec.ofNat 32 j

theorem blk_ne (A : Word) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    A + 72#32 + BitVec.ofNat 32 j ≠ A + 72#32 + BitVec.ofNat 32 k := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem loop_flag (k rem : Nat) (hk : k < 16) (hr : rem < 16) :
    (BitVec.ofNat 32 k + 1#32 - BitVec.ofNat 32 rem == 0#32) = decide (k + 1 = rem) := by
  by_cases h : k + 1 = rem
  · subst h; simp [show (BitVec.ofNat 32 k + 1#32 : Word) = BitVec.ofNat 32 (k + 1) from by
      apply BitVec.eq_of_toNat_eq; simp]
  · rw [decide_eq_false h]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp [BitVec.toNat_sub, BitVec.toNat_add] at this; omega

/-- Target of a backward branch, proved algebraically (`omega` over `% 2^32` with a
large constant does not terminate in reasonable time here). -/
theorem back_target (a k : Nat) :
    BitVec.ofNat 32 (a + k) + 4#32 + (-(BitVec.ofNat 32 (k + 4))) = BitVec.ofNat 32 a := by
  rw [BitVec.ofNat_add, show (BitVec.ofNat 32 (k + 4)) = BitVec.ofNat 32 k + 4#32 from BitVec.ofNat_add _ _]
  rw [BitVec.neg_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 4#32, BitVec.sub_add_cancel,
    ← BitVec.sub_eq_add_neg, BitVec.sub_self, BitVec.add_zero]

theorem se_fa : (((brImm8 macBr2Off macLOff) ++ 0#1).signExtend 32 : BitVec 32) = -(BitVec.ofNat 32 (seqSize macL + 4)) := by decide +kernel

/-- **Copy loop.** -/
theorem mac_loop (base A dq : Word) (M0 : Mem) (R : Reg → Word) (m rem : Nat)
    (hseq : seqAt B (m + macLOff) macL = true) (hbr : instrAt B (m + macBr2Off) = some (.bcond 1 (brImm8 (m + macBr2Off) (m + macLOff))))
    (hb : base.toNat % 4 = 0) (hm : m % 2 = 0) (hmx : m + macSize ≤ Artifacts.Release.size) (hr : rem < 16)
    (hdq : ∀ j < rem, OutBlk A (dq + BitVec.ofNat 32 j)) :
    ∀ r k, k + r = rem → k < rem → ∀ u : State,
      u.pc = base + BitVec.ofNat 32 (m + macLOff) → u.regs 1 = A + 72#32 → u.regs 2 = BitVec.ofNat 32 k →
      u.regs 4 = dq → u.regs 6 = BitVec.ofNat 32 rem → u.regs 13 = A →
      (∀ q : Reg, 7 ≤ q.val → q.val < 12 → u.regs q = R q) →
      BlkHas A dq M0 k u.mem → (∀ y, OutBlk A y → u.mem y = M0 y) →
      Reach base (MacWr A) u (fun v => v.pc = base + BitVec.ofNat 32 (m + macEOff) ∧ v.regs 1 = A + 72#32 ∧
        v.regs 13 = A ∧ (∀ q : Reg, 7 ≤ q.val → q.val < 12 → v.regs q = R q) ∧
        BlkHas A dq M0 rem v.mem ∧ (∀ y, OutBlk A y → v.mem y = M0 y))
  | 0, k, h, hk, _, _, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | r + 1, k, h, hk, u, hpc, h1, h2, h4, h6, h13, hR, hblk, hout => by
    have hb2 : base.toNat % 2 = 0 := by omega
    obtain ⟨lm, l2, lz, lr⟩ := macL_effect u
    apply Reach.block hb2 macL (m + macLOff) hpc (by have := macLOff_even; omega) hseq (by decide)
      (by simp [alignedAll, macL, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, Nat.mod_one])
      (by
        intro e he' y ⟨a, ha, hw, q, hq, hy⟩
        simp only [traceAll, macL, List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with rfl | rfl | rfl | rfl
        all_goals simp [Instr.accesses, MemOp.isLoad] at ha
        all_goals try (subst ha; cases hw)
        have hq0 : q = 0 := by simpa [MemOp.width] using hq
        subst hq0
        refine .inr (.inr ⟨k, by omega, ?_⟩)
        rw [hy]
        simp only [Access.addr, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
          BitVec.add_zero]
        rw [show ((Instr.memReg MemOp.ldrb 0 4 2).next u).regs 1 = u.regs 1 from
            execAll_regs_other [.memReg .ldrb 0 4 2] u 1 (by decide) (by decide),
          show ((Instr.memReg MemOp.ldrb 0 4 2).next u).regs 2 = u.regs 2 from
            execAll_regs_other [.memReg .ldrb 0 4 2] u 2 (by decide) (by decide), h1, h2])
    generalize hv : execAll macL u = v at lm l2 lz lr
    have vpc : v.pc = base + BitVec.ofNat 32 (m + macBr2Off) := by
      rw [← hv, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    have src : read8 u.mem (u.regs 4 + u.regs 2) = (M0 (dq + BitVec.ofNat 32 k)).setWidth 32 := by
      rw [h4, h2, read8, hout _ (hdq k hk)]
    have vblk : BlkHas A dq M0 (k + 1) v.mem := by
      intro j hj
      rw [lm, h1, h2]
      by_cases e : j = k
      · subst e
        have e2 : read8 u.mem (u.regs 4 + BitVec.ofNat 32 j) = (M0 (dq + BitVec.ofNat 32 j)).setWidth 32 := by
          rw [h4, read8, hout _ (hdq j hk)]
        simp only [write8, if_true, e2, byte_copy, if_pos (show j < j + 1 by omega)]
      · rw [write8_other _ _ _ _ (blk_ne A hj (by omega) e), hblk j hj]
        by_cases hjk : j < k
        · rw [if_pos hjk, if_pos (by omega)]
        · rw [if_neg hjk, if_neg (by omega)]
    have vout : ∀ y, OutBlk A y → v.mem y = M0 y := by
      intro y hy
      rw [lm, h1, h2, write8_other _ _ _ _ (hy k (by omega)), hout y hy]
    have v2 : v.regs 2 = BitVec.ofNat 32 (k + 1) := by
      rw [l2, h2]; apply BitVec.eq_of_toNat_eq; simp
    have vz : v.z = decide (k + 1 = rem) := by
      rw [lz, h2, h6]; exact loop_flag k rem (by omega) hr
    have vr : ∀ q : Reg, q.val ≠ 0 → q.val ≠ 2 → q.val ≠ 15 → v.regs q = u.regs q := lr
    apply Reach.bcond hb2 (m + macBr2Off) (m + macLOff) 1 (brImm8 (m + macBr2Off) (m + macLOff)) vpc (by have := macBr2Off_even; omega) hbr
      (by have := macBr2Off_fits; omega)
      (by rw [brImm8_shift, se_fa, show m + macBr2Off = (m + macLOff) + seqSize macL by have := macBr2Off_back; omega]
          exact back_target _ (seqSize macL))
    · intro hne
      have hk1 : k + 1 ≠ rem := by simpa [condPassed, vz] using hne
      apply mac_loop base A dq M0 R m rem hseq hbr hb hm hmx hr hdq r (k + 1) (by omega) (by omega)
        _ (by rw [M0Crypto.Armv6M.State.pc, setReg_eq])
      all_goals first
        | (rw [setReg_ne _ _ _ _ (by decide)]; first
            | (rw [vr 1 (by decide) (by decide) (by decide), h1])
            | exact v2
            | (rw [vr 4 (by decide) (by decide) (by decide), h4])
            | (rw [vr 6 (by decide) (by decide) (by decide), h6])
            | (rw [vr 13 (by decide) (by decide) (by decide), h13]))
        | (intro q a b
           rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)),
             vr q (by omega) (by omega) (by omega), hR q a b])
        | exact vblk
        | exact vout
    · intro heq
      have hk1 : k + 1 = rem := by simpa [condPassed, vz] using heq
      have hf : m + macBr2Off + 2 = m + macEOff := by have := macBr2Off_fall; omega
      apply Reach.done
      refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq, hf],
        by rw [setReg_ne _ _ _ _ (by decide), vr 1 (by decide) (by decide) (by decide), h1],
        by rw [setReg_ne _ _ _ _ (by decide), vr 13 (by decide) (by decide) (by decide), h13],
        fun q a b => by
          rw [setReg_ne _ _ _ _ (by rintro rfl; exact absurd b (by decide)),
            vr q (by omega) (by omega) (by omega), hR q a b],
        by rw [setReg_mem, ← hk1]; exact vblk, fun y hy => by rw [setReg_mem]; exact vout y hy⟩

end M0Crypto.Release.Aead
