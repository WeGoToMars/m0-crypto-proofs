import M0Crypto.Release.AeadFinish
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Exact-byte erasure of the 64-byte context and 32-byte scratch block. -/
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem write32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-- The 96 bytes cleared by `CLEAR_FRAME`. -/
def ClearWr (A y : Word) : Prop := ∃ o < 96, y = A + BitVec.ofNat 32 (8 + o)

theorem clearWr_swr (A y : Word) (h : ClearWr A y) : SWr A y := by
  obtain ⟨o, ho, rfl⟩ := h
  exact swr_A A _ (by omega)

attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3

theorem clrA_effect (s : State) :
    (execAll clrA s).regs 0 = 0#32 ∧ (execAll clrA s).regs 1 = s.regs 13 + 8#32 ∧
    (execAll clrA s).regs 2 = 24#32 ∧ (execAll clrA s).mem = s.mem ∧
    (∀ r : Reg, 3 ≤ r.val → r.val ≠ 15 → (execAll clrA s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, rfl, fun r h3 h15 => execAll_regs_other _ _ r h15
    (by
      have h0 : r.val ≠ 0 := by omega
      have h1 : r.val ≠ 1 := by omega
      have h2 : r.val ≠ 2 := by omega
      simp [clrA, Instr.dsts, Fin.ext_iff, h0, h1, h2])⟩ <;>
    simp [clrA, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg]

theorem clrL_effect (s : State) :
    (execAll clrL s).mem = write32 s.mem (s.regs 1) (s.regs 0) ∧
    (execAll clrL s).regs 1 = s.regs 1 + 4#32 ∧ (execAll clrL s).regs 2 = s.regs 2 - 1#32 ∧
    (execAll clrL s).z = (s.regs 2 - 1#32 == 0#32) ∧
    (∀ r : Reg, r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 15 → (execAll clrL s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h15 => execAll_regs_other _ _ r h15
    (by simp [clrL, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h1, h2])⟩ <;>
    simp [clrL, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
      Instr.exec.memOp, addFlags, ChaCha20Output.add_flags, ChaCha20Loop.sub_flags, ChaCha20Loop.sub_flags (s.regs 2) 1#32]

  all_goals rw [show (4294967294#32 : Word) = ~~~1#32 from rfl, ChaCha20Loop.sub_flags]

theorem clrA_size : seqSize clrA = 6 := by decide

theorem clrL_size : seqSize clrL = 6 := by decide

theorem se_fb : (((brImm8 (seqSize clrL) 0) ++ 0#1).signExtend 32 : Word) = -(BitVec.ofNat 32 (seqSize clrL + 4)) := by decide +kernel

theorem clear_loop (base A : Word) (R : Reg → Word) (M : Mem) (off : Nat)
    (hsq : seqAt B off clrL = true) (hbr : instrAt B (off + seqSize clrL) = some (.bcond 1 (brImm8 (off + seqSize clrL) off)))
    (hb : base.toNat % 4 = 0) (ha : A.toNat % 4 = 0) (ho : off % 2 = 0)
    (hx : off + seqSize clrL + brSize ≤ Artifacts.Release.size) :
    ∀ rem k, k + rem = 24 → k < 24 → ∀ s : State,
      s.pc = base + BitVec.ofNat 32 off → s.regs 0 = 0#32 →
      s.regs 1 = A + BitVec.ofNat 32 (8 + 4*k) → s.regs 2 = BitVec.ofNat 32 rem →
      (∀ r : Reg, 3 ≤ r.val → r.val ≠ 15 → s.regs r = R r) →
      (∀ o < 4*k, s.mem (A + BitVec.ofNat 32 (8 + o)) = 0#8) →
      (∀ y, ¬ ClearWr A y → s.mem y = M y) →
      Reach base (ClearWr A) s (fun t => t.pc = base + BitVec.ofNat 32 (off + seqSize clrL + brSize) ∧
        (∀ r : Reg, 3 ≤ r.val → r.val ≠ 15 → t.regs r = R r) ∧
        (∀ o < 96, t.mem (A + BitVec.ofNat 32 (8 + o)) = 0#8) ∧
        (∀ y, ¬ ClearWr A y → t.mem y = M y))
  | 0, k, h, hk, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | rem + 1, k, h, hk, s, hpc, h0, h1, h2, hR, hz, hm => by
    have hb2 : base.toNat % 2 = 0 := by omega
    have hLs := clrL_size
    have hBs := brSize_eq
    obtain ⟨em, e1, e2, ez, er⟩ := clrL_effect s
    apply Reach.block hb2 clrL off hpc ho hsq (by decide)
      (by
        simp [alignedAll, clrL, Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, h1,
          BitVec.toNat_add, BitVec.toNat_ofNat, M0Crypto.Armv6M.State.reg]
        omega)
      (by
        intro e he y ⟨a, he', hw, q, hq, hy⟩
        simp [traceAll, clrL] at he
        rcases he with rfl | rfl | rfl <;> simp [Instr.accesses, MemOp.isLoad] at he'
        subst he'
        refine ⟨4*k+q, by simpa [MemOp.width] using (show 4*k+q < 96 by change q < 4 at hq; omega), ?_⟩
        rw [hy]
        simp [M0Crypto.Armv6M.State.reg, h1, ofNat_add_assoc, Nat.add_assoc])
    generalize ht : execAll clrL s = t at em e1 e2 ez er
    have tp : t.pc = base + BitVec.ofNat 32 (off + seqSize clrL) := by
      rw [← ht, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]
    have tz : ∀ o < 4*(k+1), t.mem (A + BitVec.ofNat 32 (8+o)) = 0#8 := by
      intro o ho'
      rw [em, h0, h1]
      by_cases hok : o < 4*k
      · exact write32_zero_pass _ _ _ (hz o hok)
      · have eo : A + BitVec.ofNat 32 (8+o) = A + BitVec.ofNat 32 (8+4*k) + BitVec.ofNat 32 (o-4*k) := by
          rw [ofNat_add_assoc]; congr 2; omega
        rw [eo]; exact write32_zero_hit _ _ _ (by omega)
    have tm : ∀ y, ¬ ClearWr A y → t.mem y = M y := by
      intro y hy
      rw [em, h1, write32_other' _ _ _ _ (fun q hq e => hy ⟨4*k+q, by omega, by
        rw [e, ofNat_add_assoc]; congr 2; omega⟩), hm y hy]
    have t1 : t.regs 1 = A + BitVec.ofNat 32 (8+4*(k+1)) := by
      rw [e1, h1, ofNat_add_assoc]; congr 2 <;> omega
    have t2 : t.regs 2 = BitVec.ofNat 32 rem := by rw [e2, h2]; bv_omega
    have zflag : t.z = decide (rem = 0) := by
      rw [ez, h2, show BitVec.ofNat 32 (rem + 1) - 1#32 = BitVec.ofNat 32 rem by bv_omega]
      have hr : rem < 2^32 := by omega
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro e; have := congrArg BitVec.toNat e; simp at this; omega
      · intro e; rw [e]
    apply Reach.bcond hb2 (off + seqSize clrL) off 1 (brImm8 (off + seqSize clrL) off) tp (by omega) hbr (by omega)
      (by rw [brImm8_base, se_fb]; exact back_target off (seqSize clrL))
    · intro hn
      have hr : rem ≠ 0 := by simpa [condPassed, zflag] using hn
      apply clear_loop base A R M off hsq hbr hb ha ho hx rem (k+1) (by omega) (by omega) (t.setReg 15 (base + BitVec.ofNat 32 off))
        (by rw [M0Crypto.Armv6M.State.pc, setReg_eq])
        (by rw [setReg_ne _ _ _ _ (by decide), er 0 (by decide) (by decide) (by decide), h0])
        (by rw [setReg_ne _ _ _ _ (by decide)]; exact t1)
        (by rw [setReg_ne _ _ _ _ (by decide)]; exact t2)
        (fun r a b => by
          rw [setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), er r (by omega) (by omega) b, hR r a b]) tz tm
    · intro heq
      have hr : rem = 0 := by simpa [condPassed, zflag] using heq
      apply Reach.done
      refine ⟨by rw [M0Crypto.Armv6M.State.pc, setReg_eq, brSize_eq],
        fun r a b => by rw [setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), er r (by omega) (by omega) b, hR r a b],
        ?_, tm⟩
      intro o ho'
      exact tz o (by omega)

structure ClearPost (base A : Word) (off : Nat) (s t : State) : Prop where
  pc : t.pc = base + BitVec.ofNat 32 (off + seqSize clrA + seqSize clrL + brSize)
  hi : ∀ r : Reg, 3 ≤ r.val → r.val ≠ 15 → t.regs r = s.regs r
  zero : ∀ o < 96, t.mem (A + BitVec.ofNat 32 (8+o)) = 0#8
  frame : ∀ y, ¬ ClearWr A y → t.mem y = s.mem y

theorem clear_reach (base A : Word) (off : Nat)
    (hA : seqAt B off clrA = true) (hL : seqAt B (off + seqSize clrA) clrL = true)
    (hbr : instrAt B (off + seqSize clrA + seqSize clrL) = some (.bcond 1 (brImm8 (off + seqSize clrA + seqSize clrL) (off + seqSize clrA))))
    (hb : base.toNat % 4 = 0) (ha : A.toNat % 4 = 0) (ho : off % 2 = 0)
    (hx : off + seqSize clrA + seqSize clrL + brSize ≤ Artifacts.Release.size)
    (s : State) (hp : s.pc = base + BitVec.ofNat 32 off) (hs : s.regs 13 = A) :
    Reach base (ClearWr A) s (ClearPost base A off s) := by
  obtain ⟨e0, e1, e2, em, er⟩ := clrA_effect s
  have hAs := clrA_size
  apply Reach.block (by omega) clrA off hp ho hA (by decide)
    (by simp [alignedAll, clrA, Instr.accesses]) (ChaCha20Block.noWrites _ _ (by decide) _)
  generalize hu : execAll clrA s = u at e0 e1 e2 em er
  have up : u.pc = base + BitVec.ofNat 32 (off + seqSize clrA) := by
    rw [← hu, execAll_pc _ _ (by decide), hp, ofNat_add_assoc]
  apply (clear_loop base A s.regs s.mem (off + seqSize clrA) hL hbr hb ha (by omega) hx
    24 0 rfl (by decide) u up e0 (by simpa [hs] using e1) e2 er
    (by intro o ho'; omega) (by intro y _; rw [em])).mono
  rintro t ⟨tp, tr, tz, tm⟩
  exact ⟨tp, tr, tz, tm⟩
end M0Crypto.Release.Aead
