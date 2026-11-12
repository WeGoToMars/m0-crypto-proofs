import M0Crypto.Release.Blake2sUpdateExit

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `update`: the prologue and the initial loop invariant -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Blake2sPro (regs_push mem_push)
open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_append bytesAt_congr bytesAt_length)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Blake2sCopy (sr_ne sr_pc cp0 cp1 cmp_eff)
open M0Crypto.Release.Blake2sFinal (l4567 b4567)

/-- Reading the context through the pushed stack is the same as before the push. -/
theorem pm_ctx {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) (k : Nat) (hk : k + 4 ≤ 112) :
    read32 (pm s) (s.regs 0 + BitVec.ofNat 32 k) = read32 s.mem (s.regs 0 + BitVec.ofNat 32 k) := by
  apply read32_congr
  intro j hj
  rw [ofNat_add_assoc]
  apply pm_eq
  intro o ho he
  exact disj_ne e.cF (i := k + j) (o := o) (by omega) ho he

theorem ctxNU_pm {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    CtxNU (pm s) (s.regs 0) st0 := by
  have h := e.ctx
  refine ⟨h.hsz, fun i hi => ?_, ?_, ?_, h.cnt, h.plen, ?_⟩
  · rw [pm_ctx e (4 * i) (by omega)]; exact h.h i hi
  · rw [show (32#32 : Word) = BitVec.ofNat 32 32 from rfl, pm_ctx e 32 (by omega)]; exact h.clo
  · rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, pm_ctx e 36 (by omega)]; exact h.chi
  · have hp := h.plen
    refine Eq.trans ?_ h.buf
    apply bytesAt_congr
    intro i hi
    rw [show (40#32 : Word) = BitVec.ofNat 32 40 from rfl, ofNat_add_assoc]
    apply pm_eq
    intro o ho he
    exact disj_ne e.cF (i := 40 + i) (o := o) (by omega) ho he

theorem rne (r n : Reg) (h : r.val ≠ n.val) : r ≠ n := fun e => h (by rw [e])

theorem upro_eff {base : Word} {s : State} {st0 : SState} (e : UpdateEntry base s st0) :
    (execAll uPro s).regs 13 = s.regs 13 - 24#32 ∧ (execAll uPro s).regs 4 = s.regs 0 ∧
    (execAll uPro s).regs 5 = s.regs 1 ∧ (execAll uPro s).regs 6 = s.regs 2 ∧
    (execAll uPro s).regs 7 = BitVec.ofNat 32 st0.pending.length ∧
    (∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → (execAll uPro s).regs r = s.regs r) ∧
    (execAll uPro s).mem = pm s := by
  obtain ⟨s1, hs1⟩ : ∃ x, x = (Instr.push 0xF0 true).next s := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ x, x = (Instr.subSp 1).next s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ x, x = (Instr.lslImm 4 0 0).next s2 := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ x, x = (Instr.lslImm 5 1 0).next s3 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ x, x = (Instr.lslImm 6 2 0).next s4 := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ x, x = (Instr.memImm .ldr 7 4 26).next s5 := ⟨_, rfl⟩
  have hx : execAll uPro s = s6 := by
    rw [hs6, hs5, hs4, hs3, hs2, hs1]; rfl
  rw [hx]
  have p1r13 : s1.regs 13 = s.regs 13 - 20#32 := by
    rw [hs1, regs_push _ _ _ _ (by decide), if_pos rfl, b4567]; rfl
  have p1o : ∀ r : Reg, r ≠ 13 → r ≠ 15 → s1.regs r = s.regs r := by
    intro r h13 h15; rw [hs1, regs_push _ _ _ _ h15, if_neg h13]
  have p1m : s1.mem = pm s := by
    rw [hs1, mem_push, l4567, b4567]; rfl
  have p2r13 : s2.regs 13 = s.regs 13 - 24#32 := by
    rw [hs2, M0Crypto.Release.Blake2sPro.regs_subSp _ _ _ (by decide), if_pos rfl, p1r13]; simp; bv_omega
  have p2o : ∀ r : Reg, r ≠ 13 → r ≠ 15 → s2.regs r = s1.regs r := by
    intro r h13 h15; rw [hs2, M0Crypto.Release.Blake2sPro.regs_subSp _ _ _ h15, if_neg h13]
  have p2m : s2.mem = s1.mem := by rw [hs2, M0Crypto.Release.Blake2sPro.mem_subSp]
  have p3o : ∀ r : Reg, r ≠ 4 → r ≠ 15 → s3.regs r = s2.regs r := by
    intro r h4 h15; rw [hs3, regs_lsl _ _ _ _ _ h15]; exact if_neg (fun h' => h4 h')
  have p3r4 : s3.regs 4 = s2.regs 0 := by
    rw [hs3, regs_lsl _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; simp [lslC, State.reg]; rfl
  have p3m : s3.mem = s2.mem := by rw [hs3, mem_lsl]
  have p4o : ∀ r : Reg, r ≠ 5 → r ≠ 15 → s4.regs r = s3.regs r := by
    intro r h5 h15; rw [hs4, regs_lsl _ _ _ _ _ h15]; exact if_neg (fun h' => h5 h')
  have p4r5 : s4.regs 5 = s3.regs 1 := by
    rw [hs4, regs_lsl _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; simp [lslC, State.reg]; rfl
  have p4m : s4.mem = s3.mem := by rw [hs4, mem_lsl]
  have p5o : ∀ r : Reg, r ≠ 6 → r ≠ 15 → s5.regs r = s4.regs r := by
    intro r h6 h15; rw [hs5, regs_lsl _ _ _ _ _ h15]; exact if_neg (fun h' => h6 h')
  have p5r6 : s5.regs 6 = s4.regs 2 := by
    rw [hs5, regs_lsl _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_; simp [lslC, State.reg]; rfl
  have p5m : s5.mem = s4.mem := by rw [hs5, mem_lsl]
  have p6o : ∀ r : Reg, r ≠ 7 → r ≠ 15 → s6.regs r = s5.regs r := by
    intro r h7 h15; rw [hs6, regs_ldr _ _ _ _ _ h15]; exact if_neg (fun h' => h7 h')
  have p6m : s6.mem = s5.mem := by rw [hs6, mem_ldr]
  have m5 : s5.mem = pm s := by rw [p5m, p4m, p3m, p2m, p1m]
  have r0_2 : s2.regs 0 = s.regs 0 := by rw [p2o 0 (by decide) (by decide), p1o 0 (by decide) (by decide)]
  have r1_3 : s3.regs 1 = s.regs 1 := by
    rw [p3o 1 (by decide) (by decide), p2o 1 (by decide) (by decide), p1o 1 (by decide) (by decide)]
  have r2_4 : s4.regs 2 = s.regs 2 := by
    rw [p4o 2 (by decide) (by decide), p3o 2 (by decide) (by decide), p2o 2 (by decide) (by decide),
      p1o 2 (by decide) (by decide)]
  have r4_5 : s5.regs 4 = s.regs 0 := by
    rw [p5o 4 (by decide) (by decide), p4o 4 (by decide) (by decide), p3r4, r0_2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p6o 13 (by decide) (by decide), p5o 13 (by decide) (by decide), p4o 13 (by decide) (by decide),
      p3o 13 (by decide) (by decide), p2r13]
  · rw [p6o 4 (by decide) (by decide), r4_5]
  · rw [p6o 5 (by decide) (by decide), p5o 5 (by decide) (by decide), p4r5, r1_3]
  · rw [p6o 6 (by decide) (by decide), p5r6, r2_4]
  · rw [hs6, regs_ldr _ _ _ _ _ (by decide)]; refine (if_pos rfl).trans ?_
    have : s5.reg 4 = s.regs 0 := r4_5
    rw [this, m5, show BitVec.ofNat 32 (BitVec.toNat (26 : BitVec 5) * 4) = 104#32 from rfl]
    rw [show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, pm_ctx e 104 (by omega)]
    exact e.ctx.used
  · intro r h8 h11
    have n15 : r ≠ 15 := rne _ _ (show r.val ≠ 15 by omega)
    rw [p6o r (rne _ _ (show r.val ≠ 7 by omega)) n15, p5o r (rne _ _ (show r.val ≠ 6 by omega)) n15,
      p4o r (rne _ _ (show r.val ≠ 5 by omega)) n15, p3o r (rne _ _ (show r.val ≠ 4 by omega)) n15,
      p2o r (rne _ _ (show r.val ≠ 13 by omega)) n15, p1o r (rne _ _ (show r.val ≠ 13 by omega)) n15]
  · rw [p6m, m5]

end M0Crypto.Release.Blake2sUpdate
