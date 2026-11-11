import M0Crypto.Release.ChaCha20Return
import M0Crypto.Release.ChaCha20Layout

set_option linter.unusedSimpArgs false

/-!
`m0c_chacha20_xor` from entry to the first block (offset `bpreOff`): prologue, the
`len == 0` and counter-overflow checks, and the input state `j[0..15]`.
-/

namespace M0Crypto.Release.ChaCha20Setup

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.ChaCha20 (wordOfBytes)
open M0Crypto.Release.ChaCha20Layout (fnStart cmpOff bneOff b0Off chkOff bccOff berrOff accOff zOff errOff
  chFrameWords chStackWords chStackBytes slotArgNonce slotArgCtr)

set_option maxRecDepth 100000

/-! ## Prologue (`fnStart` - `cmpOff`) -/

theorem pro_at : seqAt B fnStart pro = true := by decide
theorem listRegs_f0 : listRegs 0xf0 = [4, 5, 6, 7] := by decide
theorem bitCount_f0 : bitCount 0xf0 = 4 := by decide
theorem bitCount_240 : bitCount 240#8 = 4 := by decide

/-- Entry state of a call described by `c` (AAPCS: r0-r3 = out, in, len, key;
`[sp] = nonce`, `[sp + 4] = counter`). -/
structure Entry (c : Ctx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.out
  r1 : c.regs0 1 = c.inp
  r2 : c.regs0 2 = c.len
  r3 : c.regs0 3 = c.key
  argN : read32 c.m0 c.sp0 = c.nonce
  argC : read32 c.m0 (c.sp0 + 4#32) = c.ctr

theorem pro_effect (c : Ctx) (s : State) (h : Entry c s) :
    let t := execAll pro s
    t.regs 13 = c.fp ∧ t.mem = c.mP ∧
    (∀ r : Reg, r.val < 4 ∨ (7 < r.val ∧ r.val < 13) ∨ r.val = 14 → t.regs r = c.regs0 r) := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  have e0 : s.regs 13 = c.sp0 := by rw [h.regs, h.sp]
  refine ⟨?_, ?_, ?_⟩
  · simp only [execAll, pro, chFrameWords, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, bitCount_f0, listRegs_f0]
    simp (config := { decide := true }) only [ite_true, ite_false, e0]
    simp only [Ctx.fp]; bv_omega
  · simp only [execAll, pro, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, bitCount_f0, listRegs_f0]
    simp (config := { decide := true }) only [ite_true, ite_false, e0, List.map, h.mem]
    simp only [Ctx.mP, h.regs, LowReg.toReg]
    rfl
  · intro r hr
    have hne : ∀ k : Nat, (k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 13 ∨ k = 15) → r ≠ ⟨k % 16, Nat.mod_lt _ (by decide)⟩ := by
      intro k hk e; subst e; simp at hr; omega
    simp only [execAll, pro, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, bitCount_f0, listRegs_f0]
    rw [← h.regs]
    have : (r = 13) = False := eq_false (hne 13 (by omega))
    have : (r = 15) = False := eq_false (hne 15 (by omega))
    have : (r = 4) = False := eq_false (hne 4 (by omega))
    have : (r = 5) = False := eq_false (hne 5 (by omega))
    have : (r = 6) = False := eq_false (hne 6 (by omega))
    have : (r = 7) = False := eq_false (hne 7 (by omega))
    simp only [*, ite_false]

theorem fp_toNat {c : Ctx} (hv : Valid c) : c.fp.toNat = c.sp0.toNat - chStackBytes := by
  have := hv.spLo; have sSB := ChaCha20Layout.chStackBytes_eq
  simp only [Ctx.fp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem fp4 {c : Ctx} (hv : Valid c) : c.fp.toNat % 4 = 0 := by
  have := hv.sp8; have sSB := ChaCha20Layout.chStackBytes_eq; rw [fp_toNat hv]; omega

theorem wr_frame {c : Ctx} {y : Word} (h : InFrame c.fp n y) (hn : n ≤ chStackWords) : c.Wr y := by
  have hb : chStackBytes = 4 * chStackWords := rfl
  obtain ⟨o, ho, rfl⟩ := h; exact .inl ⟨o, by omega, rfl⟩

theorem pro_frame (c : Ctx) (hv : Valid c) (s : State) (h : Entry c s) :
    ∀ e ∈ traceAll pro s, ∀ y, Writes e.accesses y → ∃ o < chStackBytes, y = c.fp + BitVec.ofNat 32 o := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  have e0 : s.regs 13 = c.sp0 := by rw [h.regs, h.sp]
  intro e he y ⟨a, ha, hw, k, hk, hy⟩
  simp only [traceAll, pro, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Instr.accesses, List.not_mem_nil] at ha
  · simp only [wordAccesses, List.mem_map, List.mem_range, M0Crypto.Armv6M.State.sp, bitCount_f0, e0] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨156 + 4 * i + k, by simp at hi hk; omega, ?_⟩
    rw [hy]; simp only [Ctx.fp, Bool.toNat_true, Bool.toNat_false]
    apply BitVec.eq_of_toNat_eq; have := hv.spLo; simp at hi hk
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      bitCount_f0, listRegs_f0, wordAccesses, List.mem_map, List.mem_range] at ha
    simp (config := { decide := true }) only [ite_true, ite_false, e0] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨140 + 4 * i + k, by simp at hi hk; omega, ?_⟩
    rw [hy]; simp only [Ctx.fp, Bool.toNat_true, Bool.toNat_false]
    apply BitVec.eq_of_toNat_eq; have := hv.spLo; simp at hi hk
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem pro_writes (c : Ctx) (hv : Valid c) (s : State) (h : Entry c s) :
    WritesTo c.Wr (traceAll pro s) := fun e he y hy => .inl (pro_frame c hv s h e he y hy)

theorem wr_frameW {c : Ctx} {Wr : Word → Prop} (hW : ∀ o < chStackBytes, Wr (c.fp + BitVec.ofNat 32 o)) {y : Word}
    (h : InFrame c.fp n y) (hn : n ≤ chStackWords) : Wr y := by
  have hb : chStackBytes = 4 * chStackWords := rfl
  obtain ⟨o, ho, rfl⟩ := h; exact hW o (by omega)

/-! ## `len == 0` and the counter check (`cmpOff` - `berrOff`) -/

theorem cmp_at : instrAt B cmpOff = some (.cmpImm 2 0) := by decide
theorem bne_at : instrAt B bneOff = some (.bcond 1 (brImm8 bneOff chkOff)) := by decide +kernel
theorem b0_at : instrAt B b0Off = some (.b (brImm11 b0Off zOff)) := by decide +kernel
theorem chk_at : seqAt B chkOff chk = true := by decide
theorem bcc_at : instrAt B bccOff = some (.bcond 3 (brImm8 bccOff accOff)) := by decide +kernel
theorem berr_at : instrAt B berrOff = some (.b (brImm11 berrOff errOff)) := by decide +kernel
theorem bne_next : bneOff + 2 = b0Off := by decide
theorem bcc_next : bccOff + 2 = berrOff := by decide

theorem sub_flags (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_sub,
    Bool.toNat_true]
  omega

theorem counterOk_iff (ctr len : Word) (h : len ≠ 0) :
    M0Crypto.Spec.Aead.counterOk ctr.toNat len.toNat = true ↔
      ctr.toNat + ((len - 1#32) >>> 6).toNat < 2 ^ 32 := by
  have : len.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  have h1 : ((len - 1#32) >>> 6).toNat = (len.toNat - 1) / 64 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  simp only [M0Crypto.Spec.Aead.counterOk, decide_eq_true_eq, h1]
  omega

theorem condPassed_3 (t : State) : condPassed 3 t = !t.c := rfl
theorem condPassed_1 (t : State) : condPassed 1 t = !t.z := rfl

theorem setReg15_regs (t : State) (x : Word) (r : Reg) (h : r.val ≠ 15) : (t.setReg 15 x).regs r = t.regs r :=
  setReg_regs_ne _ _ _ _ (fun e => h (by rw [e]; rfl))

theorem setReg15_pc (t : State) (x : Word) : (t.setReg 15 x).pc = x := by
  simp [M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.pc]

/-- Facts at offset `accOff` (call accepted). -/
structure Acc (c : Ctx) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 accOff
  sp : t.regs 13 = c.fp
  mem : t.mem = c.mP
  r0 : t.regs 0 = c.out
  r1 : t.regs 1 = c.inp
  r2 : t.regs 2 = c.len
  r3 : t.regs 3 = c.key
  r4 : t.regs 4 = c.ctr
  ne : c.len ≠ 0
  ok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true
  argN : read32 c.m0 c.sp0 = c.nonce

theorem checks (c : Ctx) (hv : Valid c) (Wr : Word → Prop) (hW : ∀ o < chStackBytes, Wr (c.fp + BitVec.ofNat 32 o))
    (s : State) (h : Entry c s) (Q : State → Prop)
    (k0 : ∀ t, t.pc = c.base + BitVec.ofNat 32 zOff → t.regs 13 = c.fp → t.mem = c.mP → c.len = 0 →
      Reach c.base Wr t Q)
    (kerr : ∀ t, t.pc = c.base + BitVec.ofNat 32 errOff → t.regs 13 = c.fp → t.mem = c.mP → c.len ≠ 0 →
      M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = false → Reach c.base Wr t Q)
    (kacc : ∀ t, Acc c t → Reach c.base Wr t Q) : Reach c.base Wr s Q := by
  have sSB := ChaCha20Layout.chStackBytes_eq
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hpc0 : s.pc = c.base + BitVec.ofNat 32 fnStart := by
    show s.regs 15 = _; rw [h.regs, h.pc]; simp [fnStart, Artifacts.Release.chacha20_xor]
  obtain ⟨p13, pm, pr⟩ := pro_effect c s h
  apply Reach.block hb2 pro fnStart hpc0 (by decide) pro_at (by decide) ?_ (fun e he y hy => by obtain ⟨o, ho, rfl⟩ := pro_frame c hv s h e he y hy; exact hW o ho)
  rotate_left
  · simp [alignedAll, pro, Instr.next, Instr.exec, Instr.accesses, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, bitCount_f0, listRegs_f0, wordAccesses, List.range_succ, Access.aligned,
      h.regs, h.sp, BitVec.toNat_sub, BitVec.toNat_add]
    have := hv.sp8; have := hv.spLo
    simp only [bitCount_240]
    repeat' (first | apply And.intro | intro _ _)
    all_goals omega
  generalize ht0 : execAll pro s = t0 at p13 pm pr
  have pc0 : t0.pc = c.base + BitVec.ofNat 32 cmpOff := by
    rw [← ht0, execAll_pc pro s (by decide), hpc0, ofNat_add_assoc]; rfl
  -- cmp r2, #0
  apply Reach.block hb2 [.cmpImm 2 0] cmpOff pc0 (by decide) (by decide) (by decide)
    (by simp [alignedAll, Instr.accesses]) (by intro e he y ⟨a, ha, _⟩; simp [traceAll, Instr.accesses] at he; subst he; simp at ha)
  generalize ht1 : execAll [.cmpImm 2 0] t0 = t1
  have r1 : ∀ r : Reg, r.val ≠ 15 → t1.regs r = t0.regs r := fun r hr => by
    rw [← ht1]; exact execAll_regs_other _ _ r hr (by simp [Instr.dsts])
  have m1 : t1.mem = t0.mem := by rw [← ht1]; exact execAll_mem _ _ (by decide)
  have pc1 : t1.pc = c.base + BitVec.ofNat 32 bneOff := by
    rw [← ht1, execAll_pc _ t0 (by decide), pc0, ofNat_add_assoc]; rfl
  have z1 : t1.z = (c.len == 0) := by
    have e2 : t0.regs 2 = c.len := by rw [pr 2 (by decide)]; exact h.r2
    rw [← ht1]
    simp only [execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setNZCV,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_2, e2]
    simp (config := { decide := true }) only [ite_false, sub_flags]
    simp
  apply Reach.bcond hb2 bneOff chkOff 1 (brImm8 bneOff chkOff) pc1 (by decide) bne_at (by decide) (by decide +kernel)
  · intro hz
    simp only [condPassed, Bool.not_eq_true'] at hz
    rw [z1] at hz
    have hne : c.len ≠ 0 := by simpa using hz
    -- the counter check
    generalize ht2 : t1.setReg 15 (c.base + BitVec.ofNat 32 chkOff) = t2
    have r2 : ∀ r : Reg, r.val ≠ 15 → t2.regs r = t0.regs r := fun r hr => by
      rw [← ht2, setReg15_regs _ _ _ hr, r1 r hr]
    have pc2 : t2.pc = c.base + BitVec.ofNat 32 chkOff := by rw [← ht2, setReg15_pc]
    have m2 : t2.mem = c.mP := by rw [← ht2, ← pm, ← m1]; rfl
    have sp2 : t2.regs 13 = c.fp := by rw [r2 13 (by decide), p13]
    have arg : read32 t2.mem (t2.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 slotArgCtr).toNat * 4)) = c.ctr := by
      rw [m2, sp2, show c.fp + BitVec.ofNat 32 ((BitVec.ofNat 8 slotArgCtr).toNat * 4) = c.sp0 + BitVec.ofNat 32 4 by
        simp only [Ctx.fp, slotArgCtr, slotArgNonce, chStackWords]; simp; bv_omega]
      rw [ChaCha20Return.mP_above c hv 4 (by have := hv.outF; have := hv.codeF; simp only [Disj] at *; rw [fp_toNat hv] at *; omega)]
      exact h.argC
    have hcs := ChaCha20Layout.chStackWords_eq
    apply Reach.block hb2 chk chkOff pc2 (by decide) chk_at (by decide)
      (by simp [alignedAll, chk, Instr.accesses, Instr.next, Instr.exec, M0Crypto.Armv6M.State.sp,
            M0Crypto.Armv6M.State.setReg, Access.aligned, sp2, BitVec.toNat_add]
          have := fp4 hv; omega)
      (fun e he y hy => wr_frameW hW (by have := frameWB_writes (n := chStackWords) chk t2 (by decide) e he y hy; rwa [sp2] at this) (by omega))
    generalize ht3 : execAll chk t2 = t3
    have c3 : t3.c = decide ((BitVec.ofNat 32 (c.ctr.toNat + ((c.len - 1#32) >>> 6).toNat)).toNat ≠
        c.ctr.toNat + ((c.len - 1#32) >>> 6).toNat) := by
      have e2 : t2.regs 2 = c.len := by rw [r2 2 (by decide), pr 2 (by decide)]; exact h.r2
      rw [← ht3]
      simp only [chk, execAll, Instr.next, Instr.exec, addFlags, M0Crypto.Armv6M.State.setNZCV,
        M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.sp, lsrC]
      simp (config := { decide := true }) only [ite_true, ite_false, LowReg.toReg]
      have e2' : t2.regs ⟨(2 : LowReg).val, by decide⟩ = c.len := e2
      rw [e2', arg, sub_flags, show (BitVec.setWidth 32 (1 : BitVec 3) : Word) = 1#32 from rfl]
      simp only [M0Crypto.Armv6M.addWithCarry, Bool.toNat_false, Nat.add_zero]; rfl
    have r3 : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 4 → r.val ≠ 5 → t3.regs r = t2.regs r := fun r h15 h4 h5 => by
      rw [← ht3]; apply execAll_regs_other _ _ r h15
      simp [chk, Instr.dsts]; omega
    have m3 : t3.mem = t2.mem := by rw [← ht3]; exact execAll_mem _ _ (by decide)
    have pc3 : t3.pc = c.base + BitVec.ofNat 32 bccOff := by
      rw [← ht3, execAll_pc _ t2 (by decide), pc2, ofNat_add_assoc]; rfl
    have r43 : t3.regs 4 = c.ctr := by
      rw [← ht3]
      have : chk = [.ldrSp 4 (BitVec.ofNat 8 slotArgCtr)] ++ [.subImm3 5 2 1, .lsrImm 5 5 6, .addReg 5 4 5] := rfl
      rw [this, execAll_append, execAll_regs_other _ _ 4 (by decide) (by simp [Instr.dsts]; decide)]
      simp only [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, LowReg.toReg]
      simp (config := { decide := true }) only [ite_true, ite_false]
      exact arg
    have hok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = !t3.c := by
      rw [c3, BitVec.toNat_ofNat]
      have hi := counterOk_iff c.ctr c.len hne
      by_cases hlt : c.ctr.toNat + ((c.len - 1#32) >>> 6).toNat < 2 ^ 32
      · rw [hi.mpr hlt, Nat.mod_eq_of_lt hlt]; simp
      · have hf : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = false := by
          cases h' : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat
          · rfl
          · exact absurd (hi.mp h') hlt
        rw [hf]; simp only [Bool.false_eq, Bool.not_eq_false', decide_eq_true_eq]; omega
    apply Reach.bcond hb2 bccOff accOff 3 (brImm8 bccOff accOff) pc3 (by decide) bcc_at (by decide) (by decide +kernel)
    · intro hc
      rw [condPassed_3] at hc
      have r : ∀ r : Reg, r.val < 4 → (t3.setReg 15 (c.base + BitVec.ofNat 32 accOff)).regs r = c.regs0 r :=
        fun r hr => by rw [setReg15_regs _ _ _ (by omega), r3 r (by omega) (by omega) (by omega),
          r2 r (by omega), pr r (by omega)]
      apply kacc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne, ?_, ?_⟩
      · exact setReg15_pc _ _
      · rw [setReg15_regs _ _ 13 (by decide), r3 13 (by decide) (by decide) (by decide), sp2]
      · rw [setReg_mem, m3, m2]
      · rw [r 0 (by decide), h.r0]
      · rw [r 1 (by decide), h.r1]
      · rw [r 2 (by decide), h.r2]
      · rw [r 3 (by decide), h.r3]
      · rw [setReg15_regs _ _ 4 (by decide), r43]
      · rw [hok]; exact hc
      · exact h.argN
    · intro hc
      rw [condPassed_3] at hc
      apply Reach.b hb2 berrOff errOff (brImm11 berrOff errOff) (by rw [setReg15_pc, bcc_next]) (by decide) berr_at (by decide) (by decide +kernel)
      apply kerr
      · rw [setReg15_pc]
      · rw [setReg15_regs _ _ 13 (by decide), setReg15_regs _ _ 13 (by decide),
          r3 13 (by decide) (by decide) (by decide), sp2]
      · show t3.mem = c.mP; rw [m3, m2]
      · exact hne
      · rw [hok]; exact hc
  · intro hz
    simp only [condPassed, Bool.not_eq_false'] at hz
    rw [z1] at hz
    have hl : c.len = 0 := by simpa using hz
    apply Reach.b hb2 b0Off zOff (brImm11 b0Off zOff) (by rw [setReg15_pc, bne_next]) (by decide) b0_at (by decide) (by decide +kernel)
    apply k0
    · rw [setReg15_pc]
    · rw [setReg15_regs _ _ 13 (by decide), setReg15_regs _ _ 13 (by decide), r1 13 (by decide), p13]
    · show t1.mem = c.mP; rw [m1, pm]
    · exact hl

/-! ## `LOAD_LE32 r3, off` -/

theorem le32_r0 (t : State) (off : Nat) (hoff : off + 3 < 32) :
    (execAll (le32 off) t).regs 0 =
      wordOfBytes (t.mem (t.regs 3 + BitVec.ofNat 32 off))
        (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 1)))
        (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 2)))
        (t.mem (t.regs 3 + BitVec.ofNat 32 (off + 3))) := by
  simp only [execAll, le32, Instr.next, Instr.exec, Instr.exec.memOp, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.reg,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_3, MemOp.width, lslC, read8]
  simp (config := { decide := true }) only [ite_true, ite_false, Nat.mul_one]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 32 by omega),
    Nat.mod_eq_of_lt (show off + 1 < 32 by omega), Nat.mod_eq_of_lt (show off + 2 < 32 by omega),
    Nat.mod_eq_of_lt (show off + 3 < 32 by omega)]
  simp [wordOfBytes, BitVec.or_assoc]

end M0Crypto.Release.ChaCha20Setup
