import M0Crypto.Release.Poly1305MacDefs
import M0Crypto.Release.Layout
import M0Crypto.Release.Poly1305Spec
import M0Crypto.Release.ReachSteps

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
Straight-line pieces of `m0c_poly1305_blocks` that recur: the 20-instruction `MAC`
macro (a 32x32 -> 64 multiply-accumulate from four 16x16 products), the `NARROW`
step (`h4 * s_j`, 32-bit, added to the column) and the column end (store the low
word, shift the 64-bit column right by 32).

The column accumulator lives in `r1:r0`; `v64 t = r1 * 2^32 + r0`.
-/

namespace M0Crypto.Release.Poly1305Mac

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (frameWB frameWB_writes)

/-! ## Carry arithmetic -/

/-- `addWithCarry`: 32-bit result plus 2^32 times the carry out is the exact sum. -/
theorem awc_nat (x y : Word) (c : Bool) :
    (addWithCarry x y c).1.toNat + 2 ^ 32 * (addWithCarry x y c).2.1.toNat = x.toNat + y.toNat + c.toNat := by
  simp only [addWithCarry, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  by_cases h : (x.toNat + y.toNat + c.toNat) % 2 ^ 32 = x.toNat + y.toNat + c.toNat
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.toNat_false]; omega
  · simp only [h, ne_eq, not_false_eq_true, decide_true, Bool.toNat_true]; omega

theorem awc_lt (x y : Word) (c : Bool) : (addWithCarry x y c).2.1.toNat ≤ 1 := by
  cases (addWithCarry x y c).2.1 <;> decide

/-- One `adds lo, x; adcs hi, y` pair: 64-bit addition of `y:x`. -/
theorem adc_pair (lo hi x y : Word) :
    (addWithCarry hi y (addWithCarry lo x false).2.1).1.toNat * 2 ^ 32 + (addWithCarry lo x false).1.toNat =
      (hi.toNat * 2 ^ 32 + lo.toNat + y.toNat * 2 ^ 32 + x.toNat) % 2 ^ 64 := by
  have e1 := awc_nat lo x false
  have e2 := awc_nat hi y (addWithCarry lo x false).2.1
  have := awc_lt hi y (addWithCarry lo x false).2.1
  have := (addWithCarry hi y (addWithCarry lo x false).2.1).1.isLt
  have := (addWithCarry lo x false).1.isLt
  simp only [Bool.toNat_false] at e1
  generalize (addWithCarry hi y (addWithCarry lo x false).2.1).1.toNat = A at *
  generalize (addWithCarry hi y (addWithCarry lo x false).2.1).2.1.toNat = B at *
  generalize (addWithCarry lo x false).1.toNat = C at *
  generalize ((addWithCarry lo x false).2.1).toNat = D at *
  omega

theorem read16_lt (m : Mem) (a : Word) : (read16 m a).toNat < 2 ^ 16 := by
  simp only [read16, BitVec.toNat_setWidth]
  have := (m (a + 1#32) ++ m a).isLt
  omega

/-- Two halfword loads at `a`, `a + 2` give the word at `a`. -/
theorem read16_pair (m : Mem) (a : Word) :
    (read16 m a).toNat + 2 ^ 16 * (read16 m (a + 2#32)).toNat = (read32 m a).toNat := by
  rw [Poly1305Spec.read32_toNat]
  simp only [read16, BitVec.toNat_setWidth, BitVec.toNat_append, Poly1305Spec.shl8_or]
  rw [show a + 2#32 + 1#32 = a + 3#32 by bv_omega]
  have := (m a).isLt; have := (m (a + 1#32)).isLt; have := (m (a + 2#32)).isLt; have := (m (a + 3#32)).isLt
  omega

/-! ## `MAC` -/

/-- The MAC column identity over `Nat`: three 64-bit additions of the four 16x16 products. -/
theorem mac_nat (v aL aH L H : Nat) :
    ((((v + aH * H * 2 ^ 32 + aL * L) % 2 ^ 64 + (H * aL) / 2 ^ 16 * 2 ^ 32 + (H * aL * 2 ^ 16) % 2 ^ 32)
      % 2 ^ 64 + (L * aH) / 2 ^ 16 * 2 ^ 32 + (L * aH * 2 ^ 16) % 2 ^ 32) % 2 ^ 64) =
      (v + (aL + 2 ^ 16 * aH) * (L + 2 ^ 16 * H)) % 2 ^ 64 := by
  have e : (aL + 2 ^ 16 * aH) * (L + 2 ^ 16 * H) = aL * L + aH * H * 2 ^ 32 + H * aL * 2 ^ 16 + L * aH * 2 ^ 16 := by
    grind
  rw [e]
  generalize H * aL = X
  generalize L * aH = Y
  generalize aL * L = Z
  generalize aH * H = W
  omega

/-- The 64-bit column accumulator `r1:r0`. -/
def v64 (s : State) : Nat := (s.regs 1).toNat * 2 ^ 32 + (s.regs 0).toNat

theorem mac_v64 (s : State) (h : Reg) (k : Nat) (hk : k + 1 < 32) :
    v64 (execAll (mac h k) s) = (v64 s + (s.regs h).toNat *
      ((read16 s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k))).toNat +
        2 ^ 16 * (read16 s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k + 2))).toNat)) % 2 ^ 64 := by
  simp only [v64, execAll, mac, Instr.next, Instr.exec, Instr.exec.memOp, addFlags, M0Crypto.Armv6M.State.setReg,
    M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV,
    M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6,
    M0Crypto.Proofs.toReg_7, MemOp.width, lslC, lsrC]
  simp (config := { decide := true }) only [ite_true, ite_false]
  have ek : (BitVec.ofNat 5 k).toNat * 2 = 2 * k := by simp; omega
  have ek1 : (BitVec.ofNat 5 (k + 1)).toNat * 2 = 2 * k + 2 := by simp; omega
  rw [ek, ek1]
  have hL := read16_lt s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k))
  have hH := read16_lt s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k + 2))
  generalize s.regs h = a
  generalize read16 s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k)) = L at hL ⊢
  generalize read16 s.mem (s.regs 7 + BitVec.ofNat 32 (2 * k + 2)) = H at hH ⊢
  rw [adc_pair, adc_pair, adc_pair]
  have e16 : (16 : BitVec 5).toNat = 16 := rfl
  have ha := a.isLt
  have pmul : ∀ x y : Nat, x < 2 ^ 16 → y < 2 ^ 16 → x * y < 2 ^ 32 := fun x y hx hy =>
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)
  simp only [e16, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have haL : a.toNat % 2 ^ 16 % 2 ^ 32 = a.toNat % 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  rw [haL]
  have hal : a.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have hah : a.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  rw [Nat.mod_eq_of_lt (pmul _ _ hal hL), Nat.mod_eq_of_lt (pmul _ _ hah hH),
    Nat.mod_eq_of_lt (pmul _ _ hH hal), Nat.mod_eq_of_lt (pmul _ _ hL hah)]
  have hs : a.toNat = a.toNat % 2 ^ 16 + 2 ^ 16 * (a.toNat / 2 ^ 16) := by omega
  conv => rhs; rw [hs]
  rw [← mac_nat]


theorem mac_falls (h : Reg) (k : Nat) : (mac h k).all Instr.falls = true := by simp [mac, Instr.falls]; decide
theorem mac_noW (h : Reg) (k : Nat) : (mac h k).all (!·.writesMem) = true := by
  simp [mac, Instr.writesMem, MemOp.isLoad]
theorem mac_size (h : Reg) (k : Nat) : seqSize (mac h k) = 40 := by simp [mac, seqSize, Instr.size]

/-- One `MAC h, [r7 + 4w]`: `r1:r0 += h * word w of the context` (mod 2^64); r7-r14, SP and
memory unchanged. -/
theorem mac_run_w {base ctx : Word} (hb : base.toNat % 4 = 0) (hc : ctx.toNat % 4 = 0) {Pc Wr : Word → Prop} {t : State} {off : Nat} {h : Reg} {w : Nat}
    (hw : w < 15) (hseq : seqAt B off (mac h (2 * w)) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (h7 : t.regs 7 = ctx) (hr : InRegion Pc base off (seqSize (mac h (2 * w)))) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 40) → t'.mem = t.mem →
      (∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = (v64 t + (t.regs h).toNat * (read32 t.mem (ctx + BitVec.ofNat 32 (4 * w))).toNat) % 2 ^ 64 →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have h2w : (BitVec.ofNat 5 (2 * w)).toNat = 2 * w := by simp; omega
  have h2w1 : (BitVec.ofNat 5 (2 * w + 1)).toNat = 2 * w + 1 := by simp; omega
  apply ReachW.block hb2 (mac h (2 * w)) off hpc ho hseq (mac_falls h _)
  · simp (config := { decide := true }) [alignedAll, mac, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      Access.aligned, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZC,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4,
      M0Crypto.Proofs.toReg_5, M0Crypto.Proofs.toReg_6, M0Crypto.Proofs.toReg_7, h2w, h2w1, h7, BitVec.toNat_add]
    omega
  · exact WritesTo.of_noWritesMem _ _ (mac_noW h _) Wr
  · exact hr
  · apply k
    · rw [execAll_pc _ _ (mac_falls h _), mac_size, hpc, ofNat_add_assoc]
    · exact execAll_mem _ _ (mac_noW h _)
    · intro r h7' h15
      apply execAll_regs_other _ _ r h15
      simp [mac, Instr.dsts]
      rcases r with ⟨v, hv⟩
      simp at h7' ⊢
      omega
    · rw [mac_v64 t h (2 * w) (by omega), h7]
      simp only [show 2 * (2 * w) = 4 * w by omega, show 2 * (2 * w) + 2 = 4 * w + 2 by omega]
      rw [← ofNat_add_assoc, show (BitVec.ofNat 32 2) = 2#32 from rfl, read16_pair]


theorem mac_run {base ctx : Word} (hb : base.toNat % 4 = 0) (hc : ctx.toNat % 4 = 0) {Wr : Word → Prop} {t : State} {off : Nat} {h : Reg} {w : Nat}
    (hw : w < 15) (hseq : seqAt B off (mac h (2 * w)) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (h7 : t.regs 7 = ctx) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 40) → t'.mem = t.mem →
      (∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = (v64 t + (t.regs h).toNat * (read32 t.mem (ctx + BitVec.ofNat 32 (4 * w))).toNat) % 2 ^ 64 →
      Reach base Wr t' Q) :
    Reach base Wr t Q :=
  (mac_run_w (Pc := fun _ => True) hb hc hw hseq ho hpc h7 (fun _ _ => trivial)
    (fun t' a b c d => (k t' a b c d).toReachW)).toReach


/-! ## `NARROW`: `r1:r0 += (lr * word j) mod 2^32` -/

theorem narrow_falls (j : Nat) : (narrow j).all Instr.falls = true := by simp [narrow, Instr.falls]
theorem narrow_noW (j : Nat) : (narrow j).all (!·.writesMem) = true := by
  simp [narrow, Instr.writesMem, MemOp.isLoad]

theorem narrow_run_w {base ctx : Word} (hb : base.toNat % 4 = 0) (hc : ctx.toNat % 4 = 0)
    {Pc Wr : Word → Prop} {t : State} {off : Nat} {j : Nat} (hj : j < 16) (hseq : seqAt B off (narrow j) = true)
    (ho : off % 2 = 0) (hpc : t.pc = base + BitVec.ofNat 32 off) (h7 : t.regs 7 = ctx) (hr : InRegion Pc base off (seqSize (narrow j))) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 12) → t'.mem = t.mem →
      (∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = (v64 t + (t.regs 14).toNat * (read32 t.mem (ctx + BitVec.ofNat 32 (4 * j))).toNat % 2 ^ 32) %
        2 ^ 64 → ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have hj' : j % 32 = j := Nat.mod_eq_of_lt (by omega)
  apply ReachW.block hb2 (narrow j) off hpc ho hseq (narrow_falls j)
  · simp (config := { decide := true }) [alignedAll, narrow, Instr.next, Instr.exec, Instr.exec.memOp,
      Instr.accesses, Access.aligned, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_7, hj', h7, BitVec.toNat_add]
    omega
  · exact WritesTo.of_noWritesMem _ _ (narrow_noW j) Wr
  · exact hr
  · apply k
    · rw [execAll_pc _ _ (narrow_falls j), hpc, ofNat_add_assoc]; rfl
    · exact execAll_mem _ _ (narrow_noW j)
    · intro r h7' h15
      apply execAll_regs_other _ _ r h15
      simp [narrow, Instr.dsts]
      rcases r with ⟨v, hv⟩
      simp at h7' ⊢
      omega
    · simp only [v64, execAll, narrow, Instr.next, Instr.exec, Instr.exec.memOp, addFlags,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV,
        M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
        M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_7, MemOp.width]
      simp (config := { decide := true }) only [ite_true, ite_false]
      rw [adc_pair, h7]
      have e5 : (BitVec.ofNat 5 j).toNat * 4 = 4 * j := by simp; omega
      have e0 : (BitVec.setWidth 32 (0 : BitVec 8)).toNat = 0 := rfl
      rw [e5, e0, BitVec.toNat_mul, Nat.mul_comm (read32 t.mem _).toNat]
      simp only [Nat.zero_mul, Nat.add_zero]

theorem narrow_run {base ctx : Word} (hb : base.toNat % 4 = 0) (hc : ctx.toNat % 4 = 0)
    {Wr : Word → Prop} {t : State} {off : Nat} {j : Nat} (hj : j < 16) (hseq : seqAt B off (narrow j) = true)
    (ho : off % 2 = 0) (hpc : t.pc = base + BitVec.ofNat 32 off) (h7 : t.regs 7 = ctx) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 12) → t'.mem = t.mem →
      (∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = (v64 t + (t.regs 14).toNat * (read32 t.mem (ctx + BitVec.ofNat 32 (4 * j))).toNat % 2 ^ 32) %
        2 ^ 64 → Reach base Wr t' Q) :
    Reach base Wr t Q :=
  (narrow_run_w (Pc := fun _ => True) hb hc hj hseq ho hpc h7 (fun _ _ => trivial)
    (fun t' a b c d => (k t' a b c d).toReachW)).toReach


/-! ## Column end: `str r0, [sp, #4j]; movs r0, r1; movs r1, #0` -/

theorem colend_falls (j : Nat) : (colend j).all Instr.falls = true := by simp [colend, Instr.falls]

theorem colend_run_w {base : Word} (hb : base.toNat % 4 = 0) {Pc Wr : Word → Prop} {t : State} {off : Nat}
    {j : Nat} (hj : j < Poly1305Blocks.frameWords) (hseq : seqAt B off (colend j) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hsp4 : (t.regs 13).toNat % 4 = 0)
    (hW : ∀ o < Poly1305Blocks.frameBytes, Wr (t.regs 13 + BitVec.ofNat 32 o)) (hr : InRegion Pc base off (seqSize (colend j))) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 6) →
      t'.mem = write32 t.mem (slot (t.regs 13) j) (t.regs 0) →
      (∀ r : Reg, 2 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = v64 t / 2 ^ 32 → ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have hfw256 : Poly1305Blocks.frameWords ≤ 256 := by decide
  have hj' : j % 256 = j := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj hfw256)
  have hfw : frameWB Poly1305Blocks.frameWords (colend j) = true := by
    simp [frameWB, colend, Instr.writesMem, Instr.dsts, hj', hj]
  apply ReachW.block hb2 (colend j) off hpc ho hseq (colend_falls j)
  · simp [alignedAll, colend, Instr.accesses, Access.aligned, M0Crypto.Armv6M.State.sp, hj',
      BitVec.toNat_add]
    omega
  · intro e he y hy
    obtain ⟨o, ho, rfl⟩ := frameWB_writes _ t hfw e he y hy
    exact hW o (by simp only [Poly1305Blocks.frameBytes]; exact ho)
  · exact hr
  · apply k
    · rw [execAll_pc _ _ (colend_falls j), hpc, ofNat_add_assoc]; rfl
    · simp [execAll, colend, Instr.next, Instr.exec, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg,
        M0Crypto.Proofs.toReg_0, slot, hj', Nat.mul_comm]
    · intro r h2 h15
      apply execAll_regs_other _ _ r h15
      simp [colend, Instr.dsts]
      rcases r with ⟨v, hv⟩
      simp at h2 ⊢
      omega
    · simp only [v64, execAll, colend, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.reg,
        M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, lslC]
      simp (config := { decide := true }) only [ite_true, ite_false]
      have := (t.regs 0).isLt
      simp
      omega

theorem colend_run {base : Word} (hb : base.toNat % 4 = 0) {Wr : Word → Prop} {t : State} {off : Nat}
    {j : Nat} (hj : j < Poly1305Blocks.frameWords) (hseq : seqAt B off (colend j) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hsp4 : (t.regs 13).toNat % 4 = 0)
    (hW : ∀ o < Poly1305Blocks.frameBytes, Wr (t.regs 13 + BitVec.ofNat 32 o)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 6) →
      t'.mem = write32 t.mem (slot (t.regs 13) j) (t.regs 0) →
      (∀ r : Reg, 2 ≤ r.val → r.val ≠ 15 → t'.regs r = t.regs r) →
      v64 t' = v64 t / 2 ^ 32 → Reach base Wr t' Q) :
    Reach base Wr t Q :=
  (colend_run_w (Pc := fun _ => True) hb hj hseq ho hpc hsp4 hW (fun _ _ => trivial)
    (fun t' a b c d => (k t' a b c d).toReachW)).toReach


end M0Crypto.Release.Poly1305Mac
