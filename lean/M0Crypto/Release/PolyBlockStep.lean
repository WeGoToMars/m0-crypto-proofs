import M0Crypto.Release.PolyBlocksArith
import M0Crypto.Release.PolyBlocksLoad
import M0Crypto.Release.PolyCarry
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.PolyBlocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.PolyMac (mac narrow colend v64)
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

/-- Addition of the four loaded words and explicit high-bit argument, at the
actual five-word machine width. -/
theorem addMsg_h (s : State) :
    hval (execAll addMsg s) =
      (hval s + PolyArith.val4 (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat +
        2^128 * (s.regs 12).toNat) % 2^160 := by
  have h := PolyCarry.adc5_mod (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 14)
    (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) (s.regs 12)
  simp (config := { decide := true }) only [hval, execAll, addMsg, Instr.next, Instr.exec, addFlags,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5,
    M0Crypto.Proofs.toReg_6, M0Crypto.Proofs.toReg_7, ite_true, ite_false]
  dsimp only at h
  rw [h]
  congr 1
  simp only [hval, PolyArith.val4, PolyArith.val5]
  omega

/-- Context and stack are separate; only the first four temporary slots are
written by the multiplication columns. -/
def Sep (s : State) : Prop := Disj (s.regs 7) 64 (s.regs 13) (4 * frameWords)

theorem cw_write (s : State) (hs : Sep s) (i : Nat) (hi : i < frameWords) (v : Word) (j : Nat) (hj : j < 16) :
    read32 (write32 s.mem (slot (s.regs 13) i) v) (slot (s.regs 7) j) =
      read32 s.mem (slot (s.regs 7) j) := by
  apply read32_congr
  intro k hk
  apply M0Crypto.Armv6M.write32_other
  intro q hq
  unfold Sep at hs
  rw [slot, slot, ofNat_add_assoc, ofNat_add_assoc]
  exact ne_of_disj hs.1 hs.2.1 hs.2.2 (by omega) (by omega)

/-- Arithmetic of the narrow top-limb contribution. -/
theorem narrow_v (s : State) (j : Nat) (hj : j < 16) :
    v64 (execAll (narrow j) s) = (v64 s + (s.regs 14).toNat * cw s j % 2^32) % 2^64 := by
  simp (config := { decide := true }) only [v64, execAll, narrow, Instr.next, Instr.exec,
    Instr.exec.memOp, addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
    M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_7, MemOp.width, ite_true, ite_false]
  rw [PolyMac.adc_pair]
  have e : (BitVec.ofNat 5 j).toNat * 4 = 4*j := by simp; omega
  rw [e]
  simp only [cw, slot, BitVec.toNat_mul]
  change _ = _
  simp [BitVec.toNat_setWidth, show (0 : BitVec 8).toNat = 0 from rfl, Nat.mul_comm]

/-- Registers and context words that a column must preserve. -/
structure CF (s t : State) : Prop where
  regs : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → t.regs r = s.regs r
  words : ∀ j < 16, cw t j = cw s j

theorem CF.trans {s t u : State} (a : CF s t) (b : CF t u) : CF s u :=
  ⟨fun r h h' => (b.regs r h h').trans (a.regs r h h'),
   fun j hj => (b.words j hj).trans (a.words j hj)⟩
theorem CF.sep {s t : State} (a : CF s t) (h : Sep s) : Sep t := by
  simpa only [Sep, a.regs 7 (by decide) (by decide), a.regs 13 (by decide) (by decide)] using h

theorem mac4_cf (s : State) (a b c d : Nat) : CF s (execAll (mac4 a b c d) s) := by
  refine ⟨mac4_regs s a b c d, ?_⟩
  intro j hj
  simp only [cw, mac4_mem, mac4_regs _ _ _ _ _ 7 (by decide) (by decide)]

theorem narrow_cf (s : State) (j : Nat) : CF s (execAll (narrow j) s) := by
  have hr : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → (execAll (narrow j) s).regs r = s.regs r := by
    intro r h h'; apply execAll_regs_other _ _ _ h'
    simp [narrow, Instr.dsts]; omega
  refine ⟨hr, ?_⟩
  intro k hk
  simp only [cw, execAll_mem _ _ (PolyMac.narrow_noW _), hr 7 (by decide) (by decide)]

theorem colend_mem (s : State) (j : Nat) (hj : j < 7) :
    (execAll (colend j) s).mem = write32 s.mem (slot (s.regs 13) j) (s.regs 0) := by
  have ej : (BitVec.ofNat 8 j).toNat * 4 = 4*j := by simp; omega
  simp (config := { decide := true }) [execAll, colend, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, slot, ej, Nat.mod_eq_of_lt (by omega : j < 256), Nat.mul_comm]

theorem colend_cf (s : State) (hs : Sep s) (j : Nat) (hj : j < 7) : CF s (execAll (colend j) s) := by
  have hr : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → (execAll (colend j) s).regs r = s.regs r := by
    intro r h h'; apply execAll_regs_other _ _ _ h'
    simp [colend, Instr.dsts]; omega
  refine ⟨hr, ?_⟩
  intro k hk
  simp only [cw, colend_mem s j hj, hr 7 (by decide) (by decide), cw_write s hs j hj _ k hk]

theorem colend_v (s : State) (j : Nat) : v64 (execAll (colend j) s) = v64 s / 2^32 := by
  simp (config := { decide := true }) only [v64, execAll, colend, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.reg,
    M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, lslC, ite_true, ite_false]
  have := (s.regs 0).isLt
  simp
  omega

def zcol (s : State) : State := execAll [.movImm 0 0, .movImm 1 0] s
def c0 (s : State) : State := execAll (mac4 5 11 10 9) (zcol s)
def c1 (s : State) : State := execAll (narrow 9) (execAll (mac4 6 5 11 10) (execAll (colend 0) (c0 s)))
def c2 (s : State) : State := execAll (narrow 10) (execAll (mac4 7 6 5 11) (execAll (colend 1) (c1 s)))
def c3 (s : State) : State := execAll (narrow 11) (execAll (mac4 8 7 6 5) (execAll (colend 2) (c2 s)))

theorem zcol_cf (s : State) : CF s (zcol s) := by
  have hr : ∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → (zcol s).regs r = s.regs r := by
    intro r h h'; apply execAll_regs_other _ _ _ h'
    simp [Instr.dsts]; omega
  refine ⟨hr, ?_⟩
  intro j hj
  simp only [cw, hr 7 (by decide) (by decide)]
  rw [show (zcol s).mem = s.mem from execAll_mem [.movImm 0 0, .movImm 1 0] s (by decide)]

theorem zcol_v (s : State) : v64 (zcol s) = 0 := by
  simp (config := { decide := true }) [zcol, v64, execAll, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.setReg]

theorem columns_eq (s : State) : execAll columns s = c3 s := by
  simp only [columns, c3, c2, c1, c0, zcol, mac4, execAll_append]

theorem c0_cf (s : State) : CF s (c0 s) := (zcol_cf s).trans (mac4_cf _ _ _ _ _)
theorem c1_cf (s : State) (h : Sep s) : CF s (c1 s) :=
  ((c0_cf s).trans (colend_cf _ ((c0_cf s).sep h) 0 (by decide))).trans
    ((mac4_cf _ _ _ _ _).trans (narrow_cf _ _))
theorem c2_cf (s : State) (h : Sep s) : CF s (c2 s) :=
  ((c1_cf s h).trans (colend_cf _ ((c1_cf s h).sep h) 1 (by decide))).trans
    ((mac4_cf _ _ _ _ _).trans (narrow_cf _ _))
theorem c3_cf (s : State) (h : Sep s) : CF s (c3 s) :=
  ((c2_cf s h).trans (colend_cf _ ((c2_cf s h).sep h) 2 (by decide))).trans
    ((mac4_cf _ _ _ _ _).trans (narrow_cf _ _))

/-- Register-width polynomial contribution of four wide MACs. -/
def wideNat (s : State) (a b c d v : Nat) : Nat :=
  ((((v + (s.regs 8).toNat * cw s a) % 2^64 + (s.regs 9).toNat * cw s b) % 2^64 +
    (s.regs 10).toNat * cw s c) % 2^64 + (s.regs 11).toNat * cw s d) % 2^64

theorem wide_cf {s t : State} (hf : CF s t) (a b c d : Nat)
    (ha : a < 15) (hb : b < 15) (hc : c < 15) (hd : d < 15) :
    v64 (execAll (mac4 a b c d) t) = wideNat s a b c d (v64 t) := by
  rw [mac4_v t a b c d ha hb hc hd]
  simp only [wideNat, hf.regs 8 (by decide) (by decide), hf.regs 9 (by decide) (by decide),
    hf.regs 10 (by decide) (by decide), hf.regs 11 (by decide) (by decide),
    hf.words a (by omega), hf.words b (by omega), hf.words c (by omega), hf.words d (by omega)]

theorem narrow_v_cf {s t : State} (hf : CF s t) (j : Nat) (hj : j < 16) :
    v64 (execAll (narrow j) t) = (v64 t + (s.regs 14).toNat * cw s j % 2^32) % 2^64 := by
  rw [narrow_v t j hj, hf.regs 14 (by decide) (by decide), hf.words j hj]

theorem c0_v (s : State) : v64 (c0 s) = wideNat s 5 11 10 9 0 := by
  rw [c0, wide_cf (zcol_cf s) _ _ _ _ (by decide) (by decide) (by decide) (by decide), zcol_v]

theorem c1_v (s : State) (h : Sep s) :
    v64 (c1 s) = (wideNat s 6 5 11 10 (v64 (c0 s) / 2^32) + (s.regs 14).toNat * cw s 9 % 2^32) % 2^64 := by
  have hf := (c0_cf s).trans (colend_cf _ ((c0_cf s).sep h) 0 (by decide))
  rw [c1, narrow_v_cf (hf.trans (mac4_cf _ _ _ _ _)) 9 (by decide),
    wide_cf hf _ _ _ _ (by decide) (by decide) (by decide) (by decide), colend_v]

theorem c2_v (s : State) (h : Sep s) :
    v64 (c2 s) = (wideNat s 7 6 5 11 (v64 (c1 s) / 2^32) + (s.regs 14).toNat * cw s 10 % 2^32) % 2^64 := by
  have hf := (c1_cf s h).trans (colend_cf _ ((c1_cf s h).sep h) 1 (by decide))
  rw [c2, narrow_v_cf (hf.trans (mac4_cf _ _ _ _ _)) 10 (by decide),
    wide_cf hf _ _ _ _ (by decide) (by decide) (by decide) (by decide), colend_v]

theorem c3_v (s : State) (h : Sep s) :
    v64 (c3 s) = (wideNat s 8 7 6 5 (v64 (c2 s) / 2^32) + (s.regs 14).toNat * cw s 11 % 2^32) % 2^64 := by
  have hf := (c2_cf s h).trans (colend_cf _ ((c2_cf s h).sep h) 2 (by decide))
  rw [c3, narrow_v_cf (hf.trans (mac4_cf _ _ _ _ _)) 11 (by decide),
    wide_cf hf _ _ _ _ (by decide) (by decide) (by decide) (by decide), colend_v]

theorem c3_mem (s : State) (h : Sep s) :
    (c3 s).mem = write32 (write32 (write32 s.mem (slot (s.regs 13) 0) ((c0 s).regs 0))
      (slot (s.regs 13) 1) ((c1 s).regs 0)) (slot (s.regs 13) 2) ((c2 s).regs 0) := by
  have h0 : (c0 s).mem = s.mem := by
    rw [c0, mac4_mem]
    exact execAll_mem [.movImm 0 0, .movImm 1 0] s (by decide)
  have h1 : (c1 s).mem = write32 (c0 s).mem (slot ((c0 s).regs 13) 0) ((c0 s).regs 0) := by
    rw [c1, execAll_mem _ _ (PolyMac.narrow_noW _), mac4_mem, colend_mem _ 0 (by decide)]
  have h2 : (c2 s).mem = write32 (c1 s).mem (slot ((c1 s).regs 13) 1) ((c1 s).regs 0) := by
    rw [c2, execAll_mem _ _ (PolyMac.narrow_noW _), mac4_mem, colend_mem _ 1 (by decide)]
  rw [c3, execAll_mem _ _ (PolyMac.narrow_noW _), mac4_mem, colend_mem _ 2 (by decide)]
  rw [h2, h1, h0, (c2_cf s h).regs 13 (by decide) (by decide),
    (c1_cf s h).regs 13 (by decide) (by decide), (c0_cf s).regs 13 (by decide) (by decide)]

theorem v64_low (s : State) : (s.regs 0).toNat = v64 s % 2^32 := by
  have := (s.regs 0).isLt
  simp only [v64]; omega

theorem columns_slots (s : State) (h : Sep s) :
    (read32 (c3 s).mem (slot ((c3 s).regs 13) 0)).toNat = v64 (c0 s) % 2^32 ∧
    (read32 (c3 s).mem (slot ((c3 s).regs 13) 1)).toNat = v64 (c1 s) % 2^32 ∧
    (read32 (c3 s).mem (slot ((c3 s).regs 13) 2)).toNat = v64 (c2 s) % 2^32 := by
  rw [(c3_cf s h).regs 13 (by decide) (by decide), c3_mem s h]
  simp only [M0Crypto.Armv6M.read32_write32_slot _ _ _ 2 0 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 2 1 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 2 2 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 1 0 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 1 1 (by decide) (by decide),
    M0Crypto.Armv6M.read32_write32_slot _ _ _ 0 0 (by decide) (by decide),
    ite_true, ite_false, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
    show (1 : Nat) ≠ 0 by decide, v64_low]
  trivial

end M0Crypto.Release.PolyBlocks
