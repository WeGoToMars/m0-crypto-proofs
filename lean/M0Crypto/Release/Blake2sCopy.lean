import M0Crypto.Release.Blake2sCopyCode
import M0Crypto.Release.SymReach
import M0Crypto.Release.FrameBase

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# `m0c_blake2s_copy`: the function-level contract

`copy_correct`: for disjoint non-wrapping `dst[0,n)` and `src[0,n)` (`1 <= n <= 64`), the run
returns to `lr` with `dst[0,n) = src[0,n)`, writing only `dst[0,n)` and the 20-byte frame.
-/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
theorem sr_ne (s : State) (r r' : Reg) (x : Word) (h : r' ≠ r) : (s.setReg r x).regs r' = s.regs r' :=
  setReg_regs_ne s r r' x h


attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5 M0Crypto.Proofs.toReg_6
  M0Crypto.Proofs.toReg_7

/-! ## Little-endian packing identities -/

theorem pack_half_b (b0 b1 b2 b3 : BitVec 8) :
    (b1 ++ b0).setWidth 32 ||| ((b3 ++ b2).setWidth 32 <<< 16) = b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  have g0 := BitVec.getLsbD_of_ge b0
  have g1 := BitVec.getLsbD_of_ge b1
  have g2 := BitVec.getLsbD_of_ge b2
  have g3 := BitVec.getLsbD_of_ge b3
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [g0, g1, g2, g3]

theorem pack_byte_b (b0 b1 b2 b3 : BitVec 8) :
    b0.setWidth 32 ||| ((b2 ++ b1).setWidth 32 <<< 8) ||| (b3.setWidth 32 <<< 24) = b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  have g0 := BitVec.getLsbD_of_ge b0
  have g1 := BitVec.getLsbD_of_ge b1
  have g2 := BitVec.getLsbD_of_ge b2
  have g3 := BitVec.getLsbD_of_ge b3
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [g0, g1, g2, g3]

/-! ## Byte-level memory facts -/

theorem add_ofNat_inj (a : Word) (p q : Nat) (hp : p < 2 ^ 32) (hq : q < 2 ^ 32)
    (h : a + BitVec.ofNat 32 p = a + BitVec.ofNat 32 q) : p = q := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := a.isLt
  omega

theorem write32_hit (m : Mem) (a v : Word) (q : Nat) (hq : q < 4) :
    write32 m a v (a + BitVec.ofNat 32 q) = v.extractLsb' (8 * q) 8 := by
  have key : ∀ p q : Nat, p < 4 → q < 4 → p ≠ q → a + BitVec.ofNat 32 p ≠ a + BitVec.ofNat 32 q :=
    fun p q hp hq hne h => hne (add_ofNat_inj a p q (by omega) (by omega) h)
  have h10 := key 1 0 (by omega) (by omega) (by omega)
  have h20 := key 2 0 (by omega) (by omega) (by omega)
  have h30 := key 3 0 (by omega) (by omega) (by omega)
  have h21 := key 2 1 (by omega) (by omega) (by omega)
  have h31 := key 3 1 (by omega) (by omega) (by omega)
  have h32 := key 3 2 (by omega) (by omega) (by omega)
  simp only [show BitVec.ofNat 32 0 = 0#32 from rfl, show BitVec.ofNat 32 1 = 1#32 from rfl,
    show BitVec.ofNat 32 2 = 2#32 from rfl, show BitVec.ofNat 32 3 = 3#32 from rfl, BitVec.add_zero] at h10 h20 h30 h21 h31 h32
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
  · simp [write32]
  · simp only [write32]
    rw [if_neg h10]; simp
  · simp only [write32]
    rw [if_neg h20, if_neg h21]; simp
  · simp only [write32]
    rw [if_neg h30, if_neg h31, if_neg h32]; simp

/-- Copy progress: `m` agrees with `m0`'s source bytes in `dst[0,k)` and with `m0` elsewhere. -/
def Cp (m0 m : Mem) (d s : Word) (k : Nat) : Prop :=
  (∀ i < k, m (d + BitVec.ofNat 32 i) = m0 (s + BitVec.ofNat 32 i)) ∧
  (∀ y, (∀ i < k, y ≠ d + BitVec.ofNat 32 i) → m y = m0 y)

theorem cp_zero (m0 : Mem) (d s : Word) : Cp m0 m0 d s 0 :=
  ⟨fun i hi => absurd hi (by omega), fun _ _ => rfl⟩

theorem dj_ne {d s : Word} {n : Nat} (h : Disj d n s n) {i j : Nat} (hi : i < n) (hj : j < n) :
    d + BitVec.ofNat 32 i ≠ s + BitVec.ofNat 32 j := by
  intro e
  obtain ⟨h1, h2, h3⟩ := h
  have := congrArg BitVec.toNat e
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

theorem cp_src {m0 m : Mem} {d s : Word} {n k : Nat} (hc : Cp m0 m d s k) (hd : Disj d n s n)
    (hk : k ≤ n) {j : Nat} (hj : j < n) : m (s + BitVec.ofNat 32 j) = m0 (s + BitVec.ofNat 32 j) :=
  hc.2 _ (fun i hi e => dj_ne hd (by omega) hj e.symm)

theorem cp_w8 {m0 m : Mem} {d s : Word} {k : Nat} (hk : k < 2 ^ 32) (hc : Cp m0 m d s k) (v : Word)
    (hv : v.extractLsb' 0 8 = m0 (s + BitVec.ofNat 32 k)) :
    Cp m0 (write8 m (d + BitVec.ofNat 32 k) v) d s (k + 1) := by
  constructor
  · intro i hi
    by_cases hik : i = k
    · subst hik; simp [write8, hv]
    · have hne : d + BitVec.ofNat 32 i ≠ d + BitVec.ofNat 32 k :=
        fun h => hik (add_ofNat_inj d i k (by omega) hk h)
      simp only [write8, if_neg hne]
      exact hc.1 i (by omega)
  · intro y hy
    have hne : y ≠ d + BitVec.ofNat 32 k := hy k (by omega)
    simp only [write8, if_neg hne]
    exact hc.2 y (fun i hi => hy i (by omega))

theorem cp_w32 {m0 m : Mem} {d s : Word} {k : Nat} (hk : k + 4 < 2 ^ 32) (hc : Cp m0 m d s k) (w : Word)
    (hw : ∀ j < 4, w.extractLsb' (8 * j) 8 = m0 (s + BitVec.ofNat 32 (k + j))) :
    Cp m0 (write32 m (d + BitVec.ofNat 32 k) w) d s (k + 4) := by
  constructor
  · intro i hi
    by_cases hik : i < k
    · rw [write32_other' _ _ _ _ (fun q hq e => by
        have := add_ofNat_inj d i (k + q) (by omega) (by omega)
          (by rw [e, ofNat_add_assoc])
        omega)]
      exact hc.1 i hik
    · have hq : i = k + (i - k) := by omega
      have e1 : d + BitVec.ofNat 32 i = d + BitVec.ofNat 32 k + BitVec.ofNat 32 (i - k) := by
        rw [ofNat_add_assoc]; congr 2
      rw [e1, write32_hit _ _ _ _ (by omega), hw _ (by omega)]
      rw [show k + (i - k) = i by omega]
  · intro y hy
    rw [write32_other' _ _ _ _ (fun q hq e => hy (k + q) (by omega) (by rw [e, ofNat_add_assoc]))]
    exact hc.2 y (fun i hi => hy i (by omega))

/-- Bytes of a word read from memory. -/
theorem read32_byte (m : Mem) (a : Word) (j : Nat) (hj : j < 4) :
    (read32 m a).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 32 j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    (apply BitVec.eq_of_getLsbD_eq; intro k hk
     simp only [read32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk]
     simp [hk]
     repeat' split
     all_goals first | omega | rfl | (rw [show 16 + k - 8 - 8 = k by omega]; rfl) |
      (rw [show 24 + k - 8 - 8 - 8 = k by omega, BitVec.getLsbD_eq_getElem hk]) | (simp_all; try omega))

/-! ## Block effects -/

macro "dsts_tac" : tactic =>
  `(tactic| (simp [Instr.dsts, MemOp.isLoad, Fin.ext_iff] <;> omega))

macro "eff_tac" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp [$ts,*, execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.reg,
      M0Crypto.Armv6M.State.setNZC, lsrC, lslC, Instr.exec.memOp, addFlags, M0Crypto.Release.add_flags,
      M0Crypto.Release.sub_flags]))

theorem tst_eff (a b : LowReg) (s : State) :
    (execAll [Instr.dp .tst a b] s).z = ((s.regs a.toReg &&& s.regs b.toReg) == 0#32) ∧
    (execAll [Instr.dp .tst a b] s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 15 → (execAll [Instr.dp .tst a b] s).regs r = s.regs r) := by
  refine ⟨?_, ?_, fun r h15 => execAll_regs_other _ _ r h15 (by simp [Instr.dsts])⟩ <;>
    simp [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg]

theorem cmp_eff (n : LowReg) (k : BitVec 8) (s : State) :
    (execAll [Instr.cmpImm n k] s).c = decide (k.toNat ≤ (s.regs n.toReg).toNat) ∧
    (execAll [Instr.cmpImm n k] s).z = (s.regs n.toReg == k.setWidth 32) ∧
    (execAll [Instr.cmpImm n k] s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 15 → (execAll [Instr.cmpImm n k] s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, fun r h15 => execAll_regs_other _ _ r h15 (by simp [Instr.dsts])⟩ <;>
    simp [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setNZCV, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, addFlags, M0Crypto.Armv6M.addWithCarry]
  · have := k.isLt; have := (s.regs n.toReg).isLt; omega
  · have hk := k.isLt; have hr := (s.regs n.toReg).isLt
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth]
      omega
    · intro h
      rw [h]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth] at this
      omega

theorem byteB_eff (s : State) :
    (execAll byteB s).regs 0 = s.regs 0 + 1#32 ∧ (execAll byteB s).regs 1 = s.regs 1 + 1#32 ∧
    (execAll byteB s).regs 2 = s.regs 2 - 1#32 ∧
    (execAll byteB s).mem = write8 s.mem (s.regs 0) (read8 s.mem (s.regs 1)) ∧
    (execAll byteB s).z = (s.regs 2 - 1#32 == 0#32) ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → (execAll byteB s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h4 h15 => execAll_regs_other _ _ r h15
    (by
      have h0 : r.val ≠ 0 := by omega
      have h1 : r.val ≠ 1 := by omega
      have h2 : r.val ≠ 2 := by omega
      simp [byteB, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h1, h2] <;> omega)⟩ <;> eff_tac [byteB]
  all_goals rw [show (4294967294#32 : Word) = ~~~1#32 from rfl, M0Crypto.Release.sub_flags]

theorem l78 : ∀ x : LowReg, (120#8)[(x : Nat)] = true → (x : Nat) < 7 := by decide

theorem l78' : listRegs (120#8) = [3, 4, 5, 6] := by decide
theorem b78 : bitCount (120#8) = 4 := by decide

theorem w16B_eff (s : State) :
    (execAll w16B s).regs 0 = s.regs 0 + 16#32 ∧ (execAll w16B s).regs 1 = s.regs 1 + 16#32 ∧
    (execAll w16B s).regs 2 = s.regs 2 - 16#32 ∧
    (execAll w16B s).mem = storeWords s.mem (s.regs 0)
      [read32 s.mem (s.regs 1), read32 s.mem (s.regs 1 + 4#32), read32 s.mem (s.regs 1 + 4#32 + 4#32),
        read32 s.mem (s.regs 1 + 4#32 + 4#32 + 4#32)] ∧
    (∀ r : Reg, 7 ≤ r.val → r.val ≠ 15 → (execAll w16B s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, fun r h4 h15 => execAll_regs_other _ _ r h15
    (by
      have h0 : r.val ≠ 0 := by omega
      have h1 : r.val ≠ 1 := by omega
      have h2 : r.val ≠ 2 := by omega
      have h3 : r.val ≠ 3 := by omega
      have h4' : r.val ≠ 4 := by omega
      have h5 : r.val ≠ 5 := by omega
      have h6 : r.val ≠ 6 := by omega
      simp [w16B, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h1, h2, h3, h4', h5, h6, listRegs] <;>
        first | omega | (intro x hx he; have := l78 x hx; omega))⟩ <;>
    eff_tac [w16B, l78', b78]
  all_goals simp (config := {decide := true}) [l78', b78, loadRegs, State.setReg, LowReg.toReg, Fin.ext_iff]
  all_goals rw [show (4294967279#32 : Word) = ~~~16#32 from rfl, M0Crypto.Release.sub_flags]

theorem w4B_eff (s : State) :
    (execAll w4B s).regs 0 = s.regs 0 + 4#32 ∧ (execAll w4B s).regs 1 = s.regs 1 + 4#32 ∧
    (execAll w4B s).regs 2 = s.regs 2 - 4#32 ∧
    (execAll w4B s).mem = write32 s.mem (s.regs 0) (read32 s.mem (s.regs 1)) ∧
    (∀ r : Reg, 4 ≤ r.val → r.val ≠ 15 → (execAll w4B s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, fun r h4 h15 => execAll_regs_other _ _ r h15
    (by
      have h0 : r.val ≠ 0 := by omega
      have h1 : r.val ≠ 1 := by omega
      have h2 : r.val ≠ 2 := by omega
      simp [w4B, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h1, h2] <;> omega)⟩ <;> eff_tac [w4B]
  all_goals rw [show (4294967291#32 : Word) = ~~~4#32 from rfl, M0Crypto.Release.sub_flags]

theorem unalS_eff (s : State) :
    (execAll unalS s).regs 5 = s.regs 2 >>> 2 ∧ (execAll unalS s).regs 2 = s.regs 2 &&& s.regs 4 ∧
    (execAll unalS s).regs 3 = 1#32 ∧ (execAll unalS s).z = ((s.regs 1 &&& 1#32) == 0#32) ∧
    (execAll unalS s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 5 → r.val ≠ 15 → (execAll unalS s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h2 h3 h5 h15 => execAll_regs_other _ _ r h15
    (by simp [unalS, Instr.dsts, Fin.ext_iff, h2, h3, h5] <;> omega)⟩ <;> eff_tac [unalS]

theorem l8' : listRegs (8#8) = [3] := by decide
theorem b8 : bitCount (8#8) = 1 := by decide

theorem pbB_eff (s : State) :
    (execAll pbB s).regs 0 = s.regs 0 + 4#32 ∧ (execAll pbB s).regs 1 = s.regs 1 + 4#32 ∧
    (execAll pbB s).regs 5 = s.regs 5 - 1#32 ∧ (execAll pbB s).z = (s.regs 5 - 1#32 == 0#32) ∧
    (execAll pbB s).mem = write32 s.mem (s.regs 0)
      (read8 s.mem (s.regs 1) ||| (read16 s.mem (s.regs 1 + 1#32) <<< 8) ||| (read8 s.mem (s.regs 1 + 3#32) <<< 24)) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 3 → r.val ≠ 5 → r.val ≠ 6 → r.val ≠ 7 → r.val ≠ 15 →
      (execAll pbB s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h1 h3 h5 h6 h7 h15 => execAll_regs_other _ _ r h15
    (by simp [pbB, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h1, h3, h5, h6, h7] <;> omega)⟩ <;> eff_tac [pbB, l8', b8, MemOp.width]
  all_goals try simp (config := {decide := true}) [l8', b8, loadRegs, State.setReg, LowReg.toReg, Fin.ext_iff,
    MemOp.width]
  all_goals try rw [show (4294967294#32 : Word) = ~~~1#32 from rfl, M0Crypto.Release.sub_flags]
  all_goals rfl

theorem phB_eff (s : State) :
    (execAll phB s).regs 0 = s.regs 0 + 4#32 ∧ (execAll phB s).regs 1 = s.regs 1 + 4#32 ∧
    (execAll phB s).regs 5 = s.regs 5 - 1#32 ∧ (execAll phB s).z = (s.regs 5 - 1#32 == 0#32) ∧
    (execAll phB s).mem = write32 s.mem (s.regs 0)
      (read16 s.mem (s.regs 1) ||| (read16 s.mem (s.regs 1 + 2#32) <<< 16)) ∧
    (∀ r : Reg, r.val ≠ 0 → r.val ≠ 1 → r.val ≠ 3 → r.val ≠ 5 → r.val ≠ 6 → r.val ≠ 15 →
      (execAll phB s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h1 h3 h5 h6 h15 => execAll_regs_other _ _ r h15
    (by simp [phB, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h0, h1, h3, h5, h6] <;> omega)⟩ <;> eff_tac [phB, l8', b8, MemOp.width]
  all_goals try simp (config := {decide := true}) [l8', b8, loadRegs, State.setReg, LowReg.toReg, Fin.ext_iff,
    MemOp.width]
  all_goals try rw [show (4294967294#32 : Word) = ~~~1#32 from rfl, M0Crypto.Release.sub_flags]
  all_goals try rfl

theorem pack_byte_read (m : Mem) (a : Word) :
    read8 m a ||| (read16 m (a + 1#32) <<< 8) ||| (read8 m (a + 3#32) <<< 24) = read32 m a := by
  simp only [read8, read16, read32, show a + 1#32 + 1#32 = a + 2#32 by bv_omega]
  exact pack_byte_b _ _ _ _

theorem pack_half_read (m : Mem) (a : Word) :
    read16 m a ||| (read16 m (a + 2#32) <<< 16) = read32 m a := by
  simp only [read16, read32, show a + 2#32 + 1#32 = a + 3#32 by bv_omega]
  exact pack_half_b _ _ _ _

theorem sr_pc (s : State) (v : Word) : (s.setReg 15 v).pc = v := by
  simp [State.setReg, State.pc]

theorem cp0 (u : State) : condPassed 0 u = u.z := rfl
theorem cp1 (u : State) : condPassed 1 u = !u.z := rfl
theorem cp3 (u : State) : condPassed 3 u = !u.c := rfl

/-! ## Loop invariants -/

theorem read8_low (m : Mem) (a : Word) : (read8 m a).extractLsb' 0 8 = m a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [read8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi]
  intro _; omega

theorem cp_w32_s {m0 m ms : Mem} {d s : Word} {n k : Nat} (hc : Cp m0 m d s k)
    (hs : ∀ j < n, ms (s + BitVec.ofNat 32 j) = m0 (s + BitVec.ofNat 32 j)) (hk : k + 4 ≤ n)
    (hn : n < 2 ^ 31) :
    Cp m0 (write32 m (d + BitVec.ofNat 32 k) (read32 ms (s + BitVec.ofNat 32 k))) d s (k + 4) := by
  apply cp_w32 (by omega) hc
  intro j hj
  rw [read32_byte _ _ _ hj, ofNat_add_assoc, hs _ (by omega)]

/-- The common loop state: `k` bytes are copied, `r0`, `r1`, `r2` track the cursors. -/
structure CI (R : Reg → Word) (m0 : Mem) (d s : Word) (n k : Nat) (t : State) : Prop where
  r0 : t.regs 0 = d + BitVec.ofNat 32 k
  r1 : t.regs 1 = s + BitVec.ofNat 32 k
  r2 : t.regs 2 = BitVec.ofNat 32 (n - k)
  cp : Cp m0 t.mem d s k
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≠ 15 → t.regs r = R r
  kn : k ≤ n

theorem CI.setPc {R m0 d s n k t} (h : CI R m0 d s n k t) (v : Word) : CI R m0 d s n k (t.setReg 15 v) :=
  ⟨by rw [sr_ne _ _ _ _ (by decide)]; exact h.r0, by rw [sr_ne _ _ _ _ (by decide)]; exact h.r1,
   by rw [sr_ne _ _ _ _ (by decide)]; exact h.r2, by rw [show (t.setReg 15 v).mem = t.mem from rfl]; exact h.cp,
   fun r h8 h15 => by rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.hi r h8 h15, h.kn⟩

theorem byteB_CI {R m0 d s n k t} (h : CI R m0 d s n k t) (hk : k < n) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) :
    CI R m0 d s n (k + 1) (execAll byteB t) ∧ (execAll byteB t).z = decide (k + 1 = n) := by
  obtain ⟨e0, e1, e2, em, ez, er⟩ := byteB_eff t
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hk⟩, ?_⟩
  · rw [e0, h.r0, ofNat_add_assoc]
  · rw [e1, h.r1, ofNat_add_assoc]
  · rw [e2, h.r2]; bv_omega
  · rw [em, h.r0, h.r1]
    apply cp_w8 (by omega) h.cp
    rw [read8_low, cp_src h.cp hDj (by omega) hk]
  · intro r h8 h15
    rw [er r (by omega) h15]; exact h.hi r h8 h15
  · rw [ez, h.r2]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    · intro e; have : n - k = 1 := by omega
      rw [this]; rfl

end M0Crypto.Release.Blake2sCopy
