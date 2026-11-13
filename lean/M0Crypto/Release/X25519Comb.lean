import M0Crypto.Release.X25519Diff

set_option linter.unusedSimpArgs false

/-!
Macro `combine128` of `m0c_fe_mul`, the product case
(`square = False`): the last step of one level of Karatsuba multiplication at 128 bits.

On entry `r0`-`r3` hold the middle product `P` (`|aL - aH| * |bL - bH|`) and `r4` the mask
`neg` (all ones when `P` is subtracted); the operand area at slot `k` holds `L` (words 0-3)
and `H` (words 4-7). The macro forms `M = L + H - P` (or `+ P`) over five words, then
`L + 2^64 * M + 2^128 * H`; words 0 and 1 are `L`'s and stay in place. Words 2-7 are left in
`r0`-`r5`. The non-direct form stores all six at slot `k + 2`; the direct form stores words
4-7 at slot `k + 4` and leaves words 2 and 3 in `r0`, `r1`.

The macro is the register-and-load core `ccore` and the store `cstore`. The value is
`combine128_nat` over the carry equations of the four-word chains of `X25519W4`.
-/

namespace M0Crypto.Release.X25519Comb
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion WritesTo)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Release.X25519Macros (combine128 sl)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds c_adcs c_adds regs_lsr c_movImm c_lsr1)
open M0Crypto.Release.InstrNext (toReg_ne15 regs_eors regs_movImm)

theorem listRegs_60 : listRegs 0x60 = [5, 6] := by decide
theorem bitCount_60 : bitCount 0x60 = 2 := by decide
theorem listRegs_3c : listRegs 0x3c = [2, 3, 4, 5] := by decide
theorem bitCount_3c : bitCount 0x3c = 4 := by decide
theorem listRegs_3f : listRegs 0x3f = [0, 1, 2, 3, 4, 5] := by decide
theorem bitCount_3f : bitCount 0x3f = 6 := by decide

/-- `subs rd, #i` on a pointer `a + (x + c)` with `i ≤ c`. -/
theorem sub_imm (a : Word) (x c : Nat) (i : BitVec 8) (h : i.toNat ≤ c) :
    (addWithCarry (a + BitVec.ofNat 32 (x + c)) (~~~(i.setWidth 32)) true).1 =
      a + BitVec.ofNat 32 (x + (c - i.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have := i.isLt; have := a.isLt
  simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_not,
    BitVec.toNat_setWidth, Bool.toNat_true]
  omega

theorem t24 : (24 : BitVec 8).toNat = 24 := rfl
theorem t16 : (16 : BitVec 8).toNat = 16 := rfl

theorem lsb_mask (neg : Bool) : (mask neg).getLsbD 0 = neg := by cases neg <;> rfl

/-- The value of `combine128`. `X` is `P` or its complement; the first chain adds `L` and the
carry in `neg` over five words (the fifth is the mask word plus `z = 0`), the second adds `H`,
the third adds `L`'s high half and `H` at word 2. `M` is the middle term. -/
theorem combine128_nat (neg : Bool)
    (P X L H L0 L1 L2 L3 H0 H1 H2 H3 Av a4 m z Bv b4 Cv c4 c5 M c4a c5a c4b c5b c4c c5c c6 : Nat)
    (hX : X = if neg then 2 ^ 128 - 1 - P else P) (hP : P < 2 ^ 128)
    (hm : m = if neg then 2 ^ 32 - 1 else 0) (hz : z = 0)
    (hL : L = L0 + 2 ^ 32 * L1 + 2 ^ 64 * L2 + 2 ^ 96 * L3)
    (hH : H = H0 + 2 ^ 32 * H1 + 2 ^ 64 * H2 + 2 ^ 96 * H3)
    (l0 : L0 < 2 ^ 32) (l1 : L1 < 2 ^ 32) (l2 : L2 < 2 ^ 32) (l3 : L3 < 2 ^ 32)
    (g0 : H0 < 2 ^ 32) (g1 : H1 < 2 ^ 32) (g2 : H2 < 2 ^ 32) (g3 : H3 < 2 ^ 32)
    (hBv : Bv < 2 ^ 128) (hb4 : b4 < 2 ^ 32)
    (hCv : Cv < 2 ^ 128) (hc4 : c4 < 2 ^ 32) (hc5 : c5 < 2 ^ 32)
    (e1 : Av + 2 ^ 128 * c4a = X + L + (if neg then 1 else 0))
    (e2 : a4 + 2 ^ 32 * c5a = m + z + c4a)
    (e3 : Bv + 2 ^ 128 * c4b = Av + H + 0)
    (e4 : b4 + 2 ^ 32 * c5b = a4 + z + c4b)
    (e5 : Cv + 2 ^ 128 * c4c = Bv + (L2 + 2 ^ 32 * L3 + 2 ^ 64 * H0 + 2 ^ 96 * H1) + 0)
    (e6 : c4 + 2 ^ 32 * c5c = b4 + H2 + c4c)
    (e7 : c5 + 2 ^ 32 * c6 = z + H3 + c5c)
    (hmid : if neg then M + P = L + H else M = L + H + P) (hM : M < 2 ^ 160)
    (hZ : L + 2 ^ 64 * M + 2 ^ 128 * H < 2 ^ 256) :
    L0 + 2 ^ 32 * L1 + 2 ^ 64 * Cv + 2 ^ 192 * c4 + 2 ^ 224 * c5 =
      L + 2 ^ 64 * M + 2 ^ 128 * H := by
  subst hX hm hz hL hH
  have s1 : Bv + 2 ^ 128 * b4 = M := by
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] at e1 e2 hmid <;> omega
  omega

/-- Everything but the final store: forms the six words in `r0`-`r5`; `r7` ends 8 words past
slot `k`. -/
def ccore (k : Nat) : List Instr :=
  [.dp .eors 0 4, .dp .eors 1 4, .dp .eors 2 4, .dp .eors 3 4, .addRdSp 7 (sl k), .lsrImm 5 4 1,
   .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5,
   .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5, .subImm8 7 24,
   .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6,
   .ldm 7 0x60, .dp .adcs 4 5, .movImm 5 0, .dp .adcs 5 6]

/-- The store: words 2-7 (non-direct) or 4-7 (direct). -/
def cstore (direct : Bool) : List Instr :=
  [.subImm8 7 (if direct then 16 else 24), .stm 7 (if direct then 0x3c else 0x3f)]

theorem combine128_split (k : Nat) (direct : Bool) :
    combine128 k direct = ccore k ++ cstore direct := by cases direct <;> rfl

/-- Word `j` of the operand area at slot `k`. -/
def cw (s : State) (k j : Nat) : Word :=
  read32 s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + 4 * j))

theorem ccore_value (s : State) (k : Nat) (neg : Bool) (hm : s.regs 4 = mask neg) (M : Nat)
    (hmid : let P := w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3)
      let L := w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3)
      let H := w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7)
      if neg then M + P = L + H else M = L + H + P)
    (hM : M < 2 ^ 160)
    (hZ : w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3) + 2 ^ 64 * M +
      2 ^ 128 * w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7) < 2 ^ 256) :
    let t := execAll (ccore k) s
    (cw s k 0).toNat + 2 ^ 32 * (cw s k 1).toNat +
        2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 192 * (t.regs 4).toNat +
        2 ^ 224 * (t.regs 5).toNat =
      w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3) + 2 ^ 64 * M +
        2 ^ 128 * w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7) := by
  intro t
  have r0 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4)) = cw s k 0 := by
    simp [cw, State.sp]
  have r1 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 4)) = cw s k 1 := rfl
  have r2 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 8)) = cw s k 2 := rfl
  have r3 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 12)) = cw s k 3 := rfl
  have r4 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 16)) = cw s k 4 := rfl
  have r5 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 20)) = cw s k 5 := rfl
  have r6 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 24)) = cw s k 6 := rfl
  have r7 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 28)) = cw s k 7 := rfl
  simp only [t, ccore, execAll]
  simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_eors,
    regs_movImm, regs_lsr _ _ _ 1 (by decide), regs_addRdSp, regs_subImm8, c_adcs, c_adds, c_eors,
    c_ldm, c_movImm, c_lsr1, c_addRdSp, mem_ldm, mem_addRdSp, next_mem, State.sp,
    List.findIdx_cons, List.findIdx_nil, listRegs_60, bitCount_60, List.map, List.mem_cons,
    List.idxOf, State.reg, ne_eq, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7,
    ite_true, ite_false]
  simp only [hm, lsb_mask, ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul,
    Nat.add_zero]
  simp (config := {decide := true}) only [sub_imm, t24, Nat.reduceSub, ofNat_add_assoc,
    Nat.add_assoc, Nat.reduceAdd]
  simp only [r0, r1, r2, r3, r4, r5, r6, r7]
  simp only at hmid
  generalize cw s k 0 = L0 at *
  generalize cw s k 1 = L1 at *
  generalize cw s k 2 = L2 at *
  generalize cw s k 3 = L3 at *
  generalize cw s k 4 = H0 at *
  generalize cw s k 5 = H1 at *
  generalize cw s k 6 = H2 at *
  generalize cw s k 7 = H3 at *
  generalize hz : BitVec.setWidth 32 (0 : BitVec 8) = z
  generalize hA0 : addWithCarry (s.regs 0 ^^^ mask neg) L0 neg = A0
  generalize hA1 : addWithCarry (s.regs 1 ^^^ mask neg) L1 A0.2.1 = A1
  generalize hA2 : addWithCarry (s.regs 2 ^^^ mask neg) L2 A1.2.1 = A2
  generalize hA3 : addWithCarry (s.regs 3 ^^^ mask neg) L3 A2.2.1 = A3
  generalize hA4 : addWithCarry (mask neg) z A3.2.1 = A4
  generalize hB0 : addWithCarry A0.1 H0 false = B0
  generalize hB1 : addWithCarry A1.1 H1 B0.2.1 = B1
  generalize hB2 : addWithCarry A2.1 H2 B1.2.1 = B2
  generalize hB3 : addWithCarry A3.1 H3 B2.2.1 = B3
  generalize hB4 : addWithCarry A4.1 z B3.2.1 = B4
  generalize hC0 : addWithCarry B0.1 L2 false = C0
  generalize hC1 : addWithCarry B1.1 L3 C0.2.1 = C1
  generalize hC2 : addWithCarry B2.1 H0 C1.2.1 = C2
  generalize hC3 : addWithCarry B3.1 H1 C2.2.1 = C3
  generalize hC4 : addWithCarry B4.1 H2 C3.2.1 = C4
  generalize hC5 : addWithCarry z H3 C4.2.1 = C5
  have hz0 : z.toNat = 0 := by rw [← hz]; rfl
  have eA := add4 hA0 hA1 hA2 hA3
  have eB := add4 hB0 hB1 hB2 hB3
  have eC := add4 hC0 hC1 hC2 hC3
  have e4 := adc_nat (mask neg) z A3.2.1
  have e5 := adc_nat A4.1 z B3.2.1
  have e6 := adc_nat B4.1 H2 C3.2.1
  have e7 := adc_nat z H3 C4.2.1
  rw [hA4] at e4; rw [hB4] at e5; rw [hC4] at e6; rw [hC5] at e7
  rw [xor4] at eA
  have hneg : neg.toNat = if neg then 1 else 0 := by cases neg <;> rfl
  rw [hneg] at eA
  simp only [Bool.toNat_false] at eB eC
  have l1 := w4_lt A0.1 A1.1 A2.1 A3.1; have l2 := w4_lt B0.1 B1.1 B2.1 B3.1
  have l3 := w4_lt C0.1 C1.1 C2.1 C3.1
  have lP := w4_lt (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3)
  simp only [w4] at eA eB eC hmid hZ l1 l2 l3 lP ⊢
  have key := combine128_nat neg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ rfl
    lP (mask_toNat neg) hz0 rfl rfl L0.isLt L1.isLt L2.isLt L3.isLt H0.isLt
    H1.isLt H2.isLt H3.isLt l2 B4.1.isLt l3 C4.1.isLt C5.1.isLt
    eA e4 eB e5 eC e6 e7 hmid hM hZ
  omega

theorem ccore_falls (k : Nat) : (ccore k).all Instr.falls = true := by
  simp [ccore, Instr.falls]

theorem ccore_size (k : Nat) : seqSize (ccore k) = 66 := by
  simp [ccore, seqSize, Instr.size]

theorem ccore_noW (k : Nat) : (ccore k).all (!·.writesMem) = true := by
  simp [ccore, Instr.writesMem]

/-- `r7` after the core, memory, and the registers from `r8` up. -/
theorem ccore_regs (s : State) (k : Nat) :
    let t := execAll (ccore k) s
    t.regs 7 = s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + 32) ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t
  refine ⟨?_, execAll_mem _ _ (ccore_noW k), fun r h15 h8 => ?_⟩
  · simp only [t, ccore, execAll]
    simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_eors,
      regs_movImm, regs_lsr _ _ _ 1 (by decide), regs_addRdSp, regs_subImm8, next_mem, State.sp,
      listRegs_60, bitCount_60, List.map, List.mem_cons, State.reg, ne_eq, toReg0, toReg1,
      toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
    simp only [ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]
    simp (config := {decide := true}) only [sub_imm, t24, Nat.reduceSub, ofNat_add_assoc,
      Nat.add_assoc, Nat.reduceAdd]
  · simp only [ne_eq, Fin.ext_iff] at h15
    exact execAll_regs_other _ _ _ h15
      (by simp [ccore, Instr.dsts, LowReg.toReg, (by decide : listRegs 96#8 = [5, 6])]; omega)

theorem ccore_aligned (s : State) (k : Nat) (hsp : s.sp.toNat % 4 = 0) :
    alignedAll (ccore k) s = true := by
  simp only [ccore, alignedAll, Instr.accesses, List.all_nil, Bool.true_and, Bool.and_true]
  simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_eors,
    regs_movImm, regs_lsr _ _ _ 1 (by decide), regs_addRdSp, regs_subImm8, next_mem, State.sp,
    listRegs_60, bitCount_60, List.map, List.mem_cons, State.reg, ne_eq, toReg0, toReg1,
    toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
  simp only [ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]
  simp (config := {decide := true}) only [sub_imm, t24, Nat.reduceSub, ofNat_add_assoc,
    Nat.add_assoc, Nat.reduceAdd, Bool.and_eq_true]
  simp only [State.sp] at hsp
  and_intros <;> exact wordAccesses_aligned (word_add_aligned hsp (by omega))

/-- Byte offset of the store from slot `k`, and the stored registers. -/
def coff (direct : Bool) : Nat := if direct then 16 else 8

def cregs (direct : Bool) (t : State) : List Word :=
  if direct then [t.regs 2, t.regs 3, t.regs 4, t.regs 5]
  else [t.regs 0, t.regs 1, t.regs 2, t.regs 3, t.regs 4, t.regs 5]

theorem cregs_length (direct : Bool) (t : State) :
    (cregs direct t).length = if direct then 4 else 6 := by cases direct <;> rfl

theorem cstore_exec (s : State) (direct : Bool) (a : Word) (x : Nat)
    (h7 : s.regs 7 = a + BitVec.ofNat 32 (x + 32)) :
    let t := execAll (cstore direct) s
    (t.mem = storeWords s.mem (a + BitVec.ofNat 32 (x + coff direct)) (cregs direct s)) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 7 → t.regs r = s.regs r := by
  intro t
  constructor
  · cases direct <;>
    simp (config := {decide := true}) only [t, cstore, coff, cregs, execAll, mem_stm,
      regs_subImm8, next_mem, State.reg, toReg7, h7, ite_true, ite_false, Bool.false_eq_true,
      sub_imm, t24, t16, Nat.reduceSub, listRegs_3c, listRegs_3f, List.map, toReg0, toReg1,
      toReg2, toReg3, toReg4, toReg5, ne_eq, regs_subImm8] <;> rfl
  · intro r h15 h7'
    simp only [t, cstore, execAll, regs_stm _ _ _ _ h15, regs_subImm8 _ _ _ _ h15, toReg7, h7',
      ite_false]

theorem cstore_acc {Wr : Word → Prop} (s : State) (direct : Bool) (a : Word) (x : Nat)
    (h7 : s.regs 7 = a + BitVec.ofNat 32 (x + 32)) (ha : a.toNat % 4 = 0) (hx : x % 4 = 0)
    (hW : ∀ j < 4 * (if direct then 4 else 6), Wr (a + BitVec.ofNat 32 (x + coff direct + j))) :
    AccAll (AccOk Wr) (cstore direct) s := by
  refine accAll_cons (fun a ha => by simp [Instr.accesses] at ha) (accAll_cons ?_ (accAll_nil _ _))
  intro b hb
  have e : ((Instr.subImm8 7 (if direct then 16 else 24)).next s).reg 7 =
      a + BitVec.ofNat 32 (x + coff direct) := by
    cases direct <;>
    simp (config := {decide := true}) only [State.reg, toReg7, regs_subImm8, h7, ite_true,
      sub_imm, t24, t16, Nat.reduceSub, coff, Bool.false_eq_true, ite_false]
  simp only [Instr.accesses, e] at hb
  have hc : bitCount (if direct then 0x3c else 0x3f) = if direct then 4 else 6 := by
    cases direct <;> decide
  rw [hc] at hb
  refine wordAccesses_ok (word_add_aligned ha (by cases direct <;> simp [coff] <;> omega))
    (fun _ i hi q hq => ?_) b hb
  rw [ofNat_add_assoc, ofNat_add_assoc]
  exact hW _ (by omega)

theorem combine128_size (k : Nat) (direct : Bool) : seqSize (combine128 k direct) = 70 := by
  cases direct <;> simp [combine128, seqSize, Instr.size]

theorem combine128_falls (k : Nat) (direct : Bool) : (combine128 k direct).all Instr.falls = true := by
  cases direct <;> simp [combine128, Instr.falls]

/-- The effect of `combine128 k direct` from `s` to `t`, for the middle term `M`. -/
def CombPost (s : State) (k : Nat) (direct : Bool) (M : Nat) (t : State) : Prop :=
  (cw s k 0).toNat + 2 ^ 32 * (cw s k 1).toNat +
      2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 192 * (t.regs 4).toNat +
      2 ^ 224 * (t.regs 5).toNat =
    w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3) + 2 ^ 64 * M +
      2 ^ 128 * w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7) ∧
  t.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + coff direct))
    (cregs direct t) ∧
  ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r

/-- The hypotheses on the middle term: `M = L + H - P` (or `+ P`), with the bounds that hold for a
product. -/
def CombPre (s : State) (k : Nat) (neg : Bool) (M : Nat) : Prop :=
  s.regs 4 = mask neg ∧
  (let P := w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3)
   let L := w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3)
   let H := w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7)
   if neg then M + P = L + H else M = L + H + P) ∧
  M < 2 ^ 160 ∧
  w4 (cw s k 0) (cw s k 1) (cw s k 2) (cw s k 3) + 2 ^ 64 * M +
    2 ^ 128 * w4 (cw s k 4) (cw s k 5) (cw s k 6) (cw s k 7) < 2 ^ 256

theorem combine128_exec (s : State) (k : Nat) (direct : Bool) (neg : Bool) (M : Nat)
    (hpre : CombPre s k neg M) : CombPost s k direct M (execAll (combine128 k direct) s) := by
  obtain ⟨hm, hmid, hM, hZ⟩ := hpre
  have V := ccore_value s k neg hm M hmid hM hZ
  obtain ⟨c7, cm, co⟩ := ccore_regs s k
  rw [combine128_split, execAll_append]
  have S := cstore_exec (execAll (ccore k) s) direct _ _ c7
  generalize execAll (ccore k) s = s1 at V c7 cm co S
  generalize execAll (cstore direct) s1 = s2 at S
  obtain ⟨sm, so⟩ := S
  have k0 := so 0 (by decide) (by decide); have k1 := so 1 (by decide) (by decide)
  have k2 := so 2 (by decide) (by decide); have k3 := so 3 (by decide) (by decide)
  have k4 := so 4 (by decide) (by decide); have k5 := so 5 (by decide) (by decide)
  refine ⟨by rw [k0, k1, k2, k3, k4, k5]; exact V, ?_, fun r h15 h8 => ?_⟩
  · rw [sm, cm]; unfold cregs; rw [k0, k1, k2, k3, k4, k5]
  · rw [so r h15 (fun e => absurd h8 (by subst e; decide)), co r h15 h8]

theorem combine128_acc {Wr : Word → Prop} (s : State) (k : Nat) (direct : Bool)
    (hsp : s.sp.toNat % 4 = 0)
    (hW : ∀ j < 4 * (if direct then 4 else 6),
      Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + coff direct + j))) :
    AccAll (AccOk Wr) (combine128 k direct) s := by
  rw [combine128_split]
  refine accAll_append (accAll_of (ccore_aligned s k hsp) (WritesTo.of_noWritesMem _ _ (ccore_noW k) _)) ?_
  obtain ⟨c7, -, -⟩ := ccore_regs s k
  exact cstore_acc _ direct _ _ c7 hsp (by omega) hW

/-- One `combine128` block in a `ReachW` proof. -/
theorem combine128_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off k : Nat} {direct neg : Bool} {M : Nat}
    (hseq : seqAt B off (combine128 k direct) = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off 70)
    (hsp : t.sp.toNat % 4 = 0) (hpre : CombPre t k neg M)
    (hW : ∀ j < 4 * (if direct then 4 else 6),
      Wr (t.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + coff direct + j))) {Q : State → Prop}
    (kk : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 70) → CombPost t k direct M t' →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hf := combine128_falls k direct
  refine ReachW.blockAcc hb _ off hpc hoff hseq hf (combine128_acc t k direct hsp hW)
    (by rw [combine128_size]; exact hr) (kk _ ?_ (combine128_exec t k direct neg M hpre))
  rw [execAll_pc _ _ hf, combine128_size, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Comb
