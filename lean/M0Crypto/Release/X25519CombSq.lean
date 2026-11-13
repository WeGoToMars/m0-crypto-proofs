import M0Crypto.Release.X25519Comb

set_option linter.unusedSimpArgs false

/-!
Macro `combine128sq` of `m0c_fe_sqr` (plan `x25519-proofs.md`, phase 8), the square case of
`combine128`.

On entry `r0`-`r3` hold `P = (aL - aH)^2`, always subtracted (the words are complemented and
the chain starts with carry 1). `L` is split: words 0 and 1 at slot `k`, words 2 and 3 in `r8`
and `r10`. `H` too: words 0 and 1 in `r11` and `r12`, words 2 and 3 at slot `k + 6`. The
store is `combine128`'s (`cstore`). The value reuses `combine128_nat` with `neg = true`: the
fifth word of the first chain is `sbcs r4, r4`, which equals the mask word plus the carry.
-/

namespace M0Crypto.Release.X25519CombSq
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion WritesTo)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Release.X25519Macros (combine128sq sl)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds c_adcs c_adds c_movImm)
open M0Crypto.Release.X25519Comb
open M0Crypto.Release.Blake2s (toReg_ne15 regs_movImm regs_movHi)

/-- Everything but the final store. -/
def sqcore (k : Nat) : List Instr :=
  [.dp .mvns 0 0, .dp .mvns 1 1, .dp .mvns 2 2, .dp .mvns 3 3, .addRdSp 7 (sl k), .dp .cmp 0 0,
   .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6,
   .movHi 5 8, .movHi 6 10, .dp .adcs 2 5, .dp .adcs 3 6, .dp .sbcs 4 4,
   .movHi 5 11, .movHi 6 12,
   .addReg 0 0 5, .dp .adcs 1 6,
   .addRdSp 7 (sl (k + 6)),
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5, .subImm8 7 24,
   .movHi 5 8, .movHi 6 10, .addRdSp 7 (sl (k + 6)), .addReg 0 0 5, .dp .adcs 1 6,
   .movHi 5 11, .movHi 6 12,
   .dp .adcs 2 5, .dp .adcs 3 6,
   .ldm 7 0x60, .dp .adcs 4 5, .movImm 5 0, .dp .adcs 5 6]

theorem combine128sq_split (k : Nat) (direct : Bool) :
    combine128sq k direct = sqcore k ++ cstore direct := by cases direct <;> rfl

theorem not_mask (x : Word) : ~~~x = x ^^^ mask true := by
  simp only [mask, ite_true, BitVec.xor_allOnes]

theorem sqcore_value (s : State) (k : Nat) (h6 : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24)
    (M : Nat)
    (hmid : M + w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) =
      w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) + w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7))
    (hM : M < 2 ^ 160)
    (hZ : w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) + 2 ^ 64 * M +
      2 ^ 128 * w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7) < 2 ^ 256) :
    let t := execAll (sqcore k) s
    (cw s k 0).toNat + 2 ^ 32 * (cw s k 1).toNat +
        2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 192 * (t.regs 4).toNat +
        2 ^ 224 * (t.regs 5).toNat =
      w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) + 2 ^ 64 * M +
        2 ^ 128 * w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7) := by
  intro t
  have r0 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4)) = cw s k 0 := by
    simp [cw, State.sp]
  have r1 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 4)) = cw s k 1 := rfl
  have r6 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 24)) = cw s k 6 := rfl
  have r7 : read32 s.mem (s.regs 13 + BitVec.ofNat 32 ((sl k).toNat * 4 + 28)) = cw s k 7 := rfl
  simp only [t, sqcore, execAll]
  simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_mvns, regs_cmp,
    X25519Mul.regs_sbcs, regs_movHi, regs_movImm, regs_addRdSp, regs_subImm8, c_adcs, c_adds, c_mvns,
    c_cmp_self, X25519Mul.c_sbcs, X25519Mul.c_movHi, c_ldm, c_movImm, c_addRdSp, mem_ldm, mem_addRdSp, next_mem,
    State.sp, List.findIdx_cons, List.findIdx_nil, listRegs_60, bitCount_60, List.map,
    List.mem_cons, List.idxOf, State.reg, ne_eq, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5,
    toReg6, toReg7, ite_true, ite_false]
  simp only [h6, ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero]
  simp only [r0, r1, r6, r7, sbcs_self]
  generalize cw s k 0 = L0 at *
  generalize cw s k 1 = L1 at *
  generalize s.regs 8 = L2 at *
  generalize s.regs 10 = L3 at *
  generalize s.regs 11 = H0 at *
  generalize s.regs 12 = H1 at *
  generalize cw s k 6 = H2 at *
  generalize cw s k 7 = H3 at *
  generalize hz : BitVec.setWidth 32 (0 : BitVec 8) = z
  generalize hA0 : addWithCarry (~~~s.regs 0) L0 true = A0
  generalize hA1 : addWithCarry (~~~s.regs 1) L1 A0.2.1 = A1
  generalize hA2 : addWithCarry (~~~s.regs 2) L2 A1.2.1 = A2
  generalize hA3 : addWithCarry (~~~s.regs 3) L3 A2.2.1 = A3
  generalize hB0 : addWithCarry A0.1 H0 false = B0
  generalize hB1 : addWithCarry A1.1 H1 B0.2.1 = B1
  generalize hB2 : addWithCarry A2.1 H2 B1.2.1 = B2
  generalize hB3 : addWithCarry A3.1 H3 B2.2.1 = B3
  generalize hB4 : addWithCarry (mask (!A3.2.1)) z B3.2.1 = B4
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
  have e5 := adc_nat (mask (!A3.2.1)) z B3.2.1
  have e6 := adc_nat B4.1 H2 C3.2.1
  have e7 := adc_nat z H3 C4.2.1
  rw [hB4] at e5; rw [hC4] at e6; rw [hC5] at e7
  rw [not_mask, not_mask, not_mask, not_mask, xor4] at eA
  have e4 : (mask (!A3.2.1)).toNat + 2 ^ 32 * A3.2.1.toNat = (2 ^ 32 - 1) + z.toNat + A3.2.1.toNat := by
    rw [hz0]; cases A3.2.1 <;> rfl
  simp only [Bool.toNat_false, Bool.toNat_true, ite_true] at eA eB eC
  have l1 := w4_lt A0.1 A1.1 A2.1 A3.1; have l2 := w4_lt B0.1 B1.1 B2.1 B3.1
  have l3 := w4_lt C0.1 C1.1 C2.1 C3.1
  have lP := w4_lt (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3)
  simp only [w4] at eA eB eC hmid hZ l1 l2 l3 lP ⊢
  have key := combine128_nat true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ _ rfl
    lP rfl hz0 rfl rfl L0.isLt L1.isLt L2.isLt L3.isLt H0.isLt
    H1.isLt H2.isLt H3.isLt l2 B4.1.isLt l3 C4.1.isLt C5.1.isLt
    eA e4 eB e5 eC e6 e7 (by simp only [↓reduceIte]; exact hmid) hM hZ
  omega

theorem sqcore_falls (k : Nat) : (sqcore k).all Instr.falls = true := by
  simp [sqcore, Instr.falls]; decide

theorem sqcore_noW (k : Nat) : (sqcore k).all (!·.writesMem) = true := by
  simp [sqcore, Instr.writesMem]

theorem combine128sq_size (k : Nat) (direct : Bool) : seqSize (combine128sq k direct) = 80 := by
  cases direct <;> simp [combine128sq, seqSize, Instr.size]

theorem combine128sq_falls (k : Nat) (direct : Bool) :
    (combine128sq k direct).all Instr.falls = true := by
  cases direct <;> simp [combine128sq, Instr.falls] <;> decide

/-- `r7` after the core, memory, and the registers from `r8` up. -/
theorem sqcore_regs (s : State) (k : Nat) (h6 : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24) :
    let t := execAll (sqcore k) s
    t.regs 7 = s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + 32) ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t
  refine ⟨?_, execAll_mem _ _ (sqcore_noW k), fun r h15 h8 => ?_⟩
  · simp only [t, sqcore, execAll]
    simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_mvns, regs_cmp,
      X25519Mul.regs_sbcs, regs_movHi, regs_movImm, regs_addRdSp, regs_subImm8, next_mem,
      State.sp, listRegs_60, bitCount_60, List.map, List.mem_cons, State.reg, ne_eq, toReg0,
      toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
    simp only [h6, ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul]
  · simp only [ne_eq, Fin.ext_iff] at h15
    exact execAll_regs_other _ _ _ h15
      (by simp [sqcore, Instr.dsts, LowReg.toReg, (by decide : listRegs 96#8 = [5, 6])]; omega)

theorem sqcore_aligned (s : State) (k : Nat) (h6 : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24)
    (hsp : s.sp.toNat % 4 = 0) : alignedAll (sqcore k) s = true := by
  simp only [sqcore, alignedAll, Instr.accesses, List.all_nil, Bool.true_and, Bool.and_true]
  simp (config := {decide := true}) only [regs_ldm, regs_adcs, regs_adds, regs_mvns, regs_cmp,
    X25519Mul.regs_sbcs, regs_movHi, regs_movImm, regs_addRdSp, regs_subImm8, next_mem, State.sp,
    listRegs_60, bitCount_60, List.map, List.mem_cons, State.reg, ne_eq, toReg0, toReg1,
    toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
  simp only [h6, ofNat_add_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Bool.and_eq_true]
  simp only [State.sp] at hsp
  and_intros <;> exact wordAccesses_aligned (word_add_aligned hsp (by omega))

/-- The operands of `combine128sq` at `s`, for the middle term `M`. -/
def SqPre (s : State) (k : Nat) (M : Nat) : Prop :=
  M + w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) =
      w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) +
        w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7) ∧
  M < 2 ^ 160 ∧
  w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) + 2 ^ 64 * M +
    2 ^ 128 * w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7) < 2 ^ 256

/-- The effect of `combine128sq k direct` from `s` to `t`. -/
def SqPost (s : State) (k : Nat) (direct : Bool) (M : Nat) (t : State) : Prop :=
  (cw s k 0).toNat + 2 ^ 32 * (cw s k 1).toNat +
      2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 192 * (t.regs 4).toNat +
      2 ^ 224 * (t.regs 5).toNat =
    w4 (cw s k 0) (cw s k 1) (s.regs 8) (s.regs 10) + 2 ^ 64 * M +
      2 ^ 128 * w4 (s.regs 11) (s.regs 12) (cw s k 6) (cw s k 7) ∧
  t.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + coff direct))
    (cregs direct t) ∧
  ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r

theorem combine128sq_exec (s : State) (k : Nat) (direct : Bool) (M : Nat) (hk : k + 6 < 256)
    (hpre : SqPre s k M) : SqPost s k direct M (execAll (combine128sq k direct) s) := by
  have h6 : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24 := by
    simp only [sl, BitVec.toNat_ofNat]; omega
  obtain ⟨hmid, hM, hZ⟩ := hpre
  have V := sqcore_value s k h6 M hmid hM hZ
  obtain ⟨c7, cm, co⟩ := sqcore_regs s k h6
  rw [combine128sq_split, execAll_append]
  have S := cstore_exec (execAll (sqcore k) s) direct _ _ c7
  generalize execAll (sqcore k) s = s1 at V c7 cm co S
  generalize execAll (cstore direct) s1 = s2 at S
  obtain ⟨sm, so⟩ := S
  have k0 := so 0 (by decide) (by decide); have k1 := so 1 (by decide) (by decide)
  have k2 := so 2 (by decide) (by decide); have k3 := so 3 (by decide) (by decide)
  have k4 := so 4 (by decide) (by decide); have k5 := so 5 (by decide) (by decide)
  refine ⟨by rw [k0, k1, k2, k3, k4, k5]; exact V, ?_, fun r h15 h8 => ?_⟩
  · rw [sm, cm]; unfold cregs; rw [k0, k1, k2, k3, k4, k5]
  · rw [so r h15 (fun e => absurd h8 (by subst e; decide)), co r h15 h8]

theorem combine128sq_acc {Wr : Word → Prop} (s : State) (k : Nat) (direct : Bool) (hk : k + 6 < 256)
    (hsp : s.sp.toNat % 4 = 0)
    (hW : ∀ j < 4 * (if direct then 4 else 6),
      Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + coff direct + j))) :
    AccAll (AccOk Wr) (combine128sq k direct) s := by
  have h6 : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24 := by
    simp only [sl, BitVec.toNat_ofNat]; omega
  rw [combine128sq_split]
  refine accAll_append (accAll_of (sqcore_aligned s k h6 hsp)
    (WritesTo.of_noWritesMem _ _ (sqcore_noW k) _)) ?_
  obtain ⟨c7, -, -⟩ := sqcore_regs s k h6
  exact cstore_acc _ direct _ _ c7 hsp (by omega) hW

end M0Crypto.Release.X25519CombSq
