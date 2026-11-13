import M0Crypto.Release.X25519CRPhase

set_option linter.unusedSimpArgs false

/-!
The four-word add step that phases B and C of `combineReduce` repeat three times
(`X25519Macros.reducePhaseB`, `reducePhaseC`): `r7 := sp + 4k`, two `ldm r7!, {r4, r5}`, and
`r0..r3 += F[k..k+3]` with the carry into `r6`. `addH_exec` is its one generic lemma.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Macros (sl)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds c_adcs c_adds c_movImm)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.Blake2s (regs_movImm)

theorem regs_addRdSp_sl (s : State) (d : LowReg) (k : Nat) (hk : k < 256) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addRdSp d (sl k)).next s).regs r = if r = d.toReg then slot s.sp k else s.regs r := by
  rw [regs_addRdSp _ _ _ _ hr, sl_toNat, Nat.mod_eq_of_lt hk, Nat.mul_comm]; rfl

theorem slot_add (sp : Word) (k j : Nat) : slot sp k + BitVec.ofNat 32 (4 * j) = slot sp (k + j) := by
  simp only [slot, ofNat_add_assoc, Nat.mul_add]

theorem rd_slot (m : Mem) (sp : Word) (k j : Nat) :
    read32 m (slot sp k + BitVec.ofNat 32 (4 * j)) = fr m sp (k + j) := by
  rw [slot_add]; rfl

theorem rd_slot0 (m : Mem) (sp : Word) (k : Nat) : read32 m (slot sp k) = fr m sp k := rfl

/-- `r7 := sp + 4k`; `r0..r3 += F[k..k+3]`, carry into `r6`. -/
def addH (k : Nat) : List Instr :=
  [.addRdSp 7 (sl k), .ldm 7 0x30, .addReg 0 0 4, .dp .adcs 1 5, .ldm 7 0x30, .dp .adcs 2 4,
   .dp .adcs 3 5, .movImm 4 0, .dp .adcs 6 4]

theorem addH_exec (s : State) (k : Nat) (hk : k < 256) :
    let t := execAll (addH k) s
    let F := fr s.mem s.sp
    w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) + 2 ^ 128 * (t.regs 6).toNat =
        (w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) + 2 ^ 128 * (s.regs 6).toNat +
          w4 (F k) (F (k + 1)) (F (k + 2)) (F (k + 3))) % 2 ^ 160 ∧
      t.mem = s.mem ∧ t.regs 7 = slot s.sp (k + 4) ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t F
  have hm : t.mem = s.mem := execAll_mem _ _ (by simp [addH, Instr.writesMem])
  have h15 : (13 : Reg) ≠ 15 := by decide
  refine ⟨?_, hm, ?_, ?_⟩
  · simp only [F, t, addH, execAll]
    simp (config := {decide := true}) only [regs_adcs, regs_adds, c_adcs, c_adds, regs_ldm,
      regs_addRdSp_sl _ _ _ hk, regs_movImm, c_ldm, c_addRdSp, c_movImm, mem_ldm, mem_addRdSp,
      mem_addReg, mem_movImm, mem_dp, State.reg, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5,
      toReg6, toReg7, listRegs_30, bitCount_30, List.map, List.idxOf, List.findIdx_cons,
      List.findIdx_nil, beq_self_eq_true, Bool.cond_true, Bool.cond_false, ite_true, ite_false,
      ne_eq, List.mem_cons, State.sp, h15]
    simp only [rd_slot, slot_add, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd]
    simp only [rd_slot0]
    generalize s.regs 0 = a0; generalize s.regs 1 = a1; generalize s.regs 2 = a2
    generalize s.regs 3 = a3; generalize s.regs 6 = a6
    generalize fr s.mem (s.regs 13) k = x0; generalize fr s.mem (s.regs 13) (k + 1) = x1
    generalize fr s.mem (s.regs 13) (k + 2) = x2; generalize fr s.mem (s.regs 13) (k + 3) = x3
    have hz : (BitVec.setWidth 32 (0 : BitVec 8)).toNat = 0 := by simp
    generalize BitVec.setWidth 32 (0 : BitVec 8) = z at hz ⊢
    generalize ga0 : addWithCarry a0 x0 false = A0
    generalize ga1 : addWithCarry a1 x1 A0.2.1 = A1
    generalize ga2 : addWithCarry a2 x2 A1.2.1 = A2
    generalize ga3 : addWithCarry a3 x3 A2.2.1 = A3
    generalize ga4 : addWithCarry a6 z A3.2.1 = A4
    have e0 := adc_nat a0 x0 false; have e1 := adc_nat a1 x1 A0.2.1
    have e2 := adc_nat a2 x2 A1.2.1; have e3 := adc_nat a3 x3 A2.2.1
    have e4 := adc_nat a6 z A3.2.1
    rw [ga0] at e0; rw [ga1] at e1; rw [ga2] at e2; rw [ga3] at e3; rw [ga4] at e4
    have := carry_le a6 z A3.2.1; rw [ga4] at this
    have := A4.1.isLt
    simp only [w4, Bool.toNat_false] at *
    omega
  · simp only [t, addH, execAll]
    simp (config := {decide := true}) only [regs_adcs, regs_adds, regs_ldm,
      regs_addRdSp_sl _ _ _ hk, regs_movImm, State.reg, toReg0, toReg1, toReg2, toReg3, toReg4,
      toReg5, toReg6, toReg7, listRegs_30, bitCount_30, List.map, ite_true, ite_false,
      List.mem_cons, State.sp, slot_add]
  · intro r h15 h8
    have h15' : r.val ≠ 15 := fun e => h15 (Fin.ext e)
    exact execAll_regs_other _ _ _ h15' (by
      simp only [addH, Instr.dsts, listRegs_30]
      rcases r with ⟨n, hn⟩; simp only at h8 h15'
      simp [LowReg.toReg, show listRegs 48#8 = [4, 5] by decide]
      and_intros <;> omega)

end M0Crypto.Release.X25519CR
