import M0Crypto.Release.InstrNext
import M0Crypto.Release.X25519Carry
import M0Crypto.Release.X25519Word

set_option linter.unusedSimpArgs false

/-!
The 32-bit multiply macros of the X25519 field routines (plan `x25519-proofs.md`, phase 7):
`mul32` and `sqr32` as instruction lists that mirror the generator
(`bench/x25519/gen_x25519.py`), and their effect on a state.

The lemmas are generic in the registers: the hypotheses say only that the operands are
distinct (`Dist5`, `Dist4`). Each `_exec` lemma gives the product as a `Nat` equation,
memory unchanged, and every register outside the operands unchanged. The word identities
(`mul32_bv`, `sqr32_bv`) reduce to `X25519Word.mul32_nat` and `sqr32_nat`.
-/

namespace M0Crypto.Release.X25519Mul

open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry)
open M0Crypto.Thumb

open M0Crypto.Release.InstrNext (toReg_ne15)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)

theorem lo16 (A : Word) : (BitVec.setWidth 32 (BitVec.setWidth 16 A)).toNat = A.toNat % 2 ^ 16 := by
  simp [BitVec.toNat_setWidth]; omega

theorem hi16 (A : Word) : (A >>> 16).toNat = A.toNat / 2 ^ 16 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem mul_small (x y : Word) (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (X25519Word.mul16_lt hx hy)]

theorem shl16 (x : Word) : (x <<< 16).toNat = x.toNat % 2 ^ 16 * 2 ^ 16 := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt; omega

/-- The word identity of macro `mul32`, in the shape the instruction semantics produce. -/
theorem mul32_bv (A B : Word) :
    let aL := BitVec.setWidth 32 (BitVec.setWidth 16 A)
    let bL := BitVec.setWidth 32 (BitVec.setWidth 16 B)
    let t := aL * B >>> 16
    let u := bL * A >>> 16
    let X1 := addWithCarry (bL * aL) (t <<< 16) false
    let Y1 := addWithCarry X1.1 (u <<< 16) false
    let X2 := addWithCarry (B >>> 16 * A >>> 16) (t >>> 16) X1.2.1
    let Y2 := addWithCarry X2.1 (u >>> 16) Y1.2.1
    Y1.1.toNat + 2 ^ 32 * Y2.1.toNat = A.toNat * B.toNat := by
  intro aL bL t u X1 Y1 X2 Y2
  have haL : aL.toNat = A.toNat % 2 ^ 16 := lo16 A
  have hbL : bL.toNat = B.toNat % 2 ^ 16 := lo16 B
  have haH : (A >>> 16).toNat = A.toNat / 2 ^ 16 := hi16 A
  have hbH : (B >>> 16).toNat = B.toNat / 2 ^ 16 := hi16 B
  have := A.isLt; have := B.isLt
  have l1 : A.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have l2 : B.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have l3 : A.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  have l4 : B.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  have ht : t.toNat = B.toNat / 2 ^ 16 * (A.toNat % 2 ^ 16) := by
    simp only [t]; rw [mul_small _ _ (by omega) (by omega), haL, hbH, Nat.mul_comm]
  have hu : u.toNat = A.toNat / 2 ^ 16 * (B.toNat % 2 ^ 16) := by
    simp only [u]; rw [mul_small _ _ (by omega) (by omega), hbL, haH, Nat.mul_comm]
  have hLL : (bL * aL).toNat = A.toNat % 2 ^ 16 * (B.toNat % 2 ^ 16) := by
    rw [mul_small _ _ (by omega) (by omega), haL, hbL, Nat.mul_comm]
  have hHH : (B >>> 16 * A >>> 16).toNat = A.toNat / 2 ^ 16 * (B.toNat / 2 ^ 16) := by
    rw [mul_small _ _ (by omega) (by omega), haH, hbH, Nat.mul_comm]
  have e1 := adc_nat (bL * aL) (t <<< 16) false
  have e2 := adc_nat X1.1 (u <<< 16) false
  have e3 := adc_nat (B >>> 16 * A >>> 16) (t >>> 16) X1.2.1
  have e4 := adc_nat X2.1 (u >>> 16) Y1.2.1
  rw [shl16, ht, hLL] at e1
  rw [shl16, hu] at e2
  rw [hi16, ht, hHH] at e3
  rw [hi16, hu] at e4
  simp only [Bool.toNat_false, Nat.add_zero] at e1 e2
  have key := X25519Word.mul32_nat (A.toNat % 2 ^ 16) (A.toNat / 2 ^ 16) (B.toNat % 2 ^ 16)
    (B.toNat / 2 ^ 16) X1.1.toNat X1.2.1.toNat X2.1.toNat X2.2.1.toNat Y1.1.toNat Y1.2.1.toNat
    Y2.1.toNat Y2.2.1.toNat l1 l3 l2 l4 e1 e3 e2 e4 X1.1.isLt X2.1.isLt Y1.1.isLt Y2.1.isLt
  rw [key]
  have hA : A.toNat % 2 ^ 16 + 2 ^ 16 * (A.toNat / 2 ^ 16) = A.toNat := by omega
  have hB : B.toNat % 2 ^ 16 + 2 ^ 16 * (B.toNat / 2 ^ 16) = B.toNat := by omega
  rw [hA, hB]


theorem ne_lo (x y : LowReg) (h : x.val ≠ y.val) : (x.toReg = y.toReg) = False := by
  apply eq_false; intro e; apply h; have := congrArg Fin.val e; simpa [LowReg.toReg] using this

/-! Per-instruction effects (registers away from the PC, and the carry flag). -/

theorem regs_lsr (s : State) (d m : LowReg) (k : BitVec 5) (hk0 : k.toNat ≠ 0) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lsrImm d m k).next s).regs r =
      if r = d.toReg then s.reg m >>> k.toNat else s.regs r := by
  simp [Instr.next, Instr.exec, lsrC, State.setReg, State.setNZC, State.setNZ, hr, hk0]

theorem regs_lsl (s : State) (d m : LowReg) (k : BitVec 5) (hk0 : k.toNat ≠ 0) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lslImm d m k).next s).regs r =
      if r = d.toReg then s.reg m <<< k.toNat else s.regs r := by
  simp [Instr.next, Instr.exec, lslC, State.setReg, State.setNZC, State.setNZ, hr, hk0]

theorem c_adcs (s : State) (d m : LowReg) :
    ((Instr.dp .adcs d m).next s).c = (addWithCarry (s.reg d) (s.reg m) s.c).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ]

theorem regs_muls (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .muls d m).next s).regs r = if r = d.toReg then s.reg m * s.reg d else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_uxth (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.uxth d m).next s).regs r =
      if r = d.toReg then (s.reg m).setWidth 16 |>.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem regs_adcs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .adcs d m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (s.reg m) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, hr]

theorem regs_adds (s : State) (d n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addReg d n m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg n) (s.reg m) false).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, hr]

theorem c_adds (s : State) (d n m : LowReg) :
    ((Instr.addReg d n m).next s).c = (addWithCarry (s.reg n) (s.reg m) false).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ]

/-- Macro `mul32 rl, rh, rb, rt, ru`: `rl:rh = rl * rb`. -/
def mul32 (rl rh rb rt ru : LowReg) : List Instr :=
  [.lsrImm rt rb 16, .lsrImm rh rl 16, .dp .muls rh rt, .uxth rb rb, .lsrImm ru rl 16,
   .uxth rl rl, .dp .muls rt rl, .dp .muls ru rb, .dp .muls rl rb,
   .lsrImm rb rt 16, .lslImm rt rt 16, .addReg rl rl rt, .dp .adcs rh rb,
   .lsrImm rb ru 16, .lslImm ru ru 16, .addReg rl rl ru, .dp .adcs rh rb]

structure Dist5 (a b c d e : LowReg) : Prop where
  ab : a.val ≠ b.val
  ac : a.val ≠ c.val
  ad : a.val ≠ d.val
  ae : a.val ≠ e.val
  bc : b.val ≠ c.val
  bd : b.val ≠ d.val
  be : b.val ≠ e.val
  cd : c.val ≠ d.val
  ce : c.val ≠ e.val
  de : d.val ≠ e.val

theorem mul32_exec (s : State) (rl rh rb rt ru : LowReg) (h : Dist5 rl rh rb rt ru) :
    let s' := execAll (mul32 rl rh rb rt ru) s
    (s'.reg rl).toNat + 2 ^ 32 * (s'.reg rh).toNat = (s.reg rl).toNat * (s.reg rb).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ rl.toReg → r ≠ rh.toReg → r ≠ rb.toReg → r ≠ rt.toReg →
        r ≠ ru.toReg → s'.regs r = s.regs r := by
  obtain ⟨ab, ac, ad, ae, bc, bd, be, cd, ce, de⟩ := h
  have h16 : (16 : BitVec 5).toNat = 16 := rfl
  intro s'
  refine ⟨?_, execAll_mem _ _ (by simp [mul32, Instr.writesMem]), ?_⟩
  · simp only [s', mul32, execAll, State.reg]
    simp (config := {decide := true}) only [regs_lsr _ _ _ 16 (by decide), regs_lsl _ _ _ 16 (by decide),
      regs_muls, regs_uxth, regs_adcs, regs_adds, c_adds, c_adcs, toReg_ne15, ne_eq, not_false_eq_true,
      State.reg, h16,
      ne_lo _ _ ab, ne_lo _ _ ac, ne_lo _ _ ad, ne_lo _ _ ae, ne_lo _ _ bc, ne_lo _ _ bd, ne_lo _ _ be,
      ne_lo _ _ cd, ne_lo _ _ ce, ne_lo _ _ de,
      ne_lo _ _ (Ne.symm ab), ne_lo _ _ (Ne.symm ac), ne_lo _ _ (Ne.symm ad), ne_lo _ _ (Ne.symm ae),
      ne_lo _ _ (Ne.symm bc), ne_lo _ _ (Ne.symm bd), ne_lo _ _ (Ne.symm be), ne_lo _ _ (Ne.symm cd),
      ne_lo _ _ (Ne.symm ce), ne_lo _ _ (Ne.symm de), ite_true, ite_false]
    exact mul32_bv _ _
  · intro r h15 h1 h2 h3 h4 h5
    simp only [s', mul32, execAll]
    simp only [regs_lsr _ _ _ 16 (by decide), regs_lsl _ _ _ 16 (by decide),
      regs_muls, regs_uxth, regs_adcs, regs_adds, h15, h1, h2, h3, h4, h5, ne_eq, not_false_eq_true,
      ite_false]

theorem shl17 (x : Word) : (x <<< 17).toNat = x.toNat % 2 ^ 15 * 2 ^ 17 := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt; omega

theorem hi15 (A : Word) : (A >>> 15).toNat = A.toNat / 2 ^ 15 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The word identity of macro `sqr32`, in the shape the instruction semantics produce. -/
theorem sqr32_bv (A : Word) :
    let aL := BitVec.setWidth 32 (BitVec.setWidth 16 A)
    let m := aL * A >>> 16
    let X := addWithCarry (aL * aL) (m <<< 17) false
    let Y := addWithCarry (A >>> 16 * A >>> 16) (m >>> 15) X.2.1
    X.1.toNat + 2 ^ 32 * Y.1.toNat = A.toNat * A.toNat := by
  intro aL m X Y
  have haL : aL.toNat = A.toNat % 2 ^ 16 := lo16 A
  have haH : (A >>> 16).toNat = A.toNat / 2 ^ 16 := hi16 A
  have := A.isLt
  have l1 : A.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have l3 : A.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  have hm : m.toNat = A.toNat / 2 ^ 16 * (A.toNat % 2 ^ 16) := by
    simp only [m]; rw [mul_small _ _ (by omega) (by omega), haL, haH, Nat.mul_comm]
  have hLL : (aL * aL).toNat = A.toNat % 2 ^ 16 * (A.toNat % 2 ^ 16) := by
    rw [mul_small _ _ (by omega) (by omega), haL]
  have hHH : (A >>> 16 * A >>> 16).toNat = A.toNat / 2 ^ 16 * (A.toNat / 2 ^ 16) := by
    rw [mul_small _ _ (by omega) (by omega), haH]
  have e1 := adc_nat (aL * aL) (m <<< 17) false
  have e2 := adc_nat (A >>> 16 * A >>> 16) (m >>> 15) X.2.1
  rw [shl17, hm, hLL] at e1
  rw [hi15, hm, hHH] at e2
  simp only [Bool.toNat_false, Nat.add_zero] at e1
  have key := X25519Word.sqr32_nat (A.toNat % 2 ^ 16) (A.toNat / 2 ^ 16) X.1.toNat X.2.1.toNat
    Y.1.toNat Y.2.1.toNat l1 l3 e1 e2 X.1.isLt Y.1.isLt
  rw [key]
  have hA : A.toNat % 2 ^ 16 + 2 ^ 16 * (A.toNat / 2 ^ 16) = A.toNat := by omega
  rw [hA]

theorem regs_mov (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lslImm d m 0).next s).regs r = if r = d.toReg then s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, lslC, State.setReg, State.setNZC, State.setNZ, hr]

/-- Macro `sqr32 rl, rh, rt, ru`: `rl:rh = rl^2`. `movs rt, rh` is `lsls rt, rh, #0`. -/
def sqr32 (rl rh rt ru : LowReg) : List Instr :=
  [.lsrImm rh rl 16, .uxth rl rl, .lslImm rt rh 0, .dp .muls rt rl, .dp .muls rh rh,
   .dp .muls rl rl, .lslImm ru rt 17, .lsrImm rt rt 15, .addReg rl rl ru, .dp .adcs rh rt]

/-- Four distinct low registers. -/
structure Dist4 (a b c d : LowReg) : Prop where
  ab : a.val ≠ b.val
  ac : a.val ≠ c.val
  ad : a.val ≠ d.val
  bc : b.val ≠ c.val
  bd : b.val ≠ d.val
  cd : c.val ≠ d.val

theorem sqr32_exec (s : State) (rl rh rt ru : LowReg) (h : Dist4 rl rh rt ru) :
    let s' := execAll (sqr32 rl rh rt ru) s
    (s'.reg rl).toNat + 2 ^ 32 * (s'.reg rh).toNat = (s.reg rl).toNat * (s.reg rl).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ rl.toReg → r ≠ rh.toReg → r ≠ rt.toReg → r ≠ ru.toReg →
        s'.regs r = s.regs r := by
  obtain ⟨ab, ac, ad, bc, bd, cd⟩ := h
  have h16 : (16 : BitVec 5).toNat = 16 := rfl
  have h17 : (17 : BitVec 5).toNat = 17 := rfl
  have h15 : (15 : BitVec 5).toNat = 15 := rfl
  intro s'
  refine ⟨?_, execAll_mem _ _ (by simp [sqr32, Instr.writesMem]), ?_⟩
  · simp only [s', sqr32, execAll, State.reg]
    simp only [regs_lsr _ _ _ 16 (by decide), regs_lsr _ _ _ 15 (by decide),
      regs_lsl _ _ _ 17 (by decide), regs_mov, regs_muls, regs_uxth, regs_adcs, regs_adds,
      c_adds, toReg_ne15, ne_eq, not_false_eq_true, State.reg, h16, h17, h15,
      ne_lo _ _ ab, ne_lo _ _ ac, ne_lo _ _ ad, ne_lo _ _ bc, ne_lo _ _ bd, ne_lo _ _ cd,
      ne_lo _ _ (Ne.symm ab), ne_lo _ _ (Ne.symm ac), ne_lo _ _ (Ne.symm ad),
      ne_lo _ _ (Ne.symm bc), ne_lo _ _ (Ne.symm bd), ne_lo _ _ (Ne.symm cd), ite_true, ite_false]
    exact sqr32_bv _
  · intro r h15 h1 h2 h3 h4
    simp only [s', sqr32, execAll]
    simp only [regs_lsr _ _ _ 16 (by decide), regs_lsr _ _ _ 15 (by decide),
      regs_lsl _ _ _ 17 (by decide), regs_mov, regs_muls, regs_uxth, regs_adcs, regs_adds,
      h15, h1, h2, h3, h4, ne_eq, not_false_eq_true, ite_false]

end M0Crypto.Release.X25519Mul
