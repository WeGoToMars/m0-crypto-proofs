import M0Crypto.Release.X25519Mul
import M0Crypto.Release.X25519Kara
import M0Crypto.Thumb.SeqScan
import M0Crypto.Artifacts.Release
import M0Crypto.Release.ReachSteps
import M0Crypto.Thumb.ReleaseCheck.X25519Cases

set_option linter.unusedSimpArgs false

/-!
Macro `mul64` of the X25519 field routines (plan `x25519-proofs.md`, phase 7): one level of
Karatsuba with a signed middle term, `b1:a1:b0:a0 = (a1:a0) * (b1:b0)`.

The macro is split as the generator writes it: `mul64Pre` (save `b0`, `b1` in two high
registers, then the two absolute differences `|a1 - a0|`, `|b0 - b1|` and the sign mask),
three `mul32`, two short register moves (`mul64Mid1`, `mul64Mid2`) and the carry tail
`mul64Post`. Each piece has its own lemma; `mul64_exec` composes them. The composition never
names the operands of the inner macros: `generalize` takes them from the goal and the
`_eq` forms of the step lemmas read them from the run equation, and register disequalities
are closed by `regne`. So renaming the scratch registers of an inner `mul32`, or reordering
independent instructions inside a piece, needs no edit here (phase 7 drills (a) and (b)).

The value of the tail is `X25519Kara.mul64_tail_nat`; the middle term comes from
`X25519Kara.cross`. `mul64_run_w` is the `ReachW` block lemma, generic in the registers and
the offset. The instance checks bind the lists to the artifact at the first `mul64` of
`m0c_fe_mul` and the first `sqr32` of `m0c_fe_sqr`, from the routine symbols.
-/

namespace M0Crypto.Release.X25519Mul
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.InstrNext (toReg_ne15 regs_eors regs_movHi regs_movImm)

theorem regs_subs (s : State) (d n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subReg d n m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg n) (~~~(s.reg m)) true).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, hr]

theorem c_subs (s : State) (d n m : LowReg) :
    ((Instr.subReg d n m).next s).c = (addWithCarry (s.reg n) (~~~(s.reg m)) true).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ]

theorem regs_sbcs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .sbcs d m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (~~~(s.reg m)) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, hr]

theorem c_sbcs (s : State) (d m : LowReg) :
    ((Instr.dp .sbcs d m).next s).c = (addWithCarry (s.reg d) (~~~(s.reg m)) s.c).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ]

/-- The sign mask from a borrow: `sbcs m, m` after a subtraction with carry `c`. -/
theorem sbcs_self (M : Word) (c : Bool) :
    (addWithCarry M (~~~M) c).1 = if c then 0#32 else BitVec.allOnes 32 := by
  apply BitVec.eq_of_toNat_eq
  have e := X25519Carry.adc_nat M (~~~M) c
  have hn : (~~~M).toNat = 2 ^ 32 - 1 - M.toNat := by simp [BitVec.toNat_not]
  have := M.isLt; have := (addWithCarry M (~~~M) c).1.isLt
  have := X25519Carry.carry_le M (~~~M) c
  cases c <;> simp at e ⊢ <;> omega

/-- `subs d, x, y; sbcs m, m; eors d, m; subs d, m` on words: `d = |x - y|` and the mask `m`
is all ones exactly when `x < y`. -/
theorem absdiff_bv (X Y : Word) :
    let D := addWithCarry X (~~~Y) true
    let Mk := if D.2.1 then 0#32 else BitVec.allOnes 32
    let R := (addWithCarry (D.1 ^^^ Mk) (~~~Mk) true).1
    Mk = (if X.toNat < Y.toNat then BitVec.allOnes 32 else 0#32) ∧
      (X.toNat : Int) - Y.toNat = if X.toNat < Y.toNat then -(R.toNat : Int) else R.toNat := by
  intro D Mk R
  have e := X25519Carry.sbc_nat X Y true
  have hl := X25519Carry.carry_le X (~~~Y) true
  have := X.isLt; have := Y.isLt; have := D.1.isLt
  simp only [Bool.toNat_true] at e
  by_cases h : X.toNat < Y.toNat
  · have hc : D.2.1 = false := by
      cases hD : D.2.1
      · rfl
      · simp only [D, hD, Bool.toNat_true] at e; omega
    have hM : Mk = BitVec.allOnes 32 := by simp [Mk, hc]
    refine ⟨by simp [hM, h], ?_⟩
    simp only [h, ↓reduceIte]
    have e2 := X25519Carry.adc_nat (~~~D.1) 0#32 true
    have := X25519Carry.carry_le (~~~D.1) 0#32 true
    have hR : R = (addWithCarry (~~~D.1) 0#32 true).1 := by
      simp only [R, hM, BitVec.xor_allOnes, BitVec.not_allOnes]
    simp only [D, hc, Bool.toNat_false] at e
    rw [BitVec.toNat_not] at e2
    have := (addWithCarry (~~~D.1) 0#32 true).1.isLt
    simp only [BitVec.toNat_zero, Bool.toNat_true] at e2
    rw [hR]; simp only [D] at *; omega
  · have hc : D.2.1 = true := by
      cases hD : D.2.1
      · simp only [D, hD, Bool.toNat_false] at e; omega
      · rfl
    have hM : Mk = 0#32 := by simp [Mk, hc]
    refine ⟨by simp [hM, h], ?_⟩
    simp only [h, ↓reduceIte]
    have e2 := X25519Carry.adc_nat D.1 (BitVec.allOnes 32) true
    have := X25519Carry.carry_le D.1 (BitVec.allOnes 32) true
    have hR : R = (addWithCarry D.1 (BitVec.allOnes 32) true).1 := by
      simp only [R, hM, BitVec.xor_zero, BitVec.not_zero]
    simp only [D, hc, Bool.toNat_true] at e
    have := (addWithCarry D.1 (BitVec.allOnes 32) true).1.isLt
    simp only [BitVec.toNat_allOnes, Bool.toNat_true] at e2
    rw [hR]; simp only [D] at *; omega


/-- `subs d, x, y; sbcs m, m; eors d, m; subs d, m`. -/
def absdiff (d x y m : LowReg) : List Instr :=
  [.subReg d x y, .dp .sbcs m m, .dp .eors d m, .subReg d d m]

theorem absdiff_exec (s : State) (d x y m : LowReg) (hdm : d.val ≠ m.val) :
    let s' := execAll (absdiff d x y m) s
    s'.reg m = (if (s.reg x).toNat < (s.reg y).toNat then BitVec.allOnes 32 else 0#32) ∧
      ((s.reg x).toNat : Int) - (s.reg y).toNat =
        (if (s.reg x).toNat < (s.reg y).toNat then -((s'.reg d).toNat : Int) else (s'.reg d).toNat) ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → r ≠ m.toReg → s'.regs r = s.regs r := by
  intro s'
  have hb := absdiff_bv (s.reg x) (s.reg y)
  refine ⟨?_, ?_, execAll_mem _ _ (by simp [absdiff, Instr.writesMem]), ?_⟩
  · simp only [s', absdiff, execAll, State.reg]
    simp only [regs_subs, regs_sbcs, regs_eors, c_subs, toReg_ne15, ne_eq, not_false_eq_true,
      State.reg, ne_lo _ _ hdm, ne_lo _ _ (Ne.symm hdm), ite_true, ite_false, sbcs_self]
    simp only [State.reg] at hb; exact hb.1
  · simp only [s', absdiff, execAll, State.reg]
    simp only [regs_subs, regs_sbcs, regs_eors, c_subs, toReg_ne15, ne_eq, not_false_eq_true,
      State.reg, ne_lo _ _ hdm, ne_lo _ _ (Ne.symm hdm), ite_true, ite_false, sbcs_self]
    simp only [State.reg] at hb; exact hb.2
  · intro r h15 hd hm
    simp only [s', absdiff, execAll]
    simp only [regs_subs, regs_sbcs, regs_eors, h15, hd, hm, ne_eq, not_false_eq_true, ite_false]

def movs2 (h1 h2 : Reg) (x y : LowReg) : List Instr := [.movHi h1 x.toReg, .movHi h2 y.toReg]

def mul64Pre (a0 a1 b0 b1 t1 t3 t4 : LowReg) (h1 h2 : Reg) : List Instr :=
  movs2 h1 h2 b0 b1 ++ absdiff t1 a1 a0 t3 ++ absdiff t4 b0 b1 b1 ++ [.dp .eors t3 b1]

def mul64Mid1 (t1 t2 t3 t4 : LowReg) (h1 : Reg) : List Instr :=
  [.dp .eors t1 t3, .dp .eors t2 t3, .movHi t4.toReg h1, .movHi h1 t1.toReg]

def mul64Mid2 (t2 t4 : LowReg) (h2 : Reg) : List Instr :=
  [.movHi t4.toReg h2, .movHi h2 t2.toReg]

def mul64Post (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) : List Instr :=
  [.movHi t1.toReg h1, .movHi t2.toReg h2, .lsrImm t4 t3 1, .movImm t4 0,
   .dp .adcs t1 a0, .dp .adcs t2 b0, .dp .adcs t3 t4,
   .addReg t1 t1 a1, .dp .adcs t2 b1, .dp .adcs t3 t4,
   .addReg b0 b0 t1, .dp .adcs a1 t2, .dp .adcs b1 t3]

/-- Macro `mul64 a0, a1, b0, b1, t1, t2, t3, t4, h1, h2`. -/
def mul64 (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) : List Instr :=
  mul64Pre a0 a1 b0 b1 t1 t3 t4 h1 h2 ++ mul32 t1 t2 t4 b0 b1 ++ mul64Mid1 t1 t2 t3 t4 h1 ++
    mul32 a0 b0 t4 t1 b1 ++ mul64Mid2 t2 t4 h2 ++ mul32 a1 b1 t4 t1 t2 ++
    mul64Post a0 a1 b0 b1 t1 t2 t3 t4 h1 h2


theorem c_movHi (s : State) (d m : Reg) : ((Instr.movHi d m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem c_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem c_lsr1 (s : State) (d m : LowReg) :
    ((Instr.lsrImm d m 1).next s).c = (s.reg m).getLsbD 0 := by
  simp [Instr.next, Instr.exec, lsrC, State.setReg, State.setNZC, State.setNZ]

theorem toReg_inj (x y : LowReg) : (x.toReg = y.toReg) = (x = y) := by
  apply propext; constructor
  · intro e; apply Fin.ext; have := congrArg Fin.val e; simpa [LowReg.toReg] using this
  · intro e; rw [e]

/-- Eight distinct low registers, as the 28 disequalities a `simp` call needs. -/
def Dist8 (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) : Prop := [a0, a1, b0, b1, t1, t2, t3, t4].Nodup

/-- A high register, distinct from every low register and from PC. -/
structure High (h : Reg) : Prop where
  lo : ∀ x : LowReg, h ≠ x.toReg
  pc : h ≠ 15


theorem post_regs (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg)
    (hh1 : High h1) (hh2 : High h2) (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4) :
    let s' := execAll (mul64Post a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) s
    ∃ X1 X2 X3 Y1 Y2 Y3 Z1 Z2 Z3 : Word × Bool × Bool,
      X1 = addWithCarry (s.regs h1) (s.reg a0) ((s.reg t3).getLsbD 0) ∧
      X2 = addWithCarry (s.regs h2) (s.reg b0) X1.2.1 ∧
      X3 = addWithCarry (s.reg t3) (BitVec.setWidth 32 (0 : BitVec 8)) X2.2.1 ∧
      Y1 = addWithCarry X1.1 (s.reg a1) false ∧
      Y2 = addWithCarry X2.1 (s.reg b1) Y1.2.1 ∧
      Y3 = addWithCarry X3.1 (BitVec.setWidth 32 (0 : BitVec 8)) Y2.2.1 ∧
      Z1 = addWithCarry (s.reg b0) Y1.1 false ∧
      Z2 = addWithCarry (s.reg a1) Y2.1 Z1.2.1 ∧
      Z3 = addWithCarry (s.reg b1) Y3.1 Z2.2.1 ∧
      s'.reg a0 = s.reg a0 ∧ s'.reg b0 = Z1.1 ∧ s'.reg a1 = Z2.1 ∧ s'.reg b1 = Z3.1 := by
  obtain ⟨h1l, h1n⟩ := hh1
  obtain ⟨h2l, h2n⟩ := hh2
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨d01, d02, d03, d04, d05, d06, d07⟩, ⟨d12, d13, d14, d15, d16, d17⟩, ⟨d23, d24, d25, d26, d27⟩,
    ⟨d34, d35, d36, d37⟩, ⟨d45, d46, d47⟩, ⟨d56, d57⟩, d67⟩ := hd
  intro s'
  refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [s', mul64Post, execAll, State.reg]
  simp only [regs_lsr _ _ _ 1 (by decide), regs_movImm, regs_movHi, regs_adcs, regs_adds, c_adds,
    c_adcs, c_movHi, c_movImm, c_lsr1, toReg_ne15, ne_eq, not_false_eq_true, State.reg, toReg_inj,
    d01, d02, d03, d04, d05, d06, d07, d12, d13, d14, d15, d16, d17, d23, d24, d25, d26, d27,
    d34, d35, d36, d37, d45, d46, d47, d56, d57, d67,
    Ne.symm d01, Ne.symm d02, Ne.symm d03, Ne.symm d04, Ne.symm d05, Ne.symm d06, Ne.symm d07,
    Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, Ne.symm d17, Ne.symm d23,
    Ne.symm d24, Ne.symm d25, Ne.symm d26, Ne.symm d27, Ne.symm d34, Ne.symm d35, Ne.symm d36,
    Ne.symm d37, Ne.symm d45, Ne.symm d46, Ne.symm d47, Ne.symm d56, Ne.symm d57, Ne.symm d67,
    h1l, h2l, h1n, h2n, ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem mask_lsb (neg : Bool) :
    (if neg then BitVec.allOnes 32 else 0#32).getLsbD 0 = neg := by cases neg <;> rfl

theorem mask_toNat (neg : Bool) :
    (if neg then BitVec.allOnes 32 else 0#32).toNat = if neg then 2 ^ 32 - 1 else 0 := by
  cases neg <;> rfl

theorem post_value (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg)
    (hh1 : High h1) (hh2 : High h2) (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4)
    (A0 A1 B0 B1 p0 p1 : Nat) (neg : Bool)
    (hA0 : A0 < 2 ^ 32) (hA1 : A1 < 2 ^ 32) (hB0 : B0 < 2 ^ 32) (hB1 : B1 < 2 ^ 32)
    (hL : (s.reg a0).toNat + 2 ^ 32 * (s.reg b0).toNat = A0 * B0)
    (hH : (s.reg a1).toNat + 2 ^ 32 * (s.reg b1).toNat = A1 * B1)
    (hp0 : p0 < 2 ^ 32) (hp1 : p1 < 2 ^ 32)
    (hmid : if neg then A0 * B1 + A1 * B0 + (p0 + 2 ^ 32 * p1) = A0 * B0 + A1 * B1
      else A0 * B1 + A1 * B0 = A0 * B0 + A1 * B1 + (p0 + 2 ^ 32 * p1))
    (hQ0 : (s.regs h1).toNat = if neg then 2 ^ 32 - 1 - p0 else p0)
    (hQ1 : (s.regs h2).toNat = if neg then 2 ^ 32 - 1 - p1 else p1)
    (hMk : s.reg t3 = if neg then BitVec.allOnes 32 else 0#32) :
    let s' := execAll (mul64Post a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) s
    s'.reg a0 = s.reg a0 ∧
      (s.reg a0).toNat + 2 ^ 32 * (s'.reg b0).toNat + 2 ^ 64 * (s'.reg a1).toNat +
        2 ^ 96 * (s'.reg b1).toNat = (A0 + 2 ^ 32 * A1) * (B0 + 2 ^ 32 * B1) := by
  obtain ⟨X1, X2, X3, Y1, Y2, Y3, Z1, Z2, Z3, hX1, hX2, hX3, hY1, hY2, hY3, hZ1, hZ2, hZ3,
    r0, r1, r2, r3⟩ := post_regs s a0 a1 b0 b1 t1 t2 t3 t4 h1 h2 hh1 hh2 hd
  intro s'
  refine ⟨r0, ?_⟩
  rw [r1, r2, r3]
  have z : (BitVec.setWidth 32 (0 : BitVec 8)).toNat = 0 := rfl
  have hc : ((s.reg t3).getLsbD 0).toNat = if neg then 1 else 0 := by
    rw [hMk, mask_lsb]; cases neg <;> rfl
  have e1 := X25519Carry.adc_nat (s.regs h1) (s.reg a0) ((s.reg t3).getLsbD 0)
  have e2 := X25519Carry.adc_nat (s.regs h2) (s.reg b0) X1.2.1
  have e3 := X25519Carry.adc_nat (s.reg t3) (BitVec.setWidth 32 (0 : BitVec 8)) X2.2.1
  have e4 := X25519Carry.adc_nat X1.1 (s.reg a1) false
  have e5 := X25519Carry.adc_nat X2.1 (s.reg b1) Y1.2.1
  have e6 := X25519Carry.adc_nat X3.1 (BitVec.setWidth 32 (0 : BitVec 8)) Y2.2.1
  have e7 := X25519Carry.adc_nat (s.reg b0) Y1.1 false
  have e8 := X25519Carry.adc_nat (s.reg a1) Y2.1 Z1.2.1
  have e9 := X25519Carry.adc_nat (s.reg b1) Y3.1 Z2.2.1
  rw [← hX1] at e1; rw [← hX2] at e2; rw [← hX3] at e3; rw [← hY1] at e4; rw [← hY2] at e5
  rw [← hY3] at e6; rw [← hZ1] at e7; rw [← hZ2] at e8; rw [← hZ3] at e9
  rw [hQ0, hc] at e1
  rw [hQ1] at e2
  rw [hMk, mask_toNat, z] at e3
  rw [z] at e6
  simp only [Bool.toNat_false] at e4 e7
  have hL0 := (s.reg a0).isLt; have hL1 := (s.reg b0).isLt
  have hH0 := (s.reg a1).isLt; have hH1 := (s.reg b1).isLt
  have hLe : (s.reg a0).toNat + 2 ^ 32 * (s.reg b0).toNat = A0 * B0 := hL
  exact X25519Kara.mul64_tail_nat A0 A1 B0 B1 _ _ _ _ p0 p1 neg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hA0 hA1 hB0 hB1 hL hH hp0 hp1 hmid e1 e2 e3 e4 e5 e6 e7 e8 e9 Y1.1.isLt Y2.1.isLt Y3.1.isLt
    Z1.1.isLt Z2.1.isLt Z3.1.isLt hL0

theorem lne {x y : LowReg} (h : x ≠ y) : x.toReg ≠ y.toReg := by rw [ne_eq, toReg_inj]; exact h
theorem vne {x y : LowReg} (h : x ≠ y) : x.val ≠ y.val := fun e => h (Fin.ext e)

theorem movs2_exec (s : State) (h1 h2 : Reg) (x y : LowReg) (hh1 : High h1) (hh2 : High h2)
    (h12 : h1 ≠ h2) :
    let s' := execAll (movs2 h1 h2 x y) s
    s'.regs h1 = s.reg x ∧ s'.regs h2 = s.reg y ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ h1 → r ≠ h2 → s'.regs r = s.regs r := by
  obtain ⟨h1l, h1n⟩ := hh1
  obtain ⟨h2l, h2n⟩ := hh2
  intro s'
  refine ⟨?_, ?_, execAll_mem _ _ (by simp [movs2, Instr.writesMem]), ?_⟩
  · simp [s', movs2, execAll, regs_movHi, h1n, h2n, h12, State.reg]
  · simp [s', movs2, execAll, regs_movHi, h1n, h2n, Ne.symm (h1l y), State.reg, toReg_ne15]
  · intro r h15 hr1 hr2
    simp [s', movs2, execAll, regs_movHi, h1n, h2n, h15, hr1, hr2]

theorem eors_exec (s : State) (d m : LowReg) :
    let s' := (Instr.dp .eors d m).next s
    s'.reg d = s.reg d ^^^ s.reg m ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → s'.regs r = s.regs r := by
  intro s'
  refine ⟨?_, by simp [s', Instr.next, Instr.exec, State.setReg, State.setNZ], ?_⟩
  · simp [s', State.reg, regs_eors, toReg_ne15]
  · intro r h15 hr; simp [s', regs_eors, h15, hr]

theorem mid1_exec (s : State) (t1 t2 t3 t4 : LowReg) (h1 : Reg) (hh1 : High h1)
    (d12 : t1 ≠ t2) (d13 : t1 ≠ t3) (d14 : t1 ≠ t4) (d24 : t2 ≠ t4) :
    let s' := execAll (mul64Mid1 t1 t2 t3 t4 h1) s
    s'.reg t1 = s.reg t1 ^^^ s.reg t3 ∧ s'.reg t2 = s.reg t2 ^^^ s.reg t3 ∧
      s'.reg t4 = s.regs h1 ∧ s'.regs h1 = s.reg t1 ^^^ s.reg t3 ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t4.toReg → r ≠ h1 →
        s'.regs r = s.regs r := by
  obtain ⟨h1l, h1n⟩ := hh1
  intro s'
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [mul64Mid1, Instr.writesMem])
  simp only [s', mul64Mid1, execAll, State.reg] at hm ⊢
  have h1l' : ∀ x : LowReg, x.toReg ≠ h1 := fun x => Ne.symm (h1l x)
  simp only [regs_movHi, regs_eors, toReg_ne15, ne_eq, not_false_eq_true, State.reg, toReg_inj,
    d12, d13, d14, d24, Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d24,
    h1l, h1l', h1n, ite_true, ite_false, hm, true_and]
  intro r h15 r1 r2 r4 rh
  simp [regs_movHi, regs_eors, toReg_ne15, h1n, h15, r1, r2, r4, rh]

theorem mid2_exec (s : State) (t2 t4 : LowReg) (h2 : Reg) (hh2 : High h2) (d24 : t2 ≠ t4) :
    let s' := execAll (mul64Mid2 t2 t4 h2) s
    s'.reg t4 = s.regs h2 ∧ s'.regs h2 = s.reg t2 ∧ s'.reg t2 = s.reg t2 ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ t4.toReg → r ≠ h2 → s'.regs r = s.regs r := by
  obtain ⟨h2l, h2n⟩ := hh2
  intro s'
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [mul64Mid2, Instr.writesMem])
  simp only [s', mul64Mid2, execAll, State.reg] at hm ⊢
  have h2l' : ∀ x : LowReg, x.toReg ≠ h2 := fun x => Ne.symm (h2l x)
  simp only [regs_movHi, toReg_ne15, ne_eq, not_false_eq_true, State.reg, toReg_inj,
    d24, Ne.symm d24, h2l, h2l', h2n, ite_true, ite_false, hm, true_and]
  intro r h15 r4 rh
  simp [regs_movHi, toReg_ne15, h2n, h15, r4, rh]

set_option hygiene false in
/-- Close a register disequality from the distinctness facts in context. -/
scoped macro "regne" : tactic => `(tactic| first
  | exact toReg_ne15 _ | exact hh1.pc | exact hh2.pc | exact h12 | exact Ne.symm h12
  | exact hh1.lo _ | exact hh2.lo _ | exact Ne.symm (hh1.lo _) | exact Ne.symm (hh2.lo _)
  | exact lne ‹_› | exact Ne.symm (lne ‹_›) | assumption | exact Ne.symm ‹_›)

/-- `regne` as a term. -/
scoped macro "rg" : term => `(by regne)

/-- Close a `Dist5` goal from the distinctness facts in context. -/
scoped macro "dist5" : tactic => `(tactic| constructor <;> first | exact vne ‹_› | exact vne (Ne.symm ‹_›))

theorem mask_xor (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then BitVec.allOnes 32 else 0#32) ^^^ (if q then BitVec.allOnes 32 else 0#32)) =
      if (decide p != decide q) then BitVec.allOnes 32 else 0#32 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem xor_mask_toNat (w : Word) (neg : Bool) :
    (w ^^^ (if neg then BitVec.allOnes 32 else 0#32)).toNat =
      if neg then 2 ^ 32 - 1 - w.toNat else w.toNat := by
  cases neg
  · simp
  · simp only [ite_true]; rw [BitVec.xor_allOnes, BitVec.toNat_not]

theorem pre_exec (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg)
    (hh1 : High h1) (hh2 : High h2) (h12 : h1 ≠ h2) (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4) :
    let s' := execAll (mul64Pre a0 a1 b0 b1 t1 t3 t4 h1 h2) s
    s'.reg a0 = s.reg a0 ∧ s'.reg a1 = s.reg a1 ∧ s'.reg b0 = s.reg b0 ∧
      s'.regs h1 = s.reg b0 ∧ s'.regs h2 = s.reg b1 ∧
      ((s.reg a1).toNat : Int) - (s.reg a0).toNat =
        (if (s.reg a1).toNat < (s.reg a0).toNat then -((s'.reg t1).toNat : Int)
          else (s'.reg t1).toNat) ∧
      ((s.reg b0).toNat : Int) - (s.reg b1).toNat =
        (if (s.reg b0).toNat < (s.reg b1).toNat then -((s'.reg t4).toNat : Int)
          else (s'.reg t4).toNat) ∧
      s'.reg t3 = (if (decide ((s.reg a1).toNat < (s.reg a0).toNat) !=
        decide ((s.reg b0).toNat < (s.reg b1).toNat)) then BitVec.allOnes 32 else 0#32) ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ t1.toReg → r ≠ t3.toReg → r ≠ t4.toReg → r ≠ b1.toReg →
        r ≠ h1 → r ≠ h2 → s'.regs r = s.regs r := by
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨d01, d02, d03, d04, d05, d06, d07⟩, ⟨d12, d13, d14, d15, d16, d17⟩,
    ⟨d23, d24, d25, d26, d27⟩, ⟨d34, d35, d36, d37⟩, ⟨d45, d46, d47⟩, ⟨d56, d57⟩, d67⟩ := hd
  intro s'
  simp only [s', mul64Pre, execAll_append]
  obtain ⟨m1, m2, m3, m4⟩ := movs2_exec s h1 h2 b0 b1 hh1 hh2 h12
  generalize execAll (movs2 h1 h2 b0 b1) s = q1 at m1 m2 m3 m4 ⊢
  obtain ⟨x1, x2, x3, x4⟩ := absdiff_exec q1 t1 a1 a0 t3 (vne d46)
  generalize execAll (absdiff t1 a1 a0 t3) q1 = q2 at x1 x2 x3 x4 ⊢
  obtain ⟨y1, y2, y3, y4⟩ := absdiff_exec q2 t4 b0 b1 b1 (vne (Ne.symm d37))
  generalize execAll (absdiff t4 b0 b1 b1) q2 = q3 at y1 y2 y3 y4 ⊢
  obtain ⟨z1, z2, z3⟩ := eors_exec q3 t3 b1
  simp only [execAll]
  generalize (Instr.dp .eors t3 b1).next q3 = q4 at z1 z2 z3 ⊢
  have qa0 : q1.reg a0 = s.reg a0 := m4 _ rg rg rg
  have qa1 : q1.reg a1 = s.reg a1 := m4 _ rg rg rg
  have qb0 : q1.reg b0 = s.reg b0 := m4 _ rg rg rg
  have qb1 : q1.reg b1 = s.reg b1 := m4 _ rg rg rg
  have pb0 : q2.reg b0 = s.reg b0 := (x4 _ rg rg rg).trans qb0
  have pb1 : q2.reg b1 = s.reg b1 := (x4 _ rg rg rg).trans qb1
  rw [qa0, qa1] at x1 x2
  rw [pb0, pb1] at y1 y2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (z3 _ rg rg).trans ((y4 _ rg rg rg).trans ((x4 _ rg rg rg).trans qa0))
  · exact (z3 _ rg rg).trans ((y4 _ rg rg rg).trans ((x4 _ rg rg rg).trans qa1))
  · exact (z3 _ rg rg).trans ((y4 _ rg rg rg).trans pb0)
  · exact (z3 _ rg rg).trans ((y4 _ rg rg rg).trans ((x4 _ rg rg rg).trans m1))
  · exact (z3 _ rg rg).trans ((y4 _ rg rg rg).trans ((x4 _ rg rg rg).trans m2))
  · have e : q4.reg t1 = q2.reg t1 := (z3 _ rg rg).trans (y4 _ rg rg rg)
    rw [e]; exact x2
  · have e : q4.reg t4 = q3.reg t4 := z3 _ rg rg
    rw [e]; exact y2
  · have e : q3.reg t3 = q2.reg t3 := y4 _ rg rg rg
    rw [z1, e, x1, y1, mask_xor]
  · rw [z2, y3, x3, m3]
  · intro r h15 r1 r3 r4 rb rh1 rh2
    exact (z3 r h15 r3).trans ((y4 r h15 r4 rb).trans ((x4 r h15 r1 r3).trans (m4 r h15 rh1 rh2)))

/-- The middle term of `mul64` from the two absolute differences: `neg` is set when their
signs differ. -/
theorem mid_rel (A0 A1 B0 B1 x y P : Nat)
    (hx : (A1 : Int) - A0 = if A1 < A0 then -(x : Int) else x)
    (hy : (B0 : Int) - B1 = if B0 < B1 then -(y : Int) else y) (hP : P = x * y) :
    if (decide (A1 < A0) != decide (B0 < B1)) then A0 * B1 + A1 * B0 + P = A0 * B0 + A1 * B1
      else A0 * B1 + A1 * B0 = A0 * B0 + A1 * B1 + P := by
  have h := X25519Kara.cross A1 A0 B0 B1 x y (if A1 < A0 then 1 else 0) (if B0 < B1 then 1 else 0)
    (by split <;> simp_all) (by split <;> simp_all) (by split <;> omega) (by split <;> omega)
  subst hP
  by_cases ha : A1 < A0 <;> by_cases hb : B0 < B1 <;> simp only [ha, hb, decide_true, decide_false,
    bne_self_eq_false, Bool.true_bne, Bool.false_bne, Bool.not_true, Bool.not_false,
    ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;> grind

theorem post_frame (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) (r : Reg)
    (h15 : r ≠ 15) (ra1 : r ≠ a1.toReg) (rb0 : r ≠ b0.toReg) (rb1 : r ≠ b1.toReg)
    (r1 : r ≠ t1.toReg) (r2 : r ≠ t2.toReg) (r3 : r ≠ t3.toReg) (r4 : r ≠ t4.toReg) :
    (execAll (mul64Post a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) s).regs r = s.regs r := by
  simp only [mul64Post, execAll]
  simp only [regs_lsr _ _ _ 1 (by decide), regs_movImm, regs_movHi, regs_adcs, regs_adds,
    ne_eq, not_false_eq_true, h15, ra1, rb0, rb1, r1, r2, r3, r4, ite_false]

/-! Step lemmas in equation form: the operands come from the run equation, so the
composition below never names them. -/

theorem mul32_eq {s s' : State} {rl rh rb rt ru : LowReg} (he : execAll (mul32 rl rh rb rt ru) s = s')
    (h : Dist5 rl rh rb rt ru) :
    (s'.reg rl).toNat + 2 ^ 32 * (s'.reg rh).toNat = (s.reg rl).toNat * (s.reg rb).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ rl.toReg → r ≠ rh.toReg → r ≠ rb.toReg → r ≠ rt.toReg →
        r ≠ ru.toReg → s'.regs r = s.regs r := by
  subst he; exact mul32_exec s rl rh rb rt ru h

theorem mid1_eq {s s' : State} {t1 t2 t3 t4 : LowReg} {h1 : Reg}
    (he : execAll (mul64Mid1 t1 t2 t3 t4 h1) s = s') (hh1 : High h1)
    (d12 : t1 ≠ t2) (d13 : t1 ≠ t3) (d14 : t1 ≠ t4) (d24 : t2 ≠ t4) :
    s'.reg t1 = s.reg t1 ^^^ s.reg t3 ∧ s'.reg t2 = s.reg t2 ^^^ s.reg t3 ∧
      s'.reg t4 = s.regs h1 ∧ s'.regs h1 = s.reg t1 ^^^ s.reg t3 ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t4.toReg → r ≠ h1 →
        s'.regs r = s.regs r := by
  subst he; exact mid1_exec s t1 t2 t3 t4 h1 hh1 d12 d13 d14 d24

theorem mid2_eq {s s' : State} {t2 t4 : LowReg} {h2 : Reg}
    (he : execAll (mul64Mid2 t2 t4 h2) s = s') (hh2 : High h2) (d24 : t2 ≠ t4) :
    s'.reg t4 = s.regs h2 ∧ s'.regs h2 = s.reg t2 ∧ s'.reg t2 = s.reg t2 ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ t4.toReg → r ≠ h2 → s'.regs r = s.regs r := by
  subst he; exact mid2_exec s t2 t4 h2 hh2 d24

theorem mul64_exec (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg)
    (hh1 : High h1) (hh2 : High h2) (h12 : h1 ≠ h2) (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4) :
    let s' := execAll (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) s
    (s'.reg a0).toNat + 2 ^ 32 * (s'.reg b0).toNat + 2 ^ 64 * (s'.reg a1).toNat +
        2 ^ 96 * (s'.reg b1).toNat =
      ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) *
        ((s.reg b0).toNat + 2 ^ 32 * (s.reg b1).toNat) ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ a0.toReg → r ≠ a1.toReg → r ≠ b0.toReg → r ≠ b1.toReg →
        r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t3.toReg → r ≠ t4.toReg → r ≠ h1 → r ≠ h2 →
        s'.regs r = s.regs r := by
  have hd' := hd
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨d01, d02, d03, d04, d05, d06, d07⟩, ⟨d12, d13, d14, d15, d16, d17⟩,
    ⟨d23, d24, d25, d26, d27⟩, ⟨d34, d35, d36, d37⟩, ⟨d45, d46, d47⟩, ⟨d56, d57⟩, d67⟩ := hd'
  intro s'
  simp only [s', mul64, execAll_append]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := pre_exec s a0 a1 b0 b1 t1 t2 t3 t4 h1 h2 hh1 hh2 h12 hd
  generalize execAll (mul64Pre _ _ _ _ _ _ _ _ _) s = s1 at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 ⊢
  generalize hs2 : execAll (mul32 _ _ _ _ _) s1 = s2
  obtain ⟨u1, u2, u3⟩ := mul32_eq hs2 (by dist5)
  generalize hs3 : execAll (mul64Mid1 _ _ _ _ _) s2 = s3
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := mid1_eq hs3 hh1 rg rg rg rg
  generalize hs4 : execAll (mul32 _ _ _ _ _) s3 = s4
  obtain ⟨w1, w2, w3⟩ := mul32_eq hs4 (by dist5)
  generalize hs5 : execAll (mul64Mid2 _ _ _) s4 = s5
  obtain ⟨x1, x2, x3, x4, x5⟩ := mid2_eq hs5 hh2 rg
  generalize hs6 : execAll (mul32 _ _ _ _ _) s5 = s6
  obtain ⟨y1, y2, y3⟩ := mul32_eq hs6 (by dist5)
  -- register values entering the tail
  have mk1 : s2.reg t3 = s1.reg t3 := u3 _ rg rg rg rg rg rg
  have e3a0 : s3.reg a0 = s.reg a0 := (v6 _ rg rg rg rg rg).trans ((u3 _ rg rg rg rg rg rg).trans p1)
  have e3t4 : s3.reg t4 = s.reg b0 := v3.trans ((u3 _ rg rg rg rg rg rg).trans p4)
  have e5a1 : s5.reg a1 = s.reg a1 := (x5 _ rg rg rg).trans ((w3 _ rg rg rg rg rg rg).trans
    ((v6 _ rg rg rg rg rg).trans ((u3 _ rg rg rg rg rg rg).trans p2)))
  have e5t4 : s5.reg t4 = s.reg b1 := x1.trans ((w3 _ rg rg rg rg rg rg).trans
    ((v6 _ rg rg rg rg rg).trans ((u3 _ rg rg rg rg rg rg).trans p5)))
  have e6a0 : s6.reg a0 = s4.reg a0 := (y3 _ rg rg rg rg rg rg).trans (x5 _ rg rg rg)
  have e6b0 : s6.reg b0 = s4.reg b0 := (y3 _ rg rg rg rg rg rg).trans (x5 _ rg rg rg)
  have e6h1 : s6.regs h1 = s2.reg t1 ^^^ s2.reg t3 := (y3 _ rg rg rg rg rg rg).trans
    ((x5 _ rg rg rg).trans ((w3 _ rg rg rg rg rg rg).trans v4))
  have e6h2 : s6.regs h2 = s2.reg t2 ^^^ s2.reg t3 := (y3 _ rg rg rg rg rg rg).trans
    (x2.trans ((w3 _ rg rg rg rg rg rg).trans v2))
  have e6t3 : s6.reg t3 = s1.reg t3 := (y3 _ rg rg rg rg rg rg).trans ((x5 _ rg rg rg).trans
    ((w3 _ rg rg rg rg rg rg).trans ((v6 _ rg rg rg rg rg).trans mk1)))
  rw [e3a0, e3t4] at w1
  rw [e5a1, e5t4] at y1
  rw [mk1, p8] at e6h1 e6h2
  rw [p8] at e6t3
  have hmid := mid_rel _ _ _ _ _ _ _ p6 p7 u1
  obtain ⟨z1, z2⟩ := post_value s6 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2 hh1 hh2 hd
    (s.reg a0).toNat (s.reg a1).toNat (s.reg b0).toNat (s.reg b1).toNat
    (s2.reg t1).toNat (s2.reg t2).toNat _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (by rw [e6a0, e6b0]; exact w1) y1 (BitVec.isLt _) (BitVec.isLt _) hmid
    (by rw [e6h1, xor_mask_toNat]) (by rw [e6h2, xor_mask_toNat]) e6t3
  refine ⟨?_, ?_, ?_⟩
  · rw [z1]; exact z2
  · rw [execAll_mem _ _ (by simp [mul64Post, Instr.writesMem]), y2, x4, w2, v5, u2, p9]
  · intro r h15 r0 ra1 rb0 rb1 r1 r2 r3 r4 rh1 rh2
    exact (post_frame _ _ _ _ _ _ _ _ _ _ _ _ rg rg rg rg rg rg rg rg).trans
      ((y3 r rg rg rg rg rg rg).trans ((x5 r rg rg rg).trans ((w3 r rg rg rg rg rg rg).trans
        ((v6 r rg rg rg rg rg).trans ((u3 r rg rg rg rg rg rg).trans (p10 r rg rg rg rg rg rg rg))))))

open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feSqr) in
/-- The first `mul64` of `m0c_fe_mul`, after the routine's entry (save, frame, operand
loads). -/
theorem mul64_at_fe_mul :
    seqAt B feMul ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .strSp 2 0x23,
      .movHi 12 1, .movHi 11 2, .ldm 1 0x50, .ldm 2 0xa0] ++ mul64 4 6 5 7 0 1 2 3 8 10) = true := by
  rw [seqAt_eq_scan]; decide +kernel

open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feSqr) in
/-- The first `sqr32` of `m0c_fe_sqr`, after the routine's entry and the absolute difference
that opens `sqr64`. -/
theorem sqr32_at_fe_sqr :
    seqAt B feSqr ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .movHi 12 1,
      .ldm 1 0x50] ++ absdiff 0 6 4 1 ++ sqr32 0 1 2 3) = true := by
  rw [seqAt_eq_scan]; decide +kernel

/-- Instructions without a memory access. -/
def regOnly : Instr → Bool
  | .ldrLit _ _ | .memReg _ _ _ _ | .memImm _ _ _ _ | .strSp _ _ | .ldrSp _ _ | .push _ _
  | .pop _ _ | .stm _ _ | .ldm _ _ => false
  | _ => true

theorem accesses_regOnly (i : Instr) (s : State) (h : regOnly i = true) : i.accesses s = [] := by
  cases i <;> simp_all [regOnly, Instr.accesses]

theorem alignedAll_regOnly : ∀ (is : List Instr) (s : State), is.all regOnly = true →
    alignedAll is s = true
  | [], _, _ => rfl
  | i :: is, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [alignedAll, accesses_regOnly i s h.1, List.all_nil, Bool.true_and]
    exact alignedAll_regOnly is _ h.2

theorem mul64_regOnly (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) :
    (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2).all regOnly = true := by
  simp [mul64, mul64Pre, movs2, absdiff, mul32, mul64Mid1, mul64Mid2, mul64Post, regOnly]

theorem mul64_noW (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) :
    (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2).all (!·.writesMem) = true := by
  simp [mul64, mul64Pre, movs2, absdiff, mul32, mul64Mid1, mul64Mid2, mul64Post, Instr.writesMem]

theorem mul64_falls (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) (hh1 : High h1)
    (hh2 : High h2) : (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2).all Instr.falls = true := by
  have n1 : h1.val ≠ 15 := fun e => hh1.pc (Fin.ext e)
  have n2 : h2.val ≠ 15 := fun e => hh2.pc (Fin.ext e)
  have nl : ∀ x : LowReg, x.toReg.val ≠ 15 := fun x e => toReg_ne15 x (Fin.ext e)
  simp [mul64, mul64Pre, movs2, absdiff, mul32, mul64Mid1, mul64Mid2, mul64Post, Instr.falls,
    n1, n2, nl]

theorem mul64_size (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg) (h1 h2 : Reg) :
    seqSize (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) = 162 := by
  simp [mul64, mul64Pre, movs2, absdiff, mul32, mul64Mid1, mul64Mid2, mul64Post, seqSize,
    Instr.size]

/-- One `mul64` block in a `ReachW` proof: the 128-bit product of `a1:a0` and `b1:b0` lands
in `b1:a1:b0:a0`; memory and every register outside the ten operands are unchanged. -/
theorem mul64_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {t : State}
    {off : Nat} {a0 a1 b0 b1 t1 t2 t3 t4 : LowReg} {h1 h2 : Reg}
    (hh1 : High h1) (hh2 : High h2) (h12 : h1 ≠ h2) (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4)
    (hseq : seqAt B off (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (mul64 a0 a1 b0 b1 t1 t2 t3 t4 h1 h2)))
    {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 162) → t'.mem = t.mem →
      (t'.reg a0).toNat + 2 ^ 32 * (t'.reg b0).toNat + 2 ^ 64 * (t'.reg a1).toNat +
          2 ^ 96 * (t'.reg b1).toNat =
        ((t.reg a0).toNat + 2 ^ 32 * (t.reg a1).toNat) *
          ((t.reg b0).toNat + 2 ^ 32 * (t.reg b1).toNat) →
      (∀ r : Reg, r ≠ 15 → r ≠ a0.toReg → r ≠ a1.toReg → r ≠ b0.toReg → r ≠ b1.toReg →
        r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t3.toReg → r ≠ t4.toReg → r ≠ h1 → r ≠ h2 →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hf := mul64_falls a0 a1 b0 b1 t1 t2 t3 t4 h1 h2 hh1 hh2
  apply ReachW.block hb _ off hpc ho hseq hf (alignedAll_regOnly _ _ (mul64_regOnly ..))
    (WritesTo.of_noWritesMem _ _ (mul64_noW ..) Wr) hr
  obtain ⟨e1, e2, e3⟩ := mul64_exec t a0 a1 b0 b1 t1 t2 t3 t4 h1 h2 hh1 hh2 h12 hd
  apply k _ _ e2 e1 e3
  rw [execAll_pc _ _ hf, mul64_size, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Mul
