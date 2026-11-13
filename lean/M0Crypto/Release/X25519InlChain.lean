import M0Crypto.Release.X25519InlBase

set_option linter.unusedSimpArgs false

/-!
The carry chains shared by `fe_add_body` and `fe_sub_body` (generator `tools/gen_x25519.py`).

Both bodies are the same instruction schedule with `adds`/`adcs` (`neg = false`) or
`subs`/`sbcs` (`neg = true`). A subtraction is an addition of the complement with carry in
set, so one chain lemma covers both: with `opY neg y` the second operand as the adder sees it
(`y` or `~~~y`), every step satisfies `X25519Carry.adc_nat`.

* `sumOp neg`: the 256-bit chain `a ± b` into `r8, r10, r11, r12, r3, r4, r5, r6`, carry in C.
* `outOp neg`: add `opY K` (then `opY 0` in the upper words) to those eight words, `K` in `r7`,
  and store them to `dst` (`r0`) with two `stm`.

The fold between them (`q` of the add, `k` of the sub) is body-specific (`X25519InlAdd`,
`X25519InlSub`).
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Frame (FrameOk upd)
open M0Crypto.Release.X25519MulcChain (psum)
open M0Crypto.Release.X25519Block (AccAll AccOk accAll_cons accAll_nil accAll_append)
open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg2 toReg3 toReg4 toReg5 toReg6 toReg7)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)

/-! ## The two operations -/

def dop (neg : Bool) : DpOp := if neg then .sbcs else .adcs
def op3 (neg : Bool) (d n m : LowReg) : Instr := if neg then .subReg d n m else .addReg d n m
/-- The second operand as the adder sees it. -/
def opY (neg : Bool) (y : Word) : Word := if neg then ~~~y else y

theorem regs_dop (s : State) (neg : Bool) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp (dop neg) d m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg d) (opY neg (s.reg m)) s.c).1 else s.regs r := by
  cases neg
  · exact X25519Mul.regs_adcs s d m r hr
  · exact X25519Mul.regs_sbcs s d m r hr

theorem c_dop (s : State) (neg : Bool) (d m : LowReg) :
    ((Instr.dp (dop neg) d m).next s).c = (addWithCarry (s.reg d) (opY neg (s.reg m)) s.c).2.1 := by
  cases neg
  · exact X25519Mul.c_adcs s d m
  · exact X25519Mul.c_sbcs s d m

theorem regs_op3 (s : State) (neg : Bool) (d n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((op3 neg d n m).next s).regs r =
      if r = d.toReg then (addWithCarry (s.reg n) (opY neg (s.reg m)) neg).1 else s.regs r := by
  cases neg
  · exact X25519Mul.regs_adds s d n m r hr
  · exact X25519Mul.regs_subs s d n m r hr

theorem c_op3 (s : State) (neg : Bool) (d n m : LowReg) :
    ((op3 neg d n m).next s).c = (addWithCarry (s.reg n) (opY neg (s.reg m)) neg).2.1 := by
  cases neg
  · exact X25519Mul.c_adds s d n m
  · exact X25519Mul.c_subs s d n m

theorem mem_dop (s : State) (neg : Bool) (d m : LowReg) : ((Instr.dp (dop neg) d m).next s).mem = s.mem :=
  next_mem (by cases neg <;> rfl) s

theorem mem_op3 (s : State) (neg : Bool) (d n m : LowReg) : ((op3 neg d n m).next s).mem = s.mem :=
  next_mem (by cases neg <;> rfl) s

theorem regOnly_dop (neg : Bool) (d m : LowReg) : X25519Mul.regOnly (.dp (dop neg) d m) = true := by
  cases neg <;> rfl
theorem regOnly_op3 (neg : Bool) (d n m : LowReg) : X25519Mul.regOnly (op3 neg d n m) = true := by
  cases neg <;> rfl
theorem falls_dop (neg : Bool) (d m : LowReg) : (Instr.dp (dop neg) d m).falls = true := by
  cases neg <;> rfl
theorem falls_op3 (neg : Bool) (d n m : LowReg) : (op3 neg d n m).falls = true := by
  cases neg <;> rfl
theorem dsts_dop (neg : Bool) (d m : LowReg) : (Instr.dp (dop neg) d m).dsts = [d.val] := by
  cases neg <;> rfl
theorem dsts_op3 (neg : Bool) (d n m : LowReg) : (op3 neg d n m).dsts = [d.val] := by
  cases neg <;> rfl
theorem writesMem_dop (neg : Bool) (d m : LowReg) : (Instr.dp (dop neg) d m).writesMem = false := by
  cases neg <;> rfl
theorem writesMem_op3 (neg : Bool) (d n m : LowReg) : (op3 neg d n m).writesMem = false := by
  cases neg <;> rfl

/-! ## Pieces -/

/-- Two words of each input and their sum or difference into `r3, r4`. -/
def pairOp (neg k : Bool) : List Instr :=
  ld34 ++ [if k then .dp (dop neg) 3 5 else op3 neg 3 3 5, .dp (dop neg) 4 6]

/-- The last two words: `ldm r1!, {r5, r6}; ldm r2, {r1, r2}`, into `r5, r6`. -/
def topOp (neg : Bool) : List Instr :=
  [.ldm 1 0x60, .ldm 2 0x06, .dp (dop neg) 5 1, .dp (dop neg) 6 2]

/-- The 256-bit chain. -/
def sumOp (neg : Bool) : List Instr :=
  pairOp neg false ++ [.movHi 8 3, .movHi 10 4] ++ pairOp neg true ++ [.movHi 11 3, .movHi 12 4] ++
    pairOp neg true ++ topOp neg

/-- Add `r7` to the low words and store them. -/
def loOp (neg : Bool) : List Instr :=
  [.movHi 1 8, .movHi 2 10, op3 neg 1 1 7, .movImm 7 0, .dp (dop neg) 2 7, .stm 0 0x06]

/-- Carry into the upper words and store them. -/
def hiOp (neg : Bool) : List Instr :=
  [.movHi 1 11, .movHi 2 12, .dp (dop neg) 1 7, .dp (dop neg) 2 7, .dp (dop neg) 3 7,
    .dp (dop neg) 4 7, .dp (dop neg) 5 7, .dp (dop neg) 6 7, .stm 0 0x7e]

def outOp (neg : Bool) : List Instr := loOp neg ++ hiOp neg

/-! ## Values -/

/-- Eight words, little-endian. -/
def val8 (w0 w1 w2 w3 w4 w5 w6 w7 : Word) : Nat :=
  w0.toNat + 2 ^ 32 * w1.toNat + 2 ^ 64 * w2.toNat + 2 ^ 96 * w3.toNat + 2 ^ 128 * w4.toNat +
    2 ^ 160 * w5.toNat + 2 ^ 192 * w6.toNat + 2 ^ 224 * w7.toNat

/-- The eight words at `p`. -/
def memVal (m : Mem) (f : Word → Word) (p : Word) : Nat :=
  val8 (f (read32 m (slot p 0))) (f (read32 m (slot p 1))) (f (read32 m (slot p 2)))
    (f (read32 m (slot p 3))) (f (read32 m (slot p 4))) (f (read32 m (slot p 5)))
    (f (read32 m (slot p 6))) (f (read32 m (slot p 7)))

/-- The chain words `r8, r10, r11, r12, r3, r4, r5, r6`. -/
def regVal (t : State) : Nat :=
  val8 (t.regs 8) (t.regs 10) (t.regs 11) (t.regs 12) (t.regs 3) (t.regs 4) (t.regs 5) (t.regs 6)

theorem memVal_id (m : Mem) (p : Word) : memVal m id p = X25519Routines.feVal m p := by
  rw [X25519MulcFacts.feVal_psum]; simp only [memVal, val8, psum, id]; omega

/-- The complement words of a value. -/
theorem memVal_not (m : Mem) (p : Word) :
    memVal m (opY true) p + X25519Routines.feVal m p + 1 = 2 ^ 256 := by
  rw [X25519MulcFacts.feVal_psum]
  simp only [memVal, val8, psum, opY, ite_true, BitVec.toNat_not]
  have := (read32 m (slot p 0)).isLt; have := (read32 m (slot p 1)).isLt
  have := (read32 m (slot p 2)).isLt; have := (read32 m (slot p 3)).isLt
  have := (read32 m (slot p 4)).isLt; have := (read32 m (slot p 5)).isLt
  have := (read32 m (slot p 6)).isLt; have := (read32 m (slot p 7)).isLt
  omega

theorem pair_nat (r c1 r' c2 x y x' y' cin : Nat) (e1 : r + 2 ^ 32 * c1 = x + y + cin)
    (e2 : r' + 2 ^ 32 * c2 = x' + y' + c1) :
    r + 2 ^ 32 * r' + 2 ^ 64 * c2 = x + 2 ^ 32 * x' + y + 2 ^ 32 * y' + cin := by
  omega

/-! ## Execution of the pieces -/

theorem pairOp_exec (s : State) (neg k : Bool) :
    let t := execAll (pairOp neg k) s
    let X := fun i => read32 s.mem (slot (s.regs 1) i)
    let Y := fun i => opY neg (read32 s.mem (slot (s.regs 2) i))
    (t.regs 3).toNat + 2 ^ 32 * (t.regs 4).toNat + 2 ^ 64 * t.c.toNat =
        (X 0).toNat + 2 ^ 32 * (X 1).toNat + (Y 0).toNat + 2 ^ 32 * (Y 1).toNat +
          (if k then s.c else neg).toNat ∧
      t.regs 1 = slot (s.regs 1) 2 ∧ t.regs 2 = slot (s.regs 2) 2 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t X Y
  obtain ⟨l3, l4, l5, l6, l1, l2, lm, lc, lo⟩ := ld34_exec s
  simp only [t, pairOp, execAll_append]
  generalize execAll ld34 s = s1 at l3 l4 l5 l6 l1 l2 lm lc lo
  have h34 : (3 : Reg) ≠ LowReg.toReg 4 := by decide
  have h14 : (1 : Reg) ≠ LowReg.toReg 4 := by decide
  have h24 : (2 : Reg) ≠ LowReg.toReg 4 := by decide
  have h13 : (1 : Reg) ≠ LowReg.toReg 3 := by decide
  have h23 : (2 : Reg) ≠ LowReg.toReg 3 := by decide
  have h43 : (4 : Reg) ≠ LowReg.toReg 3 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases k
    all_goals
      simp (config := {decide := true}) only [execAll, Bool.false_eq_true, ite_true, ite_false,
        regs_dop, regs_op3, c_dop, c_op3, State.reg, toReg3, toReg4, toReg5, toReg6, l3, l4, l5, l6, lc]
      exact pair_nat _ _ _ _ _ _ _ _ _ (adc_nat _ _ _) (adc_nat _ _ _)
  all_goals cases k
  all_goals
    simp (config := {decide := true}) only [execAll, Bool.false_eq_true, ite_true, ite_false,
      regs_dop, regs_op3, mem_dop, mem_op3, toReg3, toReg4, l1, l2, lm]
  all_goals
    intro r h15 hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨-, -, n3, n4, -, -⟩ := hr'
    simp only [execAll, regs_dop _ _ _ _ _ h15, regs_op3 _ _ _ _ _ _ h15, toReg3, toReg4, n3, n4,
      ite_false, lo r h15 hr]

theorem topOp_exec (s : State) (neg : Bool) :
    let t := execAll (topOp neg) s
    let X := fun i => read32 s.mem (slot (s.regs 1) i)
    let Y := fun i => opY neg (read32 s.mem (slot (s.regs 2) i))
    (t.regs 5).toNat + 2 ^ 32 * (t.regs 6).toNat + 2 ^ 64 * t.c.toNat =
        (X 0).toNat + 2 ^ 32 * (X 1).toNat + (Y 0).toNat + 2 ^ 32 * (Y 1).toNat + s.c.toNat ∧
      t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t X Y
  refine ⟨?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [t, topOp, execAll, regs_dop, c_dop,
      X25519Mem.regs_ldm, X25519Mem.mem_ldm, X25519Mem.c_ldm, listRegs_60, listRegs_06,
      List.map, State.reg, toReg1, toReg2, toReg5, toReg6, ite_true, ite_false, List.mem_cons,
      List.idxOf, bitCount_60, List.not_mem_nil, or_false]
    exact pair_nat _ _ _ _ _ _ _ _ _ (adc_nat _ _ _) (adc_nat _ _ _)
  · simp only [t, topOp, execAll, mem_dop, X25519Mem.mem_ldm]
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h5, h6⟩ := hr
    simp (config := {decide := true}) only [t, topOp, execAll, regs_dop _ _ _ _ _ h15,
      X25519Mem.regs_ldm _ _ _ _ h15, listRegs_60, listRegs_06, List.map, toReg1, toReg2, toReg5,
      toReg6, List.mem_cons, List.not_mem_nil, h1, h2, h5, h6, or_self, ite_false]

/-- Two register moves `mov a, x; mov b, y`. -/
theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem :=
  next_mem rfl s

theorem mv2_exec (s : State) (a b x y : Reg) (ha : a ≠ 15) (hb : b ≠ 15) (hy : y ≠ 15)
    (hab : a ≠ b) (hay : a ≠ y) :
    let t := execAll [.movHi a x, .movHi b y] s
    t.regs a = s.regs x ∧ t.regs b = s.regs y ∧ t.mem = s.mem ∧ t.c = s.c ∧
      ∀ r : Reg, r ≠ 15 → r ≠ a → r ≠ b → t.regs r = s.regs r := by
  intro t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [t, execAll, InstrNext.regs_movHi, ha, hab]
  · simp [t, execAll, InstrNext.regs_movHi, hb, hy, Ne.symm hay]
  · simp [t, execAll, InstrNext.mem_movHi]
  · simp [t, execAll, X25519Mul.c_movHi]
  · intro r h15 h1 h2
    simp [t, execAll, InstrNext.regs_movHi, h15, h1, h2]

theorem sumOp_split (neg : Bool) : sumOp neg = pairOp neg false ++ ([.movHi 8 3, .movHi 10 4] ++
    (pairOp neg true ++ ([.movHi 11 3, .movHi 12 4] ++ (pairOp neg true ++ topOp neg)))) := by
  simp only [sumOp, List.append_assoc]

/-- The 256-bit chain: `a + b` (`neg = false`) or `a + ~b + 1` (`neg = true`) in the eight
chain registers and the carry. -/
theorem sumOp_exec (s : State) (neg : Bool) :
    let t := execAll (sumOp neg) s
    regVal t + 2 ^ 256 * t.c.toNat =
        memVal s.mem id (s.regs 1) + memVal s.mem (opY neg) (s.regs 2) + neg.toNat ∧
      t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4, 5, 6, 8, 10, 11, 12] : List Reg) →
        t.regs r = s.regs r := by
  intro t
  simp only [t, sumOp_split, execAll_append]
  obtain ⟨v1, p1, q1, m1, o1⟩ := pairOp_exec s neg false
  generalize execAll (pairOp neg false) s = s1 at v1 p1 q1 m1 o1
  obtain ⟨u8, u10, um, uc, uo⟩ := mv2_exec s1 8 10 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize execAll [.movHi 8 3, .movHi 10 4] s1 = s2 at u8 u10 um uc uo
  obtain ⟨v2, p2, q2, m2, o2⟩ := pairOp_exec s2 neg true
  generalize execAll (pairOp neg true) s2 = s3 at v2 p2 q2 m2 o2
  obtain ⟨w11, w12, wm, wc, wo⟩ := mv2_exec s3 11 12 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  generalize execAll [.movHi 11 3, .movHi 12 4] s3 = s4 at w11 w12 wm wc wo
  obtain ⟨v3, p3, q3, m3, o3⟩ := pairOp_exec s4 neg true
  generalize execAll (pairOp neg true) s4 = s5 at v3 p3 q3 m3 o3
  obtain ⟨v4, m4, o4⟩ := topOp_exec s5 neg
  generalize execAll (topOp neg) s5 = s6 at v4 m4 o4
  -- pointers and memory along the way
  have e1 : s2.regs 1 = slot (s.regs 1) 2 := by rw [uo 1 (by decide) (by decide) (by decide), p1]
  have e2 : s2.regs 2 = slot (s.regs 2) 2 := by rw [uo 2 (by decide) (by decide) (by decide), q1]
  have f1 : s4.regs 1 = slot (s.regs 1) 4 := by
    rw [wo 1 (by decide) (by decide) (by decide), p2, e1, slot_slot]
  have f2 : s4.regs 2 = slot (s.regs 2) 4 := by
    rw [wo 2 (by decide) (by decide) (by decide), q2, e2, slot_slot]
  have g1 : s5.regs 1 = slot (s.regs 1) 6 := by rw [p3, f1, slot_slot]
  have g2 : s5.regs 2 = slot (s.regs 2) 6 := by rw [q3, f2, slot_slot]
  have n2 : s2.mem = s.mem := by rw [um, m1]
  have n4 : s4.mem = s.mem := by rw [wm, m2, n2]
  have n5 : s5.mem = s.mem := by rw [m3, n4]
  rw [n2, e1, e2, uc] at v2
  rw [n4, f1, f2, wc] at v3
  rw [n5, g1, g2] at v4
  simp only [slot_slot, Nat.reduceAdd] at v2 v3 v4
  -- the chain registers at the end
  have r8 : s6.regs 8 = s1.regs 3 := by
    rw [o4 8 (by decide) (by decide), o3 8 (by decide) (by decide), wo 8 (by decide) (by decide)
      (by decide), o2 8 (by decide) (by decide), u8]
  have r10 : s6.regs 10 = s1.regs 4 := by
    rw [o4 10 (by decide) (by decide), o3 10 (by decide) (by decide), wo 10 (by decide) (by decide)
      (by decide), o2 10 (by decide) (by decide), u10]
  have r11 : s6.regs 11 = s3.regs 3 := by
    rw [o4 11 (by decide) (by decide), o3 11 (by decide) (by decide), w11]
  have r12 : s6.regs 12 = s3.regs 4 := by
    rw [o4 12 (by decide) (by decide), o3 12 (by decide) (by decide), w12]
  have r3 : s6.regs 3 = s5.regs 3 := o4 3 (by decide) (by decide)
  have r4 : s6.regs 4 = s5.regs 4 := o4 4 (by decide) (by decide)
  refine ⟨?_, by rw [m4, n5], ?_⟩
  · simp only [regVal, val8, memVal, id, r8, r10, r11, r12, r3, r4]
    simp only [Bool.false_eq_true, ite_false, ite_true] at v1 v2 v3
    omega
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h8, h10, h11, h12⟩ := hr
    rw [o4 r h15 (by simp [h1, h2, h5, h6]), o3 r h15 (by simp [h1, h2, h3, h4, h5, h6]),
      wo r h15 h11 h12, o2 r h15 (by simp [h1, h2, h3, h4, h5, h6]), uo r h15 h8 h10,
      o1 r h15 (by simp [h1, h2, h3, h4, h5, h6])]

theorem loOp_exec (s : State) (neg : Bool) :
    let t := execAll (loOp neg) s
    (t.regs 1).toNat + 2 ^ 32 * (t.regs 2).toNat + 2 ^ 64 * t.c.toNat =
        (s.regs 8).toNat + 2 ^ 32 * (s.regs 10).toNat + (opY neg (s.regs 7)).toNat +
          2 ^ 32 * (opY neg 0#32).toNat + neg.toNat ∧
      t.mem = storeWords s.mem (s.regs 0) [t.regs 1, t.regs 2] ∧
      t.regs 0 = slot (s.regs 0) 2 ∧ t.regs 7 = 0#32 ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 7] : List Reg) → t.regs r = s.regs r := by
  intro t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [t, loOp, execAll, regs_dop, c_dop, regs_op3, c_op3,
      InstrNext.regs_movHi, InstrNext.regs_movImm, X25519Mul.c_movHi, X25519Mul.c_movImm,
      X25519Mem.regs_stm, X25519Mem.c_stm, State.reg, toReg0, toReg1, toReg2, toReg7, ite_true,
      ite_false]
    exact pair_nat _ _ _ _ _ _ _ _ _ (adc_nat _ _ _) (adc_nat _ _ _)
  · simp (config := {decide := true}) only [t, loOp, execAll, X25519Mem.mem_stm, mem_dop, mem_op3,
      InstrNext.mem_movHi, mem_movImm, regs_dop, regs_op3, InstrNext.regs_movHi, InstrNext.regs_movImm,
      X25519Mem.regs_stm, listRegs_06, List.map, State.reg, toReg0, toReg1, toReg2, toReg7,
      ite_true, ite_false]
  · simp (config := {decide := true}) only [t, loOp, execAll, regs_dop, regs_op3,
      InstrNext.regs_movHi, InstrNext.regs_movImm, X25519Mem.regs_stm, State.reg, toReg0, toReg1,
      toReg2, toReg7, ite_true, ite_false, bitCount_06]
    try rfl
  · simp (config := {decide := true}) only [t, loOp, execAll, regs_dop, regs_op3,
      InstrNext.regs_movHi, InstrNext.regs_movImm, X25519Mem.regs_stm, State.reg, toReg0, toReg1,
      toReg2, toReg7, ite_true, ite_false]
    try rfl
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h7⟩ := hr
    simp only [t, loOp, execAll, regs_dop _ _ _ _ _ h15, regs_op3 _ _ _ _ _ _ h15,
      InstrNext.regs_movHi _ _ _ _ h15, InstrNext.regs_movImm _ _ _ _ h15, X25519Mem.regs_stm _ _ _ _ h15,
      toReg0, toReg1, toReg2, toReg7, h0, h1, h2, h7, ite_false]

theorem chain6_nat (r1 r2 r3 r4 r5 r6 c1 c2 c3 c4 c5 c6 x1 x2 x3 x4 x5 x6 y cin : Nat)
    (e1 : r1 + 2 ^ 32 * c1 = x1 + y + cin) (e2 : r2 + 2 ^ 32 * c2 = x2 + y + c1)
    (e3 : r3 + 2 ^ 32 * c3 = x3 + y + c2) (e4 : r4 + 2 ^ 32 * c4 = x4 + y + c3)
    (e5 : r5 + 2 ^ 32 * c5 = x5 + y + c4) (e6 : r6 + 2 ^ 32 * c6 = x6 + y + c5) :
    r1 + 2 ^ 32 * r2 + 2 ^ 64 * r3 + 2 ^ 96 * r4 + 2 ^ 128 * r5 + 2 ^ 160 * r6 + 2 ^ 192 * c6 =
      x1 + 2 ^ 32 * x2 + 2 ^ 64 * x3 + 2 ^ 96 * x4 + 2 ^ 128 * x5 + 2 ^ 160 * x6 +
        y * (1 + 2 ^ 32 + 2 ^ 64 + 2 ^ 96 + 2 ^ 128 + 2 ^ 160) + cin := by
  omega

theorem hiOp_exec (s : State) (neg : Bool) :
    let t := execAll (hiOp neg) s
    let y := (opY neg (s.regs 7)).toNat
    (t.regs 1).toNat + 2 ^ 32 * (t.regs 2).toNat + 2 ^ 64 * (t.regs 3).toNat +
        2 ^ 96 * (t.regs 4).toNat + 2 ^ 128 * (t.regs 5).toNat + 2 ^ 160 * (t.regs 6).toNat +
        2 ^ 192 * t.c.toNat =
      (s.regs 11).toNat + 2 ^ 32 * (s.regs 12).toNat + 2 ^ 64 * (s.regs 3).toNat +
        2 ^ 96 * (s.regs 4).toNat + 2 ^ 128 * (s.regs 5).toNat + 2 ^ 160 * (s.regs 6).toNat +
        y * (1 + 2 ^ 32 + 2 ^ 64 + 2 ^ 96 + 2 ^ 128 + 2 ^ 160) + s.c.toNat ∧
      t.mem = storeWords s.mem (s.regs 0)
        [t.regs 1, t.regs 2, t.regs 3, t.regs 4, t.regs 5, t.regs 6] ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t y
  refine ⟨?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [t, hiOp, execAll, regs_dop, c_dop,
      InstrNext.regs_movHi, X25519Mul.c_movHi, X25519Mem.regs_stm, X25519Mem.c_stm, State.reg,
      toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
    exact chain6_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (adc_nat _ _ _) (adc_nat _ _ _)
      (adc_nat _ _ _) (adc_nat _ _ _) (adc_nat _ _ _) (adc_nat _ _ _)
  · simp (config := {decide := true}) only [t, hiOp, execAll, X25519Mem.mem_stm, mem_dop,
      InstrNext.mem_movHi, regs_dop, InstrNext.regs_movHi, X25519Mem.regs_stm, listRegs_7e, List.map,
      State.reg, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false]
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hr
    simp only [t, hiOp, execAll, regs_dop _ _ _ _ _ h15, InstrNext.regs_movHi _ _ _ _ h15,
      X25519Mem.regs_stm _ _ _ _ h15, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6,
      h0, h1, h2, h3, h4, h5, h6, ite_false]

/-- The store chain: the eight chain words plus `opY K` (then `opY 0` per upper word) go to
`dst`; nothing outside `Region dst 32` changes. -/
theorem outOp_exec (s : State) (neg : Bool) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll (outOp neg) s
    X25519Routines.feVal t.mem (s.regs 0) + 2 ^ 256 * t.c.toNat =
        regVal s + (opY neg (s.regs 7)).toNat +
          (opY neg 0#32).toNat * (2 ^ 32 + 2 ^ 64 + 2 ^ 96 + 2 ^ 128 + 2 ^ 160 + 2 ^ 192 + 2 ^ 224) +
          neg.toNat ∧
      (∀ y, ¬ Region (s.regs 0) 32 y → t.mem y = s.mem y) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6, 7] : List Reg) → t.regs r = s.regs r := by
  intro t
  simp only [t, outOp, execAll_append]
  obtain ⟨lv, lm, l0, l7, lo⟩ := loOp_exec s neg
  generalize execAll (loOp neg) s = s1 at lv lm l0 l7 lo
  obtain ⟨hv, hm, ho⟩ := hiOp_exec s1 neg
  generalize execAll (hiOp neg) s1 = s2 at hv hm ho
  have F1 := (frame_init s.mem hf).storeWords [s1.regs 1, s1.regs 2] (k := 0) (by simp)
  rw [slot_zero, ← lm] at F1
  have F2 := F1.storeWords [s2.regs 1, s2.regs 2, s2.regs 3, s2.regs 4, s2.regs 5, s2.regs 6]
    (k := 2) (by simp)
  rw [← l0, ← hm] at F2
  have q : ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 7] : List Reg) → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) →
      s2.regs r = s.regs r := fun r h15 h1 h2 => by rw [ho r h15 h2, lo r h15 h1]
  refine ⟨?_, fun y hy => frame_out F2 y hy, ?_⟩
  · rw [feVal_frame F2]
    have e11 : s1.regs 11 = s.regs 11 := lo 11 (by decide) (by decide)
    have e12 : s1.regs 12 = s.regs 12 := lo 12 (by decide) (by decide)
    have e3 : s1.regs 3 = s.regs 3 := lo 3 (by decide) (by decide)
    have e4 : s1.regs 4 = s.regs 4 := lo 4 (by decide) (by decide)
    have e5 : s1.regs 5 = s.regs 5 := lo 5 (by decide) (by decide)
    have e6 : s1.regs 6 = s.regs 6 := lo 6 (by decide) (by decide)
    rw [e11, e12, e3, e4, e5, e6, l7] at hv
    simp only [psum, upd, regVal, val8]
    simp
    omega
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hr
    exact q r h15 (by simp [h0, h1, h2, h7]) (by simp [h0, h1, h2, h3, h4, h5, h6])

/-! ## Accesses -/

theorem pairOp_acc {Wr : Word → Prop} (s : State) (neg k : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (pairOp neg k) s :=
  accAll_append (ld34_acc s h1 h2)
    (X25519MulcWord.accAll_regOnly _ _ (by cases k <;> simp [regOnly_dop, regOnly_op3]))

theorem topOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (topOp neg) s := by
  refine accAll_cons (ldm_acc s 1 _ h1) (accAll_cons (ldm_acc _ 2 _ ?_)
    (X25519MulcWord.accAll_regOnly _ _ (by simp [regOnly_dop])))
  have : ((Instr.ldm 1 0x60).next s).regs 2 = s.regs 2 := by
    simp (config := {decide := true}) only [X25519Mem.regs_ldm, listRegs_60, List.map,
      toReg5, toReg6, toReg1, List.mem_cons, List.not_mem_nil, ite_false, or_self]
  show (((Instr.ldm 1 0x60).next s).regs (LowReg.toReg 2)).toNat % 4 = 0
  rw [toReg2, this]; exact h2

theorem mv2_acc {Wr : Word → Prop} (s : State) (a b x y : Reg) :
    AccAll (AccOk Wr) [.movHi a x, .movHi b y] s :=
  X25519MulcWord.accAll_regOnly _ _ rfl

theorem sumOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h1 : (s.regs 1).toNat % 4 = 0)
    (h2 : (s.regs 2).toNat % 4 = 0) : AccAll (AccOk Wr) (sumOp neg) s := by
  rw [sumOp_split]
  obtain ⟨-, p1, q1, -, -⟩ := pairOp_exec s neg false
  refine accAll_append (pairOp_acc s neg false h1 h2) ?_
  generalize execAll (pairOp neg false) s = s1 at p1 q1
  obtain ⟨-, -, -, -, uo⟩ := mv2_exec s1 8 10 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine accAll_append (mv2_acc s1 _ _ _ _) ?_
  generalize execAll [.movHi 8 3, .movHi 10 4] s1 = s2 at uo
  have e1 : s2.regs 1 = slot (s.regs 1) 2 := by rw [uo 1 (by decide) (by decide) (by decide), p1]
  have e2 : s2.regs 2 = slot (s.regs 2) 2 := by rw [uo 2 (by decide) (by decide) (by decide), q1]
  obtain ⟨-, p2, q2, -, -⟩ := pairOp_exec s2 neg true
  refine accAll_append (pairOp_acc s2 neg true (by rw [e1]; exact slot_al h1 2)
    (by rw [e2]; exact slot_al h2 2)) ?_
  generalize execAll (pairOp neg true) s2 = s3 at p2 q2
  obtain ⟨-, -, -, -, wo⟩ := mv2_exec s3 11 12 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine accAll_append (mv2_acc s3 _ _ _ _) ?_
  generalize execAll [.movHi 11 3, .movHi 12 4] s3 = s4 at wo
  have f1 : s4.regs 1 = slot (s.regs 1) 4 := by
    rw [wo 1 (by decide) (by decide) (by decide), p2, e1, slot_slot]
  have f2 : s4.regs 2 = slot (s.regs 2) 4 := by
    rw [wo 2 (by decide) (by decide) (by decide), q2, e2, slot_slot]
  obtain ⟨-, p3, q3, -, -⟩ := pairOp_exec s4 neg true
  refine accAll_append (pairOp_acc s4 neg true (by rw [f1]; exact slot_al h1 4)
    (by rw [f2]; exact slot_al h2 4)) ?_
  refine topOp_acc _ neg (by rw [p3, f1, slot_slot]; exact slot_al h1 6)
    (by rw [q3, f2, slot_slot]; exact slot_al h2 6)

theorem regs0_keep (s : State) (is : List Instr) (h : is.all (fun i => !(i.dsts.contains 0)) = true) :
    (execAll is s).regs 0 = s.regs 0 :=
  execAll_regs_other is s 0 (by decide) h

theorem loOp_split (neg : Bool) : loOp neg =
    [.movHi 1 8, .movHi 2 10, op3 neg 1 1 7, .movImm 7 0, .dp (dop neg) 2 7] ++ [.stm 0 0x06] := rfl

theorem hiOp_split (neg : Bool) : hiOp neg =
    [.movHi 1 11, .movHi 2 12, .dp (dop neg) 1 7, .dp (dop neg) 2 7, .dp (dop neg) 3 7,
      .dp (dop neg) 4 7, .dp (dop neg) 5 7, .dp (dop neg) 6 7] ++ [.stm 0 0x7e] := rfl

theorem outOp_acc {Wr : Word → Prop} (s : State) (neg : Bool) (h0 : (s.regs 0).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) (outOp neg) s := by
  obtain ⟨-, -, l0, -, -⟩ := loOp_exec s neg
  refine accAll_append ?_ ?_
  · rw [loOp_split]
    refine accAll_append (X25519MulcWord.accAll_regOnly _ _ (by cases neg <;> decide))
      (accAll_cons (stm_acc _ 0 _ ?_ ?_) (accAll_nil _ _))
    all_goals
      have e : (execAll [.movHi 1 8, .movHi 2 10, op3 neg 1 1 7, .movImm 7 0, .dp (dop neg) 2 7]
          s).reg 0 = s.regs 0 := regs0_keep _ _ (by cases neg <;> decide)
      rw [e]
    · exact h0
    · intro i hi q hq
      have := wr_words hW (k := 0) (n := 2) (by omega) i (by rw [bitCount_06] at hi; exact hi) q hq
      rwa [slot_zero] at this
  · rw [hiOp_split]
    generalize execAll (loOp neg) s = s1 at l0
    refine accAll_append (X25519MulcWord.accAll_regOnly _ _ (by cases neg <;> decide))
      (accAll_cons (stm_acc _ 0 _ ?_ ?_) (accAll_nil _ _))
    all_goals
      have e : (execAll [.movHi 1 11, .movHi 2 12, .dp (dop neg) 1 7, .dp (dop neg) 2 7,
          .dp (dop neg) 3 7, .dp (dop neg) 4 7, .dp (dop neg) 5 7, .dp (dop neg) 6 7] s1).reg 0 =
          s1.regs 0 := regs0_keep _ _ (by cases neg <;> decide)
      rw [e, l0]
    · exact slot_al h0 2
    · intro i hi q hq
      exact wr_words hW (k := 2) (n := 6) (by omega) i (by rw [bitCount_7e] at hi; exact hi) q hq

end M0Crypto.Release.X25519Inl
