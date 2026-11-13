import M0Crypto.Release.X25519Mul64

set_option linter.unusedSimpArgs false

/-!
Macro `sqr64` of the X25519 field routines (plan `x25519-proofs.md`, phase 7): one level of
Karatsuba squaring, `o3:a1:o1:a0 = (a1:a0)^2`.

The macro is split as the generator writes it: the absolute difference `|a1 - a0|`
(`absdiff`, its mask is not needed: a square has no sign), three `sqr32` (the difference,
`a0` and `a1`) and the tail `sqr64Post`. The tail subtracts the low square from the middle
square over three words (`t3:t2:t1 = D - L`, with `sbcs t3, t3` as the top word), adds the
high square at words 1 and 2 (`o3:a1:o1 = L1 + H + 2^32 * H`), and subtracts the first from
the second. Modulo `2^96` this is `L1 + L + H - D + 2^32 * H`, and `L + H - D = 2 * a0 * a1`
by `X25519Kara.cross_sq`. The value of the tail is `sqr64_tail_nat`.

`sqr64_exec` composes the piece lemmas without naming the operands of the inner macros:
`generalize` takes them from the goal, the `_eq` forms of the step lemmas read them from the
run equation, and register disequalities are closed by `regne`. So renaming the scratch
registers of an inner `sqr32`, or reordering independent instructions inside a piece, needs
no edit here. `sqr64_run_w` is the `ReachW` block lemma, generic in the registers and the
offset. The instance check binds the list to the artifact at the first `sqr64` of
`m0c_fe_sqr`, from the routine symbol.
-/

namespace M0Crypto.Release.X25519Kara

/-- Two-word subtraction `subs`/`sbcs` from its borrow equations. -/
theorem sub2 (u1 u2 L0 L1 d0 d1 p1 p2 : Nat)
    (s1 : u1 + L0 + (1 - 1) = d0 + 2 ^ 32 * (1 - p1))
    (s2 : u2 + L1 + (1 - p1) = d1 + 2 ^ 32 * (1 - p2)) :
    u1 + 2 ^ 32 * u2 + (L0 + 2 ^ 32 * L1) = d0 + 2 ^ 32 * d1 + 2 ^ 64 * (1 - p2) := by
  omega

/-- Three-word subtraction `subs`/`sbcs`/`sbcs` from its borrow equations. -/
theorem sub3 (w1 w2 w3 u1 u2 M v1 v2 v3 q1 q2 q3 : Nat)
    (z1 : w1 + u1 + (1 - 1) = v1 + 2 ^ 32 * (1 - q1))
    (z2 : w2 + u2 + (1 - q1) = v2 + 2 ^ 32 * (1 - q2))
    (z3 : w3 + M + (1 - q2) = v3 + 2 ^ 32 * (1 - q3)) :
    w1 + 2 ^ 32 * w2 + 2 ^ 64 * w3 + (u1 + 2 ^ 32 * u2 + 2 ^ 64 * M) =
      v1 + 2 ^ 32 * v2 + 2 ^ 64 * v3 + 2 ^ 96 * (1 - q3) := by
  omega

/-- The linear core of the `sqr64` tail: the 96-bit result `W` agrees with the middle part
of the square modulo `2^96`, and both are below `2^96`. -/
theorem sqr64_tail_lin (L H P D L0 L1 H0 H1 W U V b c k : Nat)
    (cs : H + L = P + P + D)
    (cv : V + 2 ^ 96 * k = L1 + 2 ^ 32 * H0 + 2 ^ 64 * H1 + (H0 + 2 ^ 32 * H1 + 2 ^ 64 * 0) + 0)
    (cu : U + L = D + 2 ^ 64 * b) (hb : b ≤ 1)
    (cw : W + (U + 2 ^ 64 * (b * (2 ^ 32 - 1))) = V + 2 ^ 96 * c)
    (hL : L0 + 2 ^ 32 * L1 = L) (hH : H0 + 2 ^ 32 * H1 = H)
    (hW : W < 2 ^ 96) (hprod : L + 2 ^ 32 * (P + P) + 2 ^ 32 * 2 ^ 32 * H < 2 ^ 128) :
    L0 + 2 ^ 32 * W = L + 2 ^ 32 * (P + P) + 2 ^ 32 * 2 ^ 32 * H := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> omega

/-- `cross_sq` for `x = |A1 - A0|`, in the orientation of the `sqr64` tail. -/
theorem sq_cross (A0 A1 x : Nat) (hx : (A1 : Int) - A0 = if A1 < A0 then -(x : Int) else x) :
    A1 * A1 + A0 * A0 = A0 * A1 + A0 * A1 + x * x := by
  have cs := cross_sq A1 A0 x (if A1 < A0 then 1 else 0) (by split <;> simp_all)
    (by split <;> omega)
  rw [Nat.mul_comm A1 A0] at cs
  exact cs

theorem sq64_lt {A0 A1 : Nat} (hA0 : A0 < 2 ^ 32) (hA1 : A1 < 2 ^ 32) :
    (A0 + 2 ^ 32 * A1) * (A0 + 2 ^ 32 * A1) < 2 ^ 128 := by
  have := Nat.mul_lt_mul_of_lt_of_lt (show A0 + 2 ^ 32 * A1 < 2 ^ 64 by omega)
    (show A0 + 2 ^ 32 * A1 < 2 ^ 64 by omega)
  simpa using this

theorem w4_split (L0 w1 w2 w3 : Nat) :
    L0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 =
      L0 + 2 ^ 32 * (w1 + 2 ^ 32 * w2 + 2 ^ 64 * w3) := by
  omega

/-- The tail of macro `sqr64`. `L`, `H`, `D` are the squares of `A0`, `A1` and
`x = |A1 - A0|`. The first chain is `D - L` over three words (`p` are carries, the top word
`M` is the borrow mask), the second `L1 + H + 2^32 * H` (`k` carries), the third their
difference (`q` carries). The result is the 128-bit square. -/
theorem sqr64_tail_nat (A0 A1 x L0 L1 H0 H1 d0 d1 : Nat)
    (u1 u2 p1 p2 M v1 v2 v3 k1 k2 k3 w1 w2 w3 q1 q2 q3 : Nat)
    (hA0 : A0 < 2 ^ 32) (hA1 : A1 < 2 ^ 32)
    (hL : L0 + 2 ^ 32 * L1 = A0 * A0) (hH : H0 + 2 ^ 32 * H1 = A1 * A1)
    (hD : d0 + 2 ^ 32 * d1 = x * x)
    (hx : (A1 : Int) - A0 = if A1 < A0 then -(x : Int) else x)
    (s1 : u1 + L0 + (1 - 1) = d0 + 2 ^ 32 * (1 - p1))
    (s2 : u2 + L1 + (1 - p1) = d1 + 2 ^ 32 * (1 - p2))
    (hM : M = (1 - p2) * (2 ^ 32 - 1))
    (a1 : v1 + 2 ^ 32 * k1 = L1 + H0 + 0)
    (a2 : v2 + 2 ^ 32 * k2 = H0 + H1 + k1)
    (a3 : v3 + 2 ^ 32 * k3 = H1 + 0 + k2)
    (z1 : w1 + u1 + (1 - 1) = v1 + 2 ^ 32 * (1 - q1))
    (z2 : w2 + u2 + (1 - q1) = v2 + 2 ^ 32 * (1 - q2))
    (z3 : w3 + M + (1 - q2) = v3 + 2 ^ 32 * (1 - q3))
    (l1 : w1 < 2 ^ 32) (l2 : w2 < 2 ^ 32) (l3 : w3 < 2 ^ 32) :
    L0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 = (A0 + 2 ^ 32 * A1) * (A0 + 2 ^ 32 * A1) := by
  have hprod := sq64_lt hA0 hA1
  have cs := sq_cross A0 A1 x hx
  have hk := kara_split (2 ^ 32) A0 A1 A0 A1
  rw [Nat.mul_comm A1 A0] at hk
  have cv := chain3 _ _ _ _ _ _ _ _ _ _ _ _ _ a1 a2 a3
  have cu := sub2 _ _ _ _ _ _ _ _ s1 s2
  have cw := sub3 _ _ _ _ _ _ _ _ _ _ _ _ z1 z2 z3
  rw [hM] at cw
  have hW := w3_lt l1 l2 l3
  rw [hk] at hprod ⊢
  rw [w4_split]; rw [hD, hL] at cu
  exact sqr64_tail_lin _ _ _ _ L0 L1 H0 H1 _ _ _ _ _ _ cs cv cu (Nat.sub_le 1 p2) cw hL hH hW
    hprod

end M0Crypto.Release.X25519Kara

namespace M0Crypto.Release.X25519Mul
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2s (toReg_ne15 regs_movImm)

/-- The tail of `sqr64`: `t3:t2:t1 -= 0:o1:a0`, `o3:a1:o1 += o3:a1` at word 1,
then `o3:a1:o1 -= t3:t2:t1`. -/
def sqr64Post (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) : List Instr :=
  [.subReg t1 t1 a0, .dp .sbcs t2 o1, .dp .sbcs t3 t3,
   .addReg o1 o1 a1, .dp .adcs a1 o3, .movImm t4 0, .dp .adcs o3 t4,
   .subReg o1 o1 t1, .dp .sbcs a1 t2, .dp .sbcs o3 t3]

/-- Macro `sqr64 a0, a1, o1, o3, t1, t2, t3, t4`: `o3:a1:o1:a0 = (a1:a0)^2`. -/
def sqr64 (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) : List Instr :=
  absdiff t1 a1 a0 t2 ++ sqr32 t1 t2 t3 t4 ++ sqr32 a0 o1 t3 t4 ++ sqr32 a1 o3 t3 t4 ++
    sqr64Post a0 a1 o1 o3 t1 t2 t3 t4

theorem sqrPost_regs (s : State) (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg)
    (hd : Dist8 a0 a1 o1 o3 t1 t2 t3 t4) :
    let s' := execAll (sqr64Post a0 a1 o1 o3 t1 t2 t3 t4) s
    ∃ X1 X2 X3 Y1 Y2 Y3 Z1 Z2 Z3 : Word × Bool × Bool,
      X1 = addWithCarry (s.reg t1) (~~~(s.reg a0)) true ∧
      X2 = addWithCarry (s.reg t2) (~~~(s.reg o1)) X1.2.1 ∧
      X3 = addWithCarry (s.reg t3) (~~~(s.reg t3)) X2.2.1 ∧
      Y1 = addWithCarry (s.reg o1) (s.reg a1) false ∧
      Y2 = addWithCarry (s.reg a1) (s.reg o3) Y1.2.1 ∧
      Y3 = addWithCarry (s.reg o3) (BitVec.setWidth 32 (0 : BitVec 8)) Y2.2.1 ∧
      Z1 = addWithCarry Y1.1 (~~~X1.1) true ∧
      Z2 = addWithCarry Y2.1 (~~~X2.1) Z1.2.1 ∧
      Z3 = addWithCarry Y3.1 (~~~X3.1) Z2.2.1 ∧
      s'.reg a0 = s.reg a0 ∧ s'.reg o1 = Z1.1 ∧ s'.reg a1 = Z2.1 ∧ s'.reg o3 = Z3.1 := by
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨d01, d02, d03, d04, d05, d06, d07⟩, ⟨d12, d13, d14, d15, d16, d17⟩,
    ⟨d23, d24, d25, d26, d27⟩, ⟨d34, d35, d36, d37⟩, ⟨d45, d46, d47⟩, ⟨d56, d57⟩, d67⟩ := hd
  intro s'
  refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [s', sqr64Post, execAll, State.reg]
  simp only [regs_movImm, regs_adcs, regs_adds, regs_subs, regs_sbcs, c_adds, c_adcs, c_subs,
    c_sbcs, c_movImm, toReg_ne15, ne_eq, not_false_eq_true, State.reg, toReg_inj,
    d01, d02, d03, d04, d05, d06, d07, d12, d13, d14, d15, d16, d17, d23, d24, d25, d26, d27,
    d34, d35, d36, d37, d45, d46, d47, d56, d57, d67,
    Ne.symm d01, Ne.symm d02, Ne.symm d03, Ne.symm d04, Ne.symm d05, Ne.symm d06, Ne.symm d07,
    Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, Ne.symm d17, Ne.symm d23,
    Ne.symm d24, Ne.symm d25, Ne.symm d26, Ne.symm d27, Ne.symm d34, Ne.symm d35, Ne.symm d36,
    Ne.symm d37, Ne.symm d45, Ne.symm d46, Ne.symm d47, Ne.symm d56, Ne.symm d57, Ne.symm d67,
    ite_true, ite_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem mask_borrow_toNat (c : Bool) :
    (if c then 0#32 else BitVec.allOnes 32).toNat = (1 - c.toNat) * (2 ^ 32 - 1) := by
  cases c <;> rfl

theorem sqrPost_value (s : State) (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg)
    (hd : Dist8 a0 a1 o1 o3 t1 t2 t3 t4) (A0 A1 x : Nat) (hA0 : A0 < 2 ^ 32) (hA1 : A1 < 2 ^ 32)
    (hL : (s.reg a0).toNat + 2 ^ 32 * (s.reg o1).toNat = A0 * A0)
    (hH : (s.reg a1).toNat + 2 ^ 32 * (s.reg o3).toNat = A1 * A1)
    (hD : (s.reg t1).toNat + 2 ^ 32 * (s.reg t2).toNat = x * x)
    (hx : (A1 : Int) - A0 = if A1 < A0 then -(x : Int) else x) :
    let s' := execAll (sqr64Post a0 a1 o1 o3 t1 t2 t3 t4) s
    s'.reg a0 = s.reg a0 ∧
      (s.reg a0).toNat + 2 ^ 32 * (s'.reg o1).toNat + 2 ^ 64 * (s'.reg a1).toNat +
        2 ^ 96 * (s'.reg o3).toNat = (A0 + 2 ^ 32 * A1) * (A0 + 2 ^ 32 * A1) := by
  obtain ⟨X1, X2, X3, Y1, Y2, Y3, Z1, Z2, Z3, hX1, hX2, hX3, hY1, hY2, hY3, hZ1, hZ2, hZ3,
    r0, r1, r2, r3⟩ := sqrPost_regs s a0 a1 o1 o3 t1 t2 t3 t4 hd
  intro s'
  refine ⟨r0, ?_⟩
  rw [r1, r2, r3]
  have z : (BitVec.setWidth 32 (0 : BitVec 8)).toNat = 0 := rfl
  have e1 := X25519Carry.sbc_nat (s.reg t1) (s.reg a0) true
  have e2 := X25519Carry.sbc_nat (s.reg t2) (s.reg o1) X1.2.1
  have e4 := X25519Carry.adc_nat (s.reg o1) (s.reg a1) false
  have e5 := X25519Carry.adc_nat (s.reg a1) (s.reg o3) Y1.2.1
  have e6 := X25519Carry.adc_nat (s.reg o3) (BitVec.setWidth 32 (0 : BitVec 8)) Y2.2.1
  have e7 := X25519Carry.sbc_nat Y1.1 X1.1 true
  have e8 := X25519Carry.sbc_nat Y2.1 X2.1 Z1.2.1
  have e9 := X25519Carry.sbc_nat Y3.1 X3.1 Z2.2.1
  rw [← hX1] at e1; rw [← hX2] at e2; rw [← hY1] at e4; rw [← hY2] at e5; rw [← hY3] at e6
  rw [← hZ1] at e7; rw [← hZ2] at e8; rw [← hZ3] at e9
  rw [z] at e6
  have hM : X3.1.toNat = (1 - X2.2.1.toNat) * (2 ^ 32 - 1) := by
    rw [hX3, sbcs_self, mask_borrow_toNat]
  exact X25519Kara.sqr64_tail_nat A0 A1 x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hA0 hA1 hL hH hD hx e1 e2 hM e4 e5 e6 e7 e8 e9 Z1.1.isLt Z2.1.isLt Z3.1.isLt

theorem sqrPost_frame (s : State) (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) (r : Reg)
    (h15 : r ≠ 15) (ra1 : r ≠ a1.toReg) (ro1 : r ≠ o1.toReg) (ro3 : r ≠ o3.toReg)
    (r1 : r ≠ t1.toReg) (r2 : r ≠ t2.toReg) (r3 : r ≠ t3.toReg) (r4 : r ≠ t4.toReg) :
    (execAll (sqr64Post a0 a1 o1 o3 t1 t2 t3 t4) s).regs r = s.regs r := by
  simp only [sqr64Post, execAll]
  simp only [regs_movImm, regs_adcs, regs_adds, regs_subs, regs_sbcs,
    ne_eq, not_false_eq_true, h15, ra1, ro1, ro3, r1, r2, r3, r4, ite_false]

/-! Step lemmas in equation form: the operands come from the run equation, so the
composition below never names them. -/

theorem absdiff_eq {s s' : State} {d x y m : LowReg} (he : execAll (absdiff d x y m) s = s')
    (hdm : d ≠ m) :
    ((s.reg x).toNat : Int) - (s.reg y).toNat =
        (if (s.reg x).toNat < (s.reg y).toNat then -((s'.reg d).toNat : Int)
          else (s'.reg d).toNat) ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → r ≠ m.toReg → s'.regs r = s.regs r := by
  subst he
  obtain ⟨_, h2, h3, h4⟩ := absdiff_exec s d x y m (vne hdm)
  exact ⟨h2, h3, h4⟩

theorem sqr32_eq {s s' : State} {rl rh rt ru : LowReg} (he : execAll (sqr32 rl rh rt ru) s = s')
    (h : Dist4 rl rh rt ru) :
    (s'.reg rl).toNat + 2 ^ 32 * (s'.reg rh).toNat = (s.reg rl).toNat * (s.reg rl).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ rl.toReg → r ≠ rh.toReg → r ≠ rt.toReg → r ≠ ru.toReg →
        s'.regs r = s.regs r := by
  subst he; exact sqr32_exec s rl rh rt ru h

/-- Close a `LowReg` disequality from the distinctness facts in context. -/
macro "lowne" : tactic => `(tactic| first | assumption | exact Ne.symm ‹_›)

/-- Close a `Dist4` goal from the distinctness facts in context. -/
macro "dist4" : tactic => `(tactic| constructor <;> first | exact vne ‹_› | exact vne (Ne.symm ‹_›))

theorem sqr64_exec (s : State) (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg)
    (hd : Dist8 a0 a1 o1 o3 t1 t2 t3 t4) :
    let s' := execAll (sqr64 a0 a1 o1 o3 t1 t2 t3 t4) s
    (s'.reg a0).toNat + 2 ^ 32 * (s'.reg o1).toNat + 2 ^ 64 * (s'.reg a1).toNat +
        2 ^ 96 * (s'.reg o3).toNat =
      ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) *
        ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ a0.toReg → r ≠ a1.toReg → r ≠ o1.toReg → r ≠ o3.toReg →
        r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t3.toReg → r ≠ t4.toReg →
        s'.regs r = s.regs r := by
  have hd' := hd
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨d01, d02, d03, d04, d05, d06, d07⟩, ⟨d12, d13, d14, d15, d16, d17⟩,
    ⟨d23, d24, d25, d26, d27⟩, ⟨d34, d35, d36, d37⟩, ⟨d45, d46, d47⟩, ⟨d56, d57⟩, d67⟩ := hd'
  intro s'
  simp only [s', sqr64, execAll_append]
  generalize hs1 : execAll (absdiff _ _ _ _) s = s1
  obtain ⟨p1, p2, p3⟩ := absdiff_eq hs1 (by lowne)
  generalize hs2 : execAll (sqr32 _ _ _ _) s1 = s2
  obtain ⟨u1, u2, u3⟩ := sqr32_eq hs2 (by dist4)
  generalize hs3 : execAll (sqr32 _ _ _ _) s2 = s3
  obtain ⟨v1, v2, v3⟩ := sqr32_eq hs3 (by dist4)
  generalize hs4 : execAll (sqr32 _ _ _ _) s3 = s4
  obtain ⟨w1, w2, w3⟩ := sqr32_eq hs4 (by dist4)
  -- register values entering the tail
  have e2a0 : s2.reg a0 = s.reg a0 := (u3 _ rg rg rg rg rg).trans (p3 _ rg rg rg)
  have e3a1 : s3.reg a1 = s.reg a1 :=
    (v3 _ rg rg rg rg rg).trans ((u3 _ rg rg rg rg rg).trans (p3 _ rg rg rg))
  have e4a0 : s4.reg a0 = s3.reg a0 := w3 _ rg rg rg rg rg
  have e4o1 : s4.reg o1 = s3.reg o1 := w3 _ rg rg rg rg rg
  have e4t1 : s4.reg t1 = s2.reg t1 := (w3 _ rg rg rg rg rg).trans (v3 _ rg rg rg rg rg)
  have e4t2 : s4.reg t2 = s2.reg t2 := (w3 _ rg rg rg rg rg).trans (v3 _ rg rg rg rg rg)
  rw [e2a0] at v1
  rw [e3a1] at w1
  obtain ⟨z1, z2⟩ := sqrPost_value s4 a0 a1 o1 o3 t1 t2 t3 t4 hd
    (s.reg a0).toNat (s.reg a1).toNat (s1.reg t1).toNat (BitVec.isLt _) (BitVec.isLt _)
    (by rw [e4a0, e4o1]; exact v1) w1 (by rw [e4t1, e4t2]; exact u1) p1
  refine ⟨?_, ?_, ?_⟩
  · rw [z1]; exact z2
  · rw [execAll_mem _ _ (by simp [sqr64Post, Instr.writesMem]), w2, v2, u2, p2]
  · intro r h15 r0 ra1 ro1 ro3 r1 r2 r3 r4
    exact (sqrPost_frame _ _ _ _ _ _ _ _ _ _ rg rg rg rg rg rg rg rg).trans
      ((w3 r rg rg rg rg rg).trans ((v3 r rg rg rg rg rg).trans ((u3 r rg rg rg rg rg).trans
        (p3 r rg rg rg))))

open M0Crypto.Thumb.ReleaseCheck.X25519 (feSqr) in
/-- The first `sqr64` of `m0c_fe_sqr`, after the routine's entry (save, frame, operand
load). -/
theorem sqr64_at_fe_sqr :
    seqAt B feSqr ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .movHi 12 1,
      .ldm 1 0x50] ++ sqr64 4 6 5 7 0 1 2 3) = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem sqr64_regOnly (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) :
    (sqr64 a0 a1 o1 o3 t1 t2 t3 t4).all regOnly = true := by
  simp [sqr64, absdiff, sqr32, sqr64Post, regOnly]

theorem sqr64_noW (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) :
    (sqr64 a0 a1 o1 o3 t1 t2 t3 t4).all (!·.writesMem) = true := by
  simp [sqr64, absdiff, sqr32, sqr64Post, Instr.writesMem]

theorem sqr64_falls (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) :
    (sqr64 a0 a1 o1 o3 t1 t2 t3 t4).all Instr.falls = true := by
  have nl : ∀ x : LowReg, x.toReg.val ≠ 15 := fun x e => toReg_ne15 x (Fin.ext e)
  simp [sqr64, absdiff, sqr32, sqr64Post, Instr.falls, nl]

theorem sqr64_size (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg) :
    seqSize (sqr64 a0 a1 o1 o3 t1 t2 t3 t4) = 88 := by
  simp [sqr64, absdiff, sqr32, sqr64Post, seqSize, Instr.size]

/-- One `sqr64` block in a `ReachW` proof: the 128-bit square of `a1:a0` lands in
`o3:a1:o1:a0`; memory and every register outside the eight operands are unchanged. -/
theorem sqr64_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {t : State}
    {off : Nat} {a0 a1 o1 o3 t1 t2 t3 t4 : LowReg} (hd : Dist8 a0 a1 o1 o3 t1 t2 t3 t4)
    (hseq : seqAt B off (sqr64 a0 a1 o1 o3 t1 t2 t3 t4) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (sqr64 a0 a1 o1 o3 t1 t2 t3 t4)))
    {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 88) → t'.mem = t.mem →
      (t'.reg a0).toNat + 2 ^ 32 * (t'.reg o1).toNat + 2 ^ 64 * (t'.reg a1).toNat +
          2 ^ 96 * (t'.reg o3).toNat =
        ((t.reg a0).toNat + 2 ^ 32 * (t.reg a1).toNat) *
          ((t.reg a0).toNat + 2 ^ 32 * (t.reg a1).toNat) →
      (∀ r : Reg, r ≠ 15 → r ≠ a0.toReg → r ≠ a1.toReg → r ≠ o1.toReg → r ≠ o3.toReg →
        r ≠ t1.toReg → r ≠ t2.toReg → r ≠ t3.toReg → r ≠ t4.toReg →
        t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hf := sqr64_falls a0 a1 o1 o3 t1 t2 t3 t4
  apply ReachW.block hb _ off hpc ho hseq hf (alignedAll_regOnly _ _ (sqr64_regOnly ..))
    (WritesTo.of_noWritesMem _ _ (sqr64_noW ..) Wr) hr
  obtain ⟨e1, e2, e3⟩ := sqr64_exec t a0 a1 o1 o3 t1 t2 t3 t4 hd
  apply k _ _ e2 e1 e3
  rw [execAll_pc _ _ hf, sqr64_size, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Mul
