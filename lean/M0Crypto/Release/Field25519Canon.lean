import M0Crypto.Release.BlockEffect
import M0Crypto.Release.Field25519Facts
import M0Crypto.Release.Field25519Routines
import M0Crypto.Release.Field25519Reduce

/-!
# `m0c_fe_canon`

`push {lr}`, `canon_body` (generator `tools/gen_x25519.py`) and `pop {pc}`: the element at `r0`
becomes its canonical representative, in place.

The body is three decided blocks (`BlockEffect`): the head and the first pass (`e1`), the second
pass and the middle (`e2`), the third pass and the tail (`e3`). Each pass is the add chain
`outW` over its input words, whose value is `chain_val`; `Field25519Reduce.canon_passes` (the
numbers of the three passes) gives the result.
-/

namespace M0Crypto.Release.Field25519Canon

open M0Crypto.Armv6M (Word Reg State Mem read32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.BlockEffect
open M0Crypto.Release.Field25519Facts (psum psum_congr feVal_psum)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Sym (SExpr SBool SMem)

/-! ## An add chain -/

/-- The carry into word `n` of `adds` then `adcs` over the words `x`: `y` is added to word 0,
`z` to the others. -/
def carryW (x : Nat → SExpr) (y z : SExpr) : Nat → SBool
  | 0 => .const false
  | n + 1 => .awcC (x n) (if n = 0 then y else z) (carryW x y z n)

/-- Word `n` of the chain. -/
def outW (x : Nat → SExpr) (y z : SExpr) (n : Nat) : SExpr :=
  .awc (x n) (if n = 0 then y else z) (carryW x y z n)

/-- With `z = 0`: the words of the chain and its carry are the words `x` plus `y`. -/
theorem chain_val (x : Nat → SExpr) (y z : SExpr) (s : State) (hz : z.denote s = 0#32) :
    ∀ n, psum (fun i => ((outW x y z i).denote s).toNat) (n + 1) +
      2 ^ (32 * (n + 1)) * ((carryW x y z (n + 1)).denote s).toNat =
        psum (fun i => ((x i).denote s).toNat) (n + 1) + (y.denote s).toNat
  | 0 => by
    have := Field25519Carry.adc_nat ((x 0).denote s) (y.denote s) false
    simp only [psum, outW, carryW, ↓reduceIte, SExpr.denote, SBool.denote, Bool.toNat_false,
      Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one] at this ⊢
    omega
  | n + 1 => by
    have ih := chain_val x y z s hz n
    have a := Field25519Carry.adc_nat ((x (n + 1)).denote s) (z.denote s) ((carryW x y z (n + 1)).denote s)
    have ps : ∀ f : Nat → Nat, psum f (n + 1 + 1) = psum f (n + 1) + 2 ^ (32 * (n + 1)) * f (n + 1) :=
      fun _ => rfl
    have co : carryW x y z (n + 1 + 1) = .awcC (x (n + 1)) z (carryW x y z (n + 1)) := rfl
    have ou : outW x y z (n + 1) = .awc (x (n + 1)) z (carryW x y z (n + 1)) := rfl
    rw [ps, ps, co, ou, show 32 * (n + 1 + 1) = 32 * (n + 1) + 32 by omega, Nat.pow_add, Nat.mul_assoc]
    simp only [SExpr.denote, SBool.denote, hz, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at a ⊢
    generalize 2 ^ (32 * (n + 1)) = P at ih ⊢
    have a' := congrArg (P * ·) a
    simp only [Nat.mul_add] at a'
    omega

/-! ## The blocks -/

abbrev cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)
/-- The address of word `i` at `r0`, and its entry value. -/
def wA (i : Nat) : SExpr := .add (.reg0 0) (cw (4 * i))
def ldW (i : Nat) : SExpr := .ld32 .mem0 (wA i)
/-- Bit 31 cleared, and bit 31. -/
def clr (e : SExpr) : SExpr := .lsr (.lsl e 1) 1
def top (e : SExpr) : SExpr := .lsr e 31
/-- The eight words at `r0` read back as `w`. -/
def rds (w : Nat → SExpr) : List (SExpr × SExpr) := (List.range 8).map fun i => (wA i, w i)

/-- Word `i` of a pass adding `r_c` (word 0) or `r2` with carry, stored if `st`. -/
def word (c : M0Crypto.Armv6M.LowReg) (st : Bool) (i : Nat) : List Instr :=
  [.memImm .ldr 1 0 (BitVec.ofNat 5 i), if i = 0 then .addReg 1 1 c else .dp .adcs 1 2] ++
    (if st then [.memImm .str 1 0 (BitVec.ofNat 5 i)] else [])
def pass (c : M0Crypto.Armv6M.LowReg) (st : Bool) : List Instr := (List.range 8).flatMap (word c st)
/-- `r2 = 0`, `r3 = 19`, `r4 = 19 · bit 255`, bit 255 cleared in memory. -/
def head : List Instr :=
  [.movImm 2 0, .movImm 3 19, .memImm .ldr 1 0 7, .lsrImm 4 1 31, .lslImm 1 1 1, .lsrImm 1 1 1,
    .memImm .str 1 0 7, .dp .muls 4 3]
def mid : List Instr := [.lsrImm 4 1 31, .dp .muls 4 3]
def tail : List Instr := [.lslImm 1 1 1, .lsrImm 1 1 1, .memImm .str 1 0 7]

def b1 : List Instr := head ++ pass 4 true
def b2 : List Instr := pass 3 false ++ mid
def b3 : List Instr := pass 4 true ++ tail
def body : List Instr := b1 ++ b2 ++ b3

/-- Pass 1: `19 · bit 255` added to the input with bit 255 cleared, stored. -/
def x1 (i : Nat) : SExpr := if i = 7 then clr (ldW 7) else ldW i
def y1 : SExpr := .mul (cw 19) (top (ldW 7))
def w1 : Nat → SExpr := outW x1 y1 (cw 0)
def e1 : Eff := { regs := [(2, cw 0), (3, cw 19), (4, y1)], clob := [1], mem := none, reads := rds w1 }

/-- Pass 2: `19` added, not stored; `r4 = 19 · bit 255` of it. -/
def w2 : Nat → SExpr := outW ldW (.reg0 3) (.reg0 2)
def e2 : Eff := { regs := [(4, .mul (.reg0 3) (top (w2 7)))], clob := [1] }

/-- Pass 3: `r4` added, stored, bit 255 cleared. -/
def w3 : Nat → SExpr := outW ldW (.reg0 4) (.reg0 2)
def e3 : Eff := { clob := [1], mem := none, reads := rds fun i => if i = 7 then clr (w3 7) else w3 i }

theorem e1_ok : effOk b1 e1 = true := by decide +kernel
theorem e2_ok : effOk b2 e2 = true := by decide +kernel
theorem e3_ok : effOk b3 e3 = true := by decide +kernel

/-! ## The value -/

theorem ldW_denote (t : State) (i : Nat) : (ldW i).denote t = read32 t.mem (slot (t.regs 0) i) := rfl

theorem rd_at {is : List Instr} {E : Eff} {t : State} {w : Nat → SExpr} (H : Holds is E t)
    (hE : E.reads = rds w) {i : Nat} (hi : i < 8) :
    read32 (execAll is t).mem (slot (t.regs 0) i) = (w i).denote t :=
  H.rd (wA i) (w i) (by rw [hE]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem toNat_clr (e : SExpr) (t : State) : ((clr e).denote t).toNat = (e.denote t).toNat % 2 ^ 31 :=
  Field25519Reduce.toNat_clear _

theorem toNat_top (a e : SExpr) (t : State) (ha : a.denote t = 19#32) :
    ((SExpr.mul a (top e)).denote t).toNat = 19 * ((e.denote t).toNat / 2 ^ 31) := by
  have := (e.denote t).isLt
  simp only [top, SExpr.denote, ha, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The body keeps `r0`. -/
theorem body_r0 (s : State) : (execAll body s).regs 0 = s.regs 0 := by
  rw [body, execAll_append, execAll_append]
  exact ((eff_run e3_ok _).reg 0 (by decide) (by decide)).trans
    (((eff_run e2_ok _).reg 0 (by decide) (by decide)).trans ((eff_run e1_ok s).reg 0 (by decide) (by decide)))

/-- **The body**: the value at `r0` becomes its canonical representative. -/
theorem body_val (s : State) :
    feVal (execAll body s).mem (s.regs 0) = feVal s.mem (s.regs 0) % pN ∧
      feVal (execAll body s).mem (s.regs 0) < pN := by
  have H1 := eff_run e1_ok s
  have u0 : (execAll b1 s).regs 0 = s.regs 0 := H1.reg 0 (by decide) (by decide)
  have u2 : (execAll b1 s).regs 2 = 0#32 := H1.reg 2 (by decide) (by decide)
  have u3 : (execAll b1 s).regs 3 = 19#32 := H1.reg 3 (by decide) (by decide)
  have r1 := fun i (hi : i < 8) => rd_at H1 rfl hi
  rw [body, execAll_append, execAll_append]
  generalize execAll b1 s = u at u0 u2 u3 r1 ⊢
  have H2 := eff_run e2_ok u
  have v0 : (execAll b2 u).regs 0 = s.regs 0 := (H2.reg 0 (by decide) (by decide)).trans u0
  have v2 : (execAll b2 u).regs 2 = 0#32 := (H2.reg 2 (by decide) (by decide)).trans u2
  have v4 := H2.reg 4 (by decide) (by decide)
  have vm : (execAll b2 u).mem = u.mem := H2.mem _ rfl
  generalize execAll b2 u = v at v0 v2 v4 vm ⊢
  have H3 := eff_run e3_ok v
  have k1 := chain_val x1 y1 (cw 0) s rfl 7
  have k2 := chain_val ldW (.reg0 3) (.reg0 2) u u2 7
  have k3 := chain_val ldW (.reg0 4) (.reg0 2) v v2 7
  have p2 : psum (fun i => ((ldW i).denote u).toNat) (7 + 1) = psum (fun i => ((w1 i).denote s).toNat) 8 :=
    psum_congr fun i hi => by rw [ldW_denote, u0, r1 i hi]
  have p3 : psum (fun i => ((ldW i).denote v).toNat) (7 + 1) = psum (fun i => ((w1 i).denote s).toNat) 8 :=
    psum_congr fun i hi => by rw [ldW_denote, vm, v0, r1 i hi]
  have p1 : psum (fun i => ((x1 i).denote s).toNat) (7 + 1) =
      psum (fun i => (read32 s.mem (slot (s.regs 0) i)).toNat) 7 +
        2 ^ 224 * ((read32 s.mem (slot (s.regs 0) 7)).toNat % 2 ^ 31) := by
    rw [show psum _ (7 + 1) = psum _ 7 + 2 ^ 224 * _ from rfl,
      psum_congr (g := fun i => (read32 s.mem (slot (s.regs 0) i)).toNat)
        fun i (hi : i < 7) => by simp only [x1, show i ≠ 7 by omega, ↓reduceIte, ldW_denote]]
    simp only [x1, ↓reduceIte, toNat_clr, ldW_denote]
  have hy3 : ((SExpr.reg0 4).denote v).toNat = 19 * (((w2 7).denote u).toNat / 2 ^ 31) := by
    rw [show (SExpr.reg0 4).denote v = v.regs 4 from rfl, v4]; exact toNat_top _ _ u u3
  rw [p1, show (y1.denote s).toNat = _ from toNat_top (cw 19) (ldW 7) s rfl, ldW_denote] at k1
  rw [p2, show (SExpr.reg0 3).denote u = u.regs 3 from rfl, u3] at k2
  rw [p3, hy3] at k3
  have e3 : psum (fun i => (read32 (execAll b3 v).mem (slot (s.regs 0) i)).toNat) 8 =
      psum (fun i => ((w3 i).denote v).toNat) 7 + 2 ^ 224 * (((w3 7).denote v).toNat % 2 ^ 31) := by
    rw [psum_congr (g := fun i => ((if i = 7 then clr (w3 7) else w3 i).denote v).toNat)
        fun i hi => by rw [← v0, rd_at (w := fun i => if i = 7 then clr (w3 7) else w3 i) H3 rfl hi],
      show psum _ 8 = psum _ 7 + 2 ^ 224 * _ from rfl,
      psum_congr (g := fun i => ((w3 i).denote v).toNat) fun i (hi : i < 7) => by
        simp only [show i ≠ 7 by omega, ↓reduceIte]]
    simp only [↓reduceIte, toNat_clr]
  rw [feVal_psum, feVal_psum, e3, show psum _ 8 = psum _ 7 + 2 ^ 224 * _ from rfl]
  simp only [Nat.reduceMul, Nat.reduceAdd] at k1 k2 k3
  exact Field25519Reduce.canon_passes _ _ _ _ _ _ _ _ _ _ _ _ (Field25519Facts.psum_lt (fun _ => BitVec.isLt _) 7) (BitVec.isLt _)
    k1 (Field25519Facts.psum_lt (fun _ => BitVec.isLt _) 8) k2 rfl
    (Field25519Facts.psum_lt (fun _ => BitVec.isLt _) 7) (BitVec.isLt _) k3 rfl
    (Field25519Facts.psum_lt (fun _ => BitVec.isLt _) 7) (BitVec.isLt _)

end M0Crypto.Release.Field25519Canon
