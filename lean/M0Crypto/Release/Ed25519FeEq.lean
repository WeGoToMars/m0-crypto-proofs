import M0Crypto.Release.Ed25519FeCanon
import M0Crypto.Release.Field25519AddSub

/-!
# `m0c_fe_eq`

`push {lr}`, `fe_sub_body` (the difference of `a` at `r1` and `b` at `r2` into `tmp` at `r0`,
`Field25519AddSub.feSub_exec`), `subs r0, #32`, `canon_body` on `tmp`
(`Ed25519FeCanon.body_val`), then the OR of its eight words into `r0` and `pop {pc}`: the status
in `r0` is `0` exactly when `a` and `b` are equal mod `p`.
-/

namespace M0Crypto.Release.Ed25519FeEq

open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.BlockEffect
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint (Rgn Has)
open M0Crypto.Release.StackEffect (InR)
open M0Crypto.Release.Field25519Facts (psum feVal_psum)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Release.Ed25519FeCanon (body body_val body_r0 cw ldW ldW_denote feVal_congr rg0)
open M0Crypto.Release.Ed25519Leaf
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Sym (SExpr)
open M0Crypto.Artifacts

def subR0 : List Instr := [.subImm8 0 32]
/-- `ldm r0!, {r1-r4}`, three `orrs`, `ldm r0!, {r2-r5}`, four `orrs`, `movs r0, r1`. -/
def tail : List Instr :=
  [.ldm 0 0x1e, .dp .orrs 1 2, .dp .orrs 1 3, .dp .orrs 1 4, .ldm 0 0x3c, .dp .orrs 1 2,
   .dp .orrs 1 3, .dp .orrs 1 4, .dp .orrs 1 5, .lslImm 0 1 0]
def eqBody : List Instr := Field25519AddSub.feSubBody ++ subR0 ++ body ++ tail

/-- `fe_sub_body` leaves `r0` 32 bytes on; `subs` takes it back. -/
def eS : Eff := { regs := [(0, .add (.reg0 0) (cw 32))], clob := [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12], mem := none }
def eR : Eff := { regs := [(0, subS (.reg0 0) 32)] }
/-- The OR of the words `0 … n` at `r0`. -/
def orW : Nat → SExpr
  | 0 => ldW 0
  | n + 1 => .or (orW n) (ldW (n + 1))
def eT : Eff := { regs := [(0, orW 7)], clob := [1, 2, 3, 4, 5] }

theorem eS_ok : effOk Field25519AddSub.feSubBody eS = true := by decide +kernel
theorem eR_ok : effOk subR0 eR = true := by decide +kernel
theorem eT_ok : effOk tail eT = true := by decide +kernel

theorem or_zero (x : State) : (orW 7).denote x = 0#32 ↔ feVal x.mem (x.regs 0) = 0 := by
  rw [feVal_psum]
  simp only [orW, SExpr.denote, BitVec.or_eq_zero_iff, ldW_denote]
  simp only [psum, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reduceAdd]
  omega

/-- **The body**: `r0` is `0` exactly when `a` and `b` are equal mod `p`. -/
theorem eq_val (t : State) (hf : (t.regs 0).toNat + 32 ≤ 2 ^ 32) :
    (execAll eqBody t).regs 0 = 0#32 ↔ feVal t.mem (t.regs 1) % pN = feVal t.mem (t.regs 2) % pN := by
  obtain ⟨hv, -, -⟩ := Field25519AddSub.feSub_exec t hf
  have S0 := (eff_run eS_ok t).reg 0 (by decide) (by decide)
  rw [eqBody, execAll_append, execAll_append, execAll_append]
  generalize execAll Field25519AddSub.feSubBody t = u at hv S0 ⊢
  have R := eff_run eR_ok u
  have w0 : (execAll subR0 u).regs 0 = t.regs 0 := by
    rw [R.reg 0 (by decide) (by decide)]
    exact (subS_denote _ _ u).trans (by rw [show (SExpr.reg0 0).denote u = u.regs 0 from rfl, S0]; exact BitVec.add_sub_cancel _ _)
  have wm : (execAll subR0 u).mem = u.mem := R.mem _ rfl
  generalize execAll subR0 u = w at w0 wm
  have C := (body_val w).1
  have C0 := body_r0 w
  generalize execAll body w = x at C C0
  rw [(eff_run eT_ok x).reg 0 (by decide) (by decide), show (eT.reg 0) = orW 7 from rfl, or_zero, C0, C, w0, wm]
  simp only [Field25519Congr.ModP, Field25519Congr.p] at hv
  simp only [pN]
  omega

/-! ## The routine -/

/-- The inputs `a`, `b`. -/
def ab : List (SExpr × Nat) := [(.reg0 1, 32), (.reg0 2, 32)]

/-- **`m0c_fe_eq`**: with word-aligned `tmp` at `r0`, `a` at `r1` and `b` at `r2`, the status in
`r0` is `0` exactly when `a` and `b` are equal mod `p`; it writes only `tmp`. -/
def eqR : Routine := leafR Ed25519Compact.fe_eq eqBody rg0 (ab ++ rg0)
  (fun s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧ (s.regs 2).toNat % 4 = 0)
  (fun s _ r => (r = 0#32 ↔ feVal s.mem (s.regs 1) % pN = feVal s.mem (s.regs 2) % pN))

/-- Its effect: it reads `a` and `b`, writes `tmp` and reads it back. -/
abbrev eqE : Word → (Nat → Word) → TrP := leafE Ed25519Compact.fe_eq [0, 1, 2] ab rg0 (rg0 ++ ab)

theorem eq_ok : leafOk eqBody [0, 1, 2] [(.reg0 0, 4), (.reg0 1, 4), (.reg0 2, 4)] rg0 (ab ++ rg0) ab rg0
    (rg0 ++ ab) = true := by
  decide +kernel

/-- `m0c_fe_eq`'s call lemma with its effect, in each build. -/
noncomputable def eq_te (b : Build) : letI := b.codeBytes; eqR.TE (leafPub [0, 1, 2]) eqE :=
  letI := b.codeBytes
  leaf_te eq_ok (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)
    (fun s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [SExpr.denote, h])
    fun s t _ hW tr hm => by
      have m1 := feVal_congr (a := s.regs 1) (m := s.mem) (m' := t.mem) fun y ⟨r, hr, hy⟩ =>
        hm y ⟨r, by simp only [List.mem_singleton] at hr; simp [sregions, ab, rg0, SExpr.denote, hr], hy⟩
      have m2 := feVal_congr (a := s.regs 2) (m := s.mem) (m' := t.mem) fun y ⟨r, hr, hy⟩ =>
        hm y ⟨r, by simp only [List.mem_singleton] at hr; simp [sregions, ab, rg0, SExpr.denote, hr], hy⟩
      have := eq_val t (by rw [tr 0 (by decide) (by decide)]; exact hW _ (List.mem_singleton_self _))
      rwa [tr 1 (by decide) (by decide), tr 2 (by decide) (by decide), m1, m2] at this

/-! ## As a callee -/

def ioEq : Iface :=
  { ins := [(1, 0, .view .fe), (2, 0, .view .fe)], outs := [], wr := [⟨0, 0, .k 32⟩],
    rd := [⟨1, 0, .k 32⟩, ⟨2, 0, .k 32⟩, ⟨0, 0, .k 32⟩], al := [0, 1, 2] }

def eqS : CalleeS := calleeAt Ed25519Compact.fe_eq ioEq [0, 1, 2]

theorem eq_pub : eqS.pub = leafPub [0, 1, 2] := rfl

/-- The leaf effect is the callee's. -/
theorem eq_eff {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) (p : Nat → Word) (tr : List Event)
    (h : eqE base p tr) : eqS.Eff p base tr :=
  leaf_eff h (by decide +kernel) (by decide) (by decide)

end M0Crypto.Release.Ed25519FeEq
