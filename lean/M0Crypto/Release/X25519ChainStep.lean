import M0Crypto.Release.X25519ChainLoop

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
One step of the inversion chain of `m0c_x25519`.

`stepChainAt o st` emits one step of `X25519Chain.invChain`: a multiplication (`mul_opW`), or
a squaring followed by nothing (`n = 1`), one more squaring (`n = 2`) or the counted loop
`sqrLoopAt` (`n > 2`). `stepChain_w` runs any such step: the destination slot ends congruent to
`CStep.rhs` of the chain values before the step (`cv`, the field value of the frame slot
`cslot x`), `Body` is kept, and of the frame only the destination slot and `LV_T` change
(`KeepDT`).

The values are stated for the destination slot only, so the lemma holds for every step,
including the last one, whose destination `dst` shares its frame slot with the input `z`.
-/

namespace M0Crypto.Release.X25519ChainStep
open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519ChainLoop
open M0Crypto.Release.X25519Chain (CSlot CStep)

/-- Value of chain slot `x` in memory `m`. -/
def cv (c : X25519.Ctx) (m : Mem) (x : CSlot) : Int := feVal m (slotAt c (cslot x))

/-- Destination of a step. -/
def _root_.M0Crypto.Release.X25519Chain.CStep.dst : CStep → CSlot
  | .sqr d .. => d
  | .mul d .. => d

/-- Exact value a step writes to its destination, from the values `f` before it. -/
def _root_.M0Crypto.Release.X25519Chain.CStep.rhs (f : CSlot → Int) : CStep → Int
  | .sqr _ a n => f a ^ (2 ^ n)
  | .mul _ a b => f a * f b

/-- Steps the machine proof covers: squaring counts from 1 to 256 (the counter is set
with an 8-bit immediate). -/
def _root_.M0Crypto.Release.X25519Chain.CStep.ok : CStep → Bool
  | .sqr _ _ n => decide (1 ≤ n ∧ n ≤ 256)
  | .mul .. => true

theorem cslot_ok (x : CSlot) : SlotOk (cslot x) := by cases x <;> decide

theorem mulOp_ok (d a b : CSlot) : Op.ok (mul (cslot d) (cslot a) (cslot b)) = true := by
  simp [Op.ok, mul, cslot_ok]

theorem sqrOp_ok (d a : CSlot) : Op.ok (sqr (cslot d) (cslot a)) = true := by
  simp [Op.ok, sqr, cslot_ok]

/-- `KeepDT` composes. -/
theorem KeepDT.trans {c : X25519.Ctx} {d : Nat} {s u t : State} (h1 : KeepDT c d s u)
    (h2 : KeepDT c d u t) : KeepDT c d s t := fun y a b e => by rw [h2 y a b e]; exact h1 y a b e

section
variable {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
include hv hcode hWr hPO

theorem stepChain_w {Q : State → Prop} {s : State} {o : Nat} (st : CStep) (hok : st.ok = true)
    (hseq : seqAt B o (stepChainAt o st) = true) (ho : o % 2 = 0)
    (hlo : lo ≤ o)
    (hend : o + seqSize (stepChainAt o st) ≤ hi)
    (hpc : s.pc = c.base + BitVec.ofNat 32 o) (hs : Body c m1 s)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (stepChainAt o st)) → Body c m1 t →
      ModP (cv c t.mem st.dst) (st.rhs (cv c s.mem)) → KeepDT c (cslot st.dst) s t →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  cases st with
  | mul d a b =>
    refine mul_opW hv hcode hWr hPO hseq ho hlo hend hpc hs (mulOp_ok d a b) (fun h => nomatch h) ?_
    intro t tpc e
    exact k t tpc e.body e.val fun y h1 h2 _ => e.keep y h1 h2
  | sqr d a n =>
    simp only [X25519Chain.CStep.ok, decide_eq_true_eq] at hok
    simp only [stepChainAt] at hseq hend k
    rw [seqAt_append, Bool.and_eq_true] at hseq
    rw [seqSize_append] at hend k
    have he := seqSize_even (opAt o (sqr (cslot d) (cslot a)))
    refine sqr_opW hv hcode hWr hPO hseq.1 ho hlo
      (by show o + seqSize (opAt o (sqr (cslot d) (cslot a))) ≤ _; omega) hpc hs (sqrOp_ok d a)
      (fun h => nomatch h) ?_
    intro u upc e
    change u.pc = c.base + BitVec.ofNat 32 (o + seqSize (opAt o (sqr (cslot d) (cslot a)))) at upc
    have v1 : ModP (cv c u.mem d) (cv c s.mem a * cv c s.mem a) := e.val
    have k1 : KeepDT c (cslot d) s u := fun y h1 h2 _ => e.keep y h1 h2
    generalize seqSize (opAt o (sqr (cslot d) (cslot a))) = n1 at he upc hseq hend k
    show ReachW _ _ _ u Q
    rcases (by omega : n = 1 ∨ n = 2 ∨ 2 < n) with h | h | h
    · subst h
      rw [if_neg (by decide), if_neg (by decide)] at k
      refine k u (by rw [upc]; rfl) e.body ?_ k1
      show ModP _ (cv c s.mem a ^ (2 ^ 1))
      exact v1.trans (ModP.of_eq (by rw [Nat.pow_one, X25519Congr.mul_self_eq_sq]))
    · subst h
      rw [if_pos rfl] at hseq hend k
      refine sqr_opW hv hcode hWr hPO hseq.2 (by omega) (by omega)
        (by show o + n1 + seqSize (opAt (o + n1) (sqr (cslot d) (cslot d))) ≤ _; omega) upc e.body
        (sqrOp_ok d d) (fun h => nomatch h) ?_
      intro t tpc e2
      have v2 : ModP (cv c t.mem d) (cv c u.mem d * cv c u.mem d) := e2.val
      refine k t (by rw [tpc, Nat.add_assoc]; rfl) e2.body ?_ (KeepDT.trans k1 fun y h1 h2 _ => e2.keep y h1 h2)
      show ModP _ (cv c s.mem a ^ (2 ^ 2))
      refine v2.trans ((ModP.mul v1 v1).trans (ModP.of_eq ?_))
      rw [← sq_pow _ 1, Nat.pow_one, X25519Congr.mul_self_eq_sq]
    · rw [if_neg (by omega), if_pos h] at hseq hend k
      refine sqrLoop_w hv hcode hWr hPO (cslot_ok d) (by omega) hok.2 hseq.2 (by omega) (by omega)
        (by omega) upc e.body fun t tpc tb tv tk => k t (by rw [tpc, Nat.add_assoc]) tb ?_ (KeepDT.trans k1 tk)
      show ModP _ (cv c s.mem a ^ (2 ^ n))
      refine tv.trans ((ModP.pow v1 _).trans (ModP.of_eq ?_))
      rw [sq_pow, Nat.sub_add_cancel (by omega)]
end

end M0Crypto.Release.X25519ChainStep
