import M0Crypto.Release.Ed25519GeProg
import M0Crypto.Release.Ed25519FeEq

/-!
# `m0c_fe_add` and `m0c_fe_sub` as callees

Both are leaves `push {lr}; body; pop {pc}` with the bodies of `Field25519AddSub`. `add_te` and
`sub_te` are their call lemmas with the byte effect of their traces (`leaf_te`): they read the
inputs at `r1`, `r2` and write the 32 bytes at `r0`. `addAd` and `subAd` are the adapters of the
callees `faS .add`, `faS .sub` of the point fragments, with values `faV`.
-/

namespace M0Crypto.Release.Ed25519GeField

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint (Rgn Has)
open M0Crypto.Release.Ed25519Leaf
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519FeCanon (rg0 feVal_congr)
open M0Crypto.Release.Ed25519FeEq (ab)
open M0Crypto.Release.Ed25519FePow (ioMul)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519AddSub (feAddBody feSubBody)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts

/-- The aligned pointers. -/
def al3 : List (Sym.SExpr × Nat) := [(.reg0 0, 4), (.reg0 1, 4), (.reg0 2, 4)]

/-- A leaf at `o` with body `body` that computes `fn` of the elements at `r1`, `r2` into `r0`. -/
def fR (o : Nat) (body : List Instr) (fn : Int → Int → Int) : Routine := leafR o body rg0 ab
  (fun s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧ (s.regs 2).toNat % 4 = 0)
  (fun s m _ => ModP (feVal m (s.regs 0)) (fn (feVal s.mem (s.regs 1)) (feVal s.mem (s.regs 2))))

/-- Its effect: it reads the inputs and writes the output. -/
abbrev fE (o : Nat) : Word → (Nat → Word) → TrP := leafE o [0, 1, 2] ab rg0 (rg0 ++ ab)

theorem add_ok : leafOk feAddBody [0, 1, 2] al3 rg0 ab ab rg0 (rg0 ++ ab) = true := by decide +kernel
theorem sub_ok : leafOk feSubBody [0, 1, 2] al3 rg0 ab ab rg0 (rg0 ++ ab) = true := by decide +kernel

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **A field leaf's call lemma with its effect**, from the body's value lemma. -/
noncomputable def f_te {o : Nat} {body : List Instr} {fn : Int → Int → Int}
    (hok : leafOk body [0, 1, 2] al3 rg0 ab ab rg0 (rg0 ++ ab) = true) (hseq : seqAt B o (wrap body) = true)
    (ho : o % 2 = 0)
    (hv : ∀ t : State, (t.regs 0).toNat + 32 ≤ 2 ^ 32 →
      ModP (feVal (execAll body t).mem (t.regs 0)) (fn (feVal t.mem (t.regs 1)) (feVal t.mem (t.regs 2)))) :
    (fR o body fn).TE (leafPub [0, 1, 2]) (fE o) :=
  leaf_te hok hseq ho
    (fun s h r hr => by
      simp only [al3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Sym.SExpr.denote, h])
    fun s t _ hW tr hm => by
      have m1 := feVal_congr (a := s.regs 1) (m := s.mem) (m' := t.mem) fun y ⟨r, hr, hy⟩ =>
        hm y ⟨r, by simp only [List.mem_singleton] at hr; simp [sregions, ab, Sym.SExpr.denote, hr], hy⟩
      have m2 := feVal_congr (a := s.regs 2) (m := s.mem) (m' := t.mem) fun y ⟨r, hr, hy⟩ =>
        hm y ⟨r, by simp only [List.mem_singleton] at hr; simp [sregions, ab, Sym.SExpr.denote, hr], hy⟩
      have := hv t (by rw [tr 0 (by decide) (by decide)]; exact hW _ (List.mem_singleton_self _))
      rwa [tr 0 (by decide) (by decide), tr 1 (by decide) (by decide), tr 2 (by decide) (by decide), m1, m2] at this

end

/-- `m0c_fe_add`'s call lemma with its effect, in each build. -/
noncomputable def add_te (b : Build) : letI := b.codeBytes
    (fR Ed25519Compact.fe_add feAddBody (· + ·)).TE (leafPub [0, 1, 2]) (fE Ed25519Compact.fe_add) :=
  letI := b.codeBytes
  f_te add_ok (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)
    fun t h => (Field25519AddSub.feAdd_exec t h).1

/-- `m0c_fe_sub`'s call lemma with its effect, in each build. -/
noncomputable def sub_te (b : Build) : letI := b.codeBytes
    (fR Ed25519Compact.fe_sub feSubBody (· - ·)).TE (leafPub [0, 1, 2]) (fE Ed25519Compact.fe_sub) :=
  letI := b.codeBytes
  f_te sub_ok (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)
    fun t h => (Field25519AddSub.feSub_exec t h).1

/-! ## The adapters -/

/-- **A field leaf's adapter**: callee `s` with `m0c_fe_mul`'s interface, the leaf at its entry, and
value `faV a`. -/
noncomputable def fAd (b : Build) (Rs : Rels) (a : FA) {o : Nat} {body : List Instr} {fn : Int → Int → Int}
    (hs : faS a = calleeAt o ioMul [0, 1, 2])
    (te : letI := b.codeBytes; (fR o body fn).TE (leafPub [0, 1, 2]) (fE o))
    (hcode : rangesSub (fR o body fn).code (footprint o) = true) (hstk : 4 = stackOf o)
    (heff : effOk (faS a).io (rg0 ++ ab) ab rg0 = true) (hrg : regsOk (faS a) [0, 1, 2] = true)
    (hfn : ∀ x y, faV a [.f x, .f y] = .f (fn x y))
    (hcg : ∀ {x x' y y'}, ModP x x' → ModP y y' → ModP (fn x y) (fn x' y')) :
    AdE Rs (cb := b.codeBytes) (faS a) := by
  letI := b.codeBytes
  rw [hs] at heff hrg ⊢
  exact Ad.ofTSpec { fR o body fn with code := footprint o } rfl rfl hstk (te.code _ hcode)
    (fun _ _ _ h => leaf_eff h heff hrg (show 4 ≤ stackOf o from hstk ▸ Nat.le_refl 4))
    (fun vs => [faV a vs])
    (fun _ _ _ _ _ hg _ _ => ⟨hg.1 0 (by simp [calleeAt, ioMul]), hg.1 1 (by simp [calleeAt, ioMul]),
      hg.1 2 (by simp [calleeAt, ioMul])⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioMul, fR, leafR, sregions, rg0,
      Sym.SExpr.denote])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, calleeAt, ioMul, fR, leafR, sregions, ab,
      Sym.SExpr.denote])
    fun _ _ _ _ _ vs _ hi hp => by
      rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | ⟨_ | y | _ | _ | _ | _, _ | _⟩⟩ <;>
        simp only [InsRel, All2, calleeAt, ioMul, Rel, In.kd, and_false, false_and, and_true] at hi
      simp only [OutsRel, All2, calleeAt, ioMul, hfn, Rel, BitVec.add_zero, and_true] at hi ⊢
      exact ModP.trans hp (hcg hi.1 hi.2)

/-- **`m0c_fe_add`'s adapter** in build `b`. -/
noncomputable def addAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (faS .add) :=
  fAd b Rs .add rfl (add_te b) (by decide +kernel) (by decide) (by decide +kernel) (by decide) (fun _ _ => rfl)
    ModP.add

/-- **`m0c_fe_sub`'s adapter** in build `b`. -/
noncomputable def subAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (faS .sub) :=
  fAd b Rs .sub rfl (sub_te b) (by decide +kernel) (by decide) (by decide +kernel) (by decide) (fun _ _ => rfl)
    ModP.sub

end M0Crypto.Release.Ed25519GeField
