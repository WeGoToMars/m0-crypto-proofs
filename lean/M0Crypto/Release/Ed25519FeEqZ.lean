import M0Crypto.Release.Ed25519DecompressVal
import M0Crypto.Release.Ed25519WordAd
import M0Crypto.Release.Ed25519CallProgStitchGood

/-!
# `m0c_fe_eq` at a stitched site

`eqAd b`, `eqZ b`: `m0c_fe_eq`'s adapter and status in build `b`. Its status is the extra
public value (`eqSt`), so that the status is a function of the public values; its trace is the
leaf's, a function of `r0`, `r1`, `r2` and `sp`. It has no outputs.
-/

namespace M0Crypto.Release.Ed25519FeEq

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519GeProg (fI)
open M0Crypto.Artifacts.Ed25519Compact (fe_eq)

variable (Rs : Rels)

/-- The status: `0` exactly when the values at `r1` and `r2` agree mod `p`. -/
def eqSt (st : State) : Word :=
  if feVal st.mem (st.regs 1) % pN = feVal st.mem (st.regs 2) % pN then 0 else 1

def xpE (st : State) : List Word := [eqSt st]

def okE : List V → Bool
  | [.f x, .f y] => decide (fI x = fI y)
  | _ => false

def xpvE (vs : List V) : List Word := [if okE vs = true then 0 else 1]

/-- The status is the public value after the registers. -/
theorem eq_pubX (st : State) : eqS.pubX xpE st 4 = eqSt st := by
  simp only [CalleeS.pubX, pubOf, xpE, eqS, calleeAt, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.getD_cons_succ, List.getD_cons_zero]

/-- `fe_eq`'s public values from the callee's: the four registers. -/
def gE (p : Nat → Word) : Nat → Word := pubOf [p 0, p 1, p 2, p 3]

theorem eq_in {c : Ctx} {sp : Word} {st : State} {vs : List V} (h : InsRel Rs c sp ioEq st vs) :
    ∃ x y, vs = [.f x, .f y] ∧ ModP (feVal st.mem (st.regs 1)) x ∧ ModP (feVal st.mem (st.regs 2)) y := by
  rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | ⟨_ | y | _ | _ | _ | _, _ | _⟩⟩ <;>
    simp only [InsRel, All2, ioEq, Rel, In.kd, and_false, false_and, and_true] at h
  simp only [BitVec.add_zero] at h
  exact ⟨x, y, rfl, h.1, h.2⟩

theorem st_iff (vs : List V) {c : Ctx} {sp : Word} {st : State} (h : InsRel Rs c sp ioEq st vs) :
    (feVal st.mem (st.regs 1) % pN = feVal st.mem (st.regs 2) % pN) ↔ okE vs = true := by
  obtain ⟨x, y, rfl, ha, hb⟩ := eq_in Rs h
  rw [Ed25519DecompressVal.eq_iff ha hb]
  simp [okE]

/-- **`m0c_fe_eq`'s adapter at a stitched site** in build `b`: no values; its trace a function
of `r0`, `r1`, `r2` and `sp`, its status the extra public value. -/
noncomputable def eqAd (b : Build) : AdX Rs (cb := b.codeBytes) eqS :=
  letI := b.codeBytes
  AdX.ofTE { eqR with code := footprint fe_eq } rfl rfl (by decide +kernel) xpE xpvE
    (fun _ _ st vs hi => by
      simp only [xpE, xpvE, eqSt, st_iff Rs vs hi])
    (((eq_te b).code (footprint fe_eq) (by decide +kernel)).repub _ gE fun _ _ => rfl) (fun _ => True)
    (fun base p tr _ h => eq_eff base p tr h) (fun _ => True) (fun _ => [])
    (fun _ _ _ _ _ hg _ _ _ => ⟨hg.1 0 (by simp [eqS, calleeAt, ioEq]),
      hg.1 1 (by simp [eqS, calleeAt, ioEq]), hg.1 2 (by simp [eqS, calleeAt, ioEq])⟩)
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, eqS, calleeAt, ioEq, eqR, Ed25519Leaf.leafR, sregions,
      Ed25519FeCanon.rg0, Sym.SExpr.denote])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, eqS, calleeAt, ioEq, eqR, Ed25519Leaf.leafR, sregions,
      Ed25519FeEq.ab, Ed25519FeCanon.rg0, Sym.SExpr.denote])
    (fun _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, eqS, calleeAt, ioEq])
    fun _ _ _ _ _ _ _ _ => trivial

/-- **`fe_eq`'s status**: `r0` is `0` exactly when the field values agree; no outputs. -/
noncomputable def eqZ (b : Build) : ZSt Rs (cb := b.codeBytes) (eqAd Rs b) :=
  letI := b.codeBytes
  { ok := okE
    okr := fun _ _ _ _ _ vs _ hin _ hp => hp.trans (st_iff Rs vs hin)
    co := []
    csem := fun _ => []
    cpost := fun _ _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel, All2]
    okp := fun p => p 4 == 0
    okp_of := fun _ _ st vs _ _ hin _ => by
      show (eqS.pubX xpE st 4 == 0) = okE vs
      rw [eq_pubX]
      unfold eqSt
      by_cases h : feVal st.mem (st.regs 1) % pN = feVal st.mem (st.regs 2) % pN
      · simp only [h, ↓reduceIte]; rw [(st_iff Rs vs hin).mp h]; rfl
      · simp only [h, ↓reduceIte]
        cases e : okE vs
        · rfl
        · exact absurd ((st_iff Rs vs hin).mpr e) h
    cef := fun base p hp _ => CalleeS.eff_withCo_nil ((eqAd Rs b).ef base p hp) }

end M0Crypto.Release.Ed25519FeEq
