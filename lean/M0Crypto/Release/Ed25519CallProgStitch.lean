import M0Crypto.Release.Ed25519CallProgAdapt

/-!
# Call programs: callees at stitched sites

A program's call names its callee's trace by the callee's public registers (`CalleeS.pubs`). A
callee whose trace also depends on memory (a decoder on its input bytes, a recoding on its
scalar, a double multiplication on its digits) is called at a site outside a program, between
straight lines that `prog_run` runs. `AdX` is its adapter: an `Ad` whose public values are the
registers of `CalleeS.pubs` followed by `xp`, values read from the entry state that are a
function `xpv` of the input values, with a premise
`vpre` on the input values for the call lemma and the result, and a premise `ppre` on the public
values for the effect. `AdE.toX` makes any adapter with an effect one, with no extra values and
no premises; `AdX.ofTE` builds one from a routine's call lemma with an effect.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb (Event condPassed execAll)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect

variable (Rs : Rels) {B : List (BitVec 8)} {BS : Nat} {cb : CodeBytes B BS}

/-- The public values of callee `s` with the extra values `xp` at its entry state. -/
def CalleeS.pubX (s : CalleeS) (xp : State → List Word) (st : State) : Nat → Word :=
  pubOf (s.pubs.map (PubW.get st) ++ xp st)

/-- **A callee adapter for a stitched site**: the routine, its call lemma with the trace `T` at
the public values `s.pubX xp`, the semantics of its interface under the premise `vpre` on the
input values, and the effect of `T` at public values with `ppre`. -/
structure AdX (s : CalleeS) where
  R : Routine
  entry : R.entry = s.entry
  code : R.code = s.code
  stack : R.stack = s.stack
  /-- The public values after the registers of `s.pubs`, read from the entry state. -/
  xp : State → List Word
  /-- The extra public values as a function of the input values. -/
  xpv : List V → List Word
  xp_of : ∀ c sp st vs, InsRel Rs c sp s.io st vs → xp st = xpv vs
  T : Word → (Nat → Word) → List Event
  hT : R.SpecT fun base st => Tr.is (T base (s.pubX xp st))
  /-- The caller's premise on the input values. -/
  vpre : List V → Prop
  sem : List V → List V
  pre : ∀ c sp base st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
    vpre vs → R.Pre base st
  wr : ∀ st, R.wr st = rgnsC st.regs s.io.wr
  rd : ∀ st, R.rd st = rgnsC st.regs s.io.rd
  post : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → vpre vs →
    R.Post st m r0 → OutsRel Rs c sp s.io st m (sem vs)
  /-- The premise on the public values under which the effect holds. -/
  ppre : (Nat → Word) → Prop
  ppre_of : ∀ c sp st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
    vpre vs → ppre (s.pubX xp st)
  ef : ∀ base p, ppre p → s.Eff p base (T base p)

/-- The callee `s` with the outputs `co` after its own. -/
def CalleeS.withCo (s : CalleeS) (co : List (Reg × Nat × Kd)) : CalleeS :=
  { s with io := { s.io with outs := s.io.outs ++ co } }

/-- **A status callee**: `r0` is zero exactly when the status `ok` of the input values holds,
and then the outputs `co` hold with values `csem`, and the trace has the effect of the callee with
`co` among its outputs. `okp` is the status as a function of the public values. -/
structure ZSt {s : CalleeS} (ad : AdX Rs (cb := cb) s) where
  ok : List V → Bool
  okr : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → ad.vpre vs →
    ad.R.Post st m r0 → (r0 = 0#32 ↔ ok vs = true)
  co : List (Reg × Nat × Kd)
  csem : List V → List V
  cpost : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → ad.vpre vs →
    ad.R.Post st m r0 → ok vs = true → OutsRel Rs c sp { s.io with outs := co } st m (csem vs)
  okp : (Nat → Word) → Bool
  okp_of : ∀ c sp st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
    ad.vpre vs → okp (s.pubX ad.xp st) = ok vs
  cef : ∀ base p, ad.ppre p → okp p = true → (s.withCo co).Eff p base (ad.T base p)

/-- **A block with a test**: after the block, the exit condition `cc` holds exactly when the
status `ok` of the input values fails, and with the status and the premise `vpre` on the input
values the outputs `co` hold with values `csem` at the block's entry registers. -/
structure ZB {b : BlockS} (bd : Bd Rs b) where
  cc : BitVec 4
  ok : List V → Bool
  okf : ∀ c sp (t : State) vs, PreG b.io t.regs → NoWrap b.io t.regs → PreV b.io c sp t.regs →
    InsRel Rs c sp b.io t vs → condPassed cc (execAll b.g t) = !ok vs
  co : List (Reg × Nat × Kd)
  csem : List V → List V
  vpre : List V → Prop
  cpost : ∀ c sp (t : State) vs, PreG b.io t.regs → NoWrap b.io t.regs → PreV b.io c sp t.regs →
    InsRel Rs c sp b.io t vs → vpre vs → ok vs = true → OutsRel Rs c sp { b.io with outs := co } t (execAll b.g t).mem (csem vs)

variable {Rs}

theorem CalleeS.pubX_nil (s : CalleeS) (st : State) : s.pubX (fun _ => []) st = s.pub 0 st := by
  simp [CalleeS.pubX, CalleeS.pub]

/-- **An adapter with an effect as a stitched-site adapter**: no extra values, no premises. -/
noncomputable def AdE.toX {s : CalleeS} (a : AdE Rs (cb := cb) s) : AdX Rs (cb := cb) s where
  R := a.ad.R
  entry := a.ad.entry
  code := a.ad.code
  stack := a.ad.stack
  xp := fun _ => []
  xpv := fun _ => []
  xp_of := fun _ _ _ _ _ => rfl
  T := a.ad.T
  hT := fun base st e => by simpa [CalleeS.pubX] using a.ad.hT base st e
  vpre := fun _ => True
  sem := a.ad.sem
  pre := fun c sp base st vs h1 h2 h3 _ => a.ad.pre c sp base st vs h1 h2 h3
  wr := a.ad.wr
  rd := a.ad.rd
  post := fun c sp st m r0 vs h1 h2 _ h4 => a.ad.post c sp st m r0 vs h1 h2 h4
  ppre := fun _ => True
  ppre_of := fun _ _ _ _ _ _ _ _ => trivial
  ef := fun base p _ => a.ef base p

/-- **A stitched-site adapter from a call lemma with an effect** at the public values
`s.pubX xp`: the trace, its spec and its effect come from `te`; `hE` gives the callee's effect
from `E` at public values with `ppre`. -/
noncomputable def AdX.ofTE {s : CalleeS} (R : Routine) (he : R.entry = s.entry) (hc : R.code = s.code)
    (hs : R.stack = s.stack) (xp : State → List Word) (xpv : List V → List Word)
    (xp_of : ∀ c sp st vs, InsRel Rs c sp s.io st vs → xp st = xpv vs) {E : Word → (Nat → Word) → TrP}
    (te : R.TE (fun _ st => s.pubX xp st) E) (ppre : (Nat → Word) → Prop)
    (hE : ∀ base p tr, ppre p → E base p tr → s.Eff p base tr) (vpre : List V → Prop) (sem : List V → List V)
    (pre : ∀ c sp base st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
      vpre vs → R.Pre base st)
    (wr : ∀ st, R.wr st = rgnsC st.regs s.io.wr) (rd : ∀ st, R.rd st = rgnsC st.regs s.io.rd)
    (post : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → vpre vs →
      R.Post st m r0 → OutsRel Rs c sp s.io st m (sem vs))
    (ppre_of : ∀ c sp st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
      vpre vs → ppre (s.pubX xp st)) : AdX Rs (cb := cb) s :=
  ⟨R, he, hc, hs, xp, xpv, xp_of, te.T, te.spec, vpre, sem, pre, wr, rd, post, ppre, ppre_of,
    fun base p hp => hE base p _ hp (te.eff base p)⟩

end M0Crypto.Release.Ed25519CallProg
