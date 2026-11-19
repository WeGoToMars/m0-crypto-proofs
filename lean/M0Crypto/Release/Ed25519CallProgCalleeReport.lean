import M0Crypto.Release.Ed25519CallProgCallee
import M0Crypto.Release.Ed25519CallProgReport
import M0Crypto.Release.Ed25519Leaf

/-!
# Callee and leaf checks: first-failure reporters

`CalleeP.okErr` names the first condition of `CalleeP.ok` that fails, with a buffer's or an
output's register and a construct's code offset (`CalleeP.okErr_eq_none`). `CalleeP.codeErr`
names the first failure of `CalleeP.codeOk` in a build: an instruction the bytes do not hold, a
construct's code check, or a range. `effC` and `leafC` are the conditions of `effOk` and
`Ed25519Leaf.leafOk`, so that `firstFail` names a leaf adapter's failing condition.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Thumb
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Sym (SExpr alignChkE rgnChk)
open M0Crypto.Armv6M (Reg)
open M0Crypto.Release.StackEffect (blkChk)

/-- `effOk`'s conditions. -/
def effC (io : Iface) (fp ini wo : List (SExpr × Nat)) : List (String × Bool) :=
  [("footprint in the interface regions", subR fp ((io.rd ++ io.wr).filterMap SRgn.e)),
   ("first reads in the inputs", covR ini (io.ins.filterMap inE)),
   ("outputs symbolic", io.outs.all fun x => (outE x).isSome),
   ("outputs written", subR (io.outs.filterMap outE) wo)]

theorem effOk_eq (io : Iface) (fp ini wo : List (SExpr × Nat)) : effOk io fp ini wo = (effC io fp ini wo).all (·.2) := by
  simp only [effOk, effC, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

/-- `leafOk`'s conditions. -/
def leafC (body : List Instr) (L : List Reg) (al W R ini wo fp : List (SExpr × Nat)) : List (String × Bool) :=
  [("falls through", body.all Instr.falls), ("keeps sp", keepsSp body), ("even size", seqSize body % 2 == 0),
   ("registers below 13", L.all (·.val < 13)), ("regions on low registers", (al ++ W ++ R).all (·.1.regsIn Ed25519Leaf.lowR)),
   ("aligned", alignChkE al body), ("writes in W", rgnChk .write W body),
   ("reads in R", rgnChk .read R body), ("trace", traceOk body L),
   ("accesses in footprints", blkChk ini wo fp body), ("written in footprint", wo.all fp.contains)]

theorem leafOk_eq (body : List Instr) (L : List Reg) (al W R ini wo fp : List (SExpr × Nat)) :
    Ed25519Leaf.leafOk body L al W R ini wo fp = (leafC body L al W R ini wo fp).all (·.2) := by
  simp only [Ed25519Leaf.leafOk, leafC, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

namespace CalleeP
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (q : CalleeP A Bk)

/-- `xOk`'s conditions. -/
def xC (x : Reg × XInfo) : List (String × Bool) :=
  [("below r13", x.1.val < 13), ("public", PubW.r x.1 ∈ q.s.pubs), ("written or read", x.2.w || x.2.r),
   ("aligned", !x.2.al4 || x.1 ∈ q.s.io.al),
   ("constant length in the interface", match x.2.len with
    | .k L => decide (0 < L) && decide (L < 2 ^ 32) && (!x.2.w || SRgn.mk x.1 0 (.k L) ∈ q.s.io.wr) &&
        (!x.2.r || SRgn.mk x.1 0 (.k L) ∈ q.s.io.rd)
    | .p _ => false)]

theorem xOk_eq (x : Reg × XInfo) : q.xOk x = (q.xC x).all (·.2) := by
  simp only [xOk, xC, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]
  rfl

/-- `ok`'s conditions before the program's. -/
def frameC : List (String × Bool) :=
  [("bounded buffers", q.sc.all q.scOk), ("frame a word multiple", q.top % 4 == 0), ("frame below 1020", decide (q.top / 4 < 255)),
   ("frame in the stack", decide (4 + q.top ≤ q.s.stack)), ("entry even", q.s.entry % 2 == 0),
   ("sp public", PubW.r 13 ∈ q.s.pubs)] ++
  each (fun x => "buffer " ++ regN x.1) q.xr q.xC ++
  each regN q.pr (fun r => [("public parameter", r.val < 13 && PubW.r r ∈ q.s.pubs)]) ++
  effC q.s.io q.fpE q.iniE q.woE ++ [("outputs in the footprint", subR q.woE q.fpE)]

/-- **The first failure of `ok`**: a named condition, a construct of the program by code offset
from the body, or an output by register. -/
def okErr : Option String :=
  (firstFail (q.frameC)) <|>
  match q.P.ty cE bE q.geo q.st0 with
  | none => (q.P.tyErr cE bE q.geo q.st0 q.body).map fun o => s!"typing at {o}"
  | some st' => ((q.P.eokErr cE bE q.geo q.st0 q.body).map fun (o, c) => s!"{c} at {o}") <|>
      (if st'.ex = none then none else some "an exit at the end") <|>
      firstFail (each (fun x => "output " ++ regN x.1) q.s.io.outs fun x => [("live, of its kind", q.outOk st'.Γ x)])

theorem frameC_all : q.frameC.all (·.2) =
    (q.sc.all q.scOk && q.top % 4 == 0 && decide (q.top / 4 < 255) && decide (4 + q.top ≤ q.s.stack) && q.s.entry % 2 == 0 &&
      PubW.r 13 ∈ q.s.pubs && q.xr.all q.xOk && q.pr.all (fun r => r.val < 13 && PubW.r r ∈ q.s.pubs) &&
      effOk q.s.io q.fpE q.iniE q.woE && subR q.woE q.fpE) := by
  simp only [frameC, List.all_append, all_each, List.all_cons, List.all_nil, Bool.and_true, ← xOk_eq, effOk_eq,
    Bool.and_assoc]

theorem okErr_eq_none : q.okErr cE bE = none ↔ q.ok cE bE = true := by
  have ht := Prog.tyErr_eq_none cE bE q.geo q.P q.st0 q.body
  have he := Prog.eokErr_eq_none cE bE q.geo q.P q.st0 q.body
  unfold okErr ok
  rw [← frameC_all]
  cases hf : firstFail q.frameC with
  | some c =>
    have : q.frameC.all (·.2) = false := by
      cases h : q.frameC.all (·.2)
      · rfl
      · rw [← firstFail_eq_none, hf] at h; cases h
    simp [this]
  | none =>
    rw [(firstFail_eq_none _).1 hf]
    cases hty : q.P.ty cE bE q.geo q.st0 with
    | none => rw [hty] at ht; cases h : q.P.tyErr cE bE q.geo q.st0 q.body <;> simp_all
    | some st' =>
      cases h : q.P.eokErr cE bE q.geo q.st0 q.body <;> cases hx : st'.ex <;>
        simp_all [firstFail_eq_none, all_each]

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **The first failure of `codeOk`** in a build with the data ranges `D`. -/
def codeErr (D : List (Nat × Nat)) : Option String :=
  ((seqErr (B.drop q.s.entry) q.s.entry (.push 0 true :: q.ks.map fun k => .subSp (BitVec.ofNat 7 k))).map
      fun (o, _, w) => s!"entry: no {repr w} at {o}") <|>
  ((seqErr (B.drop (q.epi cE bE)) (q.epi cE bE) (q.ks.map (fun k => .addSp (BitVec.ofNat 7 k)) ++ [.pop 0 true])).map
      fun (o, _, w) => s!"exit: no {repr w} at {o}") <|>
  ((q.P.bokErr cE bE q.geo [] q.body).map fun o => s!"code check at {o}") <|>
  ((piecesErr (B.drop q.body) q.body (Prog.emit cE bE [] q.body q.P)).map
      fun (o, f, w) => s!"body: {repr f} at {o}, want {repr w}") <|>
  firstFail ([("frame code in the footprint",
      rangesSub [(q.s.entry, q.s.entry + 2 + q.pro), (q.epi cE bE, q.epi cE bE + 2 + q.pro)] q.s.code),
    ("exit in the unit", decide (q.epi cE bE + 2 + q.pro ≤ BS)), ("exit even", q.epi cE bE % 2 == 0)] ++
    each (fun x => s!"code buffer {x.1}") q.cb fun x =>
      [("aligned, nonempty, in the unit", x.1 % 4 == 0 && decide (0 < x.2) && decide (x.1 + x.2 ≤ BS))] ++
    each (fun x => s!"island {x.1}..{x.2}") (pieceDat q.body (Prog.emit cE bE [] q.body q.P)) fun x =>
      [("a data range of the build", decide (x ∈ D))])

end CalleeP

end M0Crypto.Release.Ed25519CallProg
