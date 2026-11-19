import M0Crypto.Release.Ed25519DecompressRun
import M0Crypto.Release.Ed25519CallProgStitchGood
import M0Crypto.Release.Ed25519DecompressW

/-!
# `m0c_ge_decompress`: the body's effect

`body_gp`: at any bits of the tests, the body's trace `bodyTr` keeps the call program's invariant
`BI` from the entry state to the success end at `t9`, and, when the status of the bits fails, to
the fail ends at the states `failS`. The straight lines by `prog_good`, the load and its test by
`zblk_gp`, the `fe_eq` sites by `xcall_gp` (no outputs) and `tst_gp`, the tests' glue by
`tstF_gp` and `tstS_gp`. `bodyTr_uniq` and `bodyTr_ex`: the trace is unique and exists.
-/

namespace M0Crypto.Release.Ed25519DecompressGood

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint (Has)
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DecompressProg
open M0Crypto.Release.Ed25519DecompressStitch
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519FeEq (eqS eqAd)

/-! ## Decided facts -/

/-- The states at the fail ends: the load's test, the second `fe_eq`'s test, the sign test. -/
def failS : List St := [{ t1 with σ := σsp, ρ := [] }, withViews t5 [], t7]

/-- **The tests' glue and the status moves** read frame views only. -/
theorem glue_facts :
    blkChk (frIni t7.Γ) [] [frR dcGeo] zG = true ∧ blkChk (frIni t7.Γ) [] [frR dcGeo] sG = true ∧
    blkChk (frIni tT.Γ) [] [frR dcGeo] pG = true ∧ blkChk (pwIni t9.Γ) [] [frR dcGeo] [.movImm 0 0] = true ∧
    ∀ S ∈ failS, blkChk (pwIni S.Γ) [] [frR dcGeo] [.movImm 0 1] = true := by
  decide +kernel

/-! ## The body's invariant along its trace -/

section gp
variable {Rs : Rels} {b : Build} {c : Ctx} {sp0 : Word} {n : Nat} {X0 : Word → Prop}
  (fm : Frm c dcGeo sp0 n X0)
  (hcode : ∀ y, Has [@codeR b.bytes b.size b.codeBytes c.base] y → BelowEntry sp0 n y →
    AtOrAboveSp sp0 (dcGeo.fsp c) y ∧ X0 y)
  {J : Ef → Prop}

/-- The left state of a join weakens to it. -/
theorem bi_joinL {s₀ s₁ : St} {q : Ef} (h : BI c dcGeo sp0 n X0 s₀ q) : BI c dcGeo sp0 n X0 (joinSt s₀ s₁) q :=
  BI.sub (fun _ hq => (List.mem_filter.mp hq).1) h

/-- The right state of a join weakens to it. -/
theorem bi_joinR {s₀ s₁ : St} {q : Ef} (h : BI c dcGeo sp0 n X0 s₁ q) : BI c dcGeo sp0 n X0 (joinSt s₀ s₁) q :=
  BI.sub (fun _ hq => by simpa using (List.mem_filter.mp hq).2) h

include fm

/-- The success end: `movs r0, #0; b done`. -/
theorem ok_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) : GP sp0 n (BI c dcGeo sp0 n X0 t9) (tOk c) J :=
  GP.cat (pubBlk_gp fm glue_facts.2.2.2.1 _) (GP.cat (quiet_gp rfl rfl rfl) (GP.nil hJ))

/-- A fail end: `movs r0, #1`. -/
theorem fail_gp {S : St} (hS : S ∈ failS) (hJ : ∀ q, BI c dcGeo sp0 n X0 S q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 S) (tFail c) J :=
  GP.cat (pubBlk_gp fm (glue_facts.2.2.2.2 S hS) _) (GP.nil hJ)

include hcode

/-- **A straight line** by its decided type and effect. -/
theorem seg_gp {P : Prog DA DB} {o : Nat} {S S' : St} (hl : @lnChk b.bytes b.size b.codeBytes P o)
    (hty : P.ty daS dbS dcGeo S = some S') (hx : S.ex = none) (hx' : S'.ex = none)
    (he : P.eok daS dbS dcGeo S = true) {Ψ : TrP} (hΨ : GP sp0 n (BI c dcGeo sp0 n X0 S') Ψ J) :
    GP sp0 n (BI c dcGeo sp0 n X0 S) (Prog.tr daS dbS dcGeo (dT Rs b) c P o S Ψ [] []) J :=
  letI := b.codeBytes
  prog_good fm (fun a base p => (daAd Rs b a).ef base p) hcode P o S S' Ψ J [] [] hty hx he hl.1 (fun _ => hΨ)
    fun _ h => by rw [hx'] at h; cases h

/-- **The output** from `same`. -/
theorem s6_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 tK) (tS6 Rs b c) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h9, h9x, e9⟩ := sites_ty
  exact seg_gp fm hcode (lines_code b).2.2.2.2.2.2 h9 starts_ex.2.2.2.2.2 h9x e9 (ok_gp fm hJ)

/-- **The parity test** at `okz`: the negation `seg5`, then the output. -/
theorem p_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) (ng : Bool) :
    GP sp0 n (BI c dcGeo sp0 n X0 tT) (tP Rs b c ng) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h8, h8x, e8, -⟩ := sites_ty
  exact tstS_gp fm glue_facts.2.2.1
    (fun _ => seg_gp fm hcode (lines_code b).2.2.2.2.2.1 h8 starts_ex.2.2.2.2.1 h8x e8
      (GP.pre (fun _ h => bi_joinR h) (s6_gp fm hcode hJ)))
    fun _ => GP.pre (fun _ h => bi_joinL h) (s6_gp fm hcode hJ)

/-- **From `ok1`**: `x` canonical, the zero test, the sign test (exit to `fail`), the parity. -/
theorem s4_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) {z s ng : Bool}
    (hF : z = true → s = false → ∀ q, BI c dcGeo sp0 n X0 t7 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 tJ) (tS4 Rs b c z s ng) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h7, h7x, e7, -⟩ := sites_ty
  obtain ⟨g1, g2, -⟩ := glue_facts
  refine seg_gp fm hcode (lines_code b).2.2.2.2.1 h7 starts_ex.2.2.2.1 h7x e7 ?_
  refine tstF_gp fm g1 (fun hz => tstF_gp fm g2 (fun _ => GP.pre (fun _ h => BI.sub (fun _ h => h) h) (p_gp fm hcode hJ ng))
    fun hs => fail_gp fm (by simp [failS]) (hF hz hs)) fun _ => GP.pre (fun _ h => BI.sub (fun _ h => h) h) (p_gp fm hcode hJ ng)

/-- The second candidate's `F4`, into `ok1`. -/
theorem s3_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) {z s ng : Bool}
    (hF : z = true → s = false → ∀ q, BI c dcGeo sp0 n X0 t7 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 (addViews t5 [])) (tS3 Rs b c z s ng) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h6, h6x, e6, -⟩ := sites_ty
  exact seg_gp fm hcode (lines_code b).2.2.2.1 h6 starts_ex.2.2.1 h6x e6
    (GP.pre (fun _ h => bi_joinR h) (s4_gp fm hcode hJ hF))

/-- **The second `fe_eq`** and its test: on equal `F4`, else to `fail`. -/
theorem e2_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) {k2 z s ng : Bool}
    (hF5 : k2 = false → ∀ q, BI c dcGeo sp0 n X0 (withViews t5 []) q → J q)
    (hF7 : k2 = true → z = true → s = false → ∀ q, BI c dcGeo sp0 n X0 t7 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 t4) (tE2 Rs b c k2 z s ng) J := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h5, e5, -⟩ := sites_ty
  exact xcall_gp fm hcode h5 e5 rfl rfl (CalleeS.eff_withCo_nil ((eqAd Rs b).ef c.base _ trivial))
    (tst_gp fm rfl (fun hk => GP.pre (fun _ h => BI.addViews h) (s3_gp fm hcode hJ (hF7 hk)))
      fun hk => fail_gp fm (by simp [failS]) (hF5 hk))

/-- The second candidate's `F3`. -/
theorem q2_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) {k2 z s ng : Bool}
    (hF5 : k2 = false → ∀ q, BI c dcGeo sp0 n X0 (withViews t5 []) q → J q)
    (hF7 : k2 = true → z = true → s = false → ∀ q, BI c dcGeo sp0 n X0 t7 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 (addViews t3 [])) (tQ2 Rs b c k2 z s ng) J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h4, h4x, e4, -⟩ := sites_ty
  exact seg_gp fm hcode (lines_code b).2.2.1 h4 starts_ex.2.1 h4x e4 (e2_gp fm hcode hJ hF5 hF7)

/-- **The first `fe_eq`** and its test: on equal to `ok1`, else the second candidate. -/
theorem e1_gp (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q) {k1 k2 z s ng : Bool}
    (hF5 : k1 = false → k2 = false → ∀ q, BI c dcGeo sp0 n X0 (withViews t5 []) q → J q)
    (hF7 : (k1 || k2) = true → z = true → s = false → ∀ q, BI c dcGeo sp0 n X0 t7 q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 t2) (tE1 Rs b c k1 k2 z s ng) J := by
  letI := b.codeBytes
  obtain ⟨-, -, -, -, -, -, -, -, -, h3, e3, -⟩ := sites_ty
  refine xcall_gp fm hcode h3 e3 rfl rfl (CalleeS.eff_withCo_nil ((eqAd Rs b).ef c.base _ trivial))
    (tst_gp fm rfl (fun hk => ?_) fun hk => ?_)
  · have h1 : k1 = false := by simpa using hk
    exact GP.pre (fun _ h => BI.addViews h)
      (q2_gp fm hcode hJ (hF5 h1) fun (h2 : k2 = true) => hF7 (by simp [h2]))
  · have h1 : k1 = true := by simpa using hk
    exact GP.pre (fun _ h => bi_joinL (BI.sub (fun _ h => h) h)) (s4_gp fm hcode hJ (hF7 (by simp [h1])))

/-- **The body's invariant along its trace** at any bits of the tests: to `t9` at the success
end, and to the fail ends when the status of the bits fails. -/
theorem body_gp (k0 k1 k2 z s ng : Bool) (hJ : ∀ q, BI c dcGeo sp0 n X0 t9 q → J q)
    (hF : (k0 && (k1 || k2) && (!z || s)) = false → ∀ S ∈ failS, ∀ q, BI c dcGeo sp0 n X0 S q → J q) :
    GP sp0 n (BI c dcGeo sp0 n X0 stE) (bodyTr Rs b c k0 k1 k2 z s ng) J := by
  obtain ⟨h0, h0x, e0, h1, e1, hcv, h2, h2x, e2, -⟩ := sites_ty
  refine seg_gp fm hcode (lines_code b).1 h0 rfl h0x e0 ?_
  refine zblk_gp fm h1 e1 hcv (fun hk0 => ?_) fun hk0 => fail_gp fm (by simp [failS]) (hF (by simp [hk0]) _ (by simp [failS]))
  refine GP.pre (fun _ h => h) (seg_gp fm hcode (lines_code b).2.1 h2 starts_ex.1 h2x e2 (e1_gp fm hcode hJ
    (fun h1 h2 => hF (by simp [h1, h2]) _ (by simp [failS])) fun h12 hz hs => hF (by simp [hk0, h12, hz, hs]) _ (by simp [failS])))

end gp

/-! ## One trace -/

section tq
variable {Rs : Rels} {b : Build} {c : Ctx} (Q : TrP → Prop) (hi : ∀ l, Q (Tr.is l))
  (hc : ∀ {Φ Ψ : TrP}, Q Φ → Q Ψ → Q (Tr.cat Φ Ψ)) (hd : ∀ {b : Bool} {Φ Ψ : TrP}, Q Φ → Q Ψ → Q (Tr.cond b Φ Ψ))
  (hp : ∀ {P : Prog DA DB} {o : Nat} {S : St} {Ψ : TrP}, Q Ψ → Q (Prog.tr daS dbS dcGeo (dT Rs b) c P o S Ψ [] []))
  (hl : ∀ {Ψ : TrP}, Q Ψ → Q ((bL : Op DA DX).tr daS dxS dcGeo (fun _ _ _ => []) c oL t0 Ψ))
include hi hc hd hp hl

/-- **The body's trace** keeps a property of traces closed under its constructors. -/
theorem body_q (k0 k1 k2 z s ng : Bool) : Q (bodyTr Rs b c k0 k1 k2 z s ng) := by
  have ts : ∀ {o g cc T d Ψk Ψx}, Q Ψk → Q Ψx → Q (tstTr dcGeo c o g cc T d Ψk Ψx) :=
    fun hk hx => hc (hi _) (hc (hi _) (hd hk (hc (hi _) hx)))
  have tsS : ∀ {o g cc T d Ψk Ψx}, Q Ψk → Q Ψx → Q (tstSTr dcGeo c o g cc T d Ψk Ψx) :=
    fun hk hx => hc (hi _) (hc (hi _) (hd hx hk))
  have xc : ∀ {o as e Tw Ψ}, Q Ψ → Q (xcallTr dcGeo c o as e Tw Ψ) := fun h => hc (hi _) (hc (hi _) (hc (hi _) h))
  have fl : Q (tFail c) := hc (hi _) (hi _)
  have s6 : Q (tS6 Rs b c) := hp (hc (hi _) (hc (hi _) (hi _)))
  have p : Q (tP Rs b c ng) := tsS (hp s6) s6
  have s4 : Q (tS4 Rs b c z s ng) := hp (ts (ts p fl) p)
  have q2 : Q (tQ2 Rs b c k2 z s ng) := hp (xc (ts (hp s4) fl))
  exact hp (hl (ts (hp (xc (ts q2 s4))) fl))

end tq

theorem bodyTr_uniq (Rs : Rels) (b : Build) (c : Ctx) (k0 k1 k2 z s ng : Bool) :
    Tr.Uniq (bodyTr Rs b c k0 k1 k2 z s ng) :=
  body_q Tr.Uniq Tr.uniq_is Tr.uniq_cat Tr.uniq_cond
    (fun h => Prog.tr_uniq _ _ _ h fun _ hx => absurd hx List.not_mem_nil)
    (fun h => Prog.tr_uniq (.op bL .nil) _ _ (J := []) h fun _ hx => absurd hx List.not_mem_nil) _ _ _ _ _ _

theorem bodyTr_ex (Rs : Rels) (b : Build) (c : Ctx) (k0 k1 k2 z s ng : Bool) :
    Tr.Ex (bodyTr Rs b c k0 k1 k2 z s ng) :=
  body_q Tr.Ex Tr.ex_is Tr.ex_cat Tr.ex_cond
    (fun h => Prog.tr_ex _ _ _ h fun _ hx => absurd hx List.not_mem_nil)
    (fun h => Prog.tr_ex (.op bL .nil) _ _ (J := []) h fun _ hx => absurd hx List.not_mem_nil) _ _ _ _ _ _

/-! ## The effects at `ΨX` -/

section eff
open M0Crypto.Release.Ed25519DecompressW
open M0Crypto.Release.Ed25519VerifyProg (decCo)

theorem dq_ok : CalleeP.OkF dq := CalleeP.okF_parts dq_facts.2.2.2

theorem code_okW : ∀ b : Build, @CalleeP.codeOkW DA DB dq bszX b.bytes b.size b.codeBytes = true := by
  intro b; cases b <;> decide +kernel

/-- **The effect checks** without and with the point's outputs, and the outputs' views at the
success end. -/
theorem eff_facts : dq.s.io.outs = [] ∧
    effOk dq.s.io dq.fpE dq.iniE (dq.s.io.outs.filterMap outE) = true ∧
    subR (dq.s.io.outs.filterMap outE) dq.fpE = true ∧
    effOk (dq.s.withCo decCo).io dq.fpE dq.iniE ((dq.s.withCo decCo).io.outs.filterMap outE) = true ∧
    subR ((dq.s.withCo decCo).io.outs.filterMap outE) dq.fpE = true ∧
    ∀ x ∈ (dq.s.withCo decCo).io.outs, dq.outOk t9.Γ x = true := by
  decide +kernel

/-- No outputs: the frame's invariant after the body from any state's. -/
theorem sir_nil {base : Word} {p : Nat → Word} {sp0 : Word} {n : Nat} {X0 : Word → Prop} {S : St} {q : Ef}
    (h : BI (dq.ctx base p) dq.geo sp0 n X0 S q) :
    SIR sp0 (dq.geo.fsp (dq.ctx base p)) (fun y => X0 y ∨ dq.woW p dq.s.io.outs y ∧ BelowEntry sp0 n y) q :=
  dq.outs_sir dq_ok (fun x hx => by rw [eff_facts.1] at hx; cases hx) h

section
variable (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word) {sp0 : Word} {n : Nat} {X0 : Word → Prop}
  (fm : Frm (dq.ctx base p) dq.geo sp0 n X0)
  (hcode : ∀ y, Has [@codeR b.bytes b.size b.codeBytes base] y → BelowEntry sp0 n y →
    AtOrAboveSp sp0 (dq.geo.fsp (dq.ctx base p)) y ∧ X0 y)
include fm hcode

/-- **The body's effect without outputs**, at any public values. -/
theorem dec_gp : GP sp0 n (BI (dq.ctx base p) dq.geo sp0 n X0 dq.st0) (ΨX Rs b base p)
    (SIR sp0 (dq.geo.fsp (dq.ctx base p)) fun y => X0 y ∨ dq.woW p dq.s.io.outs y ∧ BelowEntry sp0 n y) :=
  body_gp fm hcode _ _ _ _ _ _ (fun _ h => sir_nil h) fun _ _ _ _ h => sir_nil h

/-- **The body's effect with the point's outputs** when the status bits of the input bytes hold. -/
theorem dec_gpCo (hp : okB (b0 (inP p)) (b1 (inP p)) (b2 (inP p)) (bz (inP p)) (bs (inP p)) = true) :
    GP sp0 n (BI (dq.ctx base p) dq.geo sp0 n X0 dq.st0) (ΨX Rs b base p)
      (SIR sp0 (dq.geo.fsp (dq.ctx base p)) fun y => X0 y ∨ dq.woW p (dq.s.withCo decCo).io.outs y ∧ BelowEntry sp0 n y) :=
  body_gp fm hcode _ _ _ _ _ _ (fun _ h => dq.outs_sir dq_ok eff_facts.2.2.2.2.2 h)
    fun h => absurd (hp.symm.trans h) (by decide)

end

/-- **`ge_decompress`'s effect** in build `b` at any public values: no outputs. -/
theorem dec_eff (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word) {tr : List Event}
    (h : dq.trW bszX base p (ΨX Rs b base p) tr) : @CalleeS.Eff dq.s p b.bytes b.size b.codeBytes base tr :=
  letI := b.codeBytes
  CalleeP.effW (q := dq) (s' := dq.s) (pp := fun _ => True) dq_ok (code_okW b) rfl rfl eff_facts.2.1 eff_facts.2.2.1
    (fun base p _ _ _ _ fm hcode => dec_gp Rs b base p fm hcode) base p trivial h

/-- **`ge_decompress`'s effect with the point's outputs** in build `b`, when the status bits of
the input bytes hold. -/
theorem dec_effCo (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word)
    (hp : okB (b0 (inP p)) (b1 (inP p)) (b2 (inP p)) (bz (inP p)) (bs (inP p)) = true) {tr : List Event}
    (h : dq.trW bszX base p (ΨX Rs b base p) tr) :
    @CalleeS.Eff (dq.s.withCo decCo) p b.bytes b.size b.codeBytes base tr :=
  letI := b.codeBytes
  CalleeP.effW (q := dq) (s' := dq.s.withCo decCo)
    (pp := fun p => okB (b0 (inP p)) (b1 (inP p)) (b2 (inP p)) (bz (inP p)) (bs (inP p)) = true) dq_ok (code_okW b)
    rfl rfl eff_facts.2.2.2.1 eff_facts.2.2.2.2.1 (fun base p hp _ _ _ fm hcode => dec_gpCo Rs b base p fm hcode hp)
    base p hp h

/-- The body's trace at `ΨX` is unique and exists. -/
theorem ψX_uniq (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word) : Tr.Uniq (ΨX Rs b base p) :=
  bodyTr_uniq _ _ _ _ _ _ _ _ _

theorem ψX_ex (Rs : Rels) (b : Build) (base : Word) (p : Nat → Word) : Tr.Ex (ΨX Rs b base p) :=
  bodyTr_ex _ _ _ _ _ _ _ _ _

end eff

end M0Crypto.Release.Ed25519DecompressGood
