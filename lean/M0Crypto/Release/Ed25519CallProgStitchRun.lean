import M0Crypto.Release.Ed25519CallProgEntryRun
import M0Crypto.Release.Ed25519CallProgStitch

set_option linter.unusedSimpArgs false

/-!
# Call programs: the stitched-site rules

Between straight lines that `prog_run` runs, a stitched site is a call through an `AdX`
(`xcall_run`) or a test (`tst_run`): the glue `g` (`cmp r0, #0`, or nothing after a block that
sets the flags) and `b<!cc> +0; b T`, which continues when the exit condition `cc` fails and
branches to `T` when it holds. A call's continuation receives the callee's entry state with its
inputs and its result `R.Post`, from which a status test derives its decision.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

variable (Rs : Rels)

/-! ## Values and traces -/

section
variable (G : Geo) (c : Ctx) (m0 : Mem)

/-- The input values of a resolved interface at registers `σ`. -/
def ioVs (st : St) (σ : List (Reg × SV)) (io : Iface) (E : Loc → V) : List V :=
  match ioRes G st σ io with
  | some r => r.srcs.map (Src.val G c m0 E)
  | none => []

/-- The values after a stitched call with semantics `sem`. -/
def xcallEv (st : St) (σ : List (Reg × SV)) (io : Iface) (sem : List V → List V) (E : Loc → V) : Loc → V :=
  match ioRes G st σ io with
  | some r => updOuts E r.outs (sem (r.srcs.map (Src.val G c m0 E)))
  | none => E

/-- The public values of a stitched call to `s`: the registers of `s.pubs`, then `xw`. -/
def xcallPub (st : St) (as : List (LowReg × Ld)) (s : CalleeS) (xw : List Word) : Nat → Word :=
  pubOf (s.pubs.map (pubV c (G.fsp c) st.Γ (regsOf st.Γ st.σ as)) ++ xw)

/-- **The trace of a stitched call** at `o`: the loads, `bl`, the callee's trace `Tw`, then `Ψ`. -/
def xcallTr (o : Nat) (as : List (LowReg × Ld)) (entry : Nat) (Tw : List Event) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTr (ldsEmit as) (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
    (Tr.cat (Tr.is [⟨c.base + BitVec.ofNat 32 (o + seqSize (ldsEmit as)),
      .bl (blImm (o + seqSize (ldsEmit as)) entry), []⟩]) (Tr.cat (Tr.is Tw) Ψ))

/-- **The trace of a test** at `o`: the glue `g`, `b<!cc> +0`, then on decision `d` the rest `Ψk`,
else `b T` and the exit `Ψx`. -/
def tstTr (o : Nat) (g : List Instr) (cc : BitVec 4) (T : Nat) (d : Bool) (Ψk Ψx : TrP) : TrP :=
  Tr.cat (Tr.is (blockTr g (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
    (Tr.cat (Tr.is [bcEv c (cc ^^^ 1) (o + seqSize g) (o + seqSize g + 4)])
      (Tr.cond d Ψk (Tr.cat (Tr.is [bEv c (o + seqSize g + 2) T]) Ψx)))

/-- The trace of a test with a short branch `b<cc> T`: the glue `g`, the branch, then `Ψx` when
taken (`d` false), else `Ψk`. -/
def tstSTr (o : Nat) (g : List Instr) (cc : BitVec 4) (T : Nat) (d : Bool) (Ψk Ψx : TrP) : TrP :=
  Tr.cat (Tr.is (blockTr g (c.base + BitVec.ofNat 32 o) [13] [G.fsp c]))
    (Tr.cat (Tr.is [bcEv c cc (o + seqSize g) T]) (Tr.cond (!d) Ψx Ψk))

/-- The views of the outputs `co` at registers `σ`. -/
def coRes (σ : List (Reg × SV)) (co : List (Reg × Nat × Kd)) : Option (List (Loc × Kd)) :=
  co.mapM fun x => (locOf σ x.1 x.2.1).map (·, x.2.2)

/-- The views `cl` are `ok`, not counters, at distinct locations. -/
def coOk (G : Geo) (cl : List (Loc × Kd)) : Bool :=
  cl.all (fun p => (Kd.sr p.1 p.2).ok G && p.2 != .cw) && (cl.map (·.1)).Nodup

/-- The state with the views `cl` added, only `sp` known. -/
def addViews (st : St) (cl : List (Loc × Kd)) : St :=
  { st with Γ := cl ++ keepViews st.Γ [] cl, σ := σsp, ρ := [] }

end

/-! ## The rules -/

section run
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS}
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (m0 : Mem)

/-- **A stitched call**: a call's loads, `bl` and the callee, through its `AdX`, whose input
values satisfy its premise. The callee's trace is at its public values with the extra values
`xpv` of the input values. The continuation receives the callee's entry state `s`, its inputs and
its result. -/
theorem xcall_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    {a : A} (ad : AdX Rs (cb := ‹CodeBytes B BS›) (cE a)) {as : List (LowReg × Ld)} {o : Nat} {st st' : St}
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.call a as : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.call a as : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (hv : ad.vpre (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))
    (k : ∀ u, At Rs B c G m0 (o + (Op.call a as : Op A Bk).size cE bE) st'
        (xcallEv G c m0 st (regsOf st.Γ st.σ as) (cE a).io ad.sem E) u →
      (∃ s : State, Holds c (G.fsp c) (regsOf st.Γ st.σ as) s.regs ∧ PreG (cE a).io s.regs ∧
        PreV (cE a).io c (G.fsp c) s.regs ∧
        InsRel Rs c (G.fsp c) (cE a).io s (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E) ∧
        ad.R.Post s u.mem (u.regs 0) ∧ (cE a).pubX ad.xp s = xcallPub G c st as (cE a)
          (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) →
      piecesAt B (o + (Op.call a as : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (xcallTr G c o as (cE a).entry (ad.T c.base (xcallPub G c st as (cE a)
        (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E)))) Ψ) := by
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hlds, hpub⟩, hstk⟩ := hc
    cases hr : ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | none => simp [hr] at hty
    | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at hty; subst hty
    simp only [ioVs, hr] at hv k ⊢
    simp only [Op.bok, Bool.and_eq_true] at hbok
    obtain ⟨hsite, htr⟩ := hbok
    have he := ad.entry
    rw [siteOk_congr (f' := ad.R) (by simp [CalleeS.toR, he]) (by simp [CalleeS.toR, ad.code])
      (by simp [CalleeS.toR, ad.stack]), ← he] at hsite
    have hl : ldsOk as = true := by simp only [ldsRes, Bool.and_eq_true] at hlds; exact hlds.1
    obtain ⟨l1, l2, -, l4⟩ := lds_run as t hl
    have hσ1 := lds_holds Rs hi hσ h13 hlds
    have h13x : (execAll (ldsEmit as) t).regs 13 = G.fsp c := by
      rw [l2 13 (by decide) (fun a _ => ne13), h13]
    generalize hs : atCall c.base ad.R (ldsEmit as) o t = s
    have hσs : Holds c (G.fsp c) (regsOf st.Γ st.σ as) s.regs := fun p hp => by
      obtain ⟨h14, hv⟩ := hσ1 p hp
      refine ⟨h14, ?_⟩
      rw [← hs, atCall, blState_regs _ _ _ _ (by omega) (by omega), hv]
    have hms : s.mem = t.mem := by rw [← hs, atCall, blState_mem, l1]
    have hs13 : s.regs 13 = G.fsp c := by rw [← hs, atCall, blState_regs _ _ _ 13, h13x]
    have hρs : ∀ r ∈ st.ρ, (regsOf st.Γ st.σ as).all (·.1 != r) = true → E (.rg r) = .w (s.regs r) :=
      fun r h hn => by
        rw [lds_ρ hρ hlds r h hn, ← hs, atCall, blState_regs _ _ _ _ (by have := (hρ r h).1; omega)
          (by have := (hρ r h).1; omega)]
    obtain ⟨hins, hpre, hpv, houts, hook, hnd, hwr, hwok, rds, hrd, hrok⟩ :=
      ioRes_sound Rs g hi hσs hρs hr
    have hins' : InsRel Rs c (G.fsp c) (cE a).io s (r.srcs.map (Src.val G c m0 E)) := by
      simp only [InsRel, hms]; exact hins
    have hstk' : G.top + ad.R.stack ≤ G.N := by rw [ad.stack]; exact hstk
    have cw := g.cwin hstk'
    have hwin : ad.R.win s = ⟨G.fsp c - BitVec.ofNat 32 ad.R.stack, ad.R.stack⟩ := by
      simp [Routine.win, hs13]
    have hpx : (cE a).pubX ad.xp s = xcallPub G c st as (cE a) (ad.xpv (r.srcs.map (Src.val G c m0 E))) := by
      rw [CalleeS.pubX, xcallPub, ad.xp_of c (G.fsp c) s _ hins']
      congr 2
      apply List.map_congr_left
      intro x hx
      simp only [pubsOk, List.all_eq_true] at hpub
      have hx' := hpub x hx
      cases x with
      | r q =>
        simp only [Option.isSome_iff_exists] at hx'
        obtain ⟨v, hv⟩ := hx'
        simp only [PubW.get, pubV, σv, hv, (hσs.get hv).1]
      | n q =>
        simp only [Option.isSome_iff_exists] at hx'
        obtain ⟨n, hn⟩ := hx'
        obtain ⟨l, hl, hm⟩ := ctxAt_mem hn
        have hr := (hi.1 _ hm).2
        have ea := locOf_addr hσs hl
        simp only [BitVec.add_zero] at ea
        simp only [PubW.get, pubV, hn, Option.map_some, Option.getD_some, hms, ea]
        cases he : E l <;> simp only [Rel, he] at hr
        rw [Rs.ctx_len hr.1, hr.2]
    simp only [Op.pieces, List.cons_append, List.nil_append, ← he] at hp
    simp only [xcallTr]
    rw [← he]
    refine siteTK ad.hT F (ldsEmit as) [(13, 4)] [] (ldsRg G) hp hsite hpc (Hi.self t)
      h13 hcode ?_ (hs ▸ ad.pre c (G.fsp c) c.base s _ hpre hpv hins' hv)
      (traceAll_blockTr l4 htr hpc (by simp [h13])) ?_ fun u hpu _ h13u hcu hmu hpost hrest => ?_
    · -- the side conditions
      unfold SiteSides; rw [hs, hwin, ad.wr, ad.rd, hwr, hrd]
      refine ⟨⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩,
        sub_cons' (sub_trans cw.1 g.wW) (sub_flatMap fun w hw => ?_),
        sub_cons' hcR (sub_cons' (sub_trans cw.1 g.wR) (sub_flatMap fun w hw => ?_)),
        sep_flatMap fun w hw => cw.2 (hwok w hw).1, sep_flatMap fun w hw => cw.2 (hrok w hw).1⟩
      · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
      · have := g.sub (hwok w hw).1 true (hwok w hw).2; simpa using this
      · have := g.sub (hrok w hw).1 false (hrok w hw).2; simpa using this
    · -- the callee's public values
      rw [hs, hpx]
    · -- after the call
      rw [hs] at hmu hpost
      rw [hwin, ad.wr, hwr] at hmu
      have hpost' := ad.post c (G.fsp c) s u.mem (u.regs 0) _ hpv hins' hv hpost
      rw [Op.size_call, ← Nat.add_assoc] at k
      refine k u ⟨hpu, h13u, hcu, holds_sp h13u, ?_, fun _ h => by simp [IoR.after] at h⟩
        ⟨s, hσs, hpre, hpv, hins', hpost, hpx⟩ hrest
      simp only [xcallEv, hr, IoR.after]
      exact inv_after Rs g hi hstk' (fun w hw => (hwok w hw).1) (by simpa [regions] using hmu) σsp []
        (fun p hp => (hook p hp).1) hnd
        (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2) houts hpost')
  · simp at hty

/-- **A test**: the glue `gs`, then `b<!cc> +0; b T`. When the exit condition `cc` fails after
the glue (`d`), the run continues after the test, else it branches to `T`; either way with only
`sp` known and the memory unchanged. -/
theorem tst_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {gs : List Instr} {cc : BitVec 4} {o T : Nat} {st : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψk Ψx : TrP} {d : Bool} {rest : List Piece} (hcc : cc.toNat < 14)
    (hbok : (Op.pub gs : Op A Bk).bok cE bE G o = true) (hbr : brOk G false (o + seqSize gs) T = true)
    (hp : piecesAt B o (.seq gs :: xitBr cc false (o + seqSize gs) T ++ rest) = true)
    (hat : At Rs B c G m0 o st E t) (hd : condPassed cc (execAll gs t) = !d)
    (kS : d = true → ∀ u, At Rs B c G m0 (o + seqSize gs + 4) { st with σ := σsp, ρ := [] } E u →
      u.mem = t.mem → (∀ r : Reg, r ≠ 15 → u.regs r = (execAll gs t).regs r) →
      piecesAt B (o + seqSize gs + 4) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψk)
    (kX : d = false → ∀ u, At Rs B c G m0 T { st with σ := σsp, ρ := [] } E u → u.mem = t.mem →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (tstTr G c o gs cc T d Ψk Ψx) := by
  simp only [Op.bok, Bool.and_eq_true] at hbok
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
  have hfa := glueOk_falls hbok.1
  have htN : G.top ≤ G.N := g.top
  simp only [tstTr]
  refine ReachFT.glue F gs [(13, 4)] [] (ldsRg G) hp1 hpc h13 hcode
    ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
    (traceAll_blockTr hfa hbok.2 hpc (by simp [h13])) (fun hpc1 h131 hc1 hm1 => ?_) hbok.1
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  have hm : (execAll gs t).mem = t.mem := by
    funext y; exact hm1 y (fun ⟨_, h, _⟩ => by simp [regions] at h)
  have hu : At Rs B c G m0 (o + seqSize gs) { st with σ := σsp, ρ := [] } E (execAll gs t) :=
    ⟨hpc1, h131, hc1, holds_sp h131, Inv.st Rs rfl rfl (by rw [hm]; exact hi), fun _ h => by cases h⟩
  have hneg : condPassed (cc ^^^ 1) (execAll gs t) = d := by
    rw [condPassed_fl, condFl_xor1 cc hcc, ← condPassed_fl, hd, Bool.not_not]
  simp only [brOk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hbr
  simp only [xitBr, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at hp2
  obtain ⟨hpi, hpr⟩ := piecesAt_cons hp2
  obtain ⟨hpj, hpk⟩ := piecesAt_cons hpr
  simp only [Piece.instrs, Piece.size_bcond, Piece.size_b] at hpi hpj hpk
  refine bc_run F hbr.1 hpi hpc1 h131 htN hneg (fun ht => ?_) (fun hf => ?_)
  · rw [hneg] at ht; subst ht
    exact kS rfl _ (by simpa using at_br Rs m0 (o' := o + seqSize gs + 4) hu) (by simp [State.setReg, hm])
      (fun r hr => by simp [State.setReg, hr]) (by simpa [Nat.add_assoc] using hpk)
  · rw [hneg] at hf; subst hf
    refine b_run F hbr.2 hpj (by simp [State.pc, State.setReg]) (by simpa [State.setReg, Geo.fsp] using h131) htN ?_
    exact kX rfl _ (at_br Rs m0 (at_br Rs m0 (o' := o + seqSize gs + 2) hu)) (by simp [State.setReg, hm])

/-- **A public block**: the glue `gs` at `o` keeps `sp` and the memory. -/
theorem pubB_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) {gs : List Instr} {o : Nat} {st : St}
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hbok : (Op.pub gs : Op A Bk).bok cE bE G o = true) (hp : piecesAt B o (.seq gs :: rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : (execAll gs t).pc = c.base + BitVec.ofNat 32 (o + seqSize gs) → (execAll gs t).regs 13 = G.fsp c →
      (execAll gs t).mem = t.mem → piecesAt B (o + seqSize gs) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) (execAll gs t) Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (Tr.cat (Tr.is (blockTr gs (c.base + BitVec.ofNat 32 o) [13] [G.fsp c])) Ψ) := by
  simp only [Op.bok, Bool.and_eq_true] at hbok
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  obtain ⟨hpc, h13, hcode, -, -, -⟩ := hat
  have hfa := glueOk_falls hbok.1
  refine ReachFT.glue F gs [(13, 4)] [] (ldsRg G) hp1 hpc h13 hcode
    ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
    (traceAll_blockTr hfa hbok.2 hpc (by simp [h13])) (fun hpc1 h131 _ hm1 => k hpc1 h131 ?_ hp2) hbok.1
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  · funext y; exact hm1 y (fun ⟨_, h, _⟩ => by simp [regions] at h)

/-- **A test with a short branch**: the public glue `gs` at `o` with decision `d` (the branch
condition `cc` fails), then `b<cc> T`: on `d` the run continues after it, else at `T`. -/
theorem tstS_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {gs : List Instr} {cc : BitVec 4} {o T : Nat} {st : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψk Ψx : TrP} {d : Bool} {rest : List Piece}
    (hbok : (Op.pub gs : Op A Bk).bok cE bE G o = true) (hbr : brOk G true (o + seqSize gs) T = true)
    (hp : piecesAt B o (.seq gs :: xitBr cc true (o + seqSize gs) T ++ rest) = true)
    (hat : At Rs B c G m0 o st E t) (hd : condPassed cc (execAll gs t) = !d)
    (kS : d = true → ∀ u, At Rs B c G m0 (o + seqSize gs + 2) { st with σ := σsp, ρ := [] } E u →
      u.mem = t.mem → piecesAt B (o + seqSize gs + 2) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψk)
    (kX : d = false → ∀ u, At Rs B c G m0 T { st with σ := σsp, ρ := [] } E u → u.mem = t.mem →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (tstSTr G c o gs cc T d Ψk Ψx) := by
  simp only [Op.bok, Bool.and_eq_true] at hbok
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
  have hfa := glueOk_falls hbok.1
  have htN : G.top ≤ G.N := g.top
  simp only [tstSTr]
  refine ReachFT.glue F gs [(13, 4)] [] (ldsRg G) hp1 hpc h13 hcode
    ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
    (traceAll_blockTr hfa hbok.2 hpc (by simp [h13])) (fun hpc1 h131 hc1 hm1 => ?_) hbok.1
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  have hm : (execAll gs t).mem = t.mem := by
    funext y; exact hm1 y (fun ⟨_, h, _⟩ => by simp [regions] at h)
  have hu : At Rs B c G m0 (o + seqSize gs) { st with σ := σsp, ρ := [] } E (execAll gs t) :=
    ⟨hpc1, h131, hc1, holds_sp h131, Inv.st Rs rfl rfl (by rw [hm]; exact hi), fun _ h => by cases h⟩
  simp only [brOk, ↓reduceIte] at hbr
  simp only [xitBr, ↓reduceIte, List.cons_append, List.nil_append] at hp2
  obtain ⟨hpi, hpk⟩ := piecesAt_cons hp2
  simp only [Piece.instrs, Piece.size_bcond] at hpi hpk
  refine bc_run F hbr hpi hpc1 h131 htN hd (fun ht => ?_) (fun hf => ?_)
  · rw [hd] at ht
    exact kX (by simpa using ht) _ (at_br Rs m0 hu) (by simp [State.setReg, hm])
  · rw [hd] at hf
    exact kS (by simpa using hf) _ (at_br Rs m0 hu) (by simp [State.setReg, hm]) (by simpa [Nat.add_assoc] using hpk)

theorem coRes_addr {sp : Word} {σ : List (Reg × SV)} {regs : Reg → Word} (hσ : Holds c sp σ regs)
    {co : List (Reg × Nat × Kd)} {cl : List (Loc × Kd)} (h : coRes σ co = some cl) :
    All2 (fun (x : Reg × Nat × Kd) p => regs x.1 + BitVec.ofNat 32 x.2.1 = p.1.addr c sp ∧ p.2 = x.2.2) co cl :=
  all2_mono (fun x p hp => by
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨l, hl, rfl⟩ := hp
    exact ⟨locOf_addr hσ hl, rfl⟩) (mapM_forall₂ h)

/-- **Added views**: views that hold in memory join the invariant. -/
theorem inv_add (g : GeoOk c G Wc Rc) {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m)
    {cl : List (Loc × Kd)} {vs : List V} (hok : coOk G cl = true)
    (hv : All2 (fun p v => Rel Rs c (G.fsp c) p.2 m (p.1.addr c (G.fsp c)) v) cl vs) :
    Inv Rs c G m0 (addViews st cl) (updOuts E cl vs) m := by
  simp only [coOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  have := inv_after Rs g hi (sw := 0) (ws := []) (by have := g.top; omega) (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ => rfl) σsp [] (fun p hp => (hok.1 p hp).1) hok.2 hv
  refine Inv.st Rs ?_ ?_ this <;> simp [addViews]

/-- **A status call**: a stitched call, `cmp r0, #0`, then `b<eq> +0; b T`. With the status `d`
of the input values, the run continues with the outputs `co` as views, else it branches to `T`
without them. -/
theorem zcall_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    {a : A} {ad : AdX Rs (cb := ‹CodeBytes B BS›) (cE a)} (z : ZSt Rs ad) {as : List (LowReg × Ld)}
    {o T : Nat} {st st' : St} {E : Loc → V} {t : State} {Q : State → Prop} {Ψk Ψx : TrP} {d : Bool}
    {rest : List Piece} {cl : List (Loc × Kd)}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.call a as : Op A Bk).bok cE bE G o = true)
    (hbt : (Op.pub [.cmpImm 0 0] : Op A Bk).bok cE bE G (o + (Op.call a as : Op A Bk).size cE bE) = true)
    (hbr : brOk G false (o + (Op.call a as : Op A Bk).size cE bE + seqSize [.cmpImm 0 0]) T = true)
    (hp : piecesAt B o ((Op.call a as : Op A Bk).pieces cE bE ++ (.seq [.cmpImm 0 0] ::
      xitBr NE false (o + (Op.call a as : Op A Bk).size cE bE + seqSize [.cmpImm 0 0]) T ++ rest)) = true)
    (hat : At Rs B c G m0 o st E t)
    (hv : ad.vpre (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))
    (hco : coRes (regsOf st.Γ st.σ as) z.co = some cl) (hcok : coOk G cl = true)
    (hd : z.ok (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E) = d)
    (kS : d = true → ad.ppre (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) ∧
        z.okp (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) = d →
      ∀ u, At Rs B c G m0 (o + (Op.call a as : Op A Bk).size cE bE + seqSize [.cmpImm 0 0] + 4)
        (addViews st' cl) (updOuts (xcallEv G c m0 st (regsOf st.Γ st.σ as) (cE a).io ad.sem E) cl
          (z.csem (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) u →
      piecesAt B (o + (Op.call a as : Op A Bk).size cE bE + seqSize [.cmpImm 0 0] + 4) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψk)
    (kX : d = false → ad.ppre (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) ∧
        z.okp (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) = d →
      ∀ u, At Rs B c G m0 T { st' with σ := σsp, ρ := [] }
        (xcallEv G c m0 st (regsOf st.Γ st.σ as) (cE a).io ad.sem E) u →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (xcallTr G c o as (cE a).entry (ad.T c.base (xcallPub G c st as (cE a)
        (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))))
        (tstTr G c (o + (Op.call a as : Op A Bk).size cE bE) [.cmpImm 0 0] NE T d Ψk Ψx)) := by
  refine xcall_run Rs m0 g F hcR ad hty hbok hp hat hv fun u hu ⟨s, hσs, hpre, hpv, hins, hpost, hpx⟩ hr => ?_
  have hz := z.okr c (G.fsp c) s u.mem (u.regs 0) _ hpv hins hv hpost
  have hpk : ad.ppre (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) ∧
      z.okp (xcallPub G c st as (cE a) (ad.xpv (ioVs G c m0 st (regsOf st.Γ st.σ as) (cE a).io E))) = d :=
    ⟨hpx ▸ ad.ppre_of c (G.fsp c) s _ hpre hpv hins hv, by rw [← hpx, z.okp_of c (G.fsp c) s _ hpre hpv hins hv, hd]⟩
  refine tst_run Rs m0 g F (by decide) hbt hbr hr hu ?_ (fun hd' u' hu' hm _ hr' => kS hd' hpk u' ?_ hr')
    (fun hd' u' hu' _ => kX hd' hpk u' hu')
  · have e : LowReg.toReg 0 = 0 := rfl
    rw [← hd]
    simp only [condPassed, NE, cmp0_z, e]
    cases h : z.ok _ <;> simp [h] at hz ⊢ <;> exact hz
  · obtain ⟨h1, h2, h3, h4, hi, -⟩ := hu'
    refine ⟨h1, h2, h3, h4, ?_, fun _ h => by cases h⟩
    have hc := z.cpost c (G.fsp c) s u.mem (u.regs 0) _ hpv hins hv hpost (hd.trans hd')
    rw [← hm] at hc
    exact inv_add Rs m0 g hi hcok (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2) (coRes_addr hσs hco) hc)

/-- **A block at a stitched site**: `blk_run` whose continuation also receives the block's entry
state `t1` with its inputs; the state after is the block's run from `t1`. -/
theorem xblk_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {semA : A → List V → List V} {T : A → Word → (Nat → Word) → List Event}
    {b : Bk} (bd : Bd Rs (bE b)) {as : List (LowReg × Ld)} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.blk b as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.blk b as : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.blk b as : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.blk b as : Op A Bk).size cE bE) st'
        ((Op.blk b as : Op A Bk).ev cE bE G semA (fun _ => bd.sem) c m0 st E) u →
      (∃ t1 : State, Holds c (G.fsp c) (regsOf st.Γ st.σ as) t1.regs ∧ PreG (bE b).io t1.regs ∧
        NoWrap (bE b).io t1.regs ∧ PreV (bE b).io c (G.fsp c) t1.regs ∧
        InsRel Rs c (G.fsp c) (bE b).io t1 (ioVs G c m0 st (regsOf st.Γ st.σ as) (bE b).io E) ∧
        u = execAll (bE b).g t1) →
      piecesAt B (o + (Op.blk b as : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.blk b as : Op A Bk).tr cE bE G T c o st Ψ) := by
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨hlds, hpub⟩, -⟩, -⟩, hnw⟩, hro⟩ := hc
    cases hr : ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
    | none => simp [hr] at hty
    | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at hty; subst hty
    simp only [ioVs, hr] at k
    simp only [Op.bok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hbok
    obtain ⟨⟨⟨⟨⟨hg1, ht1⟩, hg2⟩, ht2⟩, hkw⟩, hkr⟩ := hbok
    have hl : ldsOk as = true := by simp only [ldsRes, Bool.and_eq_true] at hlds; exact hlds.1
    obtain ⟨l1, l2, -, l4⟩ := lds_run as t hl
    have hσ1 := lds_holds Rs hi hσ h13 hlds
    simp only [Op.pieces, List.cons_append, List.nil_append] at hp
    obtain ⟨hp1, hp⟩ := piecesAt_cons hp
    obtain ⟨hp2, hp3⟩ := piecesAt_cons hp
    simp only [Piece.instrs, Piece.size] at hp1 hp2 hp3
    simp only [Op.tr]
    refine ReachFT.glue F (ldsEmit as) [(13, 4)] [] (ldsRg G) hp1 hpc h13 hcode
      ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
      (traceAll_blockTr l4 ht1 hpc (by simp [h13])) (fun hpc1 h131 hc1 _ => ?_) hg1
    · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
    obtain ⟨hins, hpre, hpv, -, hook, hnd, hwr, hwok, rds, hrd, hrok⟩ := ioRes_sound Rs g hi hσ1 (lds_ρ hρ hlds) hr
    have hins' : InsRel Rs c (G.fsp c) (bE b).io (execAll (ldsEmit as) t) (r.srcs.map (Src.val G c m0 E)) := by
      simp only [InsRel, l1]; exact hins
    obtain ⟨-, hgfa, -, -, hgwc, -, -, -⟩ : _ := by
      simp only [glueOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hg2; exact hg2
    have hwr' := regions_g (t := execAll (ldsEmit as) t) hkw
    have hrd' := regions_g (t := execAll (ldsEmit as) t) hkr
    refine ReachFT.glue F (bE b).g _ _ _ hp2 hpc1 h131 hc1
      ⟨fun p hp => ?_, ?_, ?_⟩
      (traceAll_blockTr hgfa ht2 hpc1 ?_) (fun hpc2 h132 hc2 hm2 => ?_) hg2
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp; exact hpre.1 x hx
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp; exact Nat.mod_one _
    · rw [hwr', hwr]; exact sub_flatMap fun w hw => by simpa using g.sub (hwok w hw).1 true (hwok w hw).2
    · rw [hrd', hrd]; exact sub_flatMap fun w hw => by simpa using g.sub (hrok w hw).1 false (hrok w hw).2
    · apply List.map_congr_left
      intro x hx
      simp only [pubOk, List.all_eq_true, Option.isSome_iff_exists] at hpub
      obtain ⟨v, hv⟩ := hpub x hx
      simp only [σv, hv, (hσ1.get hv).1]
    · have hnw' := nw_sound g hσ1 hnw
      have hpost := bd.post c (G.fsp c) _ _ hpre hnw' hpv hins'
      rw [hwr', hwr] at hm2
      have e : o + (Op.blk b as : Op A Bk).size cE bE = o + seqSize (ldsEmit as) + seqSize (bE b).g := by
        simp [Op.size, Op.pieces, piecesSize, Nat.add_assoc]
      rw [e] at k
      refine k _ ⟨hpc2, h132, hc2, holds_blkσ hσ1 h132, ?_, fun q hq => ⟨?_, ?_⟩⟩
        ⟨_, hσ1, hpre, hnw', hpv, hins', rfl⟩ hp3
      · simp only [Op.ev, hr, IoR.after]
        have hi' : Inv Rs c G m0 st E (execAll (ldsEmit as) t).mem := by rw [l1]; exact hi
        exact inv_setRg Rs m0 (inv_after Rs g hi' (sw := 0) (by have := g.top; omega) (fun w hw => (hwok w hw).1)
          (memEq_cons0 _ hm2) _ (bE b).io.ro (fun p hp => (hook p hp).1) hnd
          (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2)
            (ioRes_sound Rs g hi hσ1 (lds_ρ hρ hlds) hr).2.2.2.1 hpost)) _ _
      · simpa using List.all_eq_true.mp hro q hq
      · simp only [Op.ev, hr]
        exact setRg_at (bd.rpost c (G.fsp c) _ _ hpre hnw' hpv hins') hq
  · simp at hty

/-- **A block with a test**: a block through its `ZB`, then `b<!cc> +0; b T`. With the status `d`
of the input values, the run continues with the outputs `co` as views, else it branches to `T`. -/
theorem zblk_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {semA : A → List V → List V} {T' : A → Word → (Nat → Word) → List Event}
    {b : Bk} {bd : Bd Rs (bE b)} (z : ZB Rs bd) {as : List (LowReg × Ld)} {o T : Nat} {st st' : St}
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψk Ψx : TrP} {d : Bool} {rest : List Piece}
    {cl : List (Loc × Kd)} (hcc : z.cc.toNat < 14)
    (hty : (Op.blk b as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.blk b as : Op A Bk).bok cE bE G o = true)
    (hbt : (Op.pub [] : Op A Bk).bok cE bE G (o + (Op.blk b as : Op A Bk).size cE bE) = true)
    (hbr : brOk G false (o + (Op.blk b as : Op A Bk).size cE bE + seqSize []) T = true)
    (hp : piecesAt B o ((Op.blk b as : Op A Bk).pieces cE bE ++ (.seq [] ::
      xitBr z.cc false (o + (Op.blk b as : Op A Bk).size cE bE + seqSize []) T ++ rest)) = true)
    (hat : At Rs B c G m0 o st E t)
    (hco : coRes (regsOf st.Γ st.σ as) z.co = some cl) (hcok : coOk G cl = true)
    (hd : z.ok (ioVs G c m0 st (regsOf st.Γ st.σ as) (bE b).io E) = d)
    (hv : z.vpre (ioVs G c m0 st (regsOf st.Γ st.σ as) (bE b).io E))
    (kS : d = true → ∀ u, At Rs B c G m0 (o + (Op.blk b as : Op A Bk).size cE bE + seqSize [] + 4)
        (addViews st' cl) (updOuts ((Op.blk b as : Op A Bk).ev cE bE G semA (fun _ => bd.sem) c m0 st E) cl
          (z.csem (ioVs G c m0 st (regsOf st.Γ st.σ as) (bE b).io E))) u →
      piecesAt B (o + (Op.blk b as : Op A Bk).size cE bE + seqSize [] + 4) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψk)
    (kX : d = false → ∀ u, At Rs B c G m0 T { st' with σ := σsp, ρ := [] }
        ((Op.blk b as : Op A Bk).ev cE bE G semA (fun _ => bd.sem) c m0 st E) u →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψx) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.blk b as : Op A Bk).tr cE bE G T' c o st
        (tstTr G c (o + (Op.blk b as : Op A Bk).size cE bE) [] z.cc T d Ψk Ψx)) := by
  refine xblk_run Rs m0 g F (semA := semA) bd hty hbok hp hat fun u hu ⟨t1, hσs, hpre, hnw, hpv, hins, hu1⟩ hr => ?_
  refine tst_run Rs m0 g F hcc hbt hbr hr hu ?_ (fun hd' u' hu' hm _ hr' => kS hd' u' ?_ hr') (fun hd' u' hu' _ => kX hd' u' hu')
  · rw [← hd, hu1]; exact z.okf c (G.fsp c) t1 _ hpre hnw hpv hins
  · obtain ⟨h1, h2, h3, h4, hi, -⟩ := hu'
    refine ⟨h1, h2, h3, h4, ?_, fun _ h => by cases h⟩
    have hc := z.cpost c (G.fsp c) t1 _ hpre hnw hpv hins hv (hd.trans hd')
    rw [← hu1, ← hm] at hc
    exact inv_add Rs m0 g hi hcok (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2) (coRes_addr hσs hco) hc)

end run

end M0Crypto.Release.Ed25519CallProg
