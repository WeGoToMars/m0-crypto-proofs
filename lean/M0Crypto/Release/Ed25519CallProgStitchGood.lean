import M0Crypto.Release.Ed25519CallProgGood
import M0Crypto.Release.Ed25519CallProgStitchRun

set_option linter.unusedSimpArgs false

/-!
# Call programs: the byte effect of stitched sites

`tst_gp`: a test's glue and branches keep the body's invariant `BI` on both edges. `xcall_gp`: a
stitched call's trace keeps it, from the effect of the callee with the outputs `co`, and adds the
views of `co`, which the continuing edge of a status call keeps (`addViews`) and the exit edge
drops. `bi_cover`: a block's outputs `co` whose bytes are those of views it keeps add nothing.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)

/-- The state with the views `cl` before its own. -/
def withViews (st : St) (cl : List (Loc × Kd)) : St := { st with Γ := cl ++ st.Γ }

/-- The outputs `co` use public registers of `s` and are not contexts. -/
def coEok (s : CalleeS) (co : List (Reg × Nat × Kd)) : Bool :=
  co.all fun x => decide (PubW.r x.1 ∈ s.pubs) && !(x.2.2 matches .ctx _)

/-- Each view of `cl` has a view of `Γ` at its location with the same written bytes. -/
def coCov (Γ cl : List (Loc × Kd)) : Bool :=
  cl.all fun p => Γ.any fun q => q.1 == p.1 && Kd.sameIni q.2 p.2

theorem CalleeS.eff_withCo_nil {s : CalleeS} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {p : Nat → Word}
    {base : Word} {tr : List Event} (h : s.Eff p base tr) : (s.withCo []).Eff p base tr := by
  have e : s.withCo [] = s := by simp [CalleeS.withCo]
  rwa [e]

theorem getD_idxOf_app {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) (d : β) (xw : List β) {l : List α} {a : α}
    (h : a ∈ l) : (l.map f ++ xw).getD (l.idxOf a) d = f a := by
  have hl := List.idxOf_lt_length_of_mem h
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hl), ← List.getD_eq_getElem?_getD]
  exact getD_idxOf f d h

/-- The written bytes of the frame views of `Γ` but contexts: what a test's glue may read. -/
def frIni (Γ : List (Loc × Kd)) : List (SExpr × Nat) :=
  Γ.filterMap fun p => match p with
    | (.fr o, k) => match k with
      | .ctx _ => none
      | k => some (.add (.reg0 13) (.const (BitVec.ofNat 32 o)), k.sz)
    | _ => none

section
variable {c : Ctx} {G : Geo} {sp0 : Word} {n : Nat} {X0 : Word → Prop}

theorem BI.addViews {st : St} {cl : List (Loc × Kd)} {q : Ef} (h : BI c G sp0 n X0 (withViews st cl) q) :
    BI c G sp0 n X0 (addViews st cl) q :=
  BI.sub (fun _ hp => (List.mem_append.mp hp).elim (List.mem_append_left _) fun h => List.mem_append_right _ (keep_sub _ h)) h

theorem BI.dropViews {st : St} {cl : List (Loc × Kd)} {q : Ef} (h : BI c G sp0 n X0 (withViews st cl) q) :
    BI c G sp0 n X0 { st with σ := σsp, ρ := [] } q :=
  BI.sub (fun _ hp => List.mem_append_right _ hp) h

/-- **Covered views**: views at locations of views with the same written bytes. -/
theorem BI.cover {st : St} {cl : List (Loc × Kd)} (hc : coCov st.Γ cl = true) {q : Ef} (h : BI c G sp0 n X0 st q) :
    BI c G sp0 n X0 (withViews st cl) q := by
  refine ⟨h.sp, h.ab, h.sv, fun y ⟨p, hp, hy⟩ hb => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · simp only [coCov, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨p', hp', he, hs⟩ := hc p hp
    exact h.ex y ⟨p', hp', by rw [he, ← Kd.ini_same hs]; exact hy⟩ hb
  · exact h.ex y ⟨p, hp, hy⟩ hb

variable (fm : Frm c G sp0 n X0)
include fm

/-- **A test**: its glue on public words, `b<!cc> +0`, and on the exit `b T`. -/
theorem tst_gp {st : St} {gs : List Instr} (hk : blkChk (pwIni st.Γ) [] [frR G] gs = true) {o T : Nat}
    {cc : BitVec 4} {d : Bool} {Ψk Ψx : TrP} {J : Ef → Prop}
    (hΨk : d = true → GP sp0 n (BI c G sp0 n X0 st) Ψk J) (hΨx : d = false → GP sp0 n (BI c G sp0 n X0 st) Ψx J) :
    GP sp0 n (BI c G sp0 n X0 st) (tstTr G c o gs cc T d Ψk Ψx) J :=
  GP.cat (pubBlk_gp fm hk _) (GP.cat (quiet_gp rfl rfl rfl)
    (GP.cond hΨk fun h => GP.cat (quiet_gp rfl rfl rfl) (hΨx h)))

/-- **A glue block reading frame views** keeps the body's invariant. -/
theorem frBlk_gp {st : St} {g : List Instr} (hk : blkChk (frIni st.Γ) [] [frR G] g = true) (pc : Word) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTr g pc [13] [G.fsp c])) (BI c G sp0 n X0 st) := by
  refine bi_seg (blk_seg hk _ (fun _ h => h) fun y hy _ => ?_) (fun y hy _ => .inl ?_) fun y hy _ => .inl hy
  · obtain ⟨r, hr, hy⟩ := inR_region hy
    simp only [frR, List.mem_singleton] at hr; subst hr
    simp only [SExpr.denote, rs13] at hy
    exact fm.fr_above (o := 0) (m := G.top) (by omega) (by rw [BitVec.add_zero]; exact hy)
  · obtain ⟨r, hm, hy⟩ := inR_region hy
    obtain ⟨⟨l, k⟩, hp, hm⟩ := List.mem_filterMap.mp hm
    cases l with
    | fr o =>
      cases k with
      | ctx _ => simp at hm
      | _ =>
        simp only [Option.some.injEq] at hm; subst hm
        simp only [SExpr.denote, rs13] at hy
        exact ⟨_, hp, hy⟩
    | _ => simp at hm

/-- **A test reading frame views**: `tst_gp` with the glue's reads in the frame views. -/
theorem tstF_gp {st : St} {gs : List Instr} (hk : blkChk (frIni st.Γ) [] [frR G] gs = true) {o T : Nat}
    {cc : BitVec 4} {d : Bool} {Ψk Ψx : TrP} {J : Ef → Prop}
    (hΨk : d = true → GP sp0 n (BI c G sp0 n X0 st) Ψk J) (hΨx : d = false → GP sp0 n (BI c G sp0 n X0 st) Ψx J) :
    GP sp0 n (BI c G sp0 n X0 st) (tstTr G c o gs cc T d Ψk Ψx) J :=
  GP.cat (frBlk_gp fm hk _) (GP.cat (quiet_gp rfl rfl rfl)
    (GP.cond hΨk fun h => GP.cat (quiet_gp rfl rfl rfl) (hΨx h)))

/-- **A test with a short branch**: its glue on frame views and `b<cc> T`. -/
theorem tstS_gp {st : St} {gs : List Instr} (hk : blkChk (frIni st.Γ) [] [frR G] gs = true) {o T : Nat}
    {cc : BitVec 4} {d : Bool} {Ψk Ψx : TrP} {J : Ef → Prop}
    (hΨk : d = true → GP sp0 n (BI c G sp0 n X0 st) Ψk J) (hΨx : d = false → GP sp0 n (BI c G sp0 n X0 st) Ψx J) :
    GP sp0 n (BI c G sp0 n X0 st) (tstSTr G c o gs cc T d Ψk Ψx) J :=
  GP.cat (frBlk_gp fm hk _) (GP.cat (quiet_gp rfl rfl rfl)
    (GP.cond (fun h => hΨx (by simpa using h)) fun h => hΨk (by simpa using h)))

/-- **A block with a test**: the block, then the test with no glue; the outputs `co` give views
`cl` covered by the block's own views. -/
theorem zblk_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T' : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {b : Bk} {as : List (LowReg × Ld)} {o T : Nat} {cc : BitVec 4} {d : Bool}
    (hty : (Op.blk b as : Op A Bk).ty cE bE G st = some s1) (hok : (Op.blk b as : Op A Bk).eok cE bE G st = true)
    {cl : List (Loc × Kd)} (hcov : coCov s1.Γ cl = true) {Ψk Ψx : TrP} {J : Ef → Prop}
    (hΨk : d = true → GP sp0 n (BI c G sp0 n X0 (addViews s1 cl)) Ψk J)
    (hΨx : d = false → GP sp0 n (BI c G sp0 n X0 { s1 with σ := σsp, ρ := [] }) Ψx J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.blk b as : Op A Bk).tr cE bE G T' c o st
      (tstTr G c (o + (Op.blk b as : Op A Bk).size cE bE) [] cc T d Ψk Ψx)) J :=
  blk_gp fm hty hok (GP.pre (fun _ h => BI.cover hcov h) (tst_gp fm rfl
    (fun h => GP.pre (fun _ h => BI.addViews h) (hΨk h)) fun h => GP.pre (fun _ h => BI.dropViews h) (hΨx h)))

section call
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
  (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (G.fsp c) y ∧ X0 y)
include hcode

/-- **A stitched call**: its loads, the `bl`, and the callee's trace `Tw` at the public values with
the extra values `xw`, from the effect of the callee with the outputs `co`. After it, the views of
`co` join the call's. -/
theorem xcall_gp {st s1 : St} {a : A} {as : List (LowReg × Ld)} {o : Nat}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some s1) (hok : (Op.call a as : Op A Bk).eok cE bE G st = true)
    {co : List (Reg × Nat × Kd)} {cl : List (Loc × Kd)} (hcr : coRes (regsOf st.Γ st.σ as) co = some cl)
    (hcok : coEok (cE a) co = true) {xw : List Word} {Tw : List Event}
    (he : ((cE a).withCo co).Eff (xcallPub G c st as (cE a) xw) c.base Tw)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 (withViews s1 cl)) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) (xcallTr G c o as (cE a).entry Tw Ψ) J := by
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    obtain ⟨r, hres, rfl⟩ := Option.map_eq_some_iff.mp hty
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hl, -⟩, hstk⟩ := hc
    simp only [Op.eok, Bool.and_eq_true] at hok
    obtain ⟨hk, hco⟩ := hok
    refine GP.cat (lds_gp fm hk hl _) (GP.cat (quiet_gp rfl rfl rfl) (GP.cat ?_ hΨ))
    simp only [xcallPub] at he
    generalize hσ' : regsOf st.Γ st.σ as = σ' at hres hco hcr he
    generalize hp : pubOf ((cE a).pubs.map (pubV c (G.fsp c) st.Γ σ') ++ xw) = p at he
    simp only [callOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hco
    obtain ⟨⟨⟨⟨⟨hσ, h13⟩, hp13⟩, hrw⟩, hins⟩, houts⟩ := hco
    have hH := holds_σv (c := c) (sp := G.fsp c) hσ
    have hreg : ∀ r, PubW.r r ∈ (cE a).pubs → (cE a).reg p r = σv c (G.fsp c) σ' r := fun r h => by
      rw [← hp]; exact getD_idxOf_app _ _ _ h
    have hlen : ∀ l : ALen, lenPub (cE a).pubs l = true → l.val ((cE a).reg p) = l.val (σv c (G.fsp c) σ') := by
      intro l h; cases l with
      | k => rfl
      | r j => simp only [lenPub, decide_eq_true_eq] at h; simp [ALen.val, hreg j h]
    have hlen' : ∀ j, lenPub (cE a).pubs (.r j) = true → (cE a).reg p j = σv c (G.fsp c) σ' j :=
      fun j h => hreg j (by simpa [lenPub] using h)
    have hcnt : (cE a).cnt p = slen c (G.fsp c) (ctxIn (cE a) st.Γ σ') % 2 ^ 32 := by
      unfold CalleeS.cnt ctxIn
      by_cases h : PubW.n 0 ∈ (cE a).pubs
      · simp only [h, ↓reduceIte]; rw [← hp, pubOf, getD_idxOf_app _ _ _ h]; simp only [pubV]
        cases ctxAt st.Γ σ' 0 <;> simp [slen]
      · simp [h, slen]
    have e13 : (cE a).reg p 13 = G.fsp c := by rw [hreg 13 hp13]; simp [σv, h13, SV.val]
    obtain ⟨hsrc, hout, hwr, hwo, rds, hrd, hro⟩ := ioRes_parts hres
    unfold CalleeS.Eff at he
    have he : EffT (cE a).stack ((cE a).Fp p c.base) ((cE a).Rq p c.base) (fun y => (cE a).Wd p y ∨
        ∃ x ∈ co, Region ((cE a).reg p x.1 + BitVec.ofNat 32 x.2.1) ((cE a).iniOut p x.2.2) y) (G.fsp c) Tw := by
      rw [← e13]
      exact EffT.mono he (Nat.le_refl _) (fun _ h => h) (fun _ h => h) fun y h => h.elim
        (fun ⟨x, hx, h⟩ => ⟨x, List.mem_append_left _ hx, h⟩) fun ⟨x, hx, h⟩ => ⟨x, List.mem_append_right _ hx, h⟩
    have hroom := fsp_dist fm; have := fm.room; have := fm.n32
    refine bi_seg (seg_of_eff he (by omega) (by omega) fun y hy hb => ?_) (fun y hy hb => ?_) fun y hy hb => ?_
    · obtain ⟨q, hq, hy⟩ := hy
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hcode y ⟨_, List.mem_singleton_self _, hy⟩ hb).1
      have hc : ∀ l, (∀ r ∈ l, r ∈ (cE a).io.rd ++ (cE a).io.wr) → rgnsC ((cE a).reg p) l = rgnsC (σv c (G.fsp c) σ') l :=
        fun l hl => rgnsC_congr fun r hr => by
          have := hrw r (hl r hr)
          exact rgnC_congr (hreg _ this.1) fun j hj => hlen' j (hj ▸ this.2)
      rcases List.mem_append.mp hq with hq | hq
      · rw [hc _ fun r h => List.mem_append_left _ h] at hq
        exact rgns_above fm hH hrd hro ⟨q, hq, hy⟩ hb
      · rw [hc _ fun r h => List.mem_append_right _ h] at hq
        exact rgns_above fm hH hwr hwo ⟨q, hq, hy⟩ hb
    · rcases hy with hy | ⟨x, hx, hy⟩
      · exact .inr (hcode y hy hb).2
      obtain ⟨sx, hs⟩ := (All2.ex (mapM_forall₂ hsrc)).1 x hx
      refine src_ext fm hH hs ?_ hb
      by_cases hw : x.2.2 = .view .rw
      · obtain ⟨r, off, i⟩ := x; simp only at hw; subst hw; simp [CalleeS.iniIn, Kd.sz, Region] at hy
      have hi := (hins x hx).resolve_left hw
      rw [← hreg _ hi.1]
      obtain ⟨r, off, i⟩ := x
      cases i with
      | raw l => rw [show Kd.ini c (G.fsp c) ((In.raw l).kd (σv c (G.fsp c) σ')) = l.val ((cE a).reg p) from (hlen l hi.2).symm]; exact hy
      | view k =>
        cases k with
        | ctx n =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
          obtain ⟨-, ⟨⟨⟨rfl, rfl⟩, hn0⟩, hn⟩⟩ := hi
          have : ctxIn (cE a) st.Γ σ' = n := by simp [ctxIn, hn0, hn]
          simp only [CalleeS.iniIn, hcnt, this] at hy
          show Region _ (ctxBuf + slen c (G.fsp c) n % 128) y
          rwa [Nat.mod_mod_of_dvd _ (by decide)] at hy
        | _ => exact hy
    · obtain ⟨pv, hpv, hy⟩ := hy
      rcases List.mem_append.mp hpv with hpv | hpv
      · obtain ⟨x, hx, hxp⟩ := (All2.ex (mapM_forall₂ hcr)).2 pv hpv
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hxp
        simp only [coEok, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcok
        obtain ⟨hx1, hx2⟩ := hcok x hx
        refine .inr (.inr (.inr ⟨x, hx, ?_⟩))
        dsimp only at hy
        rw [← locOf_addr hH hl, ← hreg _ hx1] at hy
        obtain ⟨r, off, k⟩ := x
        cases k with
        | ctx _ => simp at hx2
        | _ => exact hy
      rcases List.mem_append.mp hpv with hpv | hpv
      · obtain ⟨x, hx, hxp⟩ := (All2.ex (mapM_forall₂ hout)).2 pv hpv
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hxp
        have ho := houts x hx
        refine .inr (.inr (.inl ⟨x, hx, ?_⟩))
        dsimp only at hy
        rw [← locOf_addr hH hl, ← hreg _ ho.1] at hy
        obtain ⟨r, off, k⟩ := x
        cases k with
        | ctx n =>
          have ho2 := ho.2
          cases hl' : rawSVs σ' (cE a).io.ins with
          | none => simp [hl'] at ho2
          | some l' =>
          simp only [hl', Option.any_some, beq_iff_eq] at ho2; subst ho2
          have hraw := raw_slen (c := c) (sp := G.fsp c) (f := (cE a).reg p) hl' fun x hx j hj =>
            hlen' j (by
              have := ((hins x hx).resolve_left (by rw [hj]; intro h; cases h)).2; rw [hj] at this; exact this)
          show Region _ (ctxBuf + ((cE a).cnt p + rawSum ((cE a).reg p) (cE a).io.ins) % 128) y
          simp only [Kd.ini, slen_append] at hy
          rw [hcnt, ← hraw, Nat.add_mod (_ % _), Nat.mod_mod_of_dvd _ (by decide), ← Nat.add_mod]; exact hy
        | _ => exact hy
      · exact .inl ⟨pv, keep_sub _ hpv, hy⟩
  · simp at hty

/-- **A status call**: the call, `cmp r0, #0` and the test. On status `d = true` the views of the
outputs `co` join the call's; on the exit edge the callee's own effect holds. -/
theorem zcall_gp {Rs : Rels} {a : A} {ad : AdX Rs (cb := ‹CodeBytes B BS›) (cE a)} (z : ZSt Rs ad) {st s1 : St}
    {as : List (LowReg × Ld)} {o T : Nat}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some s1) (hok : (Op.call a as : Op A Bk).eok cE bE G st = true)
    {cl : List (Loc × Kd)} (hcr : coRes (regsOf st.Γ st.σ as) z.co = some cl) (hcok : coEok (cE a) z.co = true)
    {xw : List Word} (hpp : ad.ppre (xcallPub G c st as (cE a) xw)) {d : Bool}
    (hd : z.okp (xcallPub G c st as (cE a) xw) = d) {Ψk Ψx : TrP} {J : Ef → Prop}
    (hΨk : d = true → GP sp0 n (BI c G sp0 n X0 (addViews s1 cl)) Ψk J)
    (hΨx : d = false → GP sp0 n (BI c G sp0 n X0 { s1 with σ := σsp, ρ := [] }) Ψx J) :
    GP sp0 n (BI c G sp0 n X0 st) (xcallTr G c o as (cE a).entry (ad.T c.base (xcallPub G c st as (cE a) xw))
      (tstTr G c (o + (Op.call a as : Op A Bk).size cE bE) [.cmpImm 0 0] NE T d Ψk Ψx)) J := by
  cases d
  · exact xcall_gp fm hcode hty hok (co := []) (cl := []) rfl rfl (CalleeS.eff_withCo_nil (ad.ef c.base _ hpp)) (tst_gp fm rfl (fun h => by cases h)
      fun _ => GP.pre (fun _ h => BI.dropViews h) (hΨx rfl))
  · exact xcall_gp fm hcode hty hok hcr hcok (z.cef c.base _ hpp hd) (tst_gp fm rfl
      (fun _ => GP.pre (fun _ h => BI.addViews h) (hΨk rfl)) fun h => by cases h)

end call

end

end M0Crypto.Release.Ed25519CallProg
