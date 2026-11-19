import M0Crypto.Release.Ed25519CallProgCallee
import M0Crypto.Release.Ed25519CallProgStitch

set_option linter.unusedSimpArgs false

/-!
# Call programs: callees whose body is given

A callee of the `emit_fn` form whose body is not one call program (a body stitched from programs
and status calls) takes its frame from `CalleeP`: `push {lr}`, `sub sp`, the body of `bsz` bytes,
`add sp`, `pop {pc}`. The frame's data are a `CalleeP`'s, whose program `P` is not read here.
`runW`, `effW` and `teW` are the call lemma, the effect and the trace with its property, from
the body's: a run from the body's start to the epilogue with the trace `Ψ` and the result `Post`,
and the body's effect from the frame's invariant. The routine is `CalleeP.RW` with `Post` and the
entry premise `xpre`; the public values are `pub`.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry InStackWindow)
open M0Crypto.Sym (SExpr)

namespace CalleeP
variable {A Bk : Type} (q : CalleeP A Bk)

/-- The epilogue after a body of `bsz` bytes. -/
def epiW (bsz : Nat) : Nat := q.body + bsz

/-- The frame's trace around the body's trace `Ψ`. -/
def frTrW (bsz : Nat) (base : Word) (Ψ : TrP) : TrP :=
  if q.k2 = 0 then
    Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 2), .subSp (BitVec.ofNat 7 q.k1), []⟩])
      (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 (q.epiW bsz), .addSp (BitVec.ofNat 7 q.k1), []⟩]))
  else
    Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 2), .subSp (BitVec.ofNat 7 q.k1), []⟩])
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.s.entry + 4), .subSp (BitVec.ofNat 7 q.k2), []⟩])
        (Tr.cat Ψ (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (q.epiW bsz), .addSp (BitVec.ofNat 7 q.k1), []⟩])
          (Tr.is [⟨base + BitVec.ofNat 32 (q.epiW bsz + 2), .addSp (BitVec.ofNat 7 q.k2), []⟩]))))

/-- **The trace** at public values `p` around the body's trace `Ψ`. -/
def trW (bsz : Nat) (base : Word) (p : Nat → Word) (Ψ : TrP) : TrP :=
  let sp := q.s.reg p 13
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 q.s.entry, .push 0 true,
      wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩])
    (Tr.cat (q.frTrW bsz base Ψ)
      (Tr.is [⟨base + BitVec.ofNat 32 (q.epiW bsz + q.pro), .pop 0 true,
        wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩]))

/-- **The frame's decided checks.** -/
def okF : Bool :=
  q.sc.all q.scOk && q.top % 4 == 0 && decide (q.top / 4 < 255) && decide (4 + q.top ≤ q.s.stack) &&
  q.s.entry % 2 == 0 && PubW.r 13 ∈ q.s.pubs && q.xr.all q.xOk &&
  q.pr.all (fun r => r.val < 13 && PubW.r r ∈ q.s.pubs)

/-- **The frame's decided code checks** after a body of `bsz` bytes. -/
def codeOkW (bsz : Nat) (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Bool :=
  seqAt B q.s.entry (.push 0 true :: q.ks.map fun k => .subSp (BitVec.ofNat 7 k)) &&
  seqAt B (q.epiW bsz) (q.ks.map (fun k => .addSp (BitVec.ofNat 7 k)) ++ [.pop 0 true]) &&
  rangesSub [(q.s.entry, q.s.entry + 2 + q.pro), (q.epiW bsz, q.epiW bsz + 2 + q.pro)] q.s.code &&
  decide (q.epiW bsz + 2 + q.pro ≤ BS) && q.epiW bsz % 2 == 0 &&
  q.cb.all (fun x => x.1 % 4 == 0 && decide (0 < x.2) && decide (x.1 + x.2 ≤ BS))

variable {q}

theorem okF_parts (h : q.okF = true) : OkF q := by
  simp only [okF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun r hr => by simpa using h7 r hr, h0⟩

theorem codeOkW_cb {bsz : Nat} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (hc : q.codeOkW bsz B BS = true) :
    ∀ x ∈ q.cb, x.1 % 4 = 0 ∧ 0 < x.2 ∧ x.1 + x.2 ≤ BS := by
  simp only [codeOkW, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  exact fun x hx => and_assoc.1 (hc.2 x hx)

/-- The registers among the public values with extra values. -/
theorem reg_pubX {s : CalleeS} {xp : State → List Word} {st : State} {r : Reg} (h : PubW.r r ∈ s.pubs) :
    s.reg (s.pubX xp st) r = st.regs r := by
  have hl := List.idxOf_lt_length_of_mem h
  simp only [CalleeS.reg, CalleeS.pubX, pubOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hl), ← List.getD_eq_getElem?_getD]
  exact getD_idxOf (PubW.get st) 0 h

/-! ## The run -/

section run
variable {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels}

/-- **The callee's call lemma** with the frame's trace around the body's trace `Ψ`, from the
body's run: from the body's start with the program state `q.st0`, to the epilogue with the
result `Post`, within the body's geometry. -/
theorem runW {bsz : Nat} {Post : State → Mem → Word → Prop} {xpre : Word → State → Prop}
    {pub : Word → State → Nat → Word} {Ψ : Word → (Nat → Word) → TrP} (ho : OkF q)
    (hc : q.codeOkW bsz B BS = true) (hpub : ∀ base s r, PubW.r r ∈ q.s.pubs → q.s.reg (pub base s) r = s.regs r)
    (hbody : ∀ base s, (q.RW Post xpre).Entry base s → ∀ t : State,
      GeoOk (q.ctx base (pub base s)) q.geo (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr)
        (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd) →
      Caller base (q.ctx base (pub base s)).sp0 q.geo.N (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr) →
      Sub [codeR base] (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd) →
      At Rs B (q.ctx base (pub base s)) q.geo t.mem q.body q.st0 (fun _ => .none) t →
      (∀ i (x : XInfo), q.geo.xs[i]? = some x → x.r = true →
        ∀ y, Has (x.rgns (q.ctx base (pub base s)) i) y → t.mem y = s.mem y) →
      ReachFT base (PcIn base q.geo.cs) (Has (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd))
        (Has (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr))
        (InStackWindow (q.ctx base (pub base s)).sp0 q.geo.N) t
        (fun u => u.pc = base + BitVec.ofNat 32 (q.epiW bsz) ∧ u.regs 13 = t.regs 13 ∧ Post s u.mem (u.regs 0))
        (Ψ base (pub base s)))
    (base : Word) (s : State) (e : (q.RW Post xpre).Entry base s) :
    ReachFT base (PcIn base q.s.code) ((q.RW Post xpre).RdP base s) ((q.RW Post xpre).WrP s)
      ((q.RW Post xpre).SpP s) s ((q.RW Post xpre).Ret s) (q.trW bsz base (pub base s) (Ψ base (pub base s))) := by
  have h13 := hpub base s 13 ho.p13
  have hcb := codeOkW_cb hc
  have g := geoOk ho hcb (hpub base s) e
  simp only [codeOkW, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hen, hep⟩, hrs⟩, hBS⟩, he2⟩, -⟩ := hc
  have n0 : 4 * nSaved 0 = 4 := by decide
  have hst := ho.stk; have hroom : q.s.stack ≤ (s.regs 13).toNat := e.room; have := (s.regs 13).isLt
  have hk12 := k12 ho; have hk1 := k1_lt (q := q); have hk2 := k2_lt ho
  have hsz : ∀ k, Instr.size (.subSp k) = 2 ∧ Instr.size (.addSp k) = 2 := fun _ => ⟨rfl, rfl⟩
  suffices hb : ∀ t : State, t.pc = base + BitVec.ofNat 32 q.body →
      t.regs 13 = s.regs 13 - 4#32 - BitVec.ofNat 32 q.top →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved 0 s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base ((q.RW Post xpre).PcP base) ((q.RW Post xpre).RdP base s)
        (Has (lowWin (q.RW Post xpre) 0 s :: (q.RW Post xpre).wr s)) ((q.RW Post xpre).SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 (q.epiW bsz) ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves 0 r → r ∉ (q.RW Post xpre).clob → u.regs r = s.regs r) ∧
          (q.RW Post xpre).Post s u.mem (u.regs 0))
        (Ψ base (pub base s)) by
    unfold trW frTrW
    by_cases hk : q.k2 = 0
    · have hpro : q.pro = 2 := by simp [pro, ks_one hk]
      rw [ks_one hk] at hen hep
      simp only [seqAt, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, (hsz _).1, (hsz _).2, show Instr.size (.push 0 true) = 2 from rfl] at hen hep
      obtain ⟨⟨hpush, -⟩, ⟨hsub, -⟩, -⟩ := hen
      obtain ⟨⟨hadd, -⟩, ⟨hpop, -⟩, -⟩ := hep
      rw [hpro] at hrs hBS
      rw [ite_eq_left hk, hpro]
      have hent : q.s.entry + 4 ≤ BS := by simp only [epiW, body, hpro] at hBS; omega
      refine ReachFT.frameK (f := q.RW Post xpre) (mask := 0) (k := q.k1) (by decide) hpush hsub hadd hpop ho.e2 he2 hBS hent
        hrs hk1 (by rw [n0]; show 4 + 4 * q.k1 ≤ q.s.stack; omega) e h13.symm
        fun t tpc t13 tr hm hcd => hb t ?_ ?_ tr hm hcd
      · rw [tpc]; simp only [body, hpro]; rfl
      · rw [t13, ← sub_sub_ofNat, fsp_eq1 ho hk]
    · have hpro : q.pro = 4 := by simp [pro, ks_two hk]
      rw [ks_two hk] at hen hep
      simp only [seqAt, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, (hsz _).1, (hsz _).2, show Instr.size (.push 0 true) = 2 from rfl,
        Nat.add_assoc] at hen hep
      obtain ⟨⟨hpush, -⟩, ⟨hsub, -⟩, ⟨hsub2, -⟩, -⟩ := hen
      obtain ⟨⟨hadd, -⟩, ⟨hadd2, -⟩, ⟨hpop, -⟩, -⟩ := hep
      rw [hpro] at hrs hBS
      rw [ite_eq_right hk, hpro]
      have hent : q.s.entry + 6 ≤ BS := by simp only [epiW, body, hpro] at hBS; omega
      refine ReachFT.frameK2 (f := q.RW Post xpre) (mask := 0) (k1 := q.k1) (k2 := q.k2) (by decide) hpush hsub hsub2
        hadd hadd2 hpop ho.e2 he2 (by omega) hent hrs hk1 hk2
        (by rw [n0]; show 4 + 4 * q.k1 + 4 * q.k2 ≤ q.s.stack; omega) e
        h13.symm fun t tpc t13 tr hm hcd => hb t ?_ ?_ tr hm hcd
      · rw [tpc]; simp only [body, hpro]; rfl
      · rw [t13, ← sub_sub_ofNat, ← sub_sub_ofNat, fsp_eq2 ho]
  intro t tpc t13 tr hm hcd
  have F := Caller.of_entry (mask := 0) e
  have F' : Caller (q.ctx base (pub base s)).base (q.ctx base (pub base s)).sp0 q.geo.N
      (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr) :=
    ⟨F.b4, g.sp4, g.room, F.codeW, F.code32⟩
  have hf : t.regs 13 = q.geo.fsp (q.ctx base (pub base s)) := by
    rw [t13]; simp only [Geo.fsp, ctx, geo, h13]
  have hH : Holds (q.ctx base (pub base s)) (q.geo.fsp (q.ctx base (pub base s))) q.σ0 t.regs :=
    holds_σ0 ho (fun r h1 hp => by rw [tr r (by omega) (by omega), hpub base s _ hp]) hf
  have hrd : ∀ i (x : XInfo), q.geo.xs[i]? = some x → x.r = true →
      ∀ y, Has (x.rgns (q.ctx base (pub base s)) i) y → t.mem y = s.mem y := by
    intro i x hi hr y hy
    have hsv : Sub [saved 0 s] [(q.RW Post xpre).win s] := by
      have := sub_toNat (a := s.regs 13) (k := 4) (by omega)
      have := sub_toNat (a := s.regs 13) (k := q.s.stack) hroom
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by simp only [saved, Routine.win, RW, n0]; omega,
        by simp only [saved, Routine.win, RW, n0]; omega, by simp only [Routine.win, RW]; omega⟩
    rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
    rotate_left
    · obtain ⟨q', hq, hy⟩ := hy
      simp only [XInfo.rgns, XLen.v, show q.cb[j].2 ≠ 0 by have := (hcb _ (List.getElem_mem hj)).2.1; omega, ↓reduceIte,
        List.mem_singleton] at hq; subst hq
      have hN := CodeBytes.lt (B := B); have := (hcb _ (List.getElem_mem hj)).2.2
      rw [ctx_code hj] at hy
      exact hm y (Sep.not_has (Sub.sep hsv fun r hr => e.sepCode.symm r (by
        rw [List.mem_singleton] at hr; exact hr ▸ List.mem_cons_self)) · ⟨_, List.mem_singleton_self _,
        Rgn.of_region (region_in (rgn_region hy (by omega)) this hN)⟩)
    obtain ⟨h, L, rfl, hL, h0, -, -, hpub', -, -, -, hR, -⟩ := buf_of ho hi
    rw [rgns_eq hL h0 (by rw [ctx_ptr h, hpub base s _ hpub'])] at hy
    exact hm y (Sep.not_has (Sub.sep hsv e.sepRd.symm) · ⟨_, rgnC_mem (hR hr) h0, by
      obtain ⟨q', hq', hy⟩ := hy; simp only [List.mem_singleton] at hq'; exact hq' ▸ hy⟩)
  have hxv : ∀ p ∈ q.geo.xv, p.2.Bnd (bytesAt t.mem ((q.ctx base (pub base s)).ptr p.1) 32) := by
    rintro ⟨i, k⟩ hi
    have hk := ho.sc _ hi
    unfold scOk at hk
    cases hxi : q.xr[i]? with
    | none => simp [hxi] at hk
    | some x =>
      simp only [hxi, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨⟨-, hr⟩, hl⟩, -⟩ := hk
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hxi
      cases hL : q.xr[i].2.len with
      | p _ => simp [hL] at hl
      | k L =>
        simp only [hL, decide_eq_true_eq] at hl
        have hg : q.geo.xs[i]? = some q.xr[i].2 := by
          simp [geo, List.getElem?_append_left, hlt]
        rw [bytesAt_congr (m2 := s.mem) (n := 32) (a := (q.ctx base (pub base s)).ptr i) fun k hk =>
          hrd i _ hg hr _ ⟨⟨(q.ctx base (pub base s)).ptr i, L⟩,
            (by rw [rgns_eq hL (by omega) rfl]; exact List.mem_singleton_self _), ⟨k, by show k < L; omega, rfl⟩⟩]
        have hpub' := (xOk_parts (ho.xs _ (List.getElem_mem hlt))).choose_spec.2.2.2.2.1
        have hb : k.Bnd (bytesAt s.mem (s.regs ((q.xr.map (·.1)).getD i 0)) 32) :=
          e.pre.1.2 (i, k) (show (i, k) ∈ q.sc from hi)
        rw [getD_fst hlt] at hb
        rw [ctx_ptr hlt, hpub base s _ hpub']; exact hb
  have hat : At Rs B (q.ctx base (pub base s)) q.geo t.mem q.body q.st0 (fun _ => .none) t :=
    ⟨tpc, hf, hcd, hH, ⟨fun p hp => by simp [st0] at hp, fun _ _ _ => rfl, hxv⟩, fun r h => by simp [st0] at h⟩
  refine ReachT.mono (hbody base s e t g F' (sub_one List.mem_cons_self F.code32) hat hrd)
    (fun x ev ⟨a1, a2, a3, a4⟩ => ⟨a1, a2, a3, ?_⟩)
    (fun u hu => ⟨hu.1, hu.2.1, fun r h4 h11 _ hK => absurd (Ed25519Routines.mem_hiRegs h4 h11) hK, hu.2.2⟩)
    fun _ h => h
  have := win_mono4 (sp := s.regs 13) (by simpa [ctx, h13] using a4)
  rwa [show 4 + q.geo.N = q.s.stack by simp only [geo]; omega] at this

end run

/-! ## The effect -/

section eff
variable {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS]

/-- The bytes `os` writes at public values `p`. -/
def woW (p : Nat → Word) (os : List (Reg × Nat × Kd)) (y : Word) : Prop := InR (pubSt q.s p) (os.filterMap outE) y

/-- **The body's end**: a program state whose views hold the outputs `os` gives the frame's
invariant after the body. -/
theorem outs_sir {st' : St} {os : List (Reg × Nat × Kd)} (ho : OkF q) (hos : ∀ x ∈ os, q.outOk st'.Γ x = true)
    {base : Word} {p : Nat → Word} {sp0 : Word} {n : Nat} {X0 : Word → Prop} {e : Ef}
    (h : BI (q.ctx base p) q.geo sp0 n X0 st' e) :
    SIR sp0 (q.geo.fsp (q.ctx base p)) (fun y => X0 y ∨ q.woW p os y ∧ BelowEntry sp0 n y) e := by
  have hH : Holds (q.ctx base p) (q.geo.fsp (q.ctx base p)) q.σ0
      (fun r => if r = 13 then q.geo.fsp (q.ctx base p) else q.s.reg p r) :=
    holds_σ0 ho (fun r h1 _ => by simp [show r ≠ 13 from fun e => absurd (e ▸ h1) (by decide)]) (by simp)
  refine ⟨h.sp, fun y hy => hy.elim (h.sv y) fun ⟨hw, hb⟩ => h.ex y ?_ hb, h.ab⟩
  obtain ⟨a, ha, o, ho', rfl⟩ := hw
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.1 ha
  obtain rfl := outE_eq q.s p he
  obtain ⟨h1, hk, l, k, hl, hm, -, hb⟩ := outOk_parts (hos x hx)
  refine ⟨_, hm, ?_⟩
  rw [← locOf_addr hH hl, ← Kd.ini_base, hb, Kd.ini_base, ini_eq (s := q.s) (p := p) hk]
  simp only [show x.1 ≠ 13 from fun e => absurd (e ▸ h1) (by decide), ↓reduceIte]
  exact region_lt ho'

/-- **The callee's effect** with the outputs of `s'` (the callee's, or with more outputs on a
status edge), at public values with `pp`, from the body's: from the frame's invariant at the
start, the trace `Ψ` reaches the frame's invariant with the outputs' bytes written. -/
theorem effW {bsz : Nat} {Ψ : Word → (Nat → Word) → TrP} {s' : CalleeS} {pp : (Nat → Word) → Prop} (ho : OkF q)
    (hc : q.codeOkW bsz B BS = true) (hps : s'.pubs = q.s.pubs) (hsk : s'.stack = q.s.stack)
    (hef : effOk s'.io q.fpE q.iniE (s'.io.outs.filterMap outE) = true)
    (hwf : subR (s'.io.outs.filterMap outE) q.fpE = true)
    (hΨ : ∀ base p, pp p → ∀ sp0 n X0, Frm (q.ctx base p) q.geo sp0 n X0 →
      (∀ y, Has [@codeR B BS _ base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (q.geo.fsp (q.ctx base p)) y ∧ X0 y) →
      GP sp0 n (BI (q.ctx base p) q.geo sp0 n X0 q.st0) (Ψ base p)
        (SIR sp0 (q.geo.fsp (q.ctx base p)) fun y => X0 y ∨ q.woW p s'.io.outs y ∧ BelowEntry sp0 n y))
    (base : Word) (p : Nat → Word) (hp : pp p) {tr : List Event} (h : q.trW bsz base p (Ψ base p) tr) :
    s'.Eff p base tr := by
  have e13 : s'.reg p 13 = q.s.reg p 13 := by simp only [CalleeS.reg, hps]
  refine CalleeS.eff_of (t := pubSt q.s p) ?_ hef (Nat.le_of_eq hsk.symm) fun r _ => by
    simp only [pubSt, CalleeS.reg, hps]
  rw [e13]
  refine effT_of_gp fun sp0 n U hroom hn hF hR => GP.is_of ?_ h
  have n0 : 4 * nSaved 0 = 4 := by decide
  have hst := ho.stk; have ht4 := ho.t4
  have hfs : q.geo.fsp (q.ctx base p) = q.s.reg p 13 - BitVec.ofNat 32 (4 + q.top) := by
    simp only [Geo.fsp, ctx, geo]; rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_ofNat]
  have hab : ∀ y, AtOrAboveSp sp0 (q.s.reg p 13) y → AtOrAboveSp sp0 (q.geo.fsp (q.ctx base p)) y :=
    fun y h => by rw [hfs]; exact above_sub h (by omega)
  have hd4 : (sp0 - (q.ctx base p).sp0).toNat = (sp0 - q.s.reg p 13).toNat + 4 := by
    show (sp0 - (q.s.reg p 13 - 4#32)).toNat = _
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, sub_sub_add, BitVec.toNat_add,
      BitVec.toNat_ofNat]; omega
  have fm : Frm (q.ctx base p) q.geo sp0 n
      (fun y => U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) := by
    refine ⟨by simp only [geo]; omega, hn, by simp only [geo]; omega, fun r hok hx y hy hb => ?_⟩
    have hcb := codeOkW_cb hc
    have hN := CodeBytes.lt (B := B)
    obtain ⟨i, x, L, hi, hL, hy', hacc⟩ := ex_rgn ho (fun x hx => by have := (hcb x hx).2.2; omega) hok hx hy
    rcases xs_cases hi with hi | ⟨j, hj, rfl, rfl⟩
    rotate_left
    · simp only [XLen.k.injEq] at hL; subst hL
      rw [ctx_code hj] at hy'
      have hy2 : Has [@codeR B BS _ base] y :=
        ⟨_, List.mem_singleton_self _, Rgn.of_region (region_in hy' (hcb _ (List.getElem_mem hj)).2.2 hN)⟩
      exact ⟨hab y (hF y (.inl hy2) hb), fun _ => .inl (hR y (.inl hy2) hb)⟩
    obtain ⟨hlt, L', rfl, hL', -, -, -, -, -, -, -, -, hbuf⟩ := buf_of ho hi
    obtain rfl : L = L' := XLen.k.inj (hL.symm.trans hL')
    rw [ctx_ptr hlt] at hy'
    refine ⟨hab y (hF y (.inr (inR_buf (List.getElem_mem hlt) hbuf hy')) hb), fun ha => .inl (hR y (.inr ?_) hb)⟩
    exact inR_buf (List.mem_filter.2 ⟨List.getElem_mem hlt, by rw [← hacc, ha]⟩) hbuf hy'
  have hB := hΨ base p hp sp0 n _ fm fun y hy hb => ⟨hab y (hF y (.inl hy) hb), .inl (hR y (.inl hy) hb)⟩
  have hk12 := k12 ho
  unfold trW frTrW
  by_cases hk : q.k2 = 0
  · rw [ite_eq_left hk]
    refine frameK_gp (mask := 0) (k := q.k1) (U := U)
      (R2 := fun y => (U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
        q.woW p s'.io.outs y ∧ BelowEntry sp0 n y) (k1_lt (q := q)) (by rw [n0]; omega)
      (by rw [fsp_eq1 ho hk]; exact GP.pre (fun q' hq => ⟨hq.hs, hq.ab, hq.r, fun y ⟨_, hp, _⟩ _ => by simp [st0] at hp⟩) hB)
      (fun y h => .inl (.inr h)) (fun y hy => hy.elim .inl fun h => .inr ⟨hF y (.inr (inR_sub hwf h.1)) h.2, .inr h⟩)
      fun y h => .inl (.inl h)
  · rw [ite_eq_right hk]
    refine frameK2_gp (mask := 0) (k1 := q.k1) (k2 := q.k2) (U := U)
      (R2 := fun y => (U y ∨ Region (q.s.reg p 13 - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y) ∨
        q.woW p s'.io.outs y ∧ BelowEntry sp0 n y) (k1_lt (q := q)) (k2_lt ho) (by rw [n0]; omega)
      (by rw [fsp_eq2 ho]; exact GP.pre (fun q' hq => ⟨hq.hs, hq.ab, hq.r, fun y ⟨_, hp, _⟩ _ => by simp [st0] at hp⟩) hB)
      (fun y h => .inl (.inr h)) (fun y hy => hy.elim .inl fun h => .inr ⟨hF y (.inr (inR_sub hwf h.1)) h.2, .inr h⟩)
      fun y h => .inl (.inl h)

end eff

/-! ## The trace with its property -/

section te
variable {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels}

/-- **The callee's call lemma with the property `E` of its trace**, from the body's run, the
body's trace being unique and existing at every public value, and `E` of the frame's trace. -/
noncomputable def teW {bsz : Nat} {Post : State → Mem → Word → Prop} {xpre : Word → State → Prop}
    {pub : Word → State → Nat → Word} {Ψ : Word → (Nat → Word) → TrP} {E : Word → (Nat → Word) → TrP}
    (ho : OkF q) (hc : q.codeOkW bsz B BS = true)
    (hpub : ∀ base s r, PubW.r r ∈ q.s.pubs → q.s.reg (pub base s) r = s.regs r)
    (hbody : ∀ base s, (q.RW Post xpre).Entry base s → ∀ t : State,
      GeoOk (q.ctx base (pub base s)) q.geo (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr)
        (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd) →
      Caller base (q.ctx base (pub base s)).sp0 q.geo.N (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr) →
      Sub [codeR base] (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd) →
      At Rs B (q.ctx base (pub base s)) q.geo t.mem q.body q.st0 (fun _ => .none) t →
      (∀ i (x : XInfo), q.geo.xs[i]? = some x → x.r = true →
        ∀ y, Has (x.rgns (q.ctx base (pub base s)) i) y → t.mem y = s.mem y) →
      ReachFT base (PcIn base q.geo.cs) (Has (codeR base :: (q.RW Post xpre).win s :: rgnsC s.regs q.s.io.rd))
        (Has (lowWin (q.RW Post xpre) 0 s :: rgnsC s.regs q.s.io.wr))
        (InStackWindow (q.ctx base (pub base s)).sp0 q.geo.N) t
        (fun u => u.pc = base + BitVec.ofNat 32 (q.epiW bsz) ∧ u.regs 13 = t.regs 13 ∧ Post s u.mem (u.regs 0))
        (Ψ base (pub base s)))
    (hu : ∀ b p, Tr.Uniq (Ψ b p)) (hx : ∀ b p, ∃ tr, Ψ b p tr)
    (hE : ∀ b p tr, q.trW bsz b p (Ψ b p) tr → E b p tr) : (q.RW Post xpre).TE pub E :=
  Routine.te_by (Φ := fun b p => q.trW bsz b p (Ψ b p)) (fun base s e => runW ho hc hpub hbody base s e)
    (fun b p => by have := hu b p; simp only [trW, frTrW]; split <;> uniq_tac)
    (fun b p => by have := hx b p; simp only [trW, frTrW]; split <;> ex_tac) hE

end te

end CalleeP

end M0Crypto.Release.Ed25519CallProg
