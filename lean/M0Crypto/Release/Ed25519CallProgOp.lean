import M0Crypto.Release.Ed25519CallProgPubSound
import M0Crypto.Release.RoutineBlock

set_option linter.unusedSimpArgs false

/-!
# Call programs: the construct rules

A callee enters a program through an adapter `Ad` (its routine and call lemma, the semantics of
its interface, and the lemmas that tie the routine's entry condition, footprints and result to the
interface); an inline block through `Bd`. `Op.bok` is the check of a construct that depends on the
code bytes. `op_run` is one refinement theorem for the constructs: from the static check, the code
check, the pieces in the code and the invariant `At`, the construct runs to its end with the
invariant of the state after it, with trace `Op.tr`.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Frame (Disj)

variable (Rs : Rels)

section br
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- `b tgt` at `o`: in the code ranges and the artifact, reaching `tgt`. -/
def bOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt : Nat) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (o + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 o + 4#32 + (brImm11 o tgt ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)

variable {base sp0 : Word} {N : Nat} {Wc Rc : List Rgn} {cs : List (Nat × Nat)}

theorem b_run (F : Caller base sp0 N Wc) {t : State} {Q : State → Prop} {Ψ : TrP} {o tgt d : Nat}
    (hok : bOk cs o tgt = true) (hi : seqAt B o [.b (brImm11 o tgt)] = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hd : d ≤ N)
    (k : ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N)
      (t.setReg 15 (base + BitVec.ofNat 32 tgt)) Q Ψ) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .b (brImm11 o tgt), []⟩]) Ψ) := by
  simp only [bOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨ho, hcs⟩, hsz⟩, ht⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  exact ReachT.b hb2 o tgt _ hpc ho (instrAt_of_seqAt hi) hsz ht
    ⟨by rw [hpc]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega)),
      fun y hy => absurd hy (writes_nil y), fun y hy => absurd hy (reads_nil y), ⟨d, hd, h13⟩⟩ k

end br

/-- A public value of a call at the callee's entry state. -/
def PubW.get (st : State) : PubW → Word
  | .r q => st.regs q
  | .n q => read32 st.mem (st.regs q)

/-- **A callee adapter**: the routine of a static callee, its call lemma with the public registers
of the callee, the semantics of its interface, and the lemmas that relate the routine to the
interface. The call lemma, with the trace `T` of the public values, is for the build's code `B`. -/
structure Ad (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] (s : CalleeS) where
  R : Routine
  entry : R.entry = s.entry
  code : R.code = s.code
  stack : R.stack = s.stack
  T : Word → (Nat → Word) → List Event
  hT : R.SpecT fun base st => Tr.is (T base (pubOf (s.pubs.map (PubW.get st))))
  sem : List V → List V
  pre : ∀ c sp base st vs, PreG s.io st.regs → PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs →
    R.Pre base st
  wr : ∀ st, R.wr st = rgnsC st.regs s.io.wr
  rd : ∀ st, R.rd st = rgnsC st.regs s.io.rd
  post : ∀ c sp st m r0 vs, PreV s.io c sp st.regs → InsRel Rs c sp s.io st vs → R.Post st m r0 →
    OutsRel Rs c sp s.io st m (sem vs)

/-- **A block adapter**: the semantics of an inline block's interface and its proof. -/
structure Bd (b : BlockS) where
  /-- The outputs' values, then the values of the registers `ro`. -/
  sem : List V → List V
  post : ∀ c sp (t : State) vs, PreG b.io t.regs → NoWrap b.io t.regs → PreV b.io c sp t.regs →
    InsRel Rs c sp b.io t vs → OutsRel Rs c sp b.io t (execAll b.g t).mem ((sem vs).take b.io.outs.length)
  rpost : ∀ c sp (t : State) vs, PreG b.io t.regs → NoWrap b.io t.regs → PreV b.io c sp t.regs →
    InsRel Rs c sp b.io t vs →
    ∀ i (h : i < b.io.ro.length), ((sem vs).drop b.io.outs.length)[i]? = some (.w ((execAll b.g t).regs b.io.ro[i]))

/-- The static callee as a routine (entry, code and stack only). -/
def CalleeS.toR (s : CalleeS) : Routine where
  entry := s.entry
  code := s.code
  stack := s.stack
  Pre := fun _ _ => True
  wr := fun _ => []
  rd := fun _ => []
  Post := fun _ _ _ => True

theorem siteOk_congr {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {f f' : Routine}
    (he : f.entry = f'.entry) (hc : f.code = f'.code) (hs : f.stack = f'.stack)
    (cs : List (Nat × Nat)) (g : List Instr) (o d N : Nat) (imm : BitVec 25) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) : siteOk cs f g o d N imm al wg rg = siteOk cs f' g o d N imm al wg rg := by
  simp only [siteOk, he, hc, hs]

/-- The length of a constant interface length. -/
def ALen.kv : ALen → Nat
  | .k n => n
  | .r _ => 0

/-- A block's regions as the register-relative regions of a glue check. -/
def SRgn.g (r : SRgn) : Reg × Word × Nat := (r.r, BitVec.ofNat 32 r.off, r.len.kv)

/-- The loads' regions: the frame, read from `sp`. -/
def ldsRg (G : Geo) : List (Reg × Word × Nat) := [(13, 0#32, G.top)]

/-- The byte that `ldrb rd, [rb, ri]` reads. -/
def ldbR (rb ri : LowReg) : M0Crypto.Sym.SExpr × Nat := (.add (.reg0 rb.toReg) (.reg0 ri.toReg), 1)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- **The code checks of a construct** at `o`. -/
def Op.bok (o : Nat) : Op A Bk → Bool
  | .call a as => siteOk G.cs (cE a).toR (ldsEmit as) o G.top G.N
      (blImm (o + seqSize (ldsEmit as)) (cE a).entry) [(13, 4)] [] (ldsRg G) &&
      traceOk (ldsEmit as) [13]
  | .blk b as => glueOk G.cs (ldsEmit as) o G.top G.N [(13, 4)] [] (ldsRg G) &&
      traceOk (ldsEmit as) [13] &&
      glueOk G.cs (bE b).g (o + seqSize (ldsEmit as)) G.top G.N
        ((bE b).io.al.map (·, 4) ++ (bE b).L.map (·, 1)) ((bE b).io.wr.map SRgn.g) ((bE b).io.rd.map SRgn.g) && traceOk (bE b).g (bE b).L &&
      (bE b).io.wr.all (fun r => decide (0 < r.len.kv)) && (bE b).io.rd.all (fun r => decide (0 < r.len.kv))
  | .spill r o' => glueOk G.cs [.strSp r (BitVec.ofNat 8 (o' / 4))] o G.top G.N [(13, 4)]
      [(13, BitVec.ofNat 32 o', 4)] [] && traceOk [.strSp r (BitVec.ofNat 8 (o' / 4))] [13]
  | .drop _ _ => true
  | .ld r (.C i e imm) => litOk G.cs o G.top G.N r (BitVec.ofNat 8 imm) &&
      glueOk G.cs [.addPc r] (o + 2) G.top G.N [(13, 4)] [] [] && traceOk [.addPc r] [13] &&
      (G.cd.lookup i).any fun s => Frame.codeWord (B := B) (litOff o (BitVec.ofNat 8 imm)) +
        BitVec.ofNat 32 (o + 6) == BitVec.ofNat 32 (s + e)
  | .ld r l => glueOk G.cs (l.emit r) o G.top G.N [(13, 4)] [] (ldsRg G) && traceOk (l.emit r) [13]
  | .pub g => glueOk G.cs g o G.top G.N [(13, 4)] [] (ldsRg G) && traceOk g [13]
  | .keep _ => true
  | .ldb rd rb ri => sglueOk G.cs [ldbI rd rb ri] o G.top G.N [ldbR rb ri] [] [ldbR rb ri] &&
      traceOk [ldbI rd rb ri] [rb.toReg, ri.toReg]
  | .isl pad n => bOk G.cs o (o + 2 + seqSize (islPad pad) + n)

end

/-! ## Footprint helpers -/

theorem sub_cons' {a : Rgn} {l g : List Rgn} (h1 : Sub [a] g) (h2 : Sub l g) : Sub (a :: l) g := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h1 r (List.mem_singleton_self _)
  · exact h2 r hr

theorem sub_flatMap {α : Type} {f : α → List Rgn} {g : List Rgn} {l : List α}
    (h : ∀ a ∈ l, Sub (f a) g) : Sub (l.flatMap f) g := by
  intro r hr
  obtain ⟨a, ha, hr⟩ := List.mem_flatMap.mp hr
  exact h a ha r hr

theorem sep_flatMap {α : Type} {f : α → List Rgn} {g : List Rgn} {l : List α}
    (h : ∀ a ∈ l, Sep (f a) g) : Sep (l.flatMap f) g := by
  intro r hr
  obtain ⟨a, ha, hr⟩ := List.mem_flatMap.mp hr
  exact h a ha r hr

theorem all2_comb {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {T : β → γ → Prop}
    (h : ∀ a b c, R a b → S a c → T b c) :
    ∀ {l : List α} {l1 : List β} {l2 : List γ}, All2 R l l1 → All2 S l l2 → All2 T l1 l2
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨a1, a2⟩, ⟨b1, b2⟩ => ⟨h _ _ _ a1 b1, all2_comb h a2 b2⟩

/-! ## The construct rules -/

theorem Op.size_call {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (a : A) (as : List (LowReg × Ld)) :
    (Op.call a as : Op A Bk).size cE bE = seqSize (ldsEmit as) + 4 := by
  simp [Op.size, Op.pieces, piecesSize]

/-- **The invariant at a construct** at offset `o`: pc, `sp`, code, the known registers and `Inv`. -/
def At (B : List (BitVec 8)) (c : Ctx) (G : Geo) (m0 : Mem) (o : Nat) (st : St) (E : Loc → V)
    (t : State) : Prop :=
  t.pc = c.base + BitVec.ofNat 32 o ∧ t.regs 13 = G.fsp c ∧ CodeAt t.mem c.base B ∧
  Holds c (G.fsp c) st.σ t.regs ∧ Inv Rs c G m0 st E t.mem ∧
  ∀ r ∈ st.ρ, r.val < 13 ∧ E (.rg r) = .w (t.regs r)

section run
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS}
variable (ads : ∀ a, Ad Rs B BS (cE a)) (bds : ∀ b, Bd Rs (bE b))
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (m0 : Mem)



theorem GeoOk.fsp4 (g : GeoOk c G Wc Rc) : (G.fsp c).toNat % 4 = 0 := by
  have := g.fsp_toNat; have := g.sp4; have := g.top4; have := g.room; have := g.top; omega

/-- A block's register output that the loads leave. -/
theorem lds_ρ {st : St} {E : Loc → V} {t : State} {as : List (LowReg × Ld)}
    (hρ : ∀ r ∈ st.ρ, r.val < 13 ∧ E (.rg r) = .w (t.regs r)) (hl : ldsRes st.Γ as = true) :
    ∀ r ∈ st.ρ, (regsOf st.Γ st.σ as).all (·.1 != r) = true → E (.rg r) = .w ((execAll (ldsEmit as) t).regs r) := by
  intro r hr hn
  obtain ⟨h13, he⟩ := hρ r hr
  simp only [ldsRes, Bool.and_eq_true, List.all_eq_true] at hl
  rw [he, (lds_run as t hl.1).2.1 r (fun e => absurd (e ▸ h13) (by decide)) fun a ha e => ?_]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hl.2 a ha)
  have := List.all_eq_true.mp hn (a.1.toReg, v) (List.mem_append_left _ (List.mem_filterMap.2 ⟨a, ha, by simp [hv]⟩))
  simp [e] at this

theorem setRg_at {E : Loc → V} {ro : List Reg} {ws : List V} {regs : Reg → Word}
    (h : ∀ i (h : i < ro.length), ws[i]? = some (.w (regs ro[i]))) {q : Reg} (hq : q ∈ ro) :
    setRg E ro ws (.rg q) = .w (regs q) := by
  simp only [setRg, hq, ↓reduceIte, h _ (List.idxOf_lt_length_of_mem hq), List.getElem_idxOf, Option.getD_some]

theorem setRg_ne {E : Loc → V} {ro : List Reg} {ws : List V} {l : Loc} (h : ∀ q, l ≠ .rg q) :
    setRg E ro ws l = E l := by
  cases l with
  | rg q => exact absurd rfl (h q)
  | _ => rfl

theorem inv_setRg {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m) (ro : List Reg) (ws : List V) :
    Inv Rs c G m0 st (setRg E ro ws) m := by
  refine ⟨fun p hp => ?_, hi.2⟩
  obtain ⟨hok, hr⟩ := hi.1 p hp
  obtain ⟨l, k⟩ := p
  cases l with
  | rg => simp [Kd.sr, SR.ok] at hok
  | _ => exact ⟨hok, hr⟩

/-- The frame, from `sp`, lies in the caller's read footprint. -/
theorem GeoOk.frame_rd (g : GeoOk c G Wc Rc) (t : State) (h13 : t.regs 13 = G.fsp c) :
    Sub (regions t (ldsRg G)) Rc := by
  refine sub_trans ?_ g.wR
  have := g.fsp_toNat; have := g.win_toNat; have := g.room; have := g.top; have := c.sp0.isLt
  intro r hr
  simp only [regions, ldsRg, List.map, List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩ <;>
    simp only [h13, BitVec.add_zero, Geo.win] at * <;> omega

theorem holds_sp {t : State} (h13 : t.regs 13 = G.fsp c) : Holds c (G.fsp c) σsp t.regs := by
  intro p hp
  simp only [σsp, List.mem_singleton] at hp; subst hp
  exact ⟨by decide, by simp [h13, SV.val]⟩

/-- After a block's instructions, `sp` and the registers they do not write hold. -/
theorem holds_blkσ {g : List Instr} {σ : List (Reg × SV)} {t : State} (hσ : Holds c (G.fsp c) σ t.regs)
    (h13 : (execAll g t).regs 13 = G.fsp c) : Holds c (G.fsp c) (blkσ g σ) (execAll g t).regs := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact holds_sp h13 p hp
  · obtain ⟨hp, hf⟩ := List.mem_filter.mp hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨h1, h2⟩ := hσ p hp
    refine ⟨h1, ?_⟩
    rw [execAll_regs_other g t p.1 (by omega) hf.2]; exact h2

theorem ctxAt_mem {Γ : List (Loc × Kd)} {σ : List (Reg × SV)} {r : Reg} {n : List SV}
    (h : ctxAt Γ σ r = some n) : ∃ l, locOf σ r 0 = some l ∧ (l, Kd.ctx n) ∈ Γ := by
  simp only [ctxAt, Option.bind_eq_some_iff] at h
  obtain ⟨l, hl, h⟩ := h
  obtain ⟨⟨l', k⟩, hm, hf⟩ := List.exists_of_findSome?_eq_some h
  cases k <;> simp at hf
  obtain ⟨h1, rfl⟩ := hf; subst h1; exact ⟨_, hl, hm⟩

/-- **The call rule**: a call's loads, `bl` and the callee, through its adapter. -/
theorem call_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    {a : A} {as : List (LowReg × Ld)} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.call a as : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.call a as : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.call a as : Op A Bk).size cE bE) st'
        ((Op.call a as : Op A Bk).ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 st E) u →
      piecesAt B (o + (Op.call a as : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.call a as : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  have ad := ads a
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hlds, hpub⟩, hstk⟩ := hc
    cases hr : ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
    | none => simp [hr] at hty
    | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at hty; subst hty
    simp only [Op.bok, Bool.and_eq_true] at hbok
    obtain ⟨hsite, htr⟩ := hbok
    have he := (ads a).entry
    rw [siteOk_congr (f' := (ads a).R) (by simp [CalleeS.toR, he]) (by simp [CalleeS.toR, (ads a).code])
      (by simp [CalleeS.toR, (ads a).stack]), ← he] at hsite
    have hl : ldsOk as = true := by simp only [ldsRes, Bool.and_eq_true] at hlds; exact hlds.1
    obtain ⟨l1, l2, -, l4⟩ := lds_run as t hl
    have hσ1 := lds_holds Rs hi hσ h13 hlds
    have h13x : (execAll (ldsEmit as) t).regs 13 = G.fsp c := by
      rw [l2 13 (by decide) (fun a _ => ne13), h13]
    generalize hs : atCall c.base (ads a).R (ldsEmit as) o t = s
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
    have hstk' : G.top + (ads a).R.stack ≤ G.N := by rw [(ads a).stack]; exact hstk
    have cw := g.cwin hstk'
    have hwin : (ads a).R.win s = ⟨G.fsp c - BitVec.ofNat 32 (ads a).R.stack, (ads a).R.stack⟩ := by
      simp [Routine.win, hs13]
    simp only [Op.pieces, List.cons_append, List.nil_append, ← he] at hp
    simp only [Op.tr]
    rw [← he]
    refine siteTK ((ads a).hT) F (ldsEmit as) [(13, 4)] [] (ldsRg G) hp hsite hpc (Hi.self t)
      h13 hcode ?_ (hs ▸ (ads a).pre c (G.fsp c) c.base s _ hpre hpv (by simp only [InsRel, hms]; exact hins))
      (traceAll_blockTr l4 htr hpc (by simp [h13])) ?_ fun u hpu _ h13u hcu hmu hpost hrest => ?_
    · -- the side conditions
      unfold SiteSides; rw [hs, hwin, (ads a).wr, (ads a).rd, hwr, hrd]
      refine ⟨⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩,
        sub_cons' (sub_trans cw.1 g.wW) (sub_flatMap fun w hw => ?_),
        sub_cons' hcR (sub_cons' (sub_trans cw.1 g.wR) (sub_flatMap fun w hw => ?_)),
        sep_flatMap fun w hw => cw.2 (hwok w hw).1, sep_flatMap fun w hw => cw.2 (hrok w hw).1⟩
      · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
      · have := g.sub (hwok w hw).1 true (hwok w hw).2; simpa using this
      · have := g.sub (hrok w hw).1 false (hrok w hw).2; simpa using this
    · -- the callee's public values
      rw [hs]
      congr 3
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
    · -- after the call
      rw [hs] at hmu hpost
      rw [hwin, (ads a).wr, hwr] at hmu
      have hpost' := (ads a).post c (G.fsp c) s u.mem (u.regs 0) _ hpv
        (by simp only [InsRel, hms]; exact hins) hpost
      rw [Op.size_call, ← Nat.add_assoc] at k
      refine k u ⟨hpu, h13u, hcu, holds_sp h13u, ?_, fun _ h => by simp [IoR.after] at h⟩ hrest
      simp only [Op.ev, hr, IoR.after]
      exact inv_after Rs g hi hstk' (fun w hw => (hwok w hw).1) (by simpa [regions] using hmu) σsp []
        (fun p hp => (hook p hp).1) hnd
        (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2) houts hpost')
  · simp at hty

/-- The invariant with fewer views and more written buffer regions. -/
theorem Inv.weaken {st st' : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m)
    (hΓ : ∀ p ∈ st'.Γ, p ∈ st.Γ) (hX : ∀ r ∈ st.X, r ∈ st'.X) : Inv Rs c G m0 st' E m :=
  ⟨fun p hp => hi.1 p (hΓ p hp), fun y hy hx => hi.2.1 y hy fun r hr => hx r (hX r hr), hi.2.2⟩

theorem memEq_cons0 {W : List Rgn} {m m' : Mem} (a : Word) (h : MemEq W m m') :
    MemEq (⟨a, 0⟩ :: W) m m' := fun y hy => h y fun hh => hy (by
      obtain ⟨q, hq, hyq⟩ := hh; exact ⟨q, List.mem_cons_of_mem _ hq, hyq⟩)

theorem regions_g {t : State} : ∀ {l : List SRgn}, (∀ r ∈ l, 0 < r.len.kv) →
    regions t (l.map SRgn.g) = rgnsC t.regs l
  | [], _ => rfl
  | r :: l, h => by
    have h1 := h r List.mem_cons_self
    have e := regions_g (t := t) (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [regions, List.map_cons, rgnsC, List.flatMap_cons] at e ⊢
    rw [e]
    obtain ⟨rr, off, len⟩ := r
    cases len with
    | r => simp [ALen.kv] at h1
    | k n =>
      simp only [ALen.kv] at h1
      simp [SRgn.g, SRgn.rgnC, ALen.val, ALen.kv, show n ≠ 0 by omega]

/-- **The no-wrap check**: a register holding a frame address with `n` bytes below the frame's
top from it keeps those bytes below `2 ^ 32`. -/
theorem nw_sound (g : GeoOk c G Wc Rc) {σ : List (Reg × SV)} {regs : Reg → Word}
    (hσ : Holds c (G.fsp c) σ regs) {io : Iface} (h : io.nw.all (nwOk G σ) = true) : NoWrap io regs := by
  intro p hp
  have hc := List.all_eq_true.mp h p hp
  simp only [nwOk] at hc
  cases hl : σ.lookup p.1 with
  | none => simp [hl] at hc
  | some v =>
    cases v <;> simp only [hl, Bool.false_eq_true, decide_eq_true_eq] at hc
    rw [(hσ.get hl).1, SV.val, g.fr_toNat (by omega)]
    have := g.room; have := g.top; have := c.sp0.isLt; omega

/-- **The block rule**: an inline block's loads and its instructions, through its adapter. -/
theorem blk_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {b : Bk} {as : List (LowReg × Ld)} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.blk b as : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.blk b as : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.blk b as : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.blk b as : Op A Bk).size cE bE) st'
        ((Op.blk b as : Op A Bk).ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 st E) u →
      piecesAt B (o + (Op.blk b as : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.blk b as : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
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
    · have hpost := (bds b).post c (G.fsp c) _ _ hpre (nw_sound g hσ1 hnw) hpv hins'
      rw [hwr', hwr] at hm2
      have e : o + (Op.blk b as : Op A Bk).size cE bE = o + seqSize (ldsEmit as) + seqSize (bE b).g := by
        simp [Op.size, Op.pieces, piecesSize, Nat.add_assoc]
      rw [e] at k
      refine k _ ⟨hpc2, h132, hc2, holds_blkσ hσ1 h132, ?_, fun q hq => ⟨?_, ?_⟩⟩ hp3
      · simp only [Op.ev, hr, IoR.after]
        have hi' : Inv Rs c G m0 st E (execAll (ldsEmit as) t).mem := by rw [l1]; exact hi
        exact inv_setRg Rs m0 (inv_after Rs g hi' (sw := 0) (by have := g.top; omega) (fun w hw => (hwok w hw).1)
          (memEq_cons0 _ hm2) _ (bE b).io.ro (fun p hp => (hook p hp).1) hnd
          (all2_comb (fun x p v h1 h2 => by rw [← h1.1, h1.2]; exact h2)
            (ioRes_sound Rs g hi hσ1 (lds_ρ hρ hlds) hr).2.2.2.1 hpost)) _ _
      · simpa using List.all_eq_true.mp hro q hq
      · simp only [Op.ev, hr]
        exact setRg_at ((bds b).rpost c (G.fsp c) _ _ hpre (nw_sound g hσ1 hnw) hpv hins') hq
  · simp at hty

theorem updOuts_single (E : Loc → V) (l : Loc) (k : Kd) : updOuts E [(l, k)] [E l] = E := by
  funext x; simp only [updOuts]; split <;> simp_all

/-- **The spill rule**: `str r, [sp, #o']` makes the frame word a view of `r`'s public value; the
flags stay. -/
theorem spill_runF (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {r : LowReg} {o' o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.spill r o' : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.spill r o' : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.spill r o' : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.spill r o' : Op A Bk).size cE bE) st' E u →
      (∀ cc, condPassed cc u = condPassed cc t) →
      piecesAt B (o + (Op.spill r o' : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.spill r o' : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  simp only [Op.ty] at hty
  cases hv : st.σ.lookup r.toReg with
  | none => simp [hv] at hty
  | some v =>
  simp only [hv] at hty
  split at hty
  · rename_i hs
    simp only [Option.some.injEq] at hty; subst hty
    simp only [slotOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
    obtain ⟨⟨h4, htop⟩, h1020⟩ := hs
    simp only [Op.bok, Bool.and_eq_true] at hbok
    obtain ⟨hg, htr⟩ := hbok
    simp only [Op.pieces, List.cons_append, List.nil_append] at hp
    obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
    simp only [Piece.instrs, Piece.size] at hp1 hp2
    have hsr : SR.ok G ⟨.fr o', .k 4⟩ = true := by simp [SR.ok]; omega
    have hrg : regions t [(13, BitVec.ofNat 32 o', 4)] = SR.rgns G c ⟨.fr o', .k 4⟩ := by
      simp [regions, SR.rgns, XLen.v, Loc.addr, h13]
    simp only [Op.tr]
    refine ReachFT.glue F _ [(13, 4)] _ [] hp1 hpc h13 hcode
      ⟨fun p hp => ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩
      (traceAll_blockTr (by rfl) htr hpc (by simp [h13])) (fun hpc1 h131 hc1 hm1 => ?_) hg
    · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
    · rw [hrg]; simpa using g.sub hsr true rfl
    · have hx : ∀ q : Reg, q ≠ 15 →
          (execAll [.strSp r (BitVec.ofNat 8 (o' / 4))] t).regs q = t.regs q := by
        intro q hq; simp [execAll, Instr.next, Instr.exec, State.setReg, hq]
      have hmem : (execAll [.strSp r (BitVec.ofNat 8 (o' / 4))] t).mem =
          write32 t.mem (G.fsp c + BitVec.ofNat 32 o') (t.regs r.toReg) := by
        have e : o' / 4 % 256 * 4 = o' := by omega
        simp [execAll, Instr.next, Instr.exec, State.setReg, State.sp, h13, e, State.reg]
      have e : o + (Op.spill r o' : Op A Bk).size cE bE = o + seqSize [.strSp r (BitVec.ofNat 8 (o' / 4))] := by
        simp [Op.size, Op.pieces, piecesSize]
      rw [e] at k
      refine k _ ⟨hpc1, h131, hc1, fun p hp => ?_, ?_, fun q hq => ⟨(hρ q hq).1, by
        rw [hx q fun e => absurd (e ▸ (hρ q hq).1) (by decide)]; exact (hρ q hq).2⟩⟩
        (fun cc => by rw [condPassed_fl, condPassed_fl]; simp [execAll, Instr.next, Instr.exec, State.setReg]) hp2
      · obtain ⟨h14, hv'⟩ := hσ p hp
        exact ⟨h14, by rw [hx p.1 (fun h => absurd (h ▸ h14) (by decide)), hv']⟩
      · rw [hrg] at hm1
        have := inv_after Rs g hi (sw := 0) (by have := g.top; omega) (ws := [⟨.fr o', .k 4⟩])
          (fun w hw => by simp at hw; subst hw; exact hsr) (memEq_cons0 _ (by simpa using hm1)) st.σ st.ρ
          (outs := [(.fr o', .pw v)]) (vs := [E (.fr o')]) (fun p hp => by simp at hp; subst hp; exact hsr)
          (by simp) ⟨by
            simp only [Rel, Loc.addr, hmem, M0Crypto.Armv6M.read32_write32_same]
            exact (hσ.get hv).1, trivial⟩
        rw [updOuts_single] at this
        exact Inv.st Rs (by simp) (by simp [Loc.isEx]) this
  · simp at hty

theorem spill_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {r : LowReg} {o' o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.spill r o' : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.spill r o' : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.spill r o' : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.spill r o' : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.spill r o' : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.spill r o' : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) :=
  spill_runF Rs ads m0 g F hty hbok hp hat fun u hu _ hr => k u hu hr

/-- **The drop rule**: the views on the bytes end; no code. -/
theorem drop_run {o' n o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.drop o' n : Op A Bk).ty cE bE G st = some st')
    (hp : piecesAt B o ((Op.drop o' n : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.drop o' n : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.drop o' n : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.drop o' n : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  simp only [Op.ty, Option.some.injEq] at hty; subst hty
  have e : (Op.drop o' n : Op A Bk).size cE bE = 0 := rfl
  rw [e, Nat.add_zero] at k
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  exact k t ⟨hpc, h13, hcode, hσ, Inv.weaken Rs m0 hi (fun p hp => by
    simp only [dropViews, keepViews, List.mem_filter] at hp; exact hp.1) (fun r hr => hr), hρ⟩ (by simpa [Op.pieces] using hp)

/-- **The keep rule**: the views at the locations, in their order; no code. -/
theorem keep_run {ls : List Loc} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.keep ls : Op A Bk).ty cE bE G st = some st')
    (hp : piecesAt B o ((Op.keep ls : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.keep ls : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.keep ls : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.keep ls : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  simp only [Op.ty] at hty
  obtain ⟨Γ', hΓ, rfl⟩ := Option.map_eq_some_iff.mp hty
  have e : (Op.keep ls : Op A Bk).size cE bE = 0 := rfl
  rw [e, Nat.add_zero] at k
  obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
  exact k t ⟨hpc, h13, hcode, holds_sp h13, Inv.weaken Rs m0 hi (keepΓ_sub hΓ) (fun r hr => hr),
    fun r hr => absurd hr List.not_mem_nil⟩ (by simpa [Op.pieces] using hp)

/-- The state after a loader of its own: `r` holds `v`, the rest is as before. -/
theorem at_ld {o o' : Nat} {st : St} {E : Loc → V} {t u : State} {r : LowReg} {v : SV}
    (hat : At Rs B c G m0 o st E t) (hpc : u.pc = c.base + BitVec.ofNat 32 o') (hm : u.mem = t.mem)
    (hr : ∀ q : Reg, q ≠ 15 → q ≠ r.toReg → u.regs q = t.regs q) (hv : u.regs r.toReg = v.val c (G.fsp c)) :
    At Rs B c G m0 o' { st with σ := (r.toReg, v) :: st.σ.filter (·.1 != r.toReg), ρ := st.ρ.filter (· != r.toReg) }
      E u := by
  obtain ⟨-, h13, hcode, hσ, hi, hρ⟩ := hat
  refine ⟨hpc, by rw [hr 13 (by decide) ne13, h13], by rw [hm]; exact hcode, fun p hp => ?_, by rw [hm]; exact hi,
    fun q hq => ⟨(hρ q (List.mem_filter.mp hq).1).1, by
      rw [hr q (fun e => absurd (e ▸ (hρ q (List.mem_filter.mp hq).1).1) (by decide))
        (by simpa using (List.mem_filter.mp hq).2)]; exact (hρ q (List.mem_filter.mp hq).1).2⟩⟩
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by have := r.isLt; simp only [toReg_val]; omega, hv⟩
  · obtain ⟨hp, hne⟩ := List.mem_filter.mp hp
    obtain ⟨h14, hpv⟩ := hσ p hp
    exact ⟨h14, by rw [hr p.1 (fun h => absurd (h ▸ h14) (by decide)) (by simpa using hne), hpv]⟩

/-- **A loader through the frame**: its code, a glue block that reads the frame. -/
theorem ldg_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) {r : LowReg} {v : SV}
    {gs : List Instr} {o : Nat} {st : St} {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP}
    (hseq : seqAt B o gs = true)
    (hok : (glueOk G.cs gs o G.top G.N [(13, 4)] [] (ldsRg G) && traceOk gs [13]) = true)
    (hrun : (execAll gs t).mem = t.mem ∧ (∀ q : Reg, q ≠ 15 → q ≠ r.toReg → (execAll gs t).regs q = t.regs q) ∧
      (execAll gs t).regs r.toReg = v.val c (G.fsp c) ∧ gs.all Instr.falls = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + seqSize gs)
      { st with σ := (r.toReg, v) :: st.σ.filter (·.1 != r.toReg), ρ := st.ρ.filter (· != r.toReg) } E u →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (Tr.cat (Tr.is (blockTr gs (c.base + BitVec.ofNat 32 o) [13] [G.fsp c])) Ψ) := by
  have ⟨hpc, h13, hcode, _, _⟩ := hat
  simp only [Bool.and_eq_true] at hok
  refine ReachFT.glue F gs [(13, 4)] [] (ldsRg G) hseq hpc h13 hcode
    ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
    (traceAll_blockTr hrun.2.2.2 hok.2 hpc (by simp [h13])) (fun hpc1 _ _ _ => ?_) hok.1
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  · exact k _ (at_ld Rs m0 hat hpc1 hrun.1 hrun.2.1 hrun.2.2.1)

theorem addPc_run (r : LowReg) (u : State) : (execAll [.addPc r] u).mem = u.mem ∧
    (∀ q : Reg, q ≠ 15 → q ≠ r.toReg → (execAll [.addPc r] u).regs q = u.regs q) ∧
    (execAll [.addPc r] u).regs r.toReg = u.regs r.toReg + (u.pc + 4#32) := by
  refine ⟨by simp [execAll, Instr.next, Instr.exec, State.setReg], fun q h15 hq => ?_, ?_⟩
  · simp [execAll, Instr.next, Instr.exec, State.setReg, h15, hq]
  · simp [execAll, Instr.next, Instr.exec, State.setReg, State.reg, State.pc, ne15, Ne.symm ne15]

theorem lit_val (base w : Word) (o s e : Nat) (h : w + BitVec.ofNat 32 (o + 6) = BitVec.ofNat 32 (s + e)) :
    w + (base + BitVec.ofNat 32 (o + 2) + 4#32) = base + BitVec.ofNat 32 s + BitVec.ofNat 32 e := by
  have e : BitVec.ofNat 32 (o + 6) = BitVec.ofNat 32 (o + 2) + 4#32 := by
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
  rw [BitVec.add_assoc base (BitVec.ofNat 32 s), ← BitVec.ofNat_add, ← h, e]
  ac_rfl

/-- **The loader rule**: `r` receives the loader's symbolic value; `C` by its literal word. -/
theorem ld_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    {r : LowReg} {l : Ld} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.ld r l : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.ld r l : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.ld r l : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.ld r l : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.ld r l : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.ld r l : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  have ⟨hpc, h13, hcode, hσ, hi, _⟩ := hat
  have hsz : (Op.ld r l : Op A Bk).size cE bE = seqSize (l.emit r) := by simp [Op.size, Op.pieces, piecesSize]
  simp only [Op.pieces, List.cons_append, List.nil_append] at hp
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  rw [hsz] at k
  simp only [Op.ty, Option.map_eq_some_iff] at hty
  obtain ⟨v, hv, rfl⟩ := hty
  cases l
  case C i e imm =>
    simp only [ldSv] at hv
    split at hv
    · rename_i hs
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
      simp only [Option.some.injEq] at hv; subst hv
      simp only [Op.bok, Bool.and_eq_true, hs, Option.any_some, beq_iff_eq] at hbok
      obtain ⟨⟨⟨hlit, hg⟩, htr⟩, hw⟩ := hbok
      have h1 := hp1
      simp only [Ld.emit, seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have hs2 : seqAt B (o + 2) [.addPc r] = true := by
        simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact ⟨h1.2.1, trivial⟩
      simp only [Op.tr]
      refine ReachFT.lit F r (BitVec.ofNat 8 imm) h1.1.1 hpc (Hi.self t) h13 hcode hcR
        (fun u hu hpu _ h13u hcu => ?_) hlit
      refine ReachFT.glue F [.addPc r] [(13, 4)] [] [] hs2 hpu h13u hcu
        ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
        (traceAll_blockTr (by rfl) htr hpu (by simp [h13u, Geo.fsp])) (fun hpc2 _ _ _ => ?_) hg
      · simp only [List.mem_singleton] at hp; subst hp; rw [h13u]; exact g.fsp4
      · obtain ⟨a1, a2, a3⟩ := addPc_run r u
        have e2 : o + seqSize (Ld.emit r (.C i e imm)) = o + 2 + seqSize [.addPc r] := by
          simp [Ld.emit, seqSize, Instr.size]
        rw [e2] at k
        refine k _ (at_ld Rs m0 hat hpc2 (by rw [a1, hu]; rfl) (fun q h15 hq => ?_) ?_) (by rw [e2] at hp2; exact hp2)
        · rw [a2 q h15 hq, hu]; simp [litState, State.setReg, h15, hq]
        · rw [a3, hpu, hu]
          simp only [litState, State.setReg, ite_true, SV.val, g.cd i s hs]
          exact lit_val _ _ _ _ _ hw
    · simp at hv
  case A n =>
    cases hl : st.σ.lookup r.toReg with
    | none => simp [ldSv, hl] at hv
    | some w =>
      obtain ⟨a1, a2, a3⟩ := adds_run r n t
      have hw := (hσ.get hl).1
      cases w <;> simp only [ldSv, hl, reduceCtorEq, Option.some.injEq] at hv <;> subst hv <;>
        refine ldg_run Rs m0 g F hp1 hbok ⟨a1.1, a1.2, ?_, a3⟩ hat fun u hu => k u hu hp2 <;>
        simp only [Ld.emit, a2, hw, SV.val, BitVec.add_assoc, BitVec.ofNat_add]
  all_goals
    simp only [ldSv] at hv
    split at hv
    · rename_i hok
      obtain ⟨a1, a2, a3⟩ := Ld.run r hok t
      exact ldg_run Rs m0 g F hp1 hbok ⟨a1.1, a1.2, by rw [a2, h13, Ld.sv_mval Rs hi hv], a3⟩ hat
        fun u hu => k u hu hp2
    · simp at hv

theorem glueOk_falls {cs : List (Nat × Nat)} {gs : List Instr} {o d N : Nat} {al : List (Reg × Nat)}
    {wg rg : List (Reg × Word × Nat)} (h : glueOk cs gs o d N al wg rg = true) : gs.all Instr.falls = true := by
  simp only [glueOk, Bool.and_eq_true, and_assoc] at h; exact h.2.1

/-- The word views of the invariant hold at their frame words. -/
theorem inv_pw {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m) :
    ∀ o v, pwAt st.Γ o = some v → read32 m (G.fsp c + BitVec.ofNat 32 o) = v.val c (G.fsp c) :=
  fun _ _ h => by simpa [Rel, Loc.addr] using (hi.1 _ (pwAt_mem h)).2

/-- A test's decision from the known flags. -/
theorem dec_sound {r : PubR} {t : State} (hn : ∀ b, r.n = some b → t.n = b) (hz : ∀ b, r.z = some b → t.z = b)
    (hc : ∀ b, r.c = some b → t.c = b) (hv : ∀ b, r.v = some b → t.v = b) {cc : BitVec 4} {b : Bool}
    (h : r.dec cc = some b) : condPassed cc t = b := by
  simp only [PubR.dec] at h
  split at h
  · rename_i e1 e2 e3 e4
    simp only [Option.some.injEq] at h; subst h
    rw [condPassed_fl, hn _ e1, hz _ e2, hc _ e3, hv _ e4]
  · simp at h

/-- **A public block with its flags**: a glue block on registers; its registers hold the values
of `pubEval`, and its known flags decide the tests. -/
theorem pub_runF (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {gs : List Instr} {o : Nat} {st : St} {r : PubR} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hr : pubEval st.σ st.Γ gs = some r)
    (hbok : (Op.pub gs : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o (.seq gs :: rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + seqSize gs) { st with σ := r.σ, ρ := [] } E u →
      (∀ cc b, r.dec cc = some b → condPassed cc u = b) →
      piecesAt B (o + seqSize gs) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.pub gs : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  simp only [Op.bok, Bool.and_eq_true] at hbok
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at hp1 hp2
  obtain ⟨hpc, h13, hcode, hσ, hi, -⟩ := hat
  have hfa := glueOk_falls hbok.1
  obtain ⟨hm, hH, hn, hz, hc, hv⟩ := pubEval_sound hσ (inv_pw Rs m0 hi) hr hfa
  simp only [Op.tr]
  refine ReachFT.glue F gs [(13, 4)] [] (ldsRg G) hp1 hpc h13 hcode
    ⟨fun p hp => ?_, fun _ h => absurd h List.not_mem_nil, g.frame_rd t h13⟩
    (traceAll_blockTr hfa hbok.2 hpc (by simp [h13])) (fun hpc1 h131 hc1 _ => ?_) hbok.1
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  · exact k _ ⟨hpc1, h131, hc1, hH, Inv.st Rs rfl rfl (by rw [hm]; exact hi), fun _ h => by cases h⟩
      (fun _ _ h => dec_sound hn hz hc hv h) hp2

/-- **A public block**: a glue block on registers; its registers hold the values `Prog.ty` gives. -/
theorem pub_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {gs : List Instr} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.pub gs : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.pub gs : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.pub gs : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.pub gs : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.pub gs : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.pub gs : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  simp only [Op.ty] at hty
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hty
  have e : o + (Op.pub gs : Op A Bk).size cE bE = o + seqSize gs := by simp [Op.size, Op.pieces, piecesSize]
  rw [e] at k
  exact pub_runF Rs ads m0 g F hr hbok (by simpa [Op.pieces] using hp) hat fun u hu _ hr => k u hu hr

/-- `ldrb rd, [rb, ri]`: `rd` receives the byte at `rb + ri`, the rest stays. -/
theorem ldb_exec (rd rb ri : LowReg) (u : State) : (execAll [ldbI rd rb ri] u).mem = u.mem ∧
    (∀ q : Reg, q ≠ 15 → q ≠ rd.toReg → (execAll [ldbI rd rb ri] u).regs q = u.regs q) ∧
    (execAll [ldbI rd rb ri] u).regs rd.toReg = M0Crypto.Thumb.read8 u.mem (u.regs rb.toReg + u.regs ri.toReg) := by
  refine ⟨by simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, ldbI, State.setReg], fun q h15 hq => ?_, ?_⟩
  · simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, ldbI, State.setReg, h15, hq]
  · simp [execAll, Instr.next, Instr.exec, Instr.exec.memOp, ldbI, State.setReg, State.reg, ne15]

/-- A region of the frame lies in the caller's read footprint. -/
theorem GeoOk.frame_sub (g : GeoOk c G Wc Rc) {a n : Nat} (h : a + n ≤ G.top) :
    Sub [⟨G.fsp c + BitVec.ofNat 32 a, n⟩] Rc := by
  refine sub_trans ?_ g.wR
  have := g.fsp_toNat; have := g.win_toNat; have := g.room; have := g.top; have := c.sp0.isLt
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩ <;>
    simp only [Geo.win, BitVec.toNat_add, BitVec.toNat_ofNat] at * <;> omega

/-- **A byte load at a public offset**: `rd` receives the byte of the frame byte view there. -/
theorem ldb_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc)
    {rd rb ri : LowReg} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.ldb rd rb ri : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.ldb rd rb ri : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.ldb rd rb ri : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.ldb rd rb ri : Op A Bk).size cE bE) st'
        ((Op.ldb rd rb ri : Op A Bk).ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 st E) u →
      piecesAt B (o + (Op.ldb rd rb ri : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.ldb rd rb ri : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  simp only [Op.ty] at hty
  cases hl : ldbOff st.σ rb ri with
  | none => simp [hl] at hty
  | some a =>
  simp only [hl] at hty
  split at hty
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha, hs⟩ := hc
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
    simp only [Option.some.injEq] at hty; subst hty
    obtain ⟨o', j, hb, hj, rfl⟩ : ∃ o' j, st.σ.lookup rb.toReg = some (.sp o') ∧
        st.σ.lookup ri.toReg = some (.k j) ∧ a = o' + j := by
      simp only [ldbOff] at hl
      split at hl
      · rename_i o' j h1 h2; simp only [Option.some.injEq] at hl; exact ⟨o', j, h1, h2, hl.symm⟩
      · simp at hl
    have va : t.regs rb.toReg + t.regs ri.toReg = G.fsp c + BitVec.ofNat 32 (o' + j) := by
      rw [(hσ.get hb).1, (hσ.get hj).1]; simp only [SV.val]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [Op.bok, Bool.and_eq_true] at hbok
    simp only [Op.pieces, List.cons_append, List.nil_append] at hp
    obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
    simp only [Piece.instrs, Piece.size] at hp1 hp2
    have hfa : [ldbI rd rb ri].all Instr.falls = true := rfl
    simp only [Op.tr]
    refine ReachFT.sglue F [ldbI rd rb ri] [ldbR rb ri] [] [ldbR rb ri] hp1 hpc h13 hcode
      ⟨fun r h => by simp only [List.mem_singleton] at h; subst h; exact Nat.mod_one _,
        fun _ h => absurd h List.not_mem_nil, ?_⟩
      (traceAll_blockTr hfa hbok.2 hpc (by simp [σv, hb, hj, (hσ.get hb).1, (hσ.get hj).1]))
      (fun hpc1 h131 hc1 _ => ?_) hbok.1
    · simp only [sregions, ldbR, List.map_cons, List.map_nil, M0Crypto.Sym.SExpr.denote]
      rw [va]; exact g.frame_sub ha
    · obtain ⟨e1, e2, e3⟩ := ldb_exec rd rb ri t
      obtain ⟨l0, n0, d, rfl, hm, hd, hn⟩ := findSlice_some hs
      have hr := slice_rel Rs hi hm hd hn
      have hev : (Op.ldb rd rb ri : Op A Bk).ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 st E =
          setRg E [rd.toReg] [byteW (Src.val G c m0 E (.slice l0 d 1))] := by simp only [Op.ev, hl, hs]
      rw [hev] at k
      have hsz : (Op.ldb rd rb ri : Op A Bk).size cE bE = seqSize [ldbI rd rb ri] := by
        simp [Op.size, Op.pieces, piecesSize]
      rw [hsz] at k
      refine k _ ⟨hpc1, h131, hc1, fun p hp => ?_, by rw [e1]; exact Inv.st Rs rfl rfl (inv_setRg Rs m0 hi _ _),
        fun q hq => ?_⟩ hp2
      · obtain ⟨hp, hne⟩ := List.mem_filter.mp hp
        obtain ⟨h14, hpv⟩ := hσ p hp
        exact ⟨h14, by rw [e2 p.1 (fun h => absurd (h ▸ h14) (by decide)) (by simpa using hne), hpv]⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · refine ⟨by have := rd.isLt; simp only [toReg_val]; omega, ?_⟩
          simp only [setRg, List.mem_singleton, ↓reduceIte, List.idxOf_cons_self, List.getElem?_cons_zero,
            Option.getD_some, e3, va]
          generalize Src.val G c m0 E (.slice l0 d 1) = v at hr
          cases v <;> simp only [Rel] at hr
          subst hr
          simp [byteW, Loc.addr, bytesAt, M0Crypto.Thumb.read8]
        · obtain ⟨hq, hne⟩ := List.mem_filter.mp hq
          obtain ⟨h13', he⟩ := hρ q hq
          have hne' : q ≠ rd.toReg := by simpa using hne
          refine ⟨h13', ?_⟩
          simp only [setRg, List.mem_singleton, hne', ↓reduceIte]
          rw [e2 q (fun e => absurd (e ▸ h13') (by decide)) hne']; exact he
  · simp at hty

/-- **The island rule**: the `b` over the island; nothing else changes. -/
theorem isl_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) {pad : Bool} {n o : Nat} {st st' : St}
    {E : Loc → V} {t : State} {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : (Op.isl pad n : Op A Bk).ty cE bE G st = some st')
    (hbok : (Op.isl pad n : Op A Bk).bok cE bE G o = true)
    (hp : piecesAt B o ((Op.isl pad n : Op A Bk).pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + (Op.isl pad n : Op A Bk).size cE bE) st' E u →
      piecesAt B (o + (Op.isl pad n : Op A Bk).size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      ((Op.isl pad n : Op A Bk).tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  simp only [Op.ty, Option.some.injEq] at hty; subst hty
  have e : o + (Op.isl pad n : Op A Bk).size cE bE = o + 2 + seqSize (islPad pad) + n := by
    simp only [Op.size, Op.pieces, piecesSize_cons, piecesSize_nil, Piece.size_over]; omega
  rw [e] at k
  obtain ⟨hp1, hp2⟩ := piecesAt_cons hp
  simp only [Op.pieces, Piece.instrs, Piece.size_over, brSize_eq] at hp1 hp2
  have hb : seqAt B o [.b (brImm11 o (o + 2 + seqSize (islPad pad) + n))] = true := by
    simp only [seqAt, Bool.and_eq_true, and_true] at hp1 ⊢; exact hp1.1
  obtain ⟨hpc, h13, hcode, hσ, hi, hρ⟩ := hat
  refine b_run F hbok hb hpc h13 g.top ?_
  refine k _ ⟨by simp [State.pc, State.setReg], by simpa [State.setReg] using h13, by simpa [State.setReg] using hcode,
    fun q hq => ?_, by simpa [State.setReg] using hi, fun r hr => ?_⟩ (by simpa only [List.append_eq, List.nil_append, Nat.add_assoc] using hp2)
  · obtain ⟨h14, hv⟩ := hσ q hq
    have hne : q.1 ≠ 15 := fun he => by rw [he] at h14; exact absurd h14 (by decide)
    exact ⟨h14, by rw [← hv]; simp [State.setReg, hne]⟩
  · obtain ⟨h13r, hv⟩ := hρ r hr
    have hne : r ≠ 15 := fun he => by rw [he] at h13r; exact absurd h13r (by decide)
    exact ⟨h13r, by rw [hv]; simp [State.setReg, hne]⟩

/-- **One construct.** -/
theorem op_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    {x : Op A Bk} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
    {Q : State → Prop} {Ψ : TrP} {rest : List Piece}
    (hty : x.ty cE bE G st = some st') (hbok : x.bok cE bE G o = true)
    (hp : piecesAt B o (x.pieces cE bE ++ rest) = true)
    (hat : At Rs B c G m0 o st E t)
    (k : ∀ u, At Rs B c G m0 (o + x.size cE bE) st'
        (x.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 st E) u →
      piecesAt B (o + x.size cE bE) rest = true →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) :
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
      (x.tr cE bE G (fun a => (ads a).T) c o st Ψ) := by
  cases x with
  | call a as => exact call_run Rs ads bds m0 g F hcR hty hbok hp hat k
  | blk b as => exact blk_run Rs ads bds m0 g F hty hbok hp hat k
  | spill r o' => exact spill_run Rs ads m0 g F hty hbok hp hat k
  | drop o' n => exact drop_run Rs ads m0 hty hp hat k
  | ld r l => exact ld_run Rs ads m0 g F hcR hty hbok hp hat k
  | pub gs => exact pub_run Rs ads m0 g F hty hbok hp hat k
  | keep ls => exact keep_run Rs ads m0 hty hp hat k
  | ldb rd rb ri => exact ldb_run Rs ads bds m0 g F hty hbok hp hat k
  | isl pad n => exact isl_run Rs ads m0 g F hty hbok hp hat k

end run

end M0Crypto.Release.Ed25519CallProg
