import M0Crypto.Release.Ed25519CallProgOp

set_option linter.unusedSimpArgs false

/-!
# Call programs: the program theorem

`prog_run` is the refinement theorem of a program: from `Prog.ty` (static), `Prog.bok` (the
code), the program's pieces in the code and the invariant `At` at its start, the program runs to
its end with the invariant of `Prog.ty`'s state and the values `Prog.ev`, with trace `Prog.tr`.
A counted loop runs its body `n` times with the counter in a frame word; a dispatch runs the arm
that its public frame word selects.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

variable (Rs : Rels)

/-! ## Branches -/

section br
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- `b<cond> tgt` at `o`: in the code ranges and the artifact, reaching `tgt`. -/
def bcOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt : Nat) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (o + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 o + 4#32 + (brImm8 o tgt ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)

variable {base sp0 : Word} {N : Nat} {Wc Rc : List Rgn} {cs : List (Nat × Nat)}

theorem bc_run (F : Caller base sp0 N Wc) {t : State} {Q : State → Prop} {ΨT ΨF : TrP} {o tgt d : Nat}
    {cond : BitVec 4} {b : Bool} (hok : bcOk cs o tgt = true)
    (hi : seqAt B o [.bcond cond (brImm8 o tgt)] = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hd : d ≤ N)
    (hc : condPassed cond t = b)
    (kT : condPassed cond t = true → ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N)
      (t.setReg 15 (base + BitVec.ofNat 32 tgt)) Q ΨT)
    (kF : condPassed cond t = false → ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N)
      (t.setReg 15 (base + BitVec.ofNat 32 (o + 2))) Q ΨF) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .bcond cond (brImm8 o tgt), []⟩]) (Tr.cond b ΨT ΨF)) := by
  simp only [bcOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨ho, hcs⟩, hsz⟩, ht⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  exact ReachFT.bcond hb2 tgt cond _ hpc ho (instrAt_of_seqAt hi) hsz ht
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega))) ⟨d, hd, h13⟩ hc kT kF

end br

/-! ## Code checks and sizes -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- The code checks of a test's branch at `ob` to `T`. -/
def brOk (sh : Bool) (ob T : Nat) : Bool :=
  if sh then bcOk (B := B) G.cs ob T else bcOk (B := B) G.cs ob (ob + 4) && bOk (B := B) G.cs (ob + 2) T

/-- **The code checks of a program** at `o`, with the exits `J` of the enclosing constructs. -/
def Prog.bok : List Nat → Prog A Bk → Nat → Bool
  | _, .nil, _ => true
  | J, .op x k, o => x.bok cE bE G o && k.bok J (o + x.size cE bE)
  | J, .loop cnt n b k, o =>
    let ob := o + seqSize (loopHead cnt n)
    let od := ob + b.size cE bE
    let oe := od + seqSize (loopDec cnt)
    glueOk G.cs (loopHead cnt n) o G.top G.N [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)] [] &&
      traceOk (loopHead cnt n) [13] && b.bok [] ob &&
      glueOk G.cs (loopDec cnt) od G.top G.N [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)]
        [(13, BitVec.ofNat 32 cnt, 4)] && traceOk (loopDec cnt) [13] &&
      bcOk G.cs oe (oe + 4) && bOk G.cs (oe + 2) ob && k.bok J (oe + 4)
  | J, .sel w i p₀ p₁ k, o =>
    let oh := o + seqSize (selHead w i)
    let o₀ := oh + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    let oo := o₁ + p₁.size cE bE + 2
    glueOk G.cs (selHead w i) o G.top G.N [(13, 4)] [] [(13, BitVec.ofNat 32 w, 4)] &&
      traceOk (selHead w i) [13] && bcOk G.cs oh o₀ && bOk G.cs (oh + 2) o₁ && p₀.bok [] o₀ &&
      bOk G.cs (o₁ - 2) oo && p₁.bok [] o₁ && bOk G.cs (oo - 2) oo && k.bok J oo
  | J, .xit g s _ sh l k, o =>
    let ob := o + xitSz g s
    (Op.pub g : Op A Bk).bok cE bE G o &&
      (match s with | none => true | some (q, o') => (Op.spill q o' : Op A Bk).bok cE bE G (o + seqSize g)) &&
      brOk G sh ob (J.getD l 0) && k.bok J (ob + xbSz sh)
  | J, .hd b h k, o =>
    let oh := o + b.size cE bE + (if h.isNil then 0 else 2)
    let oj := oh + h.size cE bE
    b.bok (oh :: J) o && (h.isNil || bOk G.cs (oh - 2) oj) && h.bok J oh && k.bok J oj
  | J, .wh _ b k, o =>
    let oe := o + b.size cE bE + 2
    b.bok (oe :: J) o && bOk G.cs (oe - 2) o && k.bok J oe

theorem xitBr_size (cc : BitVec 4) (sh : Bool) (o T : Nat) : piecesSize (xitBr cc sh o T) = xbSz sh := by
  cases sh <;> rfl

theorem Prog.size_emit : ∀ (P : Prog A Bk) (J : List Nat) (o : Nat), piecesSize (P.emit cE bE J o) = P.size cE bE
  | .nil, _, _ => rfl
  | .op x k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit k, Op.size]
  | .loop cnt n b k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit b, Prog.size_emit k,
      piecesSize_cons, piecesSize_nil, Piece.size_seq, Piece.size_bcond, Piece.size_b]
    omega
  | .sel w i p₀ p₁ k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit p₀, Prog.size_emit p₁,
      Prog.size_emit k, piecesSize_cons, piecesSize_nil, Piece.size_seq, Piece.size_bcond, Piece.size_b]
  | .xit g s cc sh l k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit k]
    cases s <;> cases sh <;> simp [xitP, xitSz, xitBr, xbSz, strR, seqSize, Instr.size] <;> omega
  | .hd b h k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit b, Prog.size_emit h, Prog.size_emit k]
    split <;> simp <;> omega
  | .wh n b k, J, o => by
    simp only [Prog.emit, Prog.size, piecesSize_append, Prog.size_emit b, Prog.size_emit k, piecesSize_cons,
      piecesSize_nil, Piece.size_b]

end

/-! ## Counter views -/

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)
variable (semA : A → List V → List V) (semB : Bk → List V → List V) (c : Ctx) (m0 : Mem)

theorem ioRes_outs {st : St} {σ : List (Reg × SV)} {io : Iface} {r : IoR} (h : ioRes G st σ io = some r) :
    ∀ p ∈ r.outs, p.2 ≠ .cw := by
  simp only [ioRes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨srcs, -, outs, -, wrs, -, rds, -, h⟩ := h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, and_assoc, List.all_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨-, -, ho, -⟩ := hc
    exact fun p hp => (ho p hp).2
  · simp at h

theorem keep_mem {Γ : List (Loc × Kd)} {ws : List SR} {outs : List (Loc × Kd)} {p : Loc × Kd}
    (h : p ∈ keepViews Γ ws outs) : p ∈ Γ ∧ ∀ q ∈ outs, q.1 ≠ p.1 := by
  simp only [keepViews, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq] at h
  exact ⟨h.1, fun q hq he => h.2.2 q hq he⟩

/-- A construct leaves a counter view's value. -/
theorem Op.ty_cw {x : Op A Bk} {st st' : St} {E : Loc → V} {l : Loc}
    (h : x.ty cE bE G st = some st') (hl : (l, Kd.cw) ∈ st'.Γ) (hlr : ∀ q, l ≠ .rg q) :
    (l, Kd.cw) ∈ st.Γ ∧ x.ev cE bE G semA semB c m0 st E l = E l := by
  cases x with
  | call a as =>
    simp only [Op.ty] at h
    split at h
    · cases hr : ioRes G st (regsOf st.Γ st.σ as) (cE a).io with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
        simp only [IoR.after, List.mem_append] at hl
        rcases hl with hl | hl
        · exact absurd rfl (ioRes_outs G hr _ hl)
        · obtain ⟨h1, h2⟩ := keep_mem hl
          exact ⟨h1, by simp only [Op.ev, hr]; exact updOuts_other h2⟩
    · simp at h
  | blk b as =>
    simp only [Op.ty] at h
    split at h
    · cases hr : ioRes G st (regsOf st.Γ st.σ as) (bE b).io with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq] at h; subst h
        simp only [IoR.after, List.mem_append] at hl
        rcases hl with hl | hl
        · exact absurd rfl (ioRes_outs G hr _ hl)
        · obtain ⟨h1, h2⟩ := keep_mem hl
          exact ⟨h1, by simp only [Op.ev, hr]; rw [setRg_ne hlr]; exact updOuts_other h2⟩
    · simp at h
  | spill r o =>
    simp only [Op.ty] at h
    cases hv : st.σ.lookup r.toReg with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hl
        exact ⟨(keep_mem hl).1, rfl⟩
      · simp at h
  | drop o n =>
    simp only [Op.ty, Option.some.injEq] at h; subst h
    exact ⟨(keep_mem hl).1, rfl⟩
  | ld r l =>
    simp only [Op.ty] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hl, rfl⟩
  | pub g =>
    simp only [Op.ty] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hl, rfl⟩
  | keep ls =>
    simp only [Op.ty] at h
    obtain ⟨Γ', hΓ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨keepΓ_sub hΓ _ hl, rfl⟩
  | ldb rd rb ri =>
    simp only [Op.ty] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨hl, ?_⟩
        simp only [Op.ev]
        cases ldbOff st.σ rb ri with
        | none => rfl
        | some a =>
          dsimp only
          cases findSlice st.Γ (.fr a) 1 with
          | none => rfl
          | some s => exact setRg_ne hlr
      · simp at h
    · simp at h
  | isl pad n => simp only [Op.ty, Option.some.injEq] at h; subst h; exact ⟨hl, rfl⟩

theorem spillSt_cw {st st' : St} {r : LowReg} {o : Nat} {l : Loc} (h : spillSt G st r o = some st')
    (hl : (l, Kd.cw) ∈ st'.Γ) : (l, Kd.cw) ∈ st.Γ := by
  simp only [spillSt] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      simp only [List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false, false_or] at hl
      exact (keep_mem hl).1
    · simp at h
  · simp at h

/-- The state after a test's store. -/
def xitPost (st1 st2 : St) : Option (LowReg × Nat) → Prop
  | none => st2 = st1
  | some (q, o) => spillSt G st1 q o = some st2

/-- A test's state: the public block's registers, then its store. -/
theorem xitSt_some {st st2 : St} {g : List Instr} {s : Option (LowReg × Nat)} {cc : BitVec 4} {b : Bool}
    (h : xitSt G st g s cc = some (st2, b)) : ∃ r, pubEval st.σ st.Γ g = some r ∧ r.dec cc = some b ∧
      cc.toNat < 14 ∧ xitPost G { st with σ := r.σ, ρ := [] } st2 s := by
  simp only [xitSt] at h
  split at h
  · rename_i r hr
    split at h
    · rename_i st3 b' h3 hb'
      split at h
      · rename_i hcc
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨r, hr, hb', hcc, ?_⟩
        cases s with
        | none => simp only [Option.some.injEq] at h3; exact h3.symm
        | some p => obtain ⟨q, o⟩ := p; exact h3
      · simp at h
    · simp at h
  · simp at h

theorem spillSt_ex {st st' : St} {r : LowReg} {o : Nat} (h : spillSt G st r o = some st') : st'.ex = st.ex := by
  simp only [spillSt] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  · simp at h

theorem xitSt_ex {st st2 : St} {g : List Instr} {s : Option (LowReg × Nat)} {cc : BitVec 4} {b : Bool}
    (h : xitSt G st g s cc = some (st2, b)) : st2.ex = st.ex := by
  obtain ⟨r, -, -, -, hs⟩ := xitSt_some G h
  cases s with
  | none => simp only [xitPost] at hs; subst hs; rfl
  | some p => obtain ⟨q, o⟩ := p; simp only [xitPost] at hs; rw [spillSt_ex G hs]

theorem xitSt_cw {st st2 : St} {g : List Instr} {s : Option (LowReg × Nat)} {cc : BitVec 4} {b : Bool}
    {l : Loc} (h : xitSt G st g s cc = some (st2, b)) (hl : (l, Kd.cw) ∈ st2.Γ) : (l, Kd.cw) ∈ st.Γ := by
  obtain ⟨r, -, -, -, hs⟩ := xitSt_some G h
  cases s with
  | none => simp only [xitPost] at hs; subst hs; exact hl
  | some p => obtain ⟨q, o⟩ := p; simp only [xitPost] at hs; have := spillSt_cw G hs hl; exact this

/-- A construct starts no exit. -/
theorem Op.ty_ex {x : Op A Bk} {st s1 : St} (h : x.ty cE bE G st = some s1) (he : st.ex = none) :
    s1.ex = none := by
  cases x with
  | call a as =>
    simp only [Op.ty] at h
    split at h
    · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    · simp at h
  | blk b as =>
    simp only [Op.ty] at h
    split at h
    · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    · simp at h
  | spill r o =>
    simp only [Op.ty] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact he
      · simp at h
    · simp at h
  | drop o n => simp only [Op.ty, Option.some.injEq] at h; subst h; exact he
  | ld r l =>
    simp only [Op.ty] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact he
  | pub g =>
    simp only [Op.ty] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact he
  | keep ls =>
    simp only [Op.ty] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact he
  | ldb rd rb ri =>
    simp only [Op.ty] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact he
      · simp at h
    · simp at h
  | isl pad n => simp only [Op.ty, Option.some.injEq] at h; subst h; exact he

theorem Prog.isNil_eq {P : Prog A Bk} (h : P.isNil = true) : P = .nil := by
  cases P <;> simp [Prog.isNil] at h ⊢

/-- The passes of a loop with exits leave a counter view, when the body and the rest do. -/
theorem whTy_cw {tb tk : St → Option St} {eb ek : St → (Loc → V) → Loc → V} {l : Loc}
    (hb : ∀ {s s' : St} E, tb s = some s' → (l, Kd.cw) ∈ s'.Γ → (l, Kd.cw) ∈ s.Γ ∧ eb s E l = E l)
    (hk : ∀ {s s' : St} E, tk s = some s' → (l, Kd.cw) ∈ s'.Γ → (l, Kd.cw) ∈ s.Γ ∧ ek s E l = E l) :
    ∀ n {st st' : St} E, whTy tb tk n st = some st' → (l, Kd.cw) ∈ st'.Γ →
      (l, Kd.cw) ∈ st.Γ ∧ whEv tb eb ek n st E l = E l
  | 0, _, _, _, h, _ => by simp [whTy] at h
  | n + 1, st, st', E, h, hl => by
    simp only [whTy] at h
    cases h1 : tb st with
    | none => simp [h1] at h
    | some s =>
      simp only [h1] at h
      simp only [whEv, h1]
      cases he : s.ex with
      | none =>
        simp only [he] at h ⊢
        obtain ⟨a1, a2⟩ := whTy_cw hb hk n (eb st E) h hl
        obtain ⟨b1, b2⟩ := hb E h1 a1
        exact ⟨b1, by rw [a2, b2]⟩
      | some j =>
        cases j with
        | zero =>
          simp only [he] at h ⊢
          obtain ⟨a1, a2⟩ := hk (eb st E) h hl
          obtain ⟨b1, b2⟩ := hb E h1 a1
          exact ⟨b1, by rw [a2, b2]⟩
        | succ j =>
          simp only [he, Option.some.injEq] at h ⊢; subst h
          exact hb E h1 hl

theorem cnt_ne {Γ : List (Loc × Kd)} {cnt : Nat} {p : Loc × Kd} (h : p ∈ cntViews Γ cnt) :
    p.1 ≠ .fr cnt :=
  fun he => (keep_mem h).2 _ List.mem_cons_self he.symm

theorem loopIt_keep {f : (Loc → V) → Loc → V} {cnt : Nat} {l : Loc} (hl : l ≠ .fr cnt)
    (hf : ∀ E, f E l = E l) : ∀ r E, loopIt f cnt r E l = E l
  | 0, _ => rfl
  | r + 1, E => by
    rw [loopIt, loopIt_keep hl hf r, hf]; simp [setCnt, hl]

/-- **A program leaves a counter view's value**, and the view was there before. -/
theorem Prog.ty_cw : ∀ (P : Prog A Bk) {st st' : St} {E : Loc → V} {l : Loc},
    P.ty cE bE G st = some st' → (l, Kd.cw) ∈ st'.Γ → (∀ q, l ≠ .rg q) →
    (l, Kd.cw) ∈ st.Γ ∧ Prog.ev cE bE G semA semB c m0 P st E l = E l
  | .nil, _, _, _, _, h, hl, _ => by simp only [Prog.ty, Option.some.injEq] at h; subst h; exact ⟨hl, rfl⟩
  | .op x k, st, st', E, l, h, hl, hlr => by
    simp only [Prog.ty, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    obtain ⟨a1, a2⟩ := Prog.ty_cw k h2 hl hlr (E := x.ev cE bE G semA semB c m0 st E)
    obtain ⟨b1, b2⟩ := Op.ty_cw cE bE G semA semB c m0 h1 a1 hlr (E := E)
    exact ⟨b1, by simp only [Prog.ev, h1]; rw [a2, b2]⟩
  | .loop cnt n b k, st, st', E, l, h, hl, hlr => by
    simp only [Prog.ty] at h
    cases hb : b.ty cE bE G (loopSt st cnt) with
    | none => simp [hb] at h
    | some sB =>
      simp only [hb] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, subL, List.all_eq_true] at hc
        obtain ⟨a1, a2⟩ := Prog.ty_cw k h hl hlr (E := loopIt (Prog.ev cE bE G semA semB c m0 b (loopSt st cnt)) cnt n E)
        have hne := cnt_ne a1
        have hin : (l, Kd.cw) ∈ (loopSt st cnt).Γ := List.mem_cons_of_mem _ a1
        have := hc.1.1.2 _ hin
        simp only [List.mem_cons, Prod.mk.injEq, hne, false_and, false_or] at this
        exact ⟨(keep_mem a1).1, by
          simp only [Prog.ev]; rw [a2]
          exact loopIt_keep hne (fun E' => (Prog.ty_cw b hb (keep_mem this).1 hlr).2) n E⟩
      · simp at h
  | .sel w i p₀ p₁ k, st, st', E, l, h, hl, hlr => by
    simp only [Prog.ty] at h
    cases hw : pwAt st.Γ w with
    | none => simp [hw] at h
    | some v =>
    cases h0 : p₀.ty cE bE G (selSt st) with
    | none => simp [hw, h0] at h
    | some s₀ =>
    cases h1 : p₁.ty cE bE G (selSt st) with
    | none => simp [hw, h0, h1] at h
    | some s₁ =>
    simp only [hw, h0, h1] at h
    split at h
    · obtain ⟨a1, a2⟩ := Prog.ty_cw k h hl hlr (E := if v.val c (G.fsp c) == BitVec.ofNat 32 i then
        Prog.ev cE bE G semA semB c m0 p₁ (selSt st) E else Prog.ev cE bE G semA semB c m0 p₀ (selSt st) E)
      simp only [joinSt, List.mem_filter, decide_eq_true_eq] at a1
      obtain ⟨b1, b2⟩ := Prog.ty_cw p₀ h0 a1.1 hlr (E := E)
      obtain ⟨-, c2⟩ := Prog.ty_cw p₁ h1 a1.2 hlr (E := E)
      refine ⟨b1, ?_⟩
      simp only [Prog.ev, hw, h0, h1]; rw [a2]; split <;> assumption
    · simp at h
  | .xit g s cc sh j k, st, st', E, l, h, hl, hlr => by
    simp only [Prog.ty] at h
    cases hx : xitSt G st g s cc with
    | none => simp [hx] at h
    | some p =>
      obtain ⟨st2, b⟩ := p
      cases b with
      | true =>
        simp only [hx, Option.some.injEq] at h; subst h
        exact ⟨xitSt_cw G hx hl, by simp only [Prog.ev, hx]⟩
      | false =>
        simp only [hx] at h
        obtain ⟨a1, a2⟩ := Prog.ty_cw k h hl hlr (E := E)
        exact ⟨xitSt_cw G hx a1, by simp only [Prog.ev, hx]; exact a2⟩
  | .hd b h k, st, st', E, l, hty, hl, hlr => by
    simp only [Prog.ty] at hty
    cases hb : b.ty cE bE G st with
    | none => simp [hb] at hty
    | some s =>
    simp only [hb] at hty
    simp only [Prog.ev, hb]
    cases he : s.ex with
    | none =>
      simp only [he] at hty ⊢
      obtain ⟨a1, a2⟩ := Prog.ty_cw k hty hl hlr (E := Prog.ev cE bE G semA semB c m0 b st E)
      obtain ⟨b1, b2⟩ := Prog.ty_cw b hb a1 hlr (E := E)
      exact ⟨b1, by rw [a2, b2]⟩
    | some j =>
    cases j with
    | succ j =>
      simp only [he, Option.some.injEq] at hty ⊢; subst hty
      exact Prog.ty_cw b hb hl hlr
    | zero =>
    simp only [he] at hty ⊢
    cases hh : h.ty cE bE G { s with ex := none } with
    | none => simp [hh] at hty
    | some s' =>
    simp only [hh] at hty ⊢
    split at hty
    · rename_i hn
      simp only [hn, ↓reduceIte]
      obtain ⟨a1, a2⟩ := Prog.ty_cw k hty hl hlr
        (E := Prog.ev cE bE G semA semB c m0 h { s with ex := none } (Prog.ev cE bE G semA semB c m0 b st E))
      obtain ⟨b1, b2⟩ := Prog.ty_cw h hh a1 hlr (E := Prog.ev cE bE G semA semB c m0 b st E)
      obtain ⟨c1, c2⟩ := Prog.ty_cw b hb b1 hlr (E := E)
      exact ⟨c1, by rw [a2, b2, c2]⟩
    · rename_i hn
      simp only [hn, ↓reduceIte]
      simp only [Option.some.injEq] at hty; subst hty
      obtain ⟨b1, b2⟩ := Prog.ty_cw h hh hl hlr (E := Prog.ev cE bE G semA semB c m0 b st E)
      obtain ⟨c1, c2⟩ := Prog.ty_cw b hb b1 hlr (E := E)
      exact ⟨c1, by rw [b2, c2]⟩
  | .wh n b k, st, st', E, l, hty, hl, hlr => by
    simp only [Prog.ty] at hty
    simp only [Prog.ev]
    exact whTy_cw (fun E h hl => Prog.ty_cw b h hl hlr) (fun E h hl => Prog.ty_cw k h hl hlr) n E hty hl

end


/-! ## Loop and dispatch instructions -/

theorem head_mem (cnt n : Nat) (t : State) (hn : n < 256) (h4 : cnt % 4 = 0) (h1 : cnt ≤ 1020) :
    (execAll (loopHead cnt n) t).mem = write32 t.mem (t.regs 13 + BitVec.ofNat 32 cnt) (BitVec.ofNat 32 n) := by
  have e : cnt / 4 % 256 * 4 = cnt := by omega
  simp [loopHead, strSpI, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, State.reg, e,
    setWidth8 hn, show (13 : Reg) ≠ LowReg.toReg 0 by decide]

theorem dec_facts (cnt : Nat) (t : State) (h4 : cnt % 4 = 0) (h1 : cnt ≤ 1020) :
    (execAll (loopDec cnt) t).mem = write32 t.mem (t.regs 13 + BitVec.ofNat 32 cnt)
      (read32 t.mem (t.regs 13 + BitVec.ofNat 32 cnt) - 1#32) ∧
    (execAll (loopDec cnt) t).z = (read32 t.mem (t.regs 13 + BitVec.ofNat 32 cnt) - 1#32 == 0#32) := by
  have e : cnt / 4 % 256 * 4 = cnt := by omega
  simp [loopDec, strSpI, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, State.reg, e,
    addFlags, State.setNZCV, Routine.addWithCarry_true_fst, show (13 : Reg) ≠ LowReg.toReg 0 by decide,
    show ∀ x : Word, x + 4294967294#32 + 1#32 = x - 1#32 from fun x => by bv_omega]

theorem sel_facts (w i : Nat) (t : State) (hi : i < 256) (h4 : w % 4 = 0) (h1 : w ≤ 1020) :
    (execAll (selHead w i) t).mem = t.mem ∧
    (execAll (selHead w i) t).z = (read32 t.mem (t.regs 13 + BitVec.ofNat 32 w) == BitVec.ofNat 32 i) := by
  have e : w / 4 % 256 * 4 = w := by omega
  refine ⟨by simp [selHead, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.setNZCV], ?_⟩
  simp [selHead, execAll, Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, State.reg, e,
    addFlags, State.setNZCV, Routine.addWithCarry_true_fst, setWidth8 hi]
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; constructor <;> intro _ <;> bv_omega

theorem ofNat_eq_zero {r : Nat} (h : r < 256) : (BitVec.ofNat 32 r == 0#32) = (r == 0) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
  constructor
  · intro he; have := congrArg BitVec.toNat he; simp at this; omega
  · rintro rfl; rfl

theorem ofNat_succ_sub (r : Nat) (_h : r + 1 < 2 ^ 32) :
    BitVec.ofNat 32 (r + 1) - 1#32 = BitVec.ofNat 32 r := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

/-! ## Invariant steps -/

section inv
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} {m0 : Mem}

theorem Inv.congrE {st : St} {E E' : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m)
    (h : ∀ p ∈ st.Γ, E' p.1 = E p.1) : Inv Rs c G m0 st E' m :=
  ⟨fun p hp => by rw [h p hp]; exact hi.1 p hp, hi.2⟩

theorem cnt_rgns {cnt : Nat} : SR.rgns G c ⟨.fr cnt, .k 4⟩ = [⟨G.fsp c + BitVec.ofNat 32 cnt, 4⟩] := by
  simp [SR.rgns, XLen.v, Loc.addr]

/-- Writing `v` to the counter word makes it the counter view; the views apart from it stay. -/
theorem inv_cnt (g : GeoOk c G Wc Rc) {st : St} {E : Loc → V} {m m' : Mem} (hi : Inv Rs c G m0 st E m)
    {cnt v : Nat} (hc : cnt + 4 ≤ G.top) (hm : MemEq [⟨G.fsp c + BitVec.ofNat 32 cnt, 4⟩] m m')
    (hv : read32 m' (G.fsp c + BitVec.ofNat 32 cnt) = BitVec.ofNat 32 v) (σ' : List (Reg × SV)) :
    Inv Rs c G m0 { Γ := (.fr cnt, .cw) :: cntViews st.Γ cnt, σ := σ', X := st.X } (setCnt E cnt v) m' := by
  have hsr : SR.ok G ⟨.fr cnt, .k 4⟩ = true := by simp [SR.ok]; omega
  have := inv_after Rs g hi (sw := 0) (by have := g.top; omega) (ws := [⟨.fr cnt, .k 4⟩])
    (fun w hw => by simp at hw; subst hw; exact hsr) (memEq_cons0 _ (by simpa [cnt_rgns] using hm)) σ' []
    (outs := [(.fr cnt, .cw)]) (vs := [.w (BitVec.ofNat 32 v)])
    (fun p hp => by simp at hp; subst hp; simpa [Kd.sr, Kd.sz] using hsr) (by simp)
    ⟨by simpa [Rel, Loc.addr] using hv, trivial⟩
  have e : updOuts E [(.fr cnt, .cw)] [.w (BitVec.ofNat 32 v)] = setCnt E cnt v := by
    funext x; simp [updOuts, setCnt]
  rw [e] at this
  simpa [Loc.isEx, cntViews] using this

end inv

/-! ## The program theorem -/

section run
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS}
variable (ads : ∀ a, Ad Rs B BS (cE a)) (bds : ∀ b, Bd Rs (bE b))
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (m0 : Mem)

theorem at_jump {o : Nat} {st : St} {E : Loc → V} {t : State} (h13 : t.regs 13 = G.fsp c)
    (hc : CodeAt t.mem c.base B) (hσ : Holds c (G.fsp c) st.σ t.regs) (hi : Inv Rs c G m0 st E t.mem)
    (hρ : st.ρ = []) : At Rs B c G m0 o st E (t.setReg 15 (c.base + BitVec.ofNat 32 o)) := by
  refine ⟨by simp [State.pc, State.setReg], by simpa [State.setReg] using h13, by simpa [State.setReg] using hc,
    fun p hp => ?_, by simpa [State.setReg] using hi, fun r h => by rw [hρ] at h; cases h⟩
  obtain ⟨h14, hv⟩ := hσ p hp
  have hne : p.1 ≠ 15 := fun he => by rw [he] at h14; exact absurd h14 (by decide)
  exact ⟨h14, by rw [← hv]; simp [State.setReg, hne]⟩

theorem cnt_sides {t : State} (g : GeoOk c G Wc Rc) (h13 : t.regs 13 = G.fsp c) {cnt : Nat}
    (hc : cnt + 4 ≤ G.top) {rg : List (Reg × Word × Nat)} (hrg : Sub (regions t rg) Rc) :
    GlueSides t Rc Wc [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)] rg := by
  have hsr : SR.ok G ⟨.fr cnt, .k 4⟩ = true := by simp [SR.ok]; omega
  refine ⟨fun p hp => ?_, ?_, hrg⟩
  · simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4
  · have := g.sub hsr true rfl
    simpa [regions, h13, cnt_rgns] using this

theorem cnt_rd {t : State} (g : GeoOk c G Wc Rc) (h13 : t.regs 13 = G.fsp c) {cnt : Nat}
    (hc : cnt + 4 ≤ G.top) : Sub (regions t [(13, BitVec.ofNat 32 cnt, 4)]) Rc := by
  have hsr : SR.ok G ⟨.fr cnt, .k 4⟩ = true := by simp [SR.ok]; omega
  have := g.sub hsr false rfl
  simpa [regions, h13, cnt_rgns] using this

theorem at_br {o o' : Nat} {st : St} {E : Loc → V} {t : State} (h : At Rs B c G m0 o st E t) :
    At Rs B c G m0 o' st E (t.setReg 15 (c.base + BitVec.ofNat 32 o')) := by
  obtain ⟨-, h13, hc, hσ, hi, hρ⟩ := h
  refine ⟨by simp [State.pc, State.setReg], by simpa [State.setReg] using h13, by simpa [State.setReg] using hc,
    fun p hp => ?_, by simpa [State.setReg] using hi, fun r hr => ?_⟩
  · obtain ⟨h14, hv⟩ := hσ p hp
    have hne : p.1 ≠ 15 := fun he => by rw [he] at h14; exact absurd h14 (by decide)
    exact ⟨h14, by rw [← hv]; simp [State.setReg, hne]⟩
  · obtain ⟨h13', hv⟩ := hρ r hr
    have hne : r ≠ 15 := fun he => by rw [he] at h13'; exact absurd h13' (by decide)
    exact ⟨h13', by rw [hv]; simp [State.setReg, hne]⟩

theorem At.exs {o : Nat} {st : St} {E : Loc → V} {t : State} (e : Option Nat) (h : At Rs B c G m0 o st E t) :
    At Rs B c G m0 o { st with ex := e } E t := h

theorem pa_skip {o : Nat} {ps qs : List Piece} (h : piecesAt B o (ps ++ qs) = true) :
    piecesAt B (o + piecesSize ps) qs = true := by
  rw [piecesAt_append, Bool.and_eq_true] at h; exact h.2

/-- **The program theorem**: a checked program runs from `At` at its start either to `At` at its
end with the state of `Prog.ty` and the values of `Prog.ev`, or, when the state names an exit
`l`, to `At` at the exit `J[l]`; with the trace `Prog.tr`, whose exits continue with `Ψs[l]`. -/
theorem prog_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc) :
    ∀ (P : Prog A Bk) {J : List Nat} {Ψs : List TrP} {o : Nat} {st st' : St} {E : Loc → V} {t : State}
      {Q : State → Prop} {Ψ : TrP} {rest : List Piece}, P.ty cE bE G st = some st' → st.ex = none →
    P.bok cE bE G J o = true → piecesAt B o (P.emit cE bE J o ++ rest) = true → At Rs B c G m0 o st E t →
    (st'.ex = none → ∀ u, At Rs B c G m0 (o + P.size cE bE) st' (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 P st E) u →
      piecesAt B (o + P.size cE bE) rest = true → ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ) →
    (∀ l, st'.ex = some l → ∀ u, At Rs B c G m0 (J.getD l 0) st' (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 P st E) u →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q (Ψs.getD l (Tr.is []))) →
    ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q (Prog.tr cE bE G (fun a => (ads a).T) c P o st Ψ J Ψs)
  | .nil, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, _, hp, hat, kk, _ => by
    simp only [Prog.ty, Option.some.injEq] at hty; subst hty
    exact kk hex t (by simpa [Prog.size, Prog.ev] using hat) (by simpa [Prog.size, Prog.emit] using hp)
  | .op x k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.ty, Option.bind_eq_some_iff] at hty
    obtain ⟨s1, h1, h2⟩ := hty
    simp only [Prog.bok, Bool.and_eq_true] at hbok
    simp only [Prog.emit, List.append_assoc] at hp
    simp only [Prog.tr, h1, Option.getD_some]
    refine op_run Rs ads bds m0 g F hcR h1 hbok.1 hp hat fun u hu hr => ?_
    have e : o + x.size cE bE + k.size cE bE = o + (Prog.op x k).size cE bE := by
      simp only [Prog.size]; omega
    refine prog_run g F hcR k h2 (Op.ty_ex cE bE G h1 hex) hbok.2 hr hu (fun hn u' hu' hr' => ?_)
      (fun l hl u' hu' => kx l hl u' (by simpa [Prog.ev, h1] using hu'))
    rw [e] at hu' hr'
    exact kk hn u' (by simpa [Prog.ev, h1] using hu') hr'
  | .loop cnt n b k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.ty] at hty
    cases hb : b.ty cE bE G (loopSt st cnt) with
    | none => simp [hb] at hty
    | some sB =>
    simp only [hb] at hty
    split at hty
    case isFalse => simp at hty
    rename_i hc
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, subL, List.all_eq_true,
      and_assoc] at hc
    obtain ⟨h4, htop, h1020, hn0, hn, hcB, hsub, hX, hxB⟩ := hc
    simp only [Prog.bok, Bool.and_eq_true, and_assoc] at hbok
    obtain ⟨hgh, htrh, hbb, hgd, htrd, hbc, hbb2, hkb⟩ := hbok
    simp only [Prog.emit, List.append_assoc, List.cons_append, List.nil_append] at hp
    obtain ⟨hph, hp2⟩ := piecesAt_cons hp
    simp only [Piece.instrs, Piece.size] at hph hp2
    obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
    have hcnt : cnt + 4 ≤ G.top := htop
    have htN : G.top ≤ G.N := g.top
    simp only [Prog.tr]
    -- the passes
    have it : ∀ r (E1 : Loc → V) (u : State), r < n →
        loopIt (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 b (loopSt st cnt)) cnt
          (r + 1) E1 = loopIt (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 b
          (loopSt st cnt)) cnt n E →
        At Rs B c G m0 (o + seqSize (loopHead cnt n)) (loopSt st cnt) (setCnt E1 cnt (r + 1)) u →
        ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q
          (loopTr (fun Ψ' => Prog.tr cE bE G (fun a => (ads a).T) c b (o + seqSize (loopHead cnt n)) (loopSt st cnt) Ψ' [] [])
            (blockTr (loopDec cnt) (c.base + BitVec.ofNat 32 (o + seqSize (loopHead cnt n) + b.size cE bE))
              [13] [G.fsp c])
            (bcEv c EQ (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt))
              (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 4))
            (bEv c (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 2)
              (o + seqSize (loopHead cnt n)))
            (Prog.tr cE bE G (fun a => (ads a).T) c k
              (o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 4) (loopOut st cnt) Ψ J Ψs)
            (r + 1)) := by
      intro r
      induction r using Nat.strongRecOn with
      | ind r ih =>
      intro E1 u hr hE hat'
      rw [loopTr]
      refine prog_run g F hcR b hb rfl hbb (by simpa using hp2) hat' (fun _ u1 hu1 hr1 => ?_)
        (fun l hl => by rw [hxB] at hl; cases hl)
      obtain ⟨hpd, hr2⟩ := piecesAt_cons hr1
      obtain ⟨hpbc, hr3⟩ := piecesAt_cons hr2
      obtain ⟨hpbb, hr4⟩ := piecesAt_cons hr3
      simp only [Piece.instrs, Piece.size_seq, Piece.size_bcond, Piece.size_b] at hpd hpbc hpbb hr4
      obtain ⟨hpc1, h131, hc1, -, hi1, -⟩ := hu1
      have hcv := (Prog.ty_cw cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 b hb hcB
        (fun _ h => Loc.noConfusion h) (E := setCnt E1 cnt (r + 1))).2
      have hrd : read32 u1.mem (G.fsp c + BitVec.ofNat 32 cnt) = BitVec.ofNat 32 (r + 1) := by
        have := (hi1.1 _ hcB).2
        rw [hcv] at this; simpa [setCnt, Rel, Loc.addr] using this
      refine ReachFT.glue F (loopDec cnt) [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)]
        [(13, BitVec.ofNat 32 cnt, 4)] hpd hpc1 h131 hc1 (cnt_sides g h131 hcnt (cnt_rd g h131 hcnt))
        (traceAll_blockTr (by rfl) htrd hpc1 (by simp [h131])) (fun hpc2 h132 hc2 hm2 => ?_) hgd
      obtain ⟨dm, dz⟩ := dec_facts cnt u1 h4 h1020
      rw [h131, hrd, ofNat_succ_sub r (by omega)] at dm dz
      have hm2' : MemEq [⟨G.fsp c + BitVec.ofNat 32 cnt, 4⟩] u1.mem (execAll (loopDec cnt) u1).mem := by
        simpa [regions, h131] using hm2
      have hv2 : read32 (execAll (loopDec cnt) u1).mem (G.fsp c + BitVec.ofNat 32 cnt) = BitVec.ofNat 32 r := by
        rw [dm, M0Crypto.Armv6M.read32_write32_same]
      have hX' : sB.X = st.X := hX
      have inv2 := inv_cnt Rs g hi1 hcnt hm2' hv2 σsp
      refine bc_run F hbc hpbc hpc2 h132 htN (b := r == 0)
        (by simp only [condPassed, EQ]; rw [dz, ofNat_eq_zero (by omega)]; rfl) (fun hz => ?_) (fun hz => ?_)
      · -- exit
        have hr0 : r = 0 := by
          simp only [condPassed, EQ] at hz; rw [dz, ofNat_eq_zero (by omega)] at hz; simpa using hz
        subst hr0
        refine prog_run g F hcR k (E := loopIt (Prog.ev cE bE G (fun a => (ads a).sem)
          (fun b => (bds b).sem) c m0 b (loopSt st cnt)) cnt n E) hty rfl hkb (by rwa [show ∀ a : Nat, a + 2 + 2 = a + 4 from fun a => rfl] at hr4)
          (at_jump Rs m0 h132 hc2 (holds_sp h132) ?_ rfl) (fun hn u' hu' hr' => ?_)
          (fun l hl u' hu' => kx l hl u' (by simpa [Prog.ev] using hu'))
        · refine Inv.congrE Rs (Inv.weaken Rs m0 inv2 (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) ?_) ?_
          · intro x hx; rw [hX'] at hx; exact hx
          · intro p hp; rw [← hE]; simp [loopIt, setCnt, cnt_ne hp]
        · have e : o + seqSize (loopHead cnt n) + b.size cE bE + seqSize (loopDec cnt) + 4 + k.size cE bE =
              o + (Prog.loop cnt n b k).size cE bE := by simp only [Prog.size]; omega
          rw [e] at hu' hr'
          exact kk hn u' (by simpa [Prog.ev] using hu') hr'
      · -- next pass
        cases r with
        | zero =>
          simp only [condPassed, EQ] at hz; rw [dz] at hz; simp at hz
        | succ r' =>
          refine b_run F hbb2 hpbb (by simp [State.pc, State.setReg]) (by simpa [State.setReg] using h132) htN ?_
          refine ih r' (by omega) _ _ (by omega) (by rw [← hE]; rfl) (at_jump Rs m0 (by simpa [State.setReg, Geo.fsp] using h132)
            (by simpa [State.setReg] using hc2) (holds_sp (by simpa [State.setReg, Geo.fsp] using h132)) ?_ rfl)
          refine Inv.weaken Rs m0 (by simpa [State.setReg] using inv2) (fun p hp => hsub p hp) ?_
          intro x hx; rw [hX'] at hx; exact hx
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    refine ReachFT.glue F (loopHead cnt (r + 1)) [(13, 4)] [(13, BitVec.ofNat 32 cnt, 4)] [] hph hpc h13 hcode
      (cnt_sides g h13 hcnt (fun _ h => absurd h List.not_mem_nil))
      (traceAll_blockTr (by rfl) htrh hpc (by simp [h13])) (fun hpc1 h131 hc1 hm1 => ?_) hgh
    have hm1' : MemEq [⟨G.fsp c + BitVec.ofNat 32 cnt, 4⟩] t.mem (execAll (loopHead cnt (r + 1)) t).mem := by
      simpa [regions, h13] using hm1
    have hv1 : read32 (execAll (loopHead cnt (r + 1)) t).mem (G.fsp c + BitVec.ofNat 32 cnt) =
        BitVec.ofNat 32 (r + 1) := by
      rw [head_mem cnt (r + 1) t hn h4 h1020, h13, M0Crypto.Armv6M.read32_write32_same]
    exact it r E _ (by omega) rfl ⟨hpc1, h131, hc1, holds_sp h131, inv_cnt Rs g hi hcnt hm1' hv1 σsp, fun _ h => by simp [loopSt] at h⟩
  | .sel w i p₀ p₁ k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.ty] at hty
    cases hw : pwAt st.Γ w with
    | none => simp [hw] at hty
    | some v =>
    cases h0 : p₀.ty cE bE G (selSt st) with
    | none => simp [hw, h0] at hty
    | some s₀ =>
    cases h1 : p₁.ty cE bE G (selSt st) with
    | none => simp [hw, h0, h1] at hty
    | some s₁ =>
    simp only [hw, h0, h1] at hty
    split at hty
    case isFalse => simp at hty
    rename_i hc
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hc
    obtain ⟨h4, htop, h1020, hi256, hx0, hx1⟩ := hc
    simp only [Prog.bok, Bool.and_eq_true, and_assoc] at hbok
    obtain ⟨hgh, htrh, hbc, hbo1, hp0b, hbe0, hp1b, hbe1, hkb⟩ := hbok
    simp only [Prog.emit, List.append_assoc, List.cons_append, List.nil_append] at hp
    obtain ⟨hph, hp2⟩ := piecesAt_cons hp
    obtain ⟨hpbc, hp3⟩ := piecesAt_cons hp2
    obtain ⟨hpb1, hp4⟩ := piecesAt_cons hp3
    simp only [Piece.instrs, Piece.size_seq, Piece.size_bcond, Piece.size_b] at hph hpbc hpb1 hp4
    rw [show o + seqSize (selHead w i) + 2 + 2 = o + seqSize (selHead w i) + 4 by omega] at hp4
    have hp1p : piecesAt B (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2)
        (p₁.emit cE bE [] (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2) ++
          (.b (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2) ::
            (k.emit cE bE J (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2) ++ rest)))
          = true := by
      rw [piecesAt_append, Prog.size_emit, Bool.and_eq_true] at hp4
      have := (piecesAt_cons hp4.2).2
      simpa only [Piece.size_b] using this
    obtain ⟨hpc, h13, hcode, -, hi, -⟩ := hat
    have htN : G.top ≤ G.N := g.top
    have hv : read32 t.mem (G.fsp c + BitVec.ofNat 32 w) = v.val c (G.fsp c) := by
      simpa [Rel, Loc.addr] using (hi.1 _ (pwAt_mem hw)).2
    have e0 : o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 - 2 =
        o + seqSize (selHead w i) + 4 + p₀.size cE bE := by omega
    have e1 : o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2 - 2 =
        o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE := by omega
    have ek : o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2 + k.size cE bE =
        o + (Prog.sel w i p₀ p₁ k).size cE bE := by simp only [Prog.size]; omega
    rw [e0] at hbe0; rw [e1] at hbe1
    simp only [Prog.tr, hw, h0, h1, Option.map_some, Option.getD_some]
    rw [e0, e1]
    -- the exit after either arm
    have hK : ∀ (Ea : Loc → V) (u : State), Inv Rs c G m0 (joinSt s₀ s₁) Ea u.mem →
        u.regs 13 = G.fsp c → CodeAt u.mem c.base B →
        Ea = (if v.val c (G.fsp c) == BitVec.ofNat 32 i then
          Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 p₁ (selSt st) E else
          Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 p₀ (selSt st) E) →
        piecesAt B (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2)
          (k.emit cE bE J (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2) ++ rest) = true →
        ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N)
          (u.setReg 15 (c.base + BitVec.ofNat 32 (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 +
            p₁.size cE bE + 2))) Q
          (Prog.tr cE bE G (fun a => (ads a).T) c k
            (o + seqSize (selHead w i) + 4 + p₀.size cE bE + 2 + p₁.size cE bE + 2) (joinSt s₀ s₁) Ψ J Ψs) := by
      intro Ea u hiu h13u hcu hEa hpk
      subst hEa
      refine prog_run g F hcR k hty rfl hkb hpk (at_jump Rs m0 h13u hcu (holds_sp h13u) hiu rfl)
        (fun hn u' hu' hr' => ?_) (fun l hl u' hu' => kx l hl u' (by simpa only [Prog.ev, hw, h0, h1] using hu'))
      rw [ek] at hu' hr'
      exact kk hn u' (by simpa only [Prog.ev, hw, h0, h1] using hu') hr'
    refine ReachFT.glue F (selHead w i) [(13, 4)] [] [(13, BitVec.ofNat 32 w, 4)] hph hpc h13 hcode
      ⟨fun p hp => by simp only [List.mem_singleton] at hp; subst hp; rw [h13]; exact g.fsp4,
        fun _ h => absurd h List.not_mem_nil, cnt_rd g h13 htop⟩
      (traceAll_blockTr (by rfl) htrh hpc (by simp [h13])) (fun hpc1 h131 hc1 _ => ?_) hgh
    obtain ⟨sm, sz⟩ := sel_facts w i t hi256 h4 h1020
    rw [h13, hv] at sz
    have hi1 : Inv Rs c G m0 (selSt st) E (execAll (selHead w i) t).mem := by rw [sm]; exact hi
    have h131' : (execAll (selHead w i) t).regs 13 = G.fsp c := h131
    refine bc_run F hbc hpbc hpc1 h131 htN (b := !(v.val c (G.fsp c) == BitVec.ofNat 32 i))
      (by simp only [condPassed, NE]; rw [sz]; rfl) (fun hz => ?_) (fun hz => ?_)
    · -- arm 0
      have hb : (v.val c (G.fsp c) == BitVec.ofNat 32 i) = false := by
        simp only [condPassed, NE] at hz; rw [sz] at hz; simpa using hz
      refine prog_run g F hcR p₀ h0 rfl hp0b hp4 (at_jump Rs m0 h131' hc1 (holds_sp h131') hi1 rfl)
        (fun _ u hu hr => ?_) (fun l hl => by rw [hx0] at hl; cases hl)
      obtain ⟨hpcu, h13u, hcu, -, hiu, -⟩ := hu
      obtain ⟨hpe, hr2⟩ := piecesAt_cons hr
      simp only [Piece.instrs, Piece.size_b] at hpe hr2
      rw [piecesAt_append, Prog.size_emit, Bool.and_eq_true] at hr2
      obtain ⟨-, hpk⟩ := piecesAt_cons hr2.2
      simp only [Piece.size_b] at hpk
      refine b_run F hbe0 hpe hpcu h13u htN ?_
      exact hK _ u
        (Inv.weaken Rs m0 hiu (fun p hp => (List.mem_filter.mp hp).1) (fun x hx => List.mem_append_left _ hx))
        h13u hcu (by simp [hb]) hpk
    · -- arm 1
      have hb : (v.val c (G.fsp c) == BitVec.ofNat 32 i) = true := by
        simp only [condPassed, NE] at hz; rw [sz] at hz; simpa using hz
      refine b_run F hbo1 hpb1 (by simp [State.pc, State.setReg]) (by simpa [State.setReg] using h131) htN ?_
      refine prog_run g F hcR p₁ h1 rfl hp1b hp1p
        (at_jump Rs m0 (by simpa [State.setReg] using h131') (by simpa [State.setReg] using hc1)
          (holds_sp (by simpa [State.setReg] using h131')) (by simpa [State.setReg] using hi1) rfl)
        (fun _ u hu hr => ?_) (fun l hl => by rw [hx1] at hl; cases hl)
      obtain ⟨hpcu, h13u, hcu, -, hiu, -⟩ := hu
      obtain ⟨hpe, hpk⟩ := piecesAt_cons hr
      simp only [Piece.instrs, Piece.size_b] at hpe hpk
      refine b_run F hbe1 hpe hpcu h13u htN ?_
      exact hK _ u
        (Inv.weaken Rs m0 hiu (fun p hp => (List.mem_filter.mp hp).2 |> of_decide_eq_true)
          (fun x hx => List.mem_append_right _ hx))
        h13u hcu (by simp [hb]) hpk

  | .xit gs s cc sh l k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.ty] at hty
    cases hx : xitSt G st gs s cc with
    | none => simp [hx] at hty
    | some p =>
    obtain ⟨st2, b⟩ := p
    rw [hx] at hty
    obtain ⟨r, hr, hdec, hcc, hs⟩ := xitSt_some G hx
    have hex2 : st2.ex = none := by rw [xitSt_ex G hx]; exact hex
    simp only [Prog.bok, Bool.and_eq_true] at hbok
    obtain ⟨⟨⟨hpb, hsb⟩, hbr⟩, hkb⟩ := hbok
    simp only [Prog.emit, List.append_assoc] at hp
    have htN : G.top ≤ G.N := g.top
    -- the block and its store, to the branch at `o + xitSz gs s`
    have hpre : ∀ Ψ' : TrP, (∀ u, At Rs B c G m0 (o + xitSz gs s) st2 E u → condPassed cc u = b →
          piecesAt B (o + xitSz gs s) (xitBr cc sh (o + xitSz gs s) (J.getD l 0) ++
            (k.emit cE bE J (o + xitSz gs s + xbSz sh) ++ rest)) = true → ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q Ψ') →
        ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t Q
          (xitT cE bE G (fun a => (ads a).T) c o st gs s Ψ') := by
      intro Ψ' kB
      cases s with
      | none =>
        simp only [xitPost] at hs; subst hs
        simp only [xitT]
        exact pub_runF Rs ads m0 g F hr hpb (by simpa [xitP] using hp) hat fun u hu hfl hr' =>
          kB u hu (hfl cc b hdec) hr'
      | some p =>
        obtain ⟨q, o'⟩ := p
        simp only [xitPost] at hs
        simp only [xitT]
        refine pub_runF Rs ads m0 g F hr hpb (by simpa [xitP] using hp) hat fun u1 hu1 hfl hr1 => ?_
        exact spill_runF Rs ads m0 g F (st := { st with σ := r.σ, ρ := [] }) hs hsb
          (by simpa [Op.pieces, strR] using hr1) hu1 fun u hu hf hr2 =>
          kB u (by simpa [Op.size, Op.pieces, piecesSize, xitSz, Nat.add_assoc, seqSize, Instr.size] using hu)
            (by rw [hf]; exact hfl cc b hdec)
            (by simpa [Op.size, Op.pieces, piecesSize, xitSz, Nat.add_assoc, seqSize, Instr.size] using hr2)
    simp only [Prog.tr, hx, Option.map_some, Option.getD_some]
    refine hpre _ fun u hu hcu hpu => ?_
    rw [piecesAt_append, xitBr_size, Bool.and_eq_true] at hpu
    obtain ⟨hpbr, hpk⟩ := hpu
    have h13u := hu.2.1
    have hneg : condPassed (cc ^^^ 1) u = !b := by
      rw [condPassed_fl, condFl_xor1 cc hcc, ← condPassed_fl, hcu]
    -- the fall to the rest
    have kF : b = false → ∀ u', At Rs B c G m0 (o + xitSz gs s + xbSz sh) st2 E u' →
        ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u' Q (Prog.tr cE bE G (fun a => (ads a).T) c k (o + xitSz gs s + xbSz sh) st2 Ψ J Ψs) := by
      intro hb u' hu'
      subst hb
      simp only at hty
      refine prog_run g F hcR k hty hex2 hkb hpk hu' (fun hn u'' hu'' hr'' => kk hn u''
        (by simpa [Prog.size, Prog.ev, hx, Nat.add_assoc] using hu'')
        (by simpa [Prog.size, Nat.add_assoc] using hr''))
        (fun l' hl' u'' hu'' => kx l' hl' u'' (by simpa [Prog.ev, hx] using hu''))
    -- the exit
    have kT : b = true → ∀ u', At Rs B c G m0 (J.getD l 0) st2 E u' → ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u' Q (Ψs.getD l (Tr.is [])) := by
      intro hb u' hu'
      subst hb
      simp only [Option.some.injEq] at hty; subst hty
      exact kx l rfl u' (by simpa [Prog.ev, hx] using At.exs Rs m0 (some l) hu')
    cases sh with
    | true =>
      simp only [brOk, ↓reduceIte, xitBr] at hbr hpbr ⊢
      obtain ⟨hpi, -⟩ := piecesAt_cons hpbr
      simp only [Piece.instrs] at hpi
      refine bc_run F hbr hpi hu.1 h13u htN hcu (fun ht => ?_) (fun hf => ?_)
      · cases b with
        | false => rw [hcu] at ht; cases ht
        | true => exact kT rfl _ (at_br Rs m0 hu)
      · cases b with
        | true => rw [hcu] at hf; cases hf
        | false => exact kF rfl _ (by simpa [xbSz] using at_br Rs m0 (o' := o + xitSz gs s + 2) hu)
    | false =>
      simp only [brOk, Bool.false_eq_true, ↓reduceIte, xitBr, Bool.and_eq_true] at hbr hpbr ⊢
      obtain ⟨hpi, hpr⟩ := piecesAt_cons hpbr
      obtain ⟨hpj, -⟩ := piecesAt_cons hpr
      simp only [Piece.instrs, Piece.size_bcond] at hpi hpj
      refine bc_run F hbr.1 hpi hu.1 h13u htN hneg (fun ht => ?_) (fun hf => ?_)
      · cases b with
        | true => rw [hneg] at ht; cases ht
        | false => exact kF rfl _ (by simpa [xbSz] using at_br Rs m0 (o' := o + xitSz gs s + 4) hu)
      · cases b with
        | false => rw [hneg] at hf; cases hf
        | true =>
          refine b_run F hbr.2 hpj (by simp [State.pc, State.setReg]) (by simpa [State.setReg, Geo.fsp] using h13u) htN ?_
          exact kT rfl _ (at_br Rs m0 (at_br Rs m0 (o' := o + xitSz gs s + 2) hu))
  | .hd b h k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.ty] at hty
    cases hb : b.ty cE bE G st with
    | none => simp [hb] at hty
    | some s =>
    rw [hb] at hty
    simp only [Prog.bok, Bool.and_eq_true] at hbok
    obtain ⟨⟨⟨hbb, hjb⟩, hhb⟩, hkb⟩ := hbok
    simp only [Prog.emit, List.append_assoc] at hp
    have htN : G.top ≤ G.N := g.top
    have hX : piecesSize (if h.isNil then [] else [Piece.b (o + b.size cE bE + (if h.isNil then 0 else 2) +
        h.size cE bE)]) = (if h.isNil then 0 else 2) := by split <;> rfl
    have hp2 := pa_skip hp
    rw [Prog.size_emit] at hp2
    have hph := pa_skip hp2
    rw [hX] at hph
    have hpk := pa_skip hph
    rw [Prog.size_emit] at hpk
    have esz : o + (Prog.hd b h k).size cE bE = o + b.size cE bE + (if h.isNil then 0 else 2) + h.size cE bE +
        k.size cE bE := by simp only [Prog.size]; omega
    simp only [Prog.tr, hb]
    -- the rest from `s'` at the join
    have kK : ∀ s' E' u, k.ty cE bE G s' = some st' → s'.ex = none →
        Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 (.hd b h k) st E =
          Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 k s' E' →
        At Rs B c G m0 (o + b.size cE bE + (if h.isNil then 0 else 2) + h.size cE bE) s' E' u →
        ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) u Q (Prog.tr cE bE G (fun a => (ads a).T) c k (o + b.size cE bE + (if h.isNil then 0 else 2) +
          h.size cE bE) s' Ψ J Ψs) := by
      intro s' E' u hk hn' hE hu
      refine prog_run g F hcR k hk hn' hkb hpk hu (fun hn u' hu' hr' => kk hn u' ?_ ?_)
        (fun l hl u' hu' => kx l hl u' (by rw [hE]; exact hu'))
      · rw [esz, hE]; exact hu'
      · rw [esz]; exact hr'
    refine prog_run g F hcR b hb hex hbb hp hat (fun hn u hu hr => ?_) (fun l hl u hu => ?_)
    · -- the body falls: to the join
      simp only [hn] at hty
      have hE : Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 (.hd b h k) st E =
          Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 k s
            (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c m0 b st E) := by
        simp only [Prog.ev, hb, hn]
      cases hnl : h.isNil with
      | true =>
        obtain rfl := Prog.isNil_eq hnl
        simp only [Prog.isNil, ↓reduceIte, Prog.size, Nat.add_zero] at kK ⊢
        exact kK s _ u hty hn hE hu
      | false =>
        simp only [hnl, Bool.false_eq_true, ↓reduceIte] at kK hr hjb ⊢
        obtain ⟨hpj, -⟩ := piecesAt_cons hr
        simp only [Piece.instrs] at hpj
        rw [show o + b.size cE bE + 2 - 2 = o + b.size cE bE by omega] at hjb ⊢
        exact b_run F hjb hpj hu.1 (by simpa [Geo.fsp] using hu.2.1) htN (kK s _ _ hty hn hE (at_br Rs m0 hu))
    · cases l with
      | succ j =>
        -- an exit of an enclosing construct
        simp only [hl, Option.some.injEq] at hty; subst hty
        exact kx j rfl u (by simpa [Prog.ev, hb, hl] using At.exs Rs m0 (some j) hu)
      | zero =>
        -- the body's exit to the handler `h`
        simp only [hl] at hty
        cases hh : h.ty cE bE G { s with ex := none } with
        | none => simp [hh] at hty
        | some s' =>
        rw [hh] at hty
        simp only [hh]
        refine prog_run g F hcR h hh rfl hhb hph (At.exs Rs m0 none hu) (fun hn u' hu' hr' => ?_)
          (fun l' hl' u' hu' => ?_)
        · simp only [hn, ↓reduceIte] at hty
          exact kK s' _ u' hty hn (by simp only [Prog.ev, hb, hl, hh, hn, ↓reduceIte]) hu'
        · simp only [hl', reduceCtorEq, ↓reduceIte, Option.some.injEq] at hty; subst hty
          exact kx l' hl' u' (by simpa [Prog.ev, hb, hl, hh, hl'] using hu')
  | .wh n b k, J, Ψs, o, st, st', E, t, Q, Ψ, rest, hty, hex, hbok, hp, hat, kk, kx => by
    simp only [Prog.bok, Bool.and_eq_true] at hbok
    obtain ⟨⟨hbb, hbe⟩, hkb⟩ := hbok
    simp only [Prog.emit, List.append_assoc, List.cons_append, List.nil_append] at hp
    have htN : G.top ≤ G.N := g.top
    have hp2 := pa_skip hp
    rw [Prog.size_emit] at hp2
    obtain ⟨hpb, hpk⟩ := piecesAt_cons hp2
    simp only [Piece.instrs, Piece.size_b] at hpb hpk
    rw [show o + b.size cE bE + 2 - 2 = o + b.size cE bE by omega] at hbe
    have esz : o + (Prog.wh n b k).size cE bE = o + b.size cE bE + 2 + k.size cE bE := by
      simp only [Prog.size]; omega
    rw [esz] at kk
    clear esz
    simp only [Prog.ty] at hty
    simp only [Prog.ev] at kk kx
    simp only [Prog.tr]
    rw [show o + b.size cE bE + 2 - 2 = o + b.size cE bE by omega]
    induction n generalizing st E t with
    | zero => simp [whTy] at hty
    | succ n ih =>
      simp only [whTy] at hty
      cases hb : b.ty cE bE G st with
      | none => simp [hb] at hty
      | some s =>
      rw [hb] at hty
      simp only [whTr, hb]
      refine prog_run g F hcR b hb hex hbb hp hat (fun hn u hu hr => ?_) (fun l hl u hu => ?_)
      · -- the body falls: the back branch and the next pass
        simp only [hn] at hty
        refine b_run F hbe hpb hu.1 (by simpa [Geo.fsp] using hu.2.1) htN ?_
        refine ih s _ _ hty hn (at_br Rs m0 hu) (fun hn' u' hu' hr' => kk hn' u' ?_ hr') (fun l hl u' hu' => kx l hl u' ?_)
        · simpa only [whEv, hb, hn] using hu'
        · simpa only [whEv, hb, hn] using hu'
      · cases l with
        | succ j =>
          simp only [hl, Option.some.injEq] at hty; subst hty
          exact kx j rfl u (by simpa only [whEv, hb, hl, List.getD_cons_succ] using At.exs Rs m0 (some j) hu)
        | zero =>
          -- the exit to the rest
          simp only [hl] at hty
          refine prog_run g F hcR k hty rfl hkb hpk (At.exs Rs m0 none hu) (fun hn u' hu' hr' => kk hn u' ?_ hr')
            (fun l' hl' u' hu' => kx l' hl' u' ?_)
          · simpa only [whEv, hb, hl] using hu'
          · simpa only [whEv, hb, hl] using hu'

end run

end M0Crypto.Release.Ed25519CallProg
