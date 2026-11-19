import M0Crypto.Release.Ed25519CallProgEntryRun
import M0Crypto.Release.Ed25519CallProgEffect
import M0Crypto.Release.StackEffectGP

set_option linter.unusedSimpArgs false

/-!
# Call programs: the byte effect of an entry

An entry's trace keeps the stack discipline over the window of `36 + N` bytes below its entry SP
(`entry_good`). The body keeps SP at the frame's and an invariant (`BI`): the saved words and the
written bytes of every live view are in the written set (`Ext`), where a SHA-512 context's
written bytes are the bytes before its buffer and its pending bytes. Each construct is a segment
at the frame's SP (`Seg`); its reads come from the views it reads, and the views it leaves are
written. The facts a construct needs beyond `Prog.ty` are decided per site (`Prog.eok`): the
loads' and the blocks' symbolic effects, that a callee's regions use its public registers, and
that a context's stream length is the one its callee reads and extends.
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

/-! ## The body's invariant -/

/-- The written bytes of a view: all of it, apart from a context's buffer past its pending bytes. -/
def Kd.ini (c : Ctx) (sp : Word) : Kd → Nat
  | .ctx n => ctxBuf + slen c sp n % 128
  | k => k.sz

theorem Kd.ini_le {c : Ctx} {sp : Word} {k k' : Kd} (h : k.le k' = true) : k'.ini c sp = k.ini c sp := by
  simp only [Kd.le, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | ⟨hk, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · rfl
  · cases k <;> simp only [Kd.isRef, Bool.false_eq_true] at hk <;> rfl
  · rfl
  · rfl

/-- The written bytes of the views `Γ`. -/
def Ext (c : Ctx) (sp : Word) (Γ : List (Loc × Kd)) (y : Word) : Prop :=
  ∃ p ∈ Γ, Region (p.1.addr c sp) (Kd.ini c sp p.2) y

/-- The saved words below `sp0`. -/
abbrev Sv (sp0 y : Word) : Prop := Region (sp0 - 36#32) 36 y

/-- **The body's invariant** in the window of `n` bytes below `sp0`, at static state `st`: SP at
the frame's, and the bytes `X0` written before the body and the written bytes of the live views
written. -/
structure BI (c : Ctx) (G : Geo) (sp0 : Word) (n : Nat) (X0 : Word → Prop) (st : St) (q : Ef) : Prop where
  sp : q.sp = G.fsp c
  ab : ∀ y, q.U y → AtOrAboveSp sp0 (G.fsp c) y
  sv : ∀ y, X0 y → q.U y
  ex : ∀ y, Ext c (G.fsp c) st.Γ y → BelowEntry sp0 n y → q.U y

/-- **The frame in the window** of `n` bytes below `sp0`: the window holds the body's, and a
buffer's bytes in it lie above the frame and, if the body may read them, in `X0`. -/
structure Frm (c : Ctx) (G : Geo) (sp0 : Word) (n : Nat) (X0 : Word → Prop) : Prop where
  room : (sp0 - c.sp0).toNat + G.N ≤ n
  n32 : n < 2 ^ 32
  top : G.top ≤ G.N
  ext : ∀ r : SR, r.ok G = true → r.loc.isEx = true → ∀ y, Has (r.rgns G c) y → BelowEntry sp0 n y →
    AtOrAboveSp sp0 (G.fsp c) y ∧ (r.acc G false = true → X0 y)

section body
variable {c : Ctx} {G : Geo} {sp0 : Word} {n : Nat} {X0 : Word → Prop}

/-- A segment at the frame's SP that reads written views or saved words and writes the views it
leaves. -/
theorem bi_seg {st st' : St} {X Y : Word → Prop} {a : List Event} (h : Seg sp0 n (G.fsp c) X a Y)
    (hX : ∀ y, X y → BelowEntry sp0 n y → Ext c (G.fsp c) st.Γ y ∨ X0 y)
    (hΓ : ∀ y, Ext c (G.fsp c) st'.Γ y → BelowEntry sp0 n y →
      Ext c (G.fsp c) st.Γ y ∨ X0 y ∨ Y y) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is a) (BI c G sp0 n X0 st') :=
  GP.seg h (fun _ hq => ⟨hq.sp, hq.ab, fun y hy hb => (hX y hy hb).elim (hq.ex y · hb) (hq.sv y)⟩)
    fun _ _ hq s u w ab => ⟨s, ab, fun y hy => u y (hq.sv y hy), fun y hy hb =>
      (hΓ y hy hb).elim (fun h => u y (hq.ex y h hb)) fun h => h.elim (fun h => u y (hq.sv y h)) (w y · hb)⟩

theorem BI.sub {st st' : St} (h : ∀ p ∈ st'.Γ, p ∈ st.Γ) {q : Ef} (hq : BI c G sp0 n X0 st q) : BI c G sp0 n X0 st' q :=
  ⟨hq.sp, hq.ab, hq.sv, fun y hy hb => hq.ex y (let ⟨p, hp, hr⟩ := hy; ⟨p, h p hp, hr⟩) hb⟩

theorem sub_sub_add (a b : Word) (k : Nat) : a - (b - BitVec.ofNat 32 k) = a - b + BitVec.ofNat 32 k := by
  bv_omega

theorem lit_in {a : Word} {p k N : Nat} (hk : k < 4) (hp : p + 4 ≤ N) (hN : N < 2 ^ 32) :
    Region a N (a + BitVec.ofNat 32 p + BitVec.ofNat 32 k) := by
  simp only [Region]; bv_omega

theorem sub_off_lt {a y : Word} {o m : Nat} (h : Region (a + BitVec.ofNat 32 o) m y) (hm : o + m < 2 ^ 32) :
    (y - a).toNat < o + m := by
  simp only [Region] at h; bv_omega

variable (fm : Frm c G sp0 n X0)
include fm

theorem fsp_dist : (sp0 - G.fsp c).toNat = (sp0 - c.sp0).toNat + G.top := by
  have := fm.room; have := fm.n32; have := fm.top
  rw [Geo.fsp, sub_sub_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A frame region lies at or above the frame's SP. -/
theorem Frm.fr_above {o m : Nat} {y : Word} (h : o + m ≤ G.top) (hy : Region (G.fsp c + BitVec.ofNat 32 o) m y) :
    AtOrAboveSp sp0 (G.fsp c) y := by
  have := fsp_dist fm; have := fm.room; have := fm.n32; have := fm.top
  show (y - G.fsp c).toNat < (sp0 - G.fsp c).toNat
  have := sub_off_lt hy (by omega); omega

/-- **A resolved region** lies at or above the frame's SP, and a readable buffer's bytes in the
window are in `X0`. -/
theorem Frm.sr_above {r : SR} (ho : r.ok G = true) {y : Word} (hy : Has (r.rgns G c) y)
    (hb : BelowEntry sp0 n y) : AtOrAboveSp sp0 (G.fsp c) y ∧ (r.loc.isEx = true → r.acc G false = true → X0 y) := by
  cases hx : r.loc.isEx
  · refine ⟨?_, nofun⟩
    obtain ⟨q, hq, hy⟩ := hy
    unfold SR.rgns at hq; split at hq; · exact absurd hq List.not_mem_nil
    simp only [List.mem_singleton] at hq; subst hq
    obtain ⟨l, m⟩ := r
    cases l with
    | ex => simp [Loc.isEx] at hx
    | rg => simp [SR.ok] at ho
    | fr o =>
      cases m with
      | p => simp [SR.ok] at ho
      | k m =>
        simp only [SR.ok, decide_eq_true_eq] at ho
        exact fm.fr_above ho (rgn_region hy (by have := fm.top; have := fm.room; have := fm.n32; show m < _; omega))
  · exact ⟨(fm.ext r ho hx y hy hb).1, fun _ => (fm.ext r ho hx y hy hb).2⟩

end body

/-- **An entry's frame**: 36 saved bytes above it, and the saved words written before the body. -/
theorem frm_entry {c : Ctx} {G : Geo} {sp0 : Word} {Wc Rc : List Rgn} (g : GeoOk c G Wc Rc)
    (hsp : c.sp0 = sp0 - 36#32) (h36 : 36 + G.N ≤ sp0.toNat) : Frm c G sp0 (36 + G.N) (Sv sp0) := by
  have e3 : c.sp0.toNat = sp0.toNat - 36 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hd : (sp0 - c.sp0).toNat = 36 := by rw [hsp]; simp [BitVec.toNat_sub]; omega
  refine ⟨by omega, by have := sp0.isLt; omega, g.top, fun r ho hx y hy hb => ?_⟩
  have hw : ¬ Region (c.sp0 - BitVec.ofNat 32 G.N) G.N y := fun h =>
    Sep.not_has (g.ex_win ho hx) hy ⟨_, List.mem_singleton_self _, Rgn.of_region h⟩
  have hs : Sv sp0 y := by
    have := g.room; have := y.isLt; have := sp0.isLt
    simp only [Sv, BelowEntry, Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at hb hw ⊢; omega
  refine ⟨?_, fun _ => hs⟩
  have e2 := g.fsp_toNat; have := g.top; have := y.isLt; have := sp0.isLt
  simp only [Sv, Region, AtOrAboveSp, BitVec.toNat_sub, BitVec.toNat_ofNat] at hs ⊢; omega

/-! ## The decided checks per site -/

/-- The frame from SP. -/
def frR (G : Geo) : SExpr × Nat := (.reg0 13, G.top)

/-- The frame word at `o`. -/
def slotR (o : Nat) : SExpr × Nat := (.add (.reg0 13) (.const (BitVec.ofNat 32 o)), 4)

/-- The frame words a call's loads read. -/
def ldsIni (as : List (LowReg × Ld)) : List (SExpr × Nat) :=
  as.filterMap fun a => match a.2 with | .W o _ => some (slotR o) | _ => none

/-- A length that is a constant or a public register. -/
def lenPub (ps : List PubW) : ALen → Bool
  | .k _ => true
  | .r j => PubW.r j ∈ ps

/-- The stream lengths a callee reads: its context's, if it reads the count. -/
def ctxIn (s : CalleeS) (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) : List SV :=
  if PubW.n 0 ∈ s.pubs then (ctxAt Γ σ 0).getD [] else []

/-- The lengths of the raw inputs, as symbolic values. -/
def rawSVs (σ : List (Reg × SV)) : List (Reg × Nat × In) → Option (List SV)
  | [] => some []
  | (_, _, .raw (.r j)) :: xs => (σ.lookup j).bind fun v => (rawSVs σ xs).map (v :: ·)
  | (_, _, .raw (.k _)) :: _ => none
  | (_, _, .view _) :: xs => rawSVs σ xs

/-- The registers are known once each, below 14. -/
def σOk (σ : List (Reg × SV)) : Bool := (σ.map (·.1)).Nodup && σ.all (·.1.val < 14)

/-- **The decided facts of a call** beyond its typing: the registers are known once each, `sp` is
the frame's, the regions use public registers, an input context is the one at `r0` whose count
the callee reads, and an output context's stream is the input's with the raw inputs appended. -/
def callOk (s : CalleeS) (Γ : List (Loc × Kd)) (σ : List (Reg × SV)) : Bool :=
  σOk σ && σ.lookup 13 == some (.sp 0) && PubW.r 13 ∈ s.pubs &&
  (s.io.rd ++ s.io.wr).all (fun r => PubW.r r.r ∈ s.pubs && lenPub s.pubs r.len) &&
  s.io.ins.all (fun x => x.2.2 == .view .rw || PubW.r x.1 ∈ s.pubs && match x.2.2 with
    | .raw l => lenPub s.pubs l
    | .view (.ctx n) => x.1 == 0 && x.2.1 == 0 && PubW.n 0 ∈ s.pubs && ctxAt Γ σ 0 == some n
    | .view _ => true) &&
  s.io.outs.all (fun x => PubW.r x.1 ∈ s.pubs && match x.2.2 with
    | .ctx n => (rawSVs σ s.io.ins).any fun l => n == ctxIn s Γ σ ++ l
    | _ => true)

/-- A register of a block's state. -/
def regIn (L : List Reg) (r : Reg) : Bool := r ∈ L && r != 15

/-- Kinds of one written extent: neither is a context, and their sizes agree. -/
def Kd.sameIni (k k' : Kd) : Bool := !(k matches .ctx _) && !(k' matches .ctx _) && k.sz == k'.sz

theorem Kd.ini_same {c : Ctx} {sp : Word} {k k' : Kd} (h : k.sameIni k' = true) : k'.ini c sp = k.ini c sp := by
  simp only [Kd.sameIni, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases k <;> cases k' <;> simp_all [Kd.ini]

/-- An output in place: an input at its register and offset is a view of the same extent. -/
def inPlace (ins : List (Reg × Nat × In)) (x : Reg × Nat × Kd) : Bool :=
  ins.any fun y => y.1 == x.1 && y.2.1 == x.2.1 && match y.2.2 with
    | .view k' => x.2.2.sameIni k'
    | .raw _ => false

theorem inPlace_mem {ins : List (Reg × Nat × In)} {r : Reg} {off : Nat} {k : Kd} (h : inPlace ins (r, off, k) = true) :
    ∃ k', (r, off, In.view k') ∈ ins ∧ k.sameIni k' = true := by
  obtain ⟨⟨r', off', i⟩, hm, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, hp⟩ := hp
  cases i with
  | view k' => exact ⟨k', hm, hp⟩
  | raw _ => simp at hp

/-- **The decided effect of a block**: its inputs are views other than contexts, or bytes of a
constant length, at registers of the block, its reads are of its inputs, its accesses lie in its footprints, and each output is
an input in place or is written whole. -/
def blkOk (b : BlockS) (σ : List (Reg × SV)) : Bool :=
  σOk σ && (b.io.rd ++ b.io.wr).all (fun r => regIn b.L r.r) &&
  b.io.ins.all (fun x => match x.2.2 with
    | .view (.ctx _) => false
    | .view .rw => true
    | .view _ => regIn b.L x.1
    | .raw l => regIn b.L x.1 && l matches .k _) &&
  b.io.outs.all (fun x => regIn b.L x.1 && !(x.2.2 matches .ctx _)) &&
  blkChk (b.io.ins.map fun x => rgnE x.1 x.2.1 (x.2.2.kd fun _ => 0).sz)
    (b.io.outs.filterMap fun x => if inPlace b.io.ins x then none else
      some (rgnE x.1 x.2.1 x.2.2.sz))
    ((b.io.rd ++ b.io.wr).map fun r => rgnE r.r r.off r.len.kv) b.g

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS) (G : Geo)

/-- The frame words of the word views `Γ`: what a public block may read. -/
def pwIni (Γ : List (Loc × Kd)) : List (SExpr × Nat) :=
  Γ.filterMap fun p => match p with
    | (.fr o, .pw _) => some (slotR o)
    | _ => none

/-- The decided effect of a construct. -/
def Op.eok (st : St) : Op A Bk → Bool
  | .call a as => blkChk (ldsIni as) [] [frR G] (ldsEmit as) && callOk (cE a) st.Γ (regsOf st.Γ st.σ as)
  | .blk b as => blkChk (ldsIni as) [] [frR G] (ldsEmit as) && blkOk (bE b) (regsOf st.Γ st.σ as)
  | .spill r o => blkChk [] [slotR o] [slotR o] [.strSp r (BitVec.ofNat 8 (o / 4))]
  | .drop _ _ => true
  | .ld r (.C ..) => blkChk [] [] [frR G] [.addPc r]
  | .ld r l => blkChk (ldsIni [(r, l)]) [] [frR G] (l.emit r)
  | .pub g => blkChk (pwIni st.Γ) [] [frR G] g
  | .keep _ => true
  | .ldb rd rb ri => blkChk [ldbR rb ri] [] [ldbR rb ri] [ldbI rd rb ri]
  | .isl _ _ => true

/-- The decided effects of the passes of a loop with exits: the body's typing `tb` and effects
`eb`, the rest's effects `ek`. -/
def whOk (tb : St → Option St) (eb ek : St → Bool) : Nat → St → Bool
  | 0, _ => false
  | n + 1, st => eb st && match tb st with
    | some s => match s.ex with
      | none => whOk tb eb ek n s
      | some 0 => ek { s with ex := none }
      | some _ => true
    | none => false

/-- **The decided effects of a program**, per site, on the path the static decisions take. -/
def Prog.eok : Prog A Bk → St → Bool
  | .nil, _ => true
  | .op x k, st => x.eok cE bE G st && match x.ty cE bE G st with
    | some st' => k.eok st'
    | none => false
  | .loop cnt n b k, st => blkChk [] [slotR cnt] [slotR cnt] (loopHead cnt n) &&
    blkChk [slotR cnt] [slotR cnt] [slotR cnt] (loopDec cnt) && b.eok (loopSt st cnt) && k.eok (loopOut st cnt)
  | .sel w i p₀ p₁ k, st => blkChk [slotR w] [] [slotR w] (selHead w i) && p₀.eok (selSt st) &&
    p₁.eok (selSt st) && match p₀.ty cE bE G (selSt st), p₁.ty cE bE G (selSt st) with
    | some s₀, some s₁ => k.eok (joinSt s₀ s₁)
    | _, _ => false
  | .xit g s cc _ _ k, st => (Op.pub g : Op A Bk).eok cE bE G st &&
    (match s with | none => true | some (q, o) => (Op.spill q o : Op A Bk).eok cE bE G st) &&
    match xitSt G st g s cc with
    | some (st2, false) => k.eok st2
    | some (_, true) => true
    | none => false
  | .hd b h k, st => b.eok st && match b.ty cE bE G st with
    | some s => match s.ex with
      | none => k.eok s
      | some 0 => h.eok { s with ex := none } && match h.ty cE bE G { s with ex := none } with
        | some s' => if s'.ex = none then k.eok s' else true
        | none => false
      | some _ => true
    | none => false
  | .wh n b k, st => whOk (fun s => b.ty cE bE G s) (fun s => b.eok s) (fun s => k.eok s) n st

end

/-! ## Facts from the checks -/

theorem lookup_of_mem {σ : List (Reg × SV)} (hn : (σ.map (·.1)).Nodup) :
    ∀ {p}, p ∈ σ → σ.lookup p.1 = some p.2 := by
  induction σ with
  | nil => nofun
  | cons q σ ih =>
    intro p hp
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [List.lookup]
    · have : (p.1 == q.1) = false := beq_eq_false_iff_ne.mpr fun h => hn.1 (h ▸ List.mem_map_of_mem hp)
      simp only [List.lookup, this]; exact ih hn.2 hp

theorem holds_σv {c : Ctx} {sp : Word} {σ : List (Reg × SV)} (h : σOk σ = true) : Holds c sp σ (σv c sp σ) := by
  simp only [σOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact fun p hp => ⟨h.2 p hp, by simp [σv, lookup_of_mem h.1 hp]⟩

theorem getD_idxOf {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) (d : β) {l : List α} {a : α} (h : a ∈ l) :
    (l.map f).getD (l.idxOf a) d = f a := by
  have hl := List.idxOf_lt_length_of_mem h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem_idxOf hl]; rfl

theorem All2.ex {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, All2 R l l' → (∀ a ∈ l, ∃ b, R a b) ∧ ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], _ => ⟨nofun, nofun⟩
  | a :: l, b :: l', ⟨h, t⟩ => by
    obtain ⟨h1, h2⟩ := All2.ex t
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, h⟩
      · exact h1 x hx
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, h⟩
      · obtain ⟨x, hx, r⟩ := h2 y hy; exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem inR_region {t : State} {rs : List (SExpr × Nat)} {y : Word} (h : InR t rs y) :
    ∃ r ∈ rs, Region (r.1.denote t) r.2 y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  refine ⟨r, hr, ?_⟩
  show ((r.1.denote t + BitVec.ofNat 32 o) - r.1.denote t).toNat < r.2
  rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega

theorem inR_of_region {t : State} {r : SExpr × Nat} {rs : List (SExpr × Nat)} (hr : r ∈ rs) {y : Word}
    (h : Region (r.1.denote t) r.2 y) : InR t rs y :=
  ⟨r, hr, (y - r.1.denote t).toNat, h, by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩

theorem region_shift {a y : Word} {d n m : Nat} (h : Region (a + BitVec.ofNat 32 d) n y) (hm : d + n ≤ m) :
    Region a m y := by
  have h' : (y - (a + BitVec.ofNat 32 d)).toNat < n := h
  show (y - a).toNat < m
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h' ⊢
  have := a.isLt; have := y.isLt; omega

theorem ext_mem {c : Ctx} {sp : Word} {Γ : List (Loc × Kd)} {p : Loc × Kd} (hp : p ∈ Γ) {y : Word}
    (h : Region (p.1.addr c sp) (Kd.ini c sp p.2) y) : Ext c sp Γ y := ⟨p, hp, h⟩

theorem ext_sub {c : Ctx} {sp : Word} {Γ Γ' : List (Loc × Kd)} (h : ∀ p ∈ Γ', p ∈ Γ) {y : Word}
    (hy : Ext c sp Γ' y) : Ext c sp Γ y :=
  let ⟨p, hp, hr⟩ := hy; ⟨p, h p hp, hr⟩

theorem keep_sub {Γ : List (Loc × Kd)} {ws : List SR} {outs : List (Loc × Kd)} :
    ∀ p ∈ keepViews Γ ws outs, p ∈ Γ := fun _ h => (List.mem_filter.mp h).1

theorem kd_ini {c : Ctx} {sp : Word} {k : Kd} (h : ¬ k matches .ctx _) : Kd.ini c sp k = k.sz := by
  cases k <;> simp_all [Kd.ini]

section body
variable {c : Ctx} {G : Geo} {sp0 : Word} {n : Nat} {X0 : Word → Prop}
  (fm : Frm c G sp0 n X0)
include fm

/-- **An input's bytes** below the entry SP are written bytes of a view or saved words. -/
theorem src_ext {st : St} {σ : List (Reg × SV)} {regs : Reg → Word} (hσ : Holds c (G.fsp c) σ regs)
    {x : Reg × Nat × In} {s : Src} (hs : inSrc G st σ x = some s) {y : Word}
    (hy : Region (regs x.1 + BitVec.ofNat 32 x.2.1) (Kd.ini c (G.fsp c) (x.2.2.kd regs)) y)
    (hb : BelowEntry sp0 n y) : Ext c (G.fsp c) st.Γ y ∨ X0 y := by
  by_cases hw : x.2.2 = .view .rw
  · obtain ⟨r, off, i⟩ := x; simp only at hw; subst hw
    simp [In.kd, Kd.ini, Kd.sz, Region] at hy
  simp only [inSrc, hw, ↓reduceIte] at hs
  obtain ⟨r, off, i⟩ := x
  cases hl : locOf σ r off with
  | none => cases i <;> simp [inSrc, hl] at hs
  | some l =>
    simp only [locOf_addr hσ hl] at hy
    have hsl : ∀ n, findSlice st.Γ l n = some s → Region (l.addr c (G.fsp c)) n y → Ext c (G.fsp c) st.Γ y := by
      intro n hf hy
      obtain ⟨l0, n0, d, rfl, hm, hd, hn⟩ := findSlice_some hf
      rw [Loc.diff_addr hd] at hy
      exact ext_mem hm (region_shift hy hn)
    cases i with
    | view k =>
      simp only [inSrc, hl] at hs
      by_cases hm : viewOf st.Γ l k = true
      · obtain ⟨k', hk', hle⟩ := viewOf_mem hm
        exact .inl (ext_mem hk' (by simp only [In.kd] at hy; rwa [Kd.ini_le hle] at hy))
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hs
        cases k <;> try simp only [reduceCtorEq] at hs
        case bytes => exact .inl (hsl _ hs hy)
        case sc | cl =>
          obtain ⟨i, k', rfl, rfl, -, -, -, hok, hacc⟩ := refSrc_some hs
          simp only [In.kd, Kd.ini, Kd.sz] at hy
          exact .inr ((fm.sr_above hok (y := y) ⟨_, by simp [SR.rgns, XLen.v], Rgn.of_region hy⟩ hb).2 rfl hacc)
        case fe =>
          split at hs
          · rename_i hc
            simp only [In.kd, Kd.ini, Kd.sz] at hy
            exact .inr ((fm.sr_above hc.2.2.1 (y := y) ⟨_, by simp [SR.rgns, XLen.v], Rgn.of_region hy⟩ hb).2
              hc.2.1 hc.2.2.2)
          · simp at hs
    | raw len =>
      simp only [inSrc, hl] at hs
      cases hr : len.res σ with
      | none => simp [hr] at hs
      | some xl =>
        simp only [hr] at hs
        simp only [In.kd, Kd.ini, Kd.sz, ALen.res_val hσ hr] at hy
        have hex : (if (st.X = [] ∨ codeRd G st l = true) ∧ l.isEx = true ∧ SR.ok G ⟨l, xl⟩ = true ∧
            SR.acc G false ⟨l, xl⟩ = true then some (Src.ext ⟨l, xl⟩) else none) = some s → X0 y := by
          intro h
          split at h
          · rename_i hc
            have hne : xl.v c ≠ 0 := fun h0 => by rw [h0] at hy; exact Nat.not_lt_zero _ hy
            exact (fm.sr_above hc.2.2.1 (y := y) ⟨_, by simp [SR.rgns, hne], Rgn.of_region hy⟩ hb).2 hc.2.1 hc.2.2.2
          · simp at h
        cases xl with
        | k n =>
          simp only at hs
          cases hf : findSlice st.Γ l n with
          | some s' =>
            simp only [hf] at hs
            exact .inl (hsl n (hf.trans hs) hy)
          | none => simp only [hf, Option.none_or] at hs; exact .inr (hex hs)
        | p j => exact .inr (hex hs)

/-- The bytes of the resolved footprints lie at or above the frame's SP. -/
theorem rgns_above {σ : List (Reg × SV)} {regs : Reg → Word} (hσ : Holds c (G.fsp c) σ regs) {l : List SRgn}
    {ws : List SR} (hm : l.mapM (SRgn.res σ) = some ws) (hok : ∀ w ∈ ws, w.ok G = true) {y : Word}
    (hy : Has (rgnsC regs l) y) (hb : BelowEntry sp0 n y) : AtOrAboveSp sp0 (G.fsp c) y := by
  rw [rgnsC_eq hσ (mapM_forall₂ hm)] at hy
  obtain ⟨q, hq, hy⟩ := hy
  obtain ⟨w, hw, hq⟩ := List.mem_flatMap.mp hq
  exact (fm.sr_above (hok w hw) ⟨q, hq, hy⟩ hb).1

end body

/-! ## Interface facts -/

theorem ioRes_parts {G : Geo} {st : St} {σ : List (Reg × SV)} {io : Iface} {r : IoR}
    (h : ioRes G st σ io = some r) :
    io.ins.mapM (inSrc G st σ) = some r.srcs ∧
    io.outs.mapM (fun x => (locOf σ x.1 x.2.1).map (·, x.2.2)) = some r.outs ∧
    io.wr.mapM (SRgn.res σ) = some r.wrs ∧ (∀ w ∈ r.wrs, w.ok G = true) ∧
    ∃ rds, io.rd.mapM (SRgn.res σ) = some rds ∧ ∀ w ∈ rds, w.ok G = true := by
  simp only [ioRes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨srcs, hsrc, outs, hout, wrs, hwr, rds, hrd, h⟩ := h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    exact ⟨hsrc, hout, hwr, fun w hw => (hc.1.1.1.1.1.1.1.1.1 w hw).1, rds, hrd,
      fun w hw => (hc.1.1.1.1.1.1.1.1.2 w hw).1⟩
  · simp at h

theorem rgnC_congr {f f' : Reg → Word} {r : SRgn} (h1 : f r.r = f' r.r) (h2 : ∀ j, r.len = .r j → f j = f' j) :
    r.rgnC f = r.rgnC f' := by
  cases hl : r.len with
  | k => simp [SRgn.rgnC, ALen.val, hl, h1]
  | r j => simp [SRgn.rgnC, ALen.val, hl, h1, h2 j hl]

theorem rgnsC_congr {f f' : Reg → Word} : ∀ {l : List SRgn}, (∀ r ∈ l, r.rgnC f = r.rgnC f') →
    rgnsC f l = rgnsC f' l
  | [], _ => rfl
  | r :: l, h => by
    simp only [rgnsC, List.flatMap_cons]
    rw [h r List.mem_cons_self]; exact congrArg _ (rgnsC_congr fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem rgnC_has {f : Reg → Word} {r : SRgn} {y : Word}
    (h : Region (f r.r + BitVec.ofNat 32 r.off) (r.len.val f) y) : Has (r.rgnC f) y := by
  have hne : r.len.val f ≠ 0 := fun h0 => by rw [h0] at h; exact Nat.not_lt_zero _ h
  exact ⟨_, by simp [SRgn.rgnC, hne], Rgn.of_region h⟩

theorem raw_slen {c : Ctx} {sp : Word} {σ : List (Reg × SV)} {f : Reg → Word} :
    ∀ {ins : List (Reg × Nat × In)} {l : List SV}, rawSVs σ ins = some l →
      (∀ x ∈ ins, ∀ j, x.2.2 = .raw (.r j) → f j = σv c sp σ j) → slen c sp l = rawSum f ins
  | [], l, h, _ => by simp [rawSVs] at h; subst h; rfl
  | (_, _, .raw (.r j)) :: xs, l, h, hf => by
    simp only [rawSVs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, l', hl', rfl⟩ := h
    have := raw_slen hl' fun x hx => hf x (List.mem_cons_of_mem _ hx)
    simp only [slen, List.map_cons, List.sum_cons] at this ⊢
    rw [this, rawSum]; simp only [ALen.val, hf _ List.mem_cons_self j rfl, σv, hv]
  | (_, _, .raw (.k _)) :: _, _, h, _ => by simp [rawSVs] at h
  | (_, _, .view _) :: xs, l, h, hf => by
    simp only [rawSVs] at h
    rw [raw_slen h fun x hx => hf x (List.mem_cons_of_mem _ hx)]; rfl

theorem slen_append {c : Ctx} {sp : Word} (a b : List SV) : slen c sp (a ++ b) = slen c sp a + slen c sp b := by
  simp [slen]

theorem rs13 (pc x : Word) : (regState pc [13] [x]).regs 13 = x := by simp [regState, List.lookup]

theorem rs_reg {pc : Word} {L : List Reg} {f : Reg → Word} {r : Reg} (h : regIn L r = true) :
    (regState pc L (L.map f)).regs r = f r := by
  simp only [regIn, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp [regState, h.2, lookup_zip_map f L r h.1]

theorem slot_reg {pc x : Word} {o : Nat} {y : Word} (h : InR (regState pc [13] [x]) [slotR o] y) :
    Region (x + BitVec.ofNat 32 o) 4 y := by
  obtain ⟨r, hr, h⟩ := inR_region h
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotR, SExpr.denote, rs13] at h; exact h

theorem slot_le {G : Geo} {o : Nat} (h : slotOk G o = true) : o + 4 ≤ G.top := by
  simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2

theorem inR_nil {t : State} {y : Word} : ¬ InR t [] y := fun ⟨_, h, _⟩ => nomatch h

/-! ## The constructs -/

section cons
variable {c : Ctx} {G : Geo} {sp0 : Word} {n : Nat} {X0 : Word → Prop}
  (fm : Frm c G sp0 n X0)
include fm

/-- A block of frame words that reads and writes the slot at `o` only. -/
theorem slot_gp {st st' : St} {is : List Instr} {o : Nat} {ini wo : List (SExpr × Nat)} (ho : o + 4 ≤ G.top)
    (h : blkChk ini wo [slotR o] is = true) (pc : Word)
    (hI : ∀ y, InR (regState pc [13] [G.fsp c]) ini y → ∃ k, (Loc.fr o, k) ∈ st.Γ ∧ Kd.ini c (G.fsp c) k = 4 ∧
      Region (G.fsp c + BitVec.ofNat 32 o) 4 y)
    (hΓ : ∀ p ∈ st'.Γ, p ∈ st.Γ ∨ (wo = [slotR o] ∧ p.1 = .fr o ∧ Kd.ini c (G.fsp c) p.2 = 4)) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTr is pc [13] [G.fsp c])) (BI c G sp0 n X0 st') := by
  refine bi_seg (blk_seg h _ (fun _ h => h) fun y hy _ => fm.fr_above ho (slot_reg hy))
    (fun y hy _ => ?_) fun y ⟨p, hp, hy⟩ _ => ?_
  · obtain ⟨k, hk, hs, hr⟩ := hI y hy
    exact .inl ⟨_, hk, by show Region _ (Kd.ini c (G.fsp c) k) y; rw [hs]; exact hr⟩
  · rcases hΓ p hp with hp | ⟨rfl, h1, h2⟩
    · exact .inl ⟨p, hp, hy⟩
    · obtain ⟨l, k⟩ := p; dsimp only at h1 h2; subst h1
      exact .inr (.inr (inR_of_region (List.mem_singleton_self _) (by
        show Region (G.fsp c + BitVec.ofNat 32 o) 4 y; rw [← h2]; exact hy)))

/-- The loads of a call's or a block's registers. -/
theorem lds_gp {st : St} {as : List (LowReg × Ld)} (hk : blkChk (ldsIni as) [] [frR G] (ldsEmit as) = true)
    (hr : ldsRes st.Γ as = true) (pc : Word) :
    GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTr (ldsEmit as) pc [13] [G.fsp c])) (BI c G sp0 n X0 st) := by
  refine bi_seg (blk_seg hk _ (fun _ h => h) fun y hy _ => ?_) (fun y hy _ => .inl ?_) fun y hy _ => .inl hy
  · obtain ⟨r, hr, hy⟩ := inR_region hy
    simp only [frR, List.mem_singleton] at hr; subst hr
    simp only [SExpr.denote, rs13] at hy
    exact fm.fr_above (o := 0) (m := G.top) (by omega) (by rw [BitVec.add_zero]; exact hy)
  · obtain ⟨r, hm, hy⟩ := inR_region hy
    obtain ⟨⟨lr, ld⟩, ha, hm⟩ := List.mem_filterMap.mp hm
    simp only [ldsRes, Bool.and_eq_true, List.all_eq_true] at hr
    have hs := hr.2 _ ha
    cases ld with
    | W o e =>
      simp only [Option.some.injEq] at hm; subst hm
      simp only [Ld.sv] at hs
      cases hp : pwAt st.Γ o with
      | none => simp [hp] at hs
      | some v =>
        simp only [slotR, SExpr.denote, rs13] at hy
        exact ⟨_, pwAt_mem hp, hy⟩
    | _ => simp at hm

/-- A public block: it reads the frame words of word views. -/
theorem pubBlk_gp {st : St} {g : List Instr} (hk : blkChk (pwIni st.Γ) [] [frR G] g = true) (pc : Word) :
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
      | pw v =>
        simp only [Option.some.injEq] at hm; subst hm
        simp only [slotR, SExpr.denote, rs13] at hy
        exact ⟨_, hp, hy⟩
      | _ => simp at hm
    | _ => simp at hm

omit fm in
theorem quiet_gp {st : St} {e : Event} (hx : spExact e.instr = true) (hs : spAfter e.instr (G.fsp c) = G.fsp c)
    (ha : e.accesses = []) : GP sp0 n (BI c G sp0 n X0 st) (Tr.is [e]) (BI c G sp0 n X0 st) := by
  have hn : ∀ y, ¬ (Reads e.accesses y ∨ Writes e.accesses y) := by
    rw [ha]; rintro y (⟨_, h, _⟩ | ⟨_, h, _⟩) <;> cases h
  exact bi_seg (ev_seg (X := fun _ => False) hx hs (fun y hy => absurd hy (hn y)) fun y hy => absurd (.inl hy) (hn y))
    (fun _ h => h.elim) fun y hy _ => .inl hy

omit fm in
theorem seg_of_eff {stk : Nat} {Fp Rq Wd : Word → Prop} {sp : Word} {tr : List Event} {n : Nat}
    (h : EffT stk Fp Rq Wd sp tr) (hr : (sp0 - sp).toNat + stk ≤ n) (hn : n < 2 ^ 32)
    (hF : ∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) : Seg sp0 n sp Rq tr Wd := by
  intro q hs hU hR; subst hs
  obtain ⟨g, s, u, w⟩ := h sp0 n q rfl hr hn hU hF hR
  exact ⟨g, s, u, w⟩

/-- **A block**: its loads, then its code by its decided effect. -/
theorem blk_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {b : Bk} {as : List (LowReg × Ld)} {o : Nat}
    (hty : (Op.blk b as : Op A Bk).ty cE bE G st = some s1) (hok : (Op.blk b as : Op A Bk).eok cE bE G st = true)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.blk b as : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    obtain ⟨r, hres, rfl⟩ := Option.map_eq_some_iff.mp hty
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨hl, -⟩, hwk⟩, hrk⟩, -⟩, -⟩ := hc
    simp only [Op.eok, Bool.and_eq_true] at hok
    obtain ⟨hk, hb⟩ := hok
    refine GP.cat (lds_gp fm hk hl _) (GP.cat ?_ hΨ)
    generalize regsOf st.Γ st.σ as = σ' at hres hb ⊢
    simp only [blkOk, Bool.and_eq_true, List.all_eq_true] at hb
    obtain ⟨⟨⟨⟨hσ, hrw⟩, hins⟩, houts⟩, hchk⟩ := hb
    have hH := holds_σv (c := c) (sp := G.fsp c) hσ
    obtain ⟨hsrc, hout, hwr, hwo, rds, hrd, hro⟩ := ioRes_parts hres
    have hreg : ∀ r, regIn (bE b).L r = true → (regState (c.base + BitVec.ofNat 32 (o + seqSize (ldsEmit as)))
        (bE b).L ((bE b).L.map (σv c (G.fsp c) σ'))).regs r = σv c (G.fsp c) σ' r := fun r h => rs_reg h
    refine bi_seg (blk_seg hchk _ (fun _ h => h) fun y hy hb => ?_) (fun y hy hb => ?_) fun y hy hb => ?_
    · obtain ⟨e, he, hy⟩ := inR_region hy
      obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp he
      simp only [rgnE, SExpr.denote, hreg _ (hrw rr hrr)] at hy
      have hkv : rr.len.kv = rr.len.val (σv c (G.fsp c) σ') := by
        have h := (List.mem_append.mp hrr).elim (hrk rr) (hwk rr)
        cases hq : rr.len with
        | k => rfl
        | r => rw [hq] at h; simp at h
      rw [hkv] at hy
      obtain ⟨q, hq, hy⟩ := rgnC_has hy
      rcases List.mem_append.mp hrr with h | h
      · exact rgns_above fm hH hrd hro ⟨q, List.mem_flatMap.mpr ⟨rr, h, hq⟩, hy⟩ hb
      · exact rgns_above fm hH hwr hwo ⟨q, List.mem_flatMap.mpr ⟨rr, h, hq⟩, hy⟩ hb
    · obtain ⟨e, he, hy⟩ := inR_region hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      have hi := hins x hx
      obtain ⟨sx, hs⟩ := (All2.ex (mapM_forall₂ hsrc)).1 x hx
      refine src_ext fm hH hs ?_ hb
      obtain ⟨r, off, i⟩ := x
      cases i with
      | raw l =>
        cases l with
        | k =>
          simp only [Bool.and_eq_true] at hi
          simp only [rgnE, SExpr.denote, hreg _ hi.1] at hy; exact hy
        | r => simp at hi
      | view k =>
        cases k with
        | ctx => simp at hi
        | rw => exact absurd hy (by simp [rgnE, Region, In.kd, Kd.sz])
        | _ => simp only [rgnE, SExpr.denote, hreg _ hi] at hy; exact hy
    · obtain ⟨pv, hpv, hy⟩ := hy
      rcases List.mem_append.mp hpv with hpv | hpv
      · obtain ⟨x, hx, hxp⟩ := (All2.ex (mapM_forall₂ hout)).2 pv hpv
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hxp
        have ho := houts x hx
        dsimp only at hy
        rw [← locOf_addr hH hl] at hy
        obtain ⟨r, off, k⟩ := x
        by_cases hin : inPlace (bE b).io.ins (r, off, k) = true
        · obtain ⟨k', hin', hle⟩ := inPlace_mem hin
          obtain ⟨sx, hs⟩ := (All2.ex (mapM_forall₂ hsrc)).1 _ hin'
          exact (src_ext fm hH hs (by simpa only [In.kd, Kd.ini_same hle] using hy) hb).elim .inl (.inr ∘ .inl)
        · refine .inr (.inr (inR_of_region (r := rgnE r off k.sz) (List.mem_filterMap.mpr ⟨(r, off, k), hx, by simp [hin]⟩) ?_))
          simp only [rgnE, SExpr.denote, hreg _ ho.1]
          rw [← kd_ini (c := c) (sp := G.fsp c) (by simpa using ho.2)]; exact hy
      · exact .inl ⟨pv, keep_sub _ hpv, hy⟩
  · simp at hty

theorem spill_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {r : LowReg} {o' o : Nat}
    (hty : (Op.spill r o' : Op A Bk).ty cE bE G st = some s1) (hok : (Op.spill r o' : Op A Bk).eok cE bE G st = true)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.spill r o' : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  simp only [Op.eok] at hok
  split at hty
  · split at hty
    · rename_i hs
      cases hty
      refine GP.cat (slot_gp fm (slot_le hs) hok _ (fun y hy => absurd hy inR_nil) fun p hp => ?_) hΨ
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr ⟨rfl, rfl, rfl⟩
      · exact .inl (keep_sub _ hp)
    · simp at hty
  · simp at hty

omit fm in
theorem drop_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {o' n' o : Nat} (hty : (Op.drop o' n' : Op A Bk).ty cE bE G st = some s1)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.drop o' n' : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty, Option.some.injEq] at hty; subst hty
  exact GP.pre (fun q hq => BI.sub keep_sub hq) hΨ

omit fm in
/-- An island: its `b` has no accesses. -/
theorem isl_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {pad : Bool} {n' o : Nat} (hty : (Op.isl pad n' : Op A Bk).ty cE bE G st = some s1)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.isl pad n' : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty, Option.some.injEq] at hty; subst hty
  exact GP.cat (quiet_gp rfl rfl rfl) hΨ

omit fm in
theorem keep_gp {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {T : A → Word → (Nat → Word) → List Event}
    {st s1 : St} {ls : List Loc} {o : Nat} (hty : (Op.keep ls : Op A Bk).ty cE bE G st = some s1)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.keep ls : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  obtain ⟨Γ', hΓ, rfl⟩ := Option.map_eq_some_iff.mp hty
  exact GP.pre (fun q hq => BI.sub (st := st) (st' := { st with Γ := Γ', σ := σsp, ρ := [] }) (keepΓ_sub hΓ) hq) hΨ

omit fm in
/-- The passes of a loop: the body from `I` to `K`, the decrement back to `I`, the exit test,
then the rest or the back branch. -/
theorem loopTr_gp {n : Nat} {I K J : Ef → Prop} {bt : TrP → TrP} {D : List Event} {bc bb : Event} {Ψk : TrP}
    (hb : ∀ Ψ, GP sp0 n K Ψ J → GP sp0 n I (bt Ψ) J) (hD : GP sp0 n K (Tr.is D) I)
    (hc : GP sp0 n I (Tr.is [bc]) I) (hbb : GP sp0 n I (Tr.is [bb]) I) (hk : GP sp0 n I Ψk J) :
    ∀ r, GP sp0 n I (loopTr bt D bc bb Ψk (r + 1)) J
  | 0 => hb _ (GP.cat hD (GP.cat hc (GP.cond (fun _ => hk) fun h => by simp at h)))
  | r + 1 => hb _ (GP.cat hD (GP.cat hc (GP.cond (fun h => by simp at h)
      fun _ => GP.cat hbb (loopTr_gp hb hD hc hbb hk r))))

section call
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
  {T : A → Word → (Nat → Word) → List Event}
  (hT : ∀ a base p, @CalleeS.Eff (cE a) p B BS _ base (T a base p))
  (hcode : ∀ y, Has [@codeR B BS _ c.base] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (G.fsp c) y ∧ X0 y)
include hT hcode

/-- **A call**: its loads, the `bl`, and the callee's trace from the callee's effect. -/
theorem call_gp {st s1 : St} {a : A} {as : List (LowReg × Ld)} {o : Nat}
    (hty : (Op.call a as : Op A Bk).ty cE bE G st = some s1) (hok : (Op.call a as : Op A Bk).eok cE bE G st = true)
    {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.call a as : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  split at hty
  · rename_i hc
    obtain ⟨r, hres, rfl⟩ := Option.map_eq_some_iff.mp hty
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hl, -⟩, hstk⟩ := hc
    simp only [Op.eok, Bool.and_eq_true] at hok
    obtain ⟨hk, hco⟩ := hok
    refine GP.cat (lds_gp fm hk hl _) (GP.cat (quiet_gp rfl rfl rfl) (GP.cat ?_ hΨ))
    generalize hσ' : regsOf st.Γ st.σ as = σ' at hres hco
    generalize hp : pubOf ((cE a).pubs.map (pubV c (G.fsp c) st.Γ σ')) = p
    simp only [callOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hco
    obtain ⟨⟨⟨⟨⟨hσ, h13⟩, hp13⟩, hrw⟩, hins⟩, houts⟩ := hco
    have hH := holds_σv (c := c) (sp := G.fsp c) hσ
    have hreg : ∀ r, PubW.r r ∈ (cE a).pubs → (cE a).reg p r = σv c (G.fsp c) σ' r := fun r h => by
      rw [← hp]; exact getD_idxOf _ _ h
    have hlen : ∀ l : ALen, lenPub (cE a).pubs l = true → l.val ((cE a).reg p) = l.val (σv c (G.fsp c) σ') := by
      intro l h; cases l with
      | k => rfl
      | r j => simp only [lenPub, decide_eq_true_eq] at h; simp [ALen.val, hreg j h]
    have hlen' : ∀ j, lenPub (cE a).pubs (.r j) = true → (cE a).reg p j = σv c (G.fsp c) σ' j :=
      fun j h => hreg j (by simpa [lenPub] using h)
    have hcnt : (cE a).cnt p = slen c (G.fsp c) (ctxIn (cE a) st.Γ σ') % 2 ^ 32 := by
      unfold CalleeS.cnt ctxIn
      by_cases h : PubW.n 0 ∈ (cE a).pubs
      · simp only [h, ↓reduceIte]; rw [← hp, pubOf, getD_idxOf _ _ h]; simp only [pubV]
        cases ctxAt st.Γ σ' 0 <;> simp [slen]
      · simp [h, slen]
    have e13 : (cE a).reg p 13 = G.fsp c := by rw [hreg 13 hp13]; simp [σv, h13, SV.val]
    obtain ⟨hsrc, hout, hwr, hwo, rds, hrd, hro⟩ := ioRes_parts hres
    have he := hT a c.base p
    unfold CalleeS.Eff at he; rw [e13] at he
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
      · obtain ⟨x, hx, hxp⟩ := (All2.ex (mapM_forall₂ hout)).2 pv hpv
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp hxp
        have ho := houts x hx
        refine .inr (.inr ⟨x, hx, ?_⟩)
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

omit hT in
/-- **A loader**: a code word and `add rd, pc` by the code bytes, or the glue's loads. -/
theorem ld_gp {st s1 : St} {r : LowReg} {l : Ld} {o : Nat}
    (hty : (Op.ld r l : Op A Bk).ty cE bE G st = some s1) (hok : (Op.ld r l : Op A Bk).eok cE bE G st = true)
    (hbok : (Op.ld r l : Op A Bk).bok cE bE G o = true) {Ψ : TrP} {J : Ef → Prop}
    (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.ld r l : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hty
  have hs : GP sp0 n (BI c G sp0 n X0 st) Ψ J := GP.pre (fun _ hq => ⟨hq.sp, hq.ab, hq.sv, hq.ex⟩) hΨ
  have hb : ∀ {is ini} (pc : Word), blkChk ini [] [frR G] is = true →
      (∀ y, InR (regState pc [13] [G.fsp c]) ini y → Ext c (G.fsp c) st.Γ y) →
      GP sp0 n (BI c G sp0 n X0 st) (Tr.is (blockTr is pc [13] [G.fsp c])) (BI c G sp0 n X0 st) := by
    intro is ini pc hk hI
    refine bi_seg (blk_seg hk _ (fun _ h => h) fun y hy _ => ?_) (fun y hy _ => .inl (hI y hy)) fun y hy _ => .inl hy
    obtain ⟨r, hr, hy⟩ := inR_region hy
    simp only [frR, List.mem_singleton] at hr; subst hr
    simp only [SExpr.denote, rs13] at hy
    exact fm.fr_above (o := 0) (m := G.top) (by omega) (by rw [BitVec.add_zero]; exact hy)
  cases l with
  | C i e imm =>
    simp only [Op.bok, Bool.and_eq_true] at hbok
    obtain ⟨⟨⟨hlit, -⟩, -⟩, -⟩ := hbok
    simp only [litOk, Bool.and_eq_true, decide_eq_true_eq] at hlit
    have hcd : ∀ y, Reads [⟨.read, c.base + BitVec.ofNat 32 (litOff o (BitVec.ofNat 8 imm)), 4⟩] y →
        Has [@codeR B BS _ c.base] y := by
      rintro y ⟨_, ha, -, k, hk, rfl⟩
      rw [List.mem_singleton] at ha; subst ha
      exact ⟨_, List.mem_singleton_self _, Rgn.of_region (lit_in hk hlit.1.1.2 CodeBytes.lt)⟩
    have hnw : ∀ y, ¬ Writes [⟨.read, c.base + BitVec.ofNat 32 (litOff o (BitVec.ofNat 8 imm)), 4⟩] y := by
      rintro y ⟨_, ha, hk, -⟩; rw [List.mem_singleton] at ha; subst ha; cases hk
    refine GP.cat (bi_seg (ev_seg (X := Has [@codeR B BS _ c.base])
      (by simp [spExact, Instr.dsts]; omega) rfl (fun y hy hb => (hcode y (hy.elim (hcd y) (absurd · (hnw y))) hb).1)
      fun y hy _ => hcd y hy) (fun y hy hb => .inr (hcode y hy hb).2) fun y hy _ => .inl hy)
      (GP.cat (hb _ hok fun y hy => absurd hy inR_nil) hs)
  | W o' e =>
    simp only [ldSv] at hv; split at hv
    · simp only [Ld.sv] at hv
      cases hp : pwAt st.Γ o' with
      | none => simp [hp] at hv
      | some w =>
        refine GP.cat (hb _ hok fun y hy => ?_) hs
        obtain ⟨r, hm, hy⟩ := inR_region hy
        simp only [ldsIni, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm; subst hm
        simp only [slotR, SExpr.denote, rs13] at hy
        exact ⟨_, pwAt_mem hp, hy⟩
    · simp at hv
  | _ => exact GP.cat (hb _ hok fun y hy => absurd hy (by simp [ldsIni]; exact inR_nil)) hs

omit hT hcode in
theorem pub_gp {st s1 : St} {g : List Instr} {o : Nat} (hty : (Op.pub g : Op A Bk).ty cE bE G st = some s1)
    (hok : (Op.pub g : Op A Bk).eok cE bE G st = true) {Ψ : TrP} {J : Ef → Prop}
    (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.pub g : Op A Bk).tr cE bE G T c o st Ψ) J := by
  simp only [Op.ty] at hty
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp hty
  exact GP.cat (pubBlk_gp fm hok _)
    (GP.pre (fun q hq => BI.sub (st := st) (st' := { st with σ := r.σ, ρ := [] }) (fun p hp => hp) hq) hΨ)

omit hT hcode in
theorem ldb_gp {st s1 : St} {rd rb ri : LowReg} {o : Nat} (hty : (Op.ldb rd rb ri : Op A Bk).ty cE bE G st = some s1)
    (hok : (Op.ldb rd rb ri : Op A Bk).eok cE bE G st = true) {Ψ : TrP} {J : Ef → Prop}
    (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) ((Op.ldb rd rb ri : Op A Bk).tr cE bE G T c o st Ψ) J := by
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
    simp only [Option.some.injEq] at hty
    obtain ⟨o', j, hb, hj, rfl⟩ : ∃ o' j, st.σ.lookup rb.toReg = some (.sp o') ∧
        st.σ.lookup ri.toReg = some (.k j) ∧ a = o' + j := by
      simp only [ldbOff] at hl
      split at hl
      · rename_i o' j h1 h2; simp only [Option.some.injEq] at hl; exact ⟨o', j, h1, h2, hl.symm⟩
      · simp at hl
    simp only [Op.eok] at hok
    have hrg : ∀ y, InR (regState (c.base + BitVec.ofNat 32 o) [rb.toReg, ri.toReg]
        ([rb.toReg, ri.toReg].map (σv c (G.fsp c) st.σ))) [ldbR rb ri] y →
        Region (G.fsp c + BitVec.ofNat 32 (o' + j)) 1 y := fun y hy => by
      obtain ⟨r, hr, hy⟩ := inR_region hy
      simp only [ldbR, List.mem_singleton] at hr; subst hr
      have e1 := rs_reg (pc := c.base + BitVec.ofNat 32 o) (f := σv c (G.fsp c) st.σ)
        (L := [rb.toReg, ri.toReg]) (r := rb.toReg) (by simp [regIn, ne15])
      have e2 := rs_reg (pc := c.base + BitVec.ofNat 32 o) (f := σv c (G.fsp c) st.σ)
        (L := [rb.toReg, ri.toReg]) (r := ri.toReg) (by simp [regIn, ne15])
      simp only [SExpr.denote, e1, e2, σv, hb, hj, SV.val] at hy
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at hy
    refine GP.cat (bi_seg (blk_seg hok _ (fun _ h => h) fun y hy _ => fm.fr_above ha (hrg y hy))
      (fun y hy _ => .inl ?_) fun y hy _ => .inl hy)
      (GP.pre (fun q hq => BI.sub (fun p hp => by rw [← hty] at hp; exact hp) hq) hΨ)
    obtain ⟨l0, n0, d, rfl, hm, hd, hn⟩ := findSlice_some hs
    have hy := hrg y hy
    rw [show G.fsp c + BitVec.ofNat 32 (o' + j) = (Loc.fr (o' + j)).addr c (G.fsp c) from rfl,
      Loc.diff_addr hd] at hy
    exact ext_mem hm (region_shift hy hn)
  · simp at hty

theorem op_good {st s1 : St} {x : Op A Bk} {o : Nat} (hty : x.ty cE bE G st = some s1)
    (hok : x.eok cE bE G st = true) (hbok : x.bok cE bE G o = true) {Ψ : TrP} {J : Ef → Prop} (hΨ : GP sp0 n (BI c G sp0 n X0 s1) Ψ J) :
    GP sp0 n (BI c G sp0 n X0 st) (x.tr cE bE G T c o st Ψ) J := by
  cases x with
  | call => exact call_gp fm hT hcode hty hok hΨ
  | blk => exact blk_gp fm hty hok hΨ
  | spill => exact spill_gp fm hty hok hΨ
  | drop => exact drop_gp hty hΨ
  | ld => exact ld_gp fm hcode hty hok hbok hΨ
  | pub => exact pub_gp fm hty hok hΨ
  | keep => exact keep_gp hty hΨ
  | ldb => exact ldb_gp fm hty hok hΨ
  | isl => exact isl_gp hty hΨ

/-- **A checked program's trace is `Good`** from the body's invariant at its static state, given
that the rest, or the exit the state names, is from the invariant at the state after it. -/
theorem prog_good : ∀ (P : Prog A Bk) (o : Nat) (st st' : St) (Ψ : TrP) (J : Ef → Prop) (Je : List Nat)
    (Ψs : List TrP), P.ty cE bE G st = some st' → st.ex = none → P.eok cE bE G st = true →
    P.bok cE bE G Je o = true → (st'.ex = none → GP sp0 n (BI c G sp0 n X0 st') Ψ J) →
    (∀ l, st'.ex = some l → GP sp0 n (BI c G sp0 n X0 st') (Ψs.getD l (Tr.is [])) J) →
    GP sp0 n (BI c G sp0 n X0 st) (Prog.tr cE bE G T c P o st Ψ Je Ψs) J
  | .nil, _, st, st', Ψ, J, _, _, h, hex, _, _, hΨ, _ => by cases h; exact hΨ hex
  | .op x k, o, st, st', Ψ, J, Je, Ψs, h, hex, he, hbk, hΨ, hx => by
    simp only [Prog.bok, Bool.and_eq_true] at hbk
    simp only [Prog.ty, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    simp only [Prog.eok, h1, Bool.and_eq_true] at he
    simp only [Prog.tr, h1, Option.getD_some]
    exact op_good fm hT hcode h1 he.1 hbk.1
      (prog_good k _ s1 st' Ψ J Je Ψs h2 (Op.ty_ex cE bE G h1 hex) he.2 hbk.2 hΨ hx)
  | .loop cnt n b k, o, st, st', Ψ, J, Je, Ψs, h, hex, he, hbk, hΨ, hx => by
    simp only [Prog.bok, Bool.and_eq_true, and_assoc] at hbk
    obtain ⟨-, -, hbb, -, -, -, -, hkb⟩ := hbk
    cases hb : b.ty cE bE G (loopSt st cnt) with
    | none => simp [Prog.ty, hb] at h
    | some sB =>
    simp only [Prog.ty, hb] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hs, hn0⟩, -⟩, hcw⟩, hsub⟩, -⟩, hxB⟩ := hc
      have hxB' : sB.ex = none := by simpa using hxB
      simp only [Prog.eok, Bool.and_eq_true] at he
      obtain ⟨⟨⟨hh, hd⟩, hbe⟩, hke⟩ := he
      have ho := slot_le hs
      simp only [Prog.tr]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      refine GP.cat (slot_gp fm (st' := loopSt st cnt) ho hh _ (fun y hy => absurd hy inR_nil)
        fun p hp => ?_) (loopTr_gp (fun Ψ hΨ => prog_good b _ _ sB Ψ J [] [] hb rfl hbe hbb (fun _ => hΨ)
          (fun l hl => by rw [hxB'] at hl; cases hl))
          (slot_gp fm ho hd _ (fun y hy => ⟨_, hcw, rfl, slot_reg hy⟩) fun p hp => ?_)
          (quiet_gp rfl rfl rfl) (quiet_gp rfl rfl rfl)
          (GP.pre (fun q hq => BI.sub (fun p hp => List.mem_cons_of_mem _ hp) hq)
            (prog_good k _ _ st' Ψ J Je Ψs h rfl hke hkb hΨ hx)) m)
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact .inr ⟨rfl, rfl, rfl⟩
        · exact .inl (keep_sub _ hp)
      · rcases List.mem_cons.mp (of_decide_eq_true (List.all_eq_true.mp hsub p hp)) with rfl | hp
        · exact .inr ⟨rfl, rfl, rfl⟩
        · exact .inl (keep_sub _ hp)
    · simp at h
  | .sel w i p₀ p₁ k, o, st, st', Ψ, J, Je, Ψs, h, hex, he, hbk, hΨ, hx => by
    simp only [Prog.bok, Bool.and_eq_true, and_assoc] at hbk
    obtain ⟨-, -, -, -, hb0, -, hb1, -, hkb⟩ := hbk
    cases hw : pwAt st.Γ w with
    | none => simp [Prog.ty, hw] at h
    | some v =>
    cases h0 : p₀.ty cE bE G (selSt st) with
    | none => simp [Prog.ty, hw, h0] at h
    | some s₀ =>
    cases h1 : p₁.ty cE bE G (selSt st) with
    | none => simp [Prog.ty, hw, h0, h1] at h
    | some s₁ =>
    simp only [Prog.ty, hw, h0, h1] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hsl, -⟩, hx0⟩, hx1⟩ := hc
      have hx0' : s₀.ex = none := by simpa using hx0
      have hx1' : s₁.ex = none := by simpa using hx1
      simp only [Prog.eok, h0, h1, Bool.and_eq_true] at he
      obtain ⟨⟨⟨hh, he0⟩, he1⟩, hke⟩ := he
      have hk := prog_good k _ (joinSt s₀ s₁) st' Ψ J Je Ψs h rfl hke hkb hΨ hx
      have hs : ∀ q, BI c G sp0 n X0 st q → BI c G sp0 n X0 (selSt st) q := fun q hq => BI.sub (st := st) (st' := selSt st) (fun p hp => hp) hq
      simp only [Prog.tr, h0, h1]
      refine GP.cat (slot_gp fm (st' := st) (slot_le hsl) hh _
        (fun y hy => ⟨_, pwAt_mem hw, rfl, slot_reg hy⟩) fun p hp => .inl hp)
        (GP.cat (quiet_gp rfl rfl rfl) (GP.cond (fun _ => GP.pre hs ?_) fun _ => GP.cat (quiet_gp rfl rfl rfl) (GP.pre hs ?_)))
      · exact prog_good p₀ _ _ s₀ _ J [] [] h0 rfl he0 hb0 (fun _ => GP.cat (quiet_gp rfl rfl rfl)
          (GP.pre (fun q hq => BI.sub (fun p hp => (List.mem_filter.mp hp).1) hq) hk))
          (fun l hl => by rw [hx0'] at hl; cases hl)
      · exact prog_good p₁ _ _ s₁ _ J [] [] h1 rfl he1 hb1 (fun _ => GP.cat (quiet_gp rfl rfl rfl)
          (GP.pre (fun q hq => BI.sub (fun p hp => of_decide_eq_true
            (List.mem_filter.mp (show p ∈ s₀.Γ.filter (· ∈ s₁.Γ) from hp)).2) hq) hk))
          (fun l hl => by rw [hx1'] at hl; cases hl)
    · simp at h
  | .xit gs s cc sh l k, o, st, st', Ψ, J, Je, Ψs, h, hex, he, hbk, hΨ, hx => by
    simp only [Prog.ty] at h
    cases hxs : xitSt G st gs s cc with
    | none => simp [hxs] at h
    | some p =>
    obtain ⟨st2, b⟩ := p
    rw [hxs] at h
    obtain ⟨r, hr, -, -, hs⟩ := xitSt_some G hxs
    have hex2 : st2.ex = none := by rw [xitSt_ex G hxs]; exact hex
    simp only [Prog.eok, hxs, Bool.and_eq_true] at he
    obtain ⟨⟨hpe, hse⟩, hke⟩ := he
    simp only [Prog.bok, Bool.and_eq_true] at hbk
    have hkb := hbk.2
    have hpt : (Op.pub gs : Op A Bk).ty cE bE G st = some { st with σ := r.σ, ρ := [] } := by
      simp [Op.ty, hr]
    have hpre : ∀ Ψ', GP sp0 n (BI c G sp0 n X0 st2) Ψ' J →
        GP sp0 n (BI c G sp0 n X0 st) (xitT cE bE G T c o st gs s Ψ') J := by
      intro Ψ' hΨ'
      cases s with
      | none =>
        simp only [xitPost] at hs; subst hs
        exact pub_gp (T := T) fm hpt hpe hΨ'
      | some p =>
        obtain ⟨q, o'⟩ := p
        simp only [xitPost] at hs
        simp only at hse
        exact pub_gp (T := T) fm hpt hpe (spill_gp (cE := cE) (bE := bE) (T := T) fm hs hse hΨ')
    simp only [Prog.tr, hxs, Option.map_some, Option.getD_some]
    refine hpre _ ?_
    have hX : GP sp0 n (BI c G sp0 n X0 st2) (Ψs.getD l (Tr.is [])) J → b = true →
        GP sp0 n (BI c G sp0 n X0 st2) (Ψs.getD l (Tr.is [])) J := fun h _ => h
    cases b with
    | true =>
      simp only [Option.some.injEq] at h; subst h
      have hl := GP.pre (fun q hq => BI.sub (st := st2) (st' := { st2 with ex := some l }) (fun p hp => hp) hq)
        (hx l rfl)
      cases sh <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true]
      · exact GP.cat (quiet_gp rfl rfl rfl) (GP.cond (fun h => by simp at h) fun _ =>
          GP.cat (quiet_gp rfl rfl rfl) hl)
      · exact GP.cat (quiet_gp rfl rfl rfl) (GP.cond (fun _ => hl) fun h => by simp at h)
    | false =>
      simp only at h hke
      have hk := prog_good k _ st2 st' Ψ J Je Ψs h hex2 hke hkb hΨ hx
      cases sh <;> simp only [↓reduceIte, Bool.false_eq_true, Bool.not_false]
      · exact GP.cat (quiet_gp rfl rfl rfl) (GP.cond (fun _ => hk) fun h => by simp at h)
      · exact GP.cat (quiet_gp rfl rfl rfl) (GP.cond (fun h => by simp at h) fun _ => hk)
  | .hd b h k, o, st, st', Ψ, J, Je, Ψs, hty, hex, he, hbk, hΨ, hx => by
    simp only [Prog.ty] at hty
    cases hb : b.ty cE bE G st with
    | none => simp [hb] at hty
    | some s =>
    rw [hb] at hty
    simp only [Prog.eok, hb, Bool.and_eq_true] at he
    obtain ⟨hbe, he2⟩ := he
    simp only [Prog.bok, Bool.and_eq_true] at hbk
    obtain ⟨⟨⟨hbb, -⟩, hhb⟩, hkb⟩ := hbk
    simp only [Prog.tr, hb]
    refine prog_good b _ st s _ J _ _ hb hex hbe hbb (fun hn => ?_) (fun l hl => ?_)
    · simp only [hn] at hty he2
      have hk := prog_good k _ s st' Ψ J Je Ψs hty hn he2 hkb hΨ hx
      cases hnl : h.isNil <;> simp only [hnl, ↓reduceIte, Bool.false_eq_true] at hk ⊢
      · exact GP.cat (quiet_gp rfl rfl rfl) hk
      · exact hk
    · cases l with
      | succ j =>
        simp only [hl, Option.some.injEq] at hty; subst hty
        simp only [List.getD_cons_succ]
        exact GP.pre (fun q hq => BI.sub (st := s) (st' := { s with ex := some j }) (fun p hp => hp) hq) (hx j rfl)
      | zero =>
        simp only [hl] at hty he2
        cases hh : h.ty cE bE G { s with ex := none } with
        | none => simp [hh] at hty
        | some s' =>
        rw [hh] at hty
        simp only [hh, Bool.and_eq_true] at he2
        obtain ⟨hhe, hke⟩ := he2
        simp only [List.getD_cons_zero]
        refine GP.pre (fun q hq => BI.sub (st := s) (st' := { s with ex := none }) (fun p hp => hp) hq)
          (prog_good h _ _ s' _ J Je Ψs hh rfl hhe hhb (fun hn => ?_) (fun l' hl' => ?_))
        · simp only [hn, ↓reduceIte] at hty hke
          exact prog_good k _ s' st' Ψ J Je Ψs hty hn hke hkb hΨ hx
        · simp only [hl', reduceCtorEq, ↓reduceIte, Option.some.injEq] at hty; subst hty
          exact hx l' hl'
  | .wh m b k, o, st, st', Ψ, J, Je, Ψs, hty, hex, he, hbk, hΨ, hx => by
    simp only [Prog.bok, Bool.and_eq_true] at hbk
    obtain ⟨⟨hbb, -⟩, hkb⟩ := hbk
    simp only [Prog.ty] at hty
    simp only [Prog.eok] at he
    simp only [Prog.tr]
    induction m generalizing st with
    | zero => simp [whTy] at hty
    | succ m ih =>
      simp only [whTy] at hty
      simp only [whOk, Bool.and_eq_true] at he
      obtain ⟨hbe, he2⟩ := he
      cases hb : b.ty cE bE G st with
      | none => simp [hb] at hty
      | some s =>
      rw [hb] at hty he2
      simp only [whTr, hb]
      refine prog_good b _ st s _ J _ _ hb hex hbe hbb (fun hn => ?_) (fun l hl => ?_)
      · simp only [hn] at hty he2
        exact GP.cat (quiet_gp rfl rfl rfl) (ih s hty hn he2)
      · cases l with
        | succ j =>
          simp only [hl, Option.some.injEq] at hty; subst hty
          simp only [List.getD_cons_succ]
          exact GP.pre (fun q hq => BI.sub (st := s) (st' := { s with ex := some j }) (fun p hp => hp) hq) (hx j rfl)
        | zero =>
          simp only [hl] at hty he2
          simp only [List.getD_cons_zero]
          exact GP.pre (fun q hq => BI.sub (st := s) (st' := { s with ex := none }) (fun p hp => hp) hq)
            (prog_good k _ _ st' Ψ J Je Ψs hty rfl he2 hkb hΨ hx)

end call

end cons

end M0Crypto.Release.Ed25519CallProg
