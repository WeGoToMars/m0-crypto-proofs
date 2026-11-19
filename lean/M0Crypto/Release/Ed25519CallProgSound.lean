import M0Crypto.Release.Ed25519CallProgCheck

set_option linter.unusedSimpArgs false

/-!
# Call programs: soundness of the static checks

`Inv` is what a run carries between constructs: each live view is `ok` and holds, and memory
outside the window and the buffer regions written so far holds its entry bytes `m0`. The lemmas
here turn the decided checks into the facts the construct rules need: the registers after a
call's loads (`lds_holds`), the inputs of an interface (`ioRes_ins`), its entry conditions
(`ioRes_pre`), its footprints (`ioRes_wr`) and the invariant after it (`inv_after`).
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Ed25519Routines (EqOrDisj)

variable (Rs : Rels)

/-- **The invariant of a run**: every live view is `ok` and holds; outside the window and the
buffer regions written so far, memory holds its entry bytes. -/
def Inv (c : Ctx) (G : Geo) (m0 : Mem) (st : St) (E : Loc → V) (m : Mem) : Prop :=
  (∀ p ∈ st.Γ, (Kd.sr p.1 p.2).ok G = true ∧ Rel Rs c (G.fsp c) p.2 m (p.1.addr c (G.fsp c)) (E p.1)) ∧
  (∀ y, ¬ (G.win c).Has y → (∀ r ∈ st.X, ¬ Has (r.rgns G c) y) → m y = m0 y) ∧
  ∀ p ∈ G.xv, p.2.Bnd (bytesAt m0 (c.ptr p.1) 32)

/-- `Inv` depends on the views and the written regions of the static state. -/
theorem Inv.st {c : Ctx} {G : Geo} {m0 : Mem} {st st' : St} {E : Loc → V} {m : Mem} (hΓ : st'.Γ = st.Γ)
    (hX : st'.X = st.X) (h : Inv Rs c G m0 st E m) : Inv Rs c G m0 st' E m := by
  unfold Inv at *; rw [hΓ, hX]; exact h

/-! ## Concrete interface regions -/

def ALen.val (regs : Reg → Word) : ALen → Nat
  | .k n => n
  | .r j => (regs j).toNat

/-- An interface region at registers `regs`; none when empty. -/
def SRgn.rgnC (regs : Reg → Word) (r : SRgn) : List Rgn :=
  if r.len.val regs = 0 then [] else [⟨regs r.r + BitVec.ofNat 32 r.off, r.len.val regs⟩]

def rgnsC (regs : Reg → Word) (l : List SRgn) : List Rgn := l.flatMap (SRgn.rgnC regs)

def In.kd (regs : Reg → Word) : In → Kd
  | .view k => k
  | .raw l => .bytes (l.val regs)

/-- `R` holds of the lists pairwise, and they have one length. -/
def All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: l' => R a b ∧ All2 R l l'
  | _, _ => False

/-- The inputs `vs` hold at `s`. -/
def InsRel (c : Ctx) (sp : Word) (io : Iface) (s : State) (vs : List V) : Prop :=
  All2 (fun (x : Reg × Nat × In) v =>
    Rel Rs c sp (x.2.2.kd s.regs) s.mem (s.regs x.1 + BitVec.ofNat 32 x.2.1) v) io.ins vs

/-- The outputs `vs` hold in `m`, at the registers of `s`. -/
def OutsRel (c : Ctx) (sp : Word) (io : Iface) (s : State) (m : Mem) (vs : List V) : Prop :=
  All2 (fun (x : Reg × Nat × Kd) v =>
    Rel Rs c sp x.2.2 m (s.regs x.1 + BitVec.ofNat 32 x.2.1) v) io.outs vs

/-- The register conditions of an interface: alignment, equal-or-apart pairs, constants. -/
def PreG (io : Iface) (regs : Reg → Word) : Prop :=
  (∀ r ∈ io.al, (regs r).toNat % 4 = 0) ∧
  (∀ p ∈ io.eqd, EqOrDisj (regs p.1) (regs p.2.1) p.2.2) ∧
  (∀ p ∈ io.kreq, regs p.1 = BitVec.ofNat 32 p.2)

/-- The value conditions of an interface: registers holding symbolic values, bounded public
lengths, regions apart. -/
def PreV (io : Iface) (c : Ctx) (sp : Word) (regs : Reg → Word) : Prop :=
  (∀ p ∈ io.kreqv, regs p.1 = p.2.val c sp) ∧ (∀ p ∈ io.lim, slen c sp p.1 < p.2) ∧
  (∀ p ∈ io.apt, Sep (rgnsC regs [p.1]) (rgnsC regs [p.2]))

/-- The no-wrap registers of an interface: `n` bytes from each stay below `2 ^ 32`. -/
def NoWrap (io : Iface) (regs : Reg → Word) : Prop := ∀ p ∈ io.nw, (regs p.1).toNat + p.2 ≤ 2 ^ 32

/-! ## List helpers -/

theorem lookup_mem {σ : List (Reg × SV)} {r : Reg} {v : SV} (h : σ.lookup r = some v) :
    (r, v) ∈ σ := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → All2 (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; trivial
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp only [ha, hl, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at h
        subst h; exact ⟨ha, mapM_forall₂ hl⟩

theorem keepΓ_sub {Γ Γ' : List (Loc × Kd)} {ls : List Loc} (h : keepΓ Γ ls = some Γ') : ∀ p ∈ Γ', p ∈ Γ := by
  have h2 := mapM_forall₂ h
  clear h
  induction ls generalizing Γ' with
  | nil => cases Γ' with
    | nil => simp
    | cons _ _ => simp [All2] at h2
  | cons l ls ih =>
    cases Γ' with
    | nil => simp [All2] at h2
    | cons q Γ' =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_of_find?_eq_some h2.1
      · exact ih h2.2 p hp

theorem pwAt_mem {Γ : List (Loc × Kd)} {o : Nat} {v : SV} (h : pwAt Γ o = some v) :
    (Loc.fr o, Kd.pw v) ∈ Γ := by
  obtain ⟨⟨l, k⟩, hm, hf⟩ := List.exists_of_findSome?_eq_some h
  cases l <;> cases k <;> simp at hf
  obtain ⟨rfl, rfl⟩ := hf; exact hm

/-! ## Registers -/

variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn}

theorem Holds.get {sp : Word} {σ : List (Reg × SV)} {regs : Reg → Word} (h : Holds c sp σ regs)
    {r : Reg} {v : SV} (hl : σ.lookup r = some v) : regs r = v.val c sp ∧ r.val < 14 := by
  have := h _ (lookup_mem hl); exact ⟨this.2, this.1⟩

theorem locOf_addr {sp : Word} {σ : List (Reg × SV)} {regs : Reg → Word} (h : Holds c sp σ regs)
    {r : Reg} {off : Nat} {l : Loc} (hl : locOf σ r off = some l) :
    regs r + BitVec.ofNat 32 off = l.addr c sp := by
  simp only [locOf, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hl
  obtain ⟨l0, ⟨v, hv, h0⟩, rfl⟩ := hl
  rw [(h.get hv).1]
  cases v <;> simp [SV.loc] at h0 <;> subst h0 <;>
    simp [SV.val, Loc.addr, Loc.add, BitVec.add_assoc, BitVec.ofNat_add]

theorem ALen.res_val {sp : Word} {σ : List (Reg × SV)} {regs : Reg → Word} (h : Holds c sp σ regs)
    {len : ALen} {xl : XLen} (hl : len.res σ = some xl) : len.val regs = xl.v c := by
  cases len with
  | k n => simp [ALen.res] at hl; subst hl; rfl
  | r j =>
    simp only [ALen.res, Option.bind_eq_some_iff] at hl
    obtain ⟨v, hv, h0⟩ := hl
    rw [ALen.val, (h.get hv).1]
    cases v with
    | prm i => simp [SV.len] at h0; subst h0; rfl
    | k n =>
      simp only [SV.len] at h0
      split at h0
      · simp at h0; subst h0; simp [SV.val, XLen.v]; omega
      · simp at h0
    | _ => simp [SV.len] at h0

theorem SRgn.res_rgns {σ : List (Reg × SV)} {regs : Reg → Word} (h : Holds c (G.fsp c) σ regs)
    {r : SRgn} {sr : SR} (hr : r.res σ = some sr) : r.rgnC regs = sr.rgns G c := by
  unfold SRgn.res at hr
  split at hr
  · rename_i l n hl hn
    simp at hr; subst hr
    simp only [SRgn.rgnC, SR.rgns, ALen.res_val h hn, locOf_addr h hl]
  · simp at hr

theorem rgnsC_eq {σ : List (Reg × SV)} {regs : Reg → Word} (h : Holds c (G.fsp c) σ regs) :
    ∀ {l : List SRgn} {ws : List SR}, All2 (fun a b => a.res σ = some b) l ws →
      rgnsC regs l = ws.flatMap (SR.rgns G c)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h1, h2⟩ => by
    have e := rgnsC_eq h h2
    simp only [rgnsC, List.flatMap_cons] at *
    rw [SRgn.res_rgns h h1, e]

/-- The value a loader leaves is the value of its symbolic value. -/
theorem Ld.sv_mval {m0 : Mem} {st : St} {E : Loc → V} {m : Mem} (hi : Inv Rs c G m0 st E m)
    {l : Ld} {v : SV} (h : l.sv st.Γ = some v) : l.mval m (G.fsp c) = v.val c (G.fsp c) := by
  cases l with
  | S off => simp [Ld.sv] at h; subst h; rfl
  | K n => simp [Ld.sv] at h; subst h; rfl
  | A _ => simp [Ld.sv] at h
  | C _ _ _ => simp [Ld.sv] at h
  | W off e =>
    simp only [Ld.sv] at h
    cases hp : pwAt st.Γ off with
    | none => simp [hp] at h
    | some v0 =>
      have := (hi.1 _ (pwAt_mem hp)).2
      simp only [Rel, Loc.addr] at this
      cases v0 with
      | ext i e0 =>
        simp [hp] at h; subst h
        simp [Ld.mval, this, SV.val, BitVec.add_assoc, BitVec.ofNat_add]
      | sp o =>
        simp [hp] at h; subst h
        simp [Ld.mval, this, SV.val, BitVec.add_assoc, BitVec.ofNat_add]
      | _ =>
        simp only [hp] at h
        split at h
        · rename_i he; subst he; simp at h; subst h; simp [Ld.mval, this]
        · simp at h

/-- **The registers after a call's loads.** -/
theorem lds_holds {m0 : Mem} {st : St} {E : Loc → V} {t : State} {as : List (LowReg × Ld)}
    (hi : Inv Rs c G m0 st E t.mem) (hσ : Holds c (G.fsp c) st.σ t.regs)
    (h13 : t.regs 13 = G.fsp c) (hok : ldsRes st.Γ as = true) :
    Holds c (G.fsp c) (regsOf st.Γ st.σ as) (execAll (ldsEmit as) t).regs := by
  simp only [ldsRes, Bool.and_eq_true, List.all_eq_true, Option.isSome_iff_exists] at hok
  obtain ⟨hl, hsv⟩ := hok
  obtain ⟨-, b2, b3, -⟩ := lds_run as t hl
  intro p hp
  simp only [regsOf, List.mem_append, List.mem_filterMap, List.mem_filter, Option.map_eq_some_iff,
    Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hp
  rcases hp with ⟨a, ha, v, hv, rfl⟩ | ⟨hp, hn⟩
  · refine ⟨by have := a.1.isLt; simp [LowReg.toReg]; omega, ?_⟩
    rw [b3 a ha, h13]; exact Ld.sv_mval Rs hi hv
  · obtain ⟨h14, hv⟩ := hσ p hp
    refine ⟨h14, ?_⟩
    rw [b2 p.1 (fun h => absurd (h ▸ h14) (by decide)) (fun a ha he => hn a ha he.symm), hv]

/-! ## Geometry of resolved regions -/

theorem GeoOk.ex_win (g : GeoOk c G Wc Rc) {r : SR} (ho : r.ok G = true) (hx : r.loc.isEx = true) :
    Sep (r.rgns G c) [G.win c] := by
  intro q hq w hw
  simp only [List.mem_singleton] at hw; subst hw
  unfold SR.rgns at hq
  split at hq
  · exact absurd hq List.not_mem_nil
  rename_i hn
  simp only [List.mem_singleton] at hq; subst hq
  obtain ⟨l, n⟩ := r
  cases l with
  | fr => simp [Loc.isEx] at hx
  | rg => simp [Loc.isEx] at hx
  | ex i e =>
    obtain ⟨x, -, -, -, hd, hle⟩ := g.ex_facts ho hn
    have := ex_toNat hd hle (Nat.pos_of_ne_zero hn)
    obtain ⟨h1, h2, h3⟩ := hd
    simp only [Loc.addr, Disj, Geo.win] at *; omega

theorem SV.al_sound (g : GeoOk c G Wc Rc) {v : SV} (h : v.al G = true) :
    (v.val c (G.fsp c)).toNat % 4 = 0 := by
  have := g.fsp_toNat; have := g.sp4; have := g.top4; have := g.room; have := g.top
  cases v with
  | sp o =>
    simp only [SV.al, beq_iff_eq] at h
    simp only [SV.val, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  | ext i e =>
    simp only [SV.al, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨he, hx⟩ := h
    cases hxi : G.xs[i]? with
    | none => simp [hxi] at hx
    | some x =>
      simp only [hxi] at hx
      have := (g.xs i x hxi).al hx
      simp only [SV.val, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  | k n => simp only [SV.al, beq_iff_eq] at h; simp only [SV.val, BitVec.toNat_ofNat]; omega
  | prm => simp [SV.al] at h

/-- An `ok` frame region lies in the window. -/
theorem GeoOk.fr_win (g : GeoOk c G Wc Rc) {r : SR} (ho : r.ok G = true) (hx : r.loc.isEx = false) :
    ∀ y, Has (r.rgns G c) y → (G.win c).Has y := by
  intro y hy
  obtain ⟨q, hq, hy⟩ := hy
  unfold SR.rgns at hq
  split at hq
  · exact absurd hq List.not_mem_nil
  simp only [List.mem_singleton] at hq; subst hq
  obtain ⟨l, n⟩ := r
  cases l with
  | ex => simp [Loc.isEx] at hx
  | rg => simp [SR.ok] at ho
  | fr o =>
    cases n with
    | p => simp [SR.ok] at ho
    | k n =>
      simp only [SR.ok, decide_eq_true_eq] at ho
      have e1 := g.fr_toNat (o := o) (by omega); have e2 := g.win_toNat; have := g.room; have := g.top
      have := c.sp0.isLt
      refine Rgn.has_sub ?_ ?_ ?_ hy <;> simp only [Loc.addr, XLen.v, Geo.win] at e1 e2 ⊢ <;> omega

/-- A view's region: the bytes the view relation reads. -/
theorem Rel.memEq' {k : Kd} {l : Loc} {W : List Rgn} {m m' : Mem} {v : V}
    (h : MemEq W m m') (hs : Sep ((Kd.sr l k).rgns G c) W)
    (hr : Rel Rs c (G.fsp c) k m (l.addr c (G.fsp c)) v) : Rel Rs c (G.fsp c) k m' (l.addr c (G.fsp c)) v := by
  by_cases h0 : k.sz = 0
  · cases k <;> simp [Kd.sz, ctxSize] at h0
    · subst h0; cases v <;> simp only [Rel] at hr ⊢
      simpa [bytesAt] using hr
    · cases v <;> simp only [Rel] at hr ⊢ <;> exact hr
  · have : (Kd.sr l k).rgns G c = [⟨l.addr c (G.fsp c), k.sz⟩] := by
      simp [SR.rgns, Kd.sr, XLen.v, h0]
    rw [this] at hs
    exact Rel.memEq Rs h hs hr

/-! ## Inputs -/

theorem bytesAt_slice (m : Mem) (a : Word) {d n n0 : Nat} (h : d + n ≤ n0) :
    bytesAt m (a + BitVec.ofNat 32 d) n = ((bytesAt m a n0).drop d).take n := by
  apply List.ext_getElem
  · simp [bytesAt_length]; omega
  · intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem Loc.diff_addr {sp : Word} {l l0 : Loc} {d : Nat} (h : l.diff l0 = some d) :
    l.addr c sp = l0.addr c sp + BitVec.ofNat 32 d := by
  cases l <;> cases l0 <;> simp only [Loc.diff, reduceCtorEq] at h
  · rename_i o p
    split at h
    · simp at h; subst h; simp only [Loc.addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · simp at h
  · rename_i i e j f
    split at h
    · rename_i hc; obtain ⟨rfl, hf⟩ := hc
      simp at h; subst h; simp only [Loc.addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · simp at h

theorem findSlice_some {Γ : List (Loc × Kd)} {l : Loc} {n : Nat} {s : Src}
    (h : findSlice Γ l n = some s) : ∃ l0 n0 d, s = .slice l0 d n ∧ (l0, Kd.bytes n0) ∈ Γ ∧
      l.diff l0 = some d ∧ d + n ≤ n0 := by
  obtain ⟨⟨l0, k⟩, hm, hf⟩ := List.exists_of_findSome?_eq_some h
  cases k <;> simp only at hf
  · rename_i n0
    cases hd : l.diff l0 with
    | none => simp [hd] at hf
    | some d =>
      simp only [hd] at hf
      split at hf
      · simp at hf; exact ⟨l0, n0, d, hf.symm, hm, hd, by omega⟩
      · simp at hf
  all_goals simp at hf

variable {m0 : Mem} {st : St} {E : Loc → V}

theorem slice_rel {m : Mem} (hi : Inv Rs c G m0 st E m) {l l0 : Loc} {n0 d n : Nat}
    (hm : (l0, Kd.bytes n0) ∈ st.Γ) (hd : l.diff l0 = some d) (hn : d + n ≤ n0) :
    Rel Rs c (G.fsp c) (.bytes n) m (l.addr c (G.fsp c)) ((Src.slice l0 d n).val G c m0 E) := by
  have := (hi.1 _ hm).2
  simp only [Src.val]
  generalize E l0 = v at this
  cases v <;> simp only [Rel] at this ⊢
  rw [Loc.diff_addr hd, bytesAt_slice m _ hn, this]

theorem ext_rel (g : GeoOk c G Wc Rc) {m : Mem} (hi : Inv Rs c G m0 st E m) {r : SR}
    (hX : st.X = [] ∨ codeRd G st r.loc = true) (ho : r.ok G = true) (hx : r.loc.isEx = true) :
    Rel Rs c (G.fsp c) (.bytes (r.len.v c)) m (r.loc.addr c (G.fsp c)) ((Src.ext r).val G c m0 E) := by
  simp only [Src.val, Rel]
  apply bytesAt_congr
  intro i hi'
  apply hi.2.1
  · intro hw
    have hm : (⟨r.loc.addr c (G.fsp c), r.len.v c⟩ : Rgn) ∈ r.rgns G c := by
      simp [SR.rgns, show r.len.v c ≠ 0 by omega]
    exact Sep.not_has (g.ex_win ho hx) ⟨_, hm, i, hi', rfl⟩ ⟨G.win c, List.mem_singleton_self _, hw⟩
  · rcases hX with hX | hX
    · simp [hX]
    · intro w hw hh
      obtain ⟨l, n⟩ := r
      cases l with
      | fr => simp [codeRd] at hX
      | rg => simp [codeRd] at hX
      | ex j e =>
        simp only [codeRd, Bool.and_eq_true, List.all_eq_true] at hX
        obtain ⟨hs, hall⟩ := hX
        obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hs
        have hwa := hall w hw
        have hm : (⟨Loc.addr c (G.fsp c) (.ex j e), n.v c⟩ : Rgn) ∈ SR.rgns G c ⟨.ex j e, n⟩ := by
          have hi2 : i < n.v c := hi'
          simp [SR.rgns, show n.v c ≠ 0 by omega]
        exact g.code_apart ho hs hwa.1 hwa.2 ⟨_, hm, i, hi', rfl⟩ hh

theorem feVal_bytes {m m' : Mem} {a : Word} (hb : bytesAt m' a 32 = bytesAt m a 32) :
    Field25519Routines.feVal m' a = Field25519Routines.feVal m a := by
  unfold Field25519Routines.feVal; congr 1; apply List.map_congr_left; intro i hi
  have hi8 : i < 8 := List.mem_range.mp hi
  rw [Frame.read32_congr fun k hk => ?_]
  have e := congrArg (·[4 * i + k]?) hb
  simp only [bytesAt, List.getElem?_map, List.getElem?_range, show 4 * i + k < 32 by omega,
    ↓reduceIte, Option.map_some, Option.some.injEq] at e
  rw [ofNat_add_assoc]; exact e

theorem extF_rel (g : GeoOk c G Wc Rc) {m : Mem} (hi : Inv Rs c G m0 st E m) {l : Loc}
    (hX : st.X = [] ∨ codeRd G st l = true)
    (ho : SR.ok G ⟨l, .k 32⟩ = true) (hx : l.isEx = true) :
    Rel Rs c (G.fsp c) .fe m (l.addr c (G.fsp c)) ((Src.extF ⟨l, .k 32⟩).val G c m0 E) := by
  have hb := ext_rel Rs g hi hX ho hx
  simp only [Src.val, Rel, XLen.v] at hb ⊢
  rw [feVal_bytes hb]; exact Field25519Congr.ModP.refl _

/-- **An input's value holds** at its register and offset. -/
theorem inSrc_rel (g : GeoOk c G Wc Rc) {m : Mem} (hi : Inv Rs c G m0 st E m) {σ : List (Reg × SV)}
    {regs : Reg → Word} (hσ : Holds c (G.fsp c) σ regs) {x : Reg × Nat × In} {s : Src}
    (hρ : ∀ r ∈ st.ρ, σ.all (·.1 != r) = true → E (.rg r) = .w (regs r)) (hs : inSrc G st σ x = some s) :
    Rel Rs c (G.fsp c) (x.2.2.kd regs) m (regs x.1 + BitVec.ofNat 32 x.2.1) (s.val G c m0 E) := by
  by_cases hw : x.2.2 = .view .rw
  · obtain ⟨r, off, i⟩ := x
    simp only at hw; subst hw
    simp only [inSrc, ↓reduceIte] at hs
    split at hs
    · rename_i hc
      obtain ⟨hr, rfl, hn⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      simp [In.kd, Src.val, Rel, hρ r hr hn]
    · split at hs
      · rename_i ho; subst ho
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hs
        simp [In.kd, Src.val, Rel, (hσ.get hv).1]
      · simp at hs
  simp only [inSrc, hw, ↓reduceIte] at hs
  obtain ⟨r, off, i⟩ := x
  cases hl : locOf σ r off with
  | none => cases i <;> simp [inSrc, hl] at hs
  | some l =>
    simp only [locOf_addr hσ hl]
    cases i with
    | view k =>
      simp only [In.kd]
      simp only [inSrc, hl] at hs
      by_cases hm : viewOf st.Γ l k = true
      · simp only [hm, ↓reduceIte, Option.some.injEq] at hs; subst hs
        obtain ⟨k', hk', hle⟩ := viewOf_mem hm
        exact Kd.le_rel Rs hle (hi.1 _ hk').2
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hs
        cases k <;> try simp only [reduceCtorEq] at hs
        case bytes =>
          obtain ⟨l0, n0, d, rfl, hm, hd, hn⟩ := findSlice_some hs
          exact slice_rel Rs hi hm hd hn
        case fe =>
          split at hs
          · rename_i hc; simp only [Option.some.injEq] at hs; subst hs
            exact extF_rel Rs g hi hc.1 hc.2.2.1 hc.2.1
          · simp at hs
        case sc | cl =>
          obtain ⟨i, k', rfl, rfl, hX, hx, hle, hok, hacc⟩ := refSrc_some hs
          have hb := ext_rel Rs g hi (.inl hX) hok rfl (E := E)
          have hv := Kd.bnd_le hle (hi.2.2 _ hx)
          simp only [Src.val, Rel, XLen.v] at hb ⊢
          exact ⟨hb, by simpa [Loc.addr, Kd.Bnd] using hv⟩
    | raw len =>
      simp only [inSrc, hl] at hs
      cases hr : len.res σ with
      | none => simp [hr] at hs
      | some xl =>
        simp only [hr] at hs
        simp only [In.kd, ALen.res_val hσ hr]
        have hex : (if (st.X = [] ∨ codeRd G st l = true) ∧ l.isEx = true ∧ SR.ok G ⟨l, xl⟩ = true ∧
            SR.acc G false ⟨l, xl⟩ = true then some (Src.ext ⟨l, xl⟩) else none) = some s →
            Rel Rs c (G.fsp c) (.bytes (xl.v c)) m (l.addr c (G.fsp c)) (s.val G c m0 E) := by
          intro h
          split at h
          · rename_i hc; simp only [Option.some.injEq] at h; subst h
            exact ext_rel Rs g hi hc.1 hc.2.2.1 hc.2.1
          · simp at h
        cases xl with
        | k n =>
          simp only at hs
          cases hf : findSlice st.Γ l n with
          | some s' =>
            simp only [hf] at hs
            have hs : some s' = some s := hs
            simp only [Option.some.injEq] at hs; subst hs
            obtain ⟨l0, n0, d, rfl, hm, hd, hn⟩ := findSlice_some hf
            exact slice_rel Rs hi hm hd hn
          | none => simp only [hf, Option.none_or] at hs; exact hex hs
        | p j => exact hex hs

/-! ## Interfaces -/

theorem all2_map {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {l : List α} {l' : List β}, All2 (fun a b => R a (f b)) l l' → All2 R l (l'.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1, all2_map h2⟩

theorem all2_mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, All2 R l l' → All2 S l l'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, all2_mono h h2⟩

/-- **The facts of a resolved interface**: inputs hold, the register conditions hold, outputs
are at their locations, the footprints are the resolved regions, `ok` and accessible. -/
theorem ioRes_sound (g : GeoOk c G Wc Rc) {m : Mem} (hi : Inv Rs c G m0 st E m)
    {σ : List (Reg × SV)} {regs : Reg → Word} (hσ : Holds c (G.fsp c) σ regs)
    (hρ : ∀ r ∈ st.ρ, σ.all (·.1 != r) = true → E (.rg r) = .w (regs r)) {io : Iface} {r : IoR}
    (h : ioRes G st σ io = some r) :
    All2 (fun (x : Reg × Nat × In) v =>
      Rel Rs c (G.fsp c) (x.2.2.kd regs) m (regs x.1 + BitVec.ofNat 32 x.2.1) v) io.ins
      (r.srcs.map (Src.val G c m0 E)) ∧
    PreG io regs ∧ PreV io c (G.fsp c) regs ∧
    All2 (fun (x : Reg × Nat × Kd) p => regs x.1 + BitVec.ofNat 32 x.2.1 = p.1.addr c (G.fsp c) ∧
      p.2 = x.2.2) io.outs r.outs ∧
    (∀ p ∈ r.outs, (Kd.sr p.1 p.2).ok G = true ∧ p.2 ≠ .cw) ∧ (r.outs.map (·.1)).Nodup ∧
    rgnsC regs io.wr = r.wrs.flatMap (SR.rgns G c) ∧ (∀ w ∈ r.wrs, w.ok G = true ∧ w.acc G true = true) ∧
    ∃ rds : List SR, rgnsC regs io.rd = rds.flatMap (SR.rgns G c) ∧
      ∀ w ∈ rds, w.ok G = true ∧ w.acc G false = true := by
  simp only [ioRes, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨srcs, hsrc, outs, hout, wrs, hwr, rds, hrd, h⟩ := h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hrdo⟩, ho⟩, hnd⟩, hal⟩, heq⟩, hk⟩, hkv⟩, hlim⟩, hapt⟩ := hc
    refine ⟨all2_map (all2_mono (fun x s hs => inSrc_rel Rs g hi hσ hρ hs) (mapM_forall₂ hsrc)),
      ⟨fun r hr => ?_, fun p hp => ?_, fun p hp => ?_⟩, ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩,
      all2_mono (fun x p hp => ?_) (mapM_forall₂ hout), fun p hp => ⟨(ho p hp).1, (ho p hp).2⟩, hnd,
      rgnsC_eq hσ (mapM_forall₂ hwr), fun w hw' => by simpa using hw w hw',
      rds, rgnsC_eq hσ (mapM_forall₂ hrd), fun w hw' => by simpa using hrdo w hw'⟩
    · have := hal r hr
      cases hl : σ.lookup r with
      | none => simp [hl] at this
      | some v =>
        simp only [hl, Option.map_some, Option.getD_some] at this
        rw [(hσ.get hl).1]; exact SV.al_sound g this
    · have := heq p hp
      simp only [eqdOk] at this
      cases ha : locOf σ p.1 0 with
      | none => simp [ha] at this
      | some a =>
        cases hb : locOf σ p.2.1 0 with
        | none => simp [ha, hb] at this
        | some b =>
          simp only [ha, hb, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
          have ea := locOf_addr hσ ha; have eb := locOf_addr hσ hb
          simp only [BitVec.add_zero] at ea eb
          rcases this with rfl | ⟨⟨⟨⟨h0, hoa⟩, hob⟩, hab⟩⟩
          · exact Or.inl (ea.trans eb.symm)
          · refine Or.inr ?_
            have := g.sepE hoa hob (by simpa only [Bool.or_eq_true] using hab)
            have hne : (XLen.k p.2.2).v c ≠ 0 := by simp [XLen.v]; omega
            simp only [SR.rgns, hne, ↓reduceIte] at this
            have := this _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
            simpa [ea, eb, XLen.v] using this
    · have := hk p hp
      simp only [beq_iff_eq] at this
      rw [(hσ.get this).1]; rfl
    · have := hkv p hp
      simp only [beq_iff_eq] at this
      exact (hσ.get this).1
    · have := hlim p hp
      simp only [limOk] at this
      split at this
      · exact Nat.lt_of_le_of_lt (g.slen_le _ ‹_›) (of_decide_eq_true this)
      · simp at this
    · have := hapt p hp
      simp only [aptOk] at this
      split at this
      · rename_i a b ha hb
        simp only [Bool.and_eq_true] at this
        rw [rgnsC_eq hσ (l := [p.1]) (ws := [a]) ⟨ha, trivial⟩,
          rgnsC_eq hσ (l := [p.2]) (ws := [b]) ⟨hb, trivial⟩]
        simpa using g.sep this.1.1 this.1.2 this.2
      · simp at this
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨l, hl, rfl⟩ := hp
      exact ⟨locOf_addr hσ hl, rfl⟩
  · simp at h

/-! ## The invariant after a construct -/

theorem updOuts_out {outs : List (Loc × Kd)} {vs : List V} {P : Loc × Kd → V → Prop}
    (h : All2 P outs vs) (hnd : (outs.map (·.1)).Nodup) :
    ∀ p ∈ outs, P p (updOuts E outs vs p.1) := by
  induction outs generalizing vs with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons q outs ih =>
    cases vs with
    | nil => exact h.elim
    | cons v vs =>
      obtain ⟨h1, h2⟩ := h
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      intro p hp
      simp only [updOuts]
      rcases List.mem_cons.mp hp with rfl | hp
      · simpa using h1
      · have : p.1 ≠ q.1 := fun he => hnd.1 ⟨p, hp, he⟩
        simp only [this, ↓reduceIte]; exact ih h2 hnd.2 p hp

theorem updOuts_other {outs : List (Loc × Kd)} {vs : List V} {l : Loc}
    (h : ∀ p ∈ outs, p.1 ≠ l) : updOuts E outs vs l = E l := by
  induction outs generalizing vs with
  | nil => cases vs <;> rfl
  | cons q outs ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [updOuts]
      rw [ite_eq_right_iff.mpr (fun he => absurd he.symm (h q List.mem_cons_self))]
      exact ih fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- **The invariant after a construct** that writes `ws` and a callee window of `sw` bytes below
the frame, with outputs `outs` holding `vs` in the new memory. -/
theorem inv_after (g : GeoOk c G Wc Rc) {m m' : Mem} (hi : Inv Rs c G m0 st E m)
    {ws : List SR} {sw : Nat} (hsw : G.top + sw ≤ G.N) (hws : ∀ w ∈ ws, w.ok G = true)
    (hm : MemEq (⟨G.fsp c - BitVec.ofNat 32 sw, sw⟩ :: ws.flatMap (SR.rgns G c)) m m')
    {outs : List (Loc × Kd)} {vs : List V} (σ' : List (Reg × SV)) (ρ' : List Reg)
    (ho : ∀ p ∈ outs, (Kd.sr p.1 p.2).ok G = true) (hnd : (outs.map (·.1)).Nodup)
    (hv : All2 (fun p v => Rel Rs c (G.fsp c) p.2 m' (p.1.addr c (G.fsp c)) v) outs vs) :
    Inv Rs c G m0 { Γ := outs ++ keepViews st.Γ ws outs, σ := σ', X := st.X ++ ws.filter (·.loc.isEx), ρ := ρ' }
      (updOuts E outs vs) m' := by
  have cw := g.cwin hsw
  refine ⟨fun p hp => ?_, fun y hy hx => ?_, hi.2.2⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact ⟨ho p hp, updOuts_out hv hnd p hp⟩
    · simp only [keepViews, List.mem_filter, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
        List.any_eq_false, beq_iff_eq] at hp
      obtain ⟨hp, hap, hno⟩ := hp
      obtain ⟨hok, hr⟩ := hi.1 p hp
      refine ⟨hok, ?_⟩
      rw [updOuts_other fun q hq he => hno q hq he]
      refine Rel.memEq' Rs hm ?_ hr
      intro a ha q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact cw.2 hok a ha _ (List.mem_singleton_self _)
      · obtain ⟨w, hw, hq⟩ := List.mem_flatMap.mp hq
        exact g.sep hok (hws w hw) (hap w hw) a ha q hq
  · rw [hm y fun hh => ?_]
    · exact hi.2.1 y hy fun r hr => hx r (List.mem_append_left _ hr)
    · obtain ⟨q, hq, hyq⟩ := hh
      rcases List.mem_cons.mp hq with rfl | hq
      · obtain ⟨q', hq', h1, h2, h3⟩ := cw.1 _ (List.mem_singleton_self _)
        simp only [List.mem_singleton] at hq'; subst hq'; exact hy (Rgn.has_sub h1 h2 h3 hyq)
      · obtain ⟨w, hw, hq⟩ := List.mem_flatMap.mp hq
        cases hxw : w.loc.isEx
        · exact hy (g.fr_win (hws w hw) hxw y ⟨q, hq, hyq⟩)
        · exact hx w (List.mem_append_right _ (List.mem_filter.mpr ⟨hw, hxw⟩)) ⟨q, hq, hyq⟩

end M0Crypto.Release.Ed25519CallProg
