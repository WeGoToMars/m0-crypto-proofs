import M0Crypto.Release.Ed25519CallProgSem

set_option linter.unusedSimpArgs false

/-!
# Call programs: decided geometry

A region of a call or a block is symbolic (`SR`): a location and a length, from the interface's
register-relative regions (`SRgn`) and the symbolic values of the registers. Every geometric
side condition is a Boolean check on symbolic regions (`SR.ok`, `SR.apart`), proved sound once
here against the dynamic facts of a run (`GeoOk`): the frame lies in the caller's window, an
external buffer lies apart from it, each region of a buffer inside the buffer.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Frame (Disj)

/-! ## Static -/

/-- A symbolic region: a location and a length. -/
structure SR where
  loc : Loc
  len : XLen
  deriving DecidableEq, Repr

def SV.loc : SV → Option Loc
  | .sp o => some (.fr o)
  | .ext i e => some (.ex i e)
  | _ => none

def Loc.add : Loc → Nat → Loc
  | .fr o, d => .fr (o + d)
  | .ex i e, d => .ex i (e + d)
  | .rg r, _ => .rg r

def SV.len : SV → Option XLen
  | .prm i => some (.p i)
  | .k n => if n < 2 ^ 32 then some (.k n) else none
  | _ => none

def ALen.res (σ : List (Reg × SV)) : ALen → Option XLen
  | .k n => some (.k n)
  | .r j => (σ.lookup j).bind SV.len

/-- The location of register `r` plus `off`. -/
def locOf (σ : List (Reg × SV)) (r : Reg) (off : Nat) : Option Loc :=
  ((σ.lookup r).bind SV.loc).map (·.add off)

def SRgn.res (σ : List (Reg × SV)) (r : SRgn) : Option SR :=
  match locOf σ r.r r.off, r.len.res σ with
  | some l, some n => some ⟨l, n⟩
  | _, _ => none

/-- A view as a region. -/
def Kd.sr (l : Loc) (k : Kd) : SR := ⟨l, .k k.sz⟩

/-- The region lies in the frame below `top`, or inside its external buffer. -/
def SR.ok (G : Geo) : SR → Bool
  | ⟨.fr o, .k n⟩ => decide (o + n ≤ G.top)
  | ⟨.fr _, .p _⟩ => false
  | ⟨.rg _, _⟩ => false
  | ⟨.ex i e, l⟩ => match G.xs[i]?, l with
    | some x, .k n => match x.len with
      | .k L => decide (e + n ≤ L)
      | .p _ => n == 0
    | some x, .p j => e == 0 && x.len == .p j
    | none, _ => false

/-- The region is empty. -/
def SR.empty : SR → Bool
  | ⟨_, .k 0⟩ => true
  | _ => false

def far (o n p m : Nat) : Bool := decide (o + n ≤ p) || decide (p + m ≤ o)

/-- Two regions lie apart: one is empty, frame regions apart, a frame region and a buffer region,
or two regions of one buffer apart. -/
def SR.apart (a b : SR) : Bool :=
  a.empty || b.empty || match a, b with
  | ⟨.fr o, .k n⟩, ⟨.fr p, .k m⟩ => far o n p m
  | ⟨.fr _, _⟩, ⟨.ex _ _, _⟩ => true
  | ⟨.ex _ _, _⟩, ⟨.fr _, _⟩ => true
  | ⟨.ex i e, .k n⟩, ⟨.ex j f, .k m⟩ => i == j && far e n f m
  | _, _ => false

/-- The region of a buffer, if it is one, writable (`w`) or readable. -/
def SR.acc (G : Geo) (w : Bool) : SR → Bool
  | ⟨.fr _, _⟩ => true
  | ⟨.rg _, _⟩ => false
  | ⟨.ex i _, _⟩ => match G.xs[i]? with
    | some x => if w then x.w else x.r
    | none => false

/-- `a` lies in a code buffer and `b` in a writable region, so apart (`GeoOk.cdW`). -/
def SR.cdSep (G : Geo) (a b : SR) : Bool :=
  match a.loc with
  | .ex i _ => (G.cd.lookup i).isSome && b.acc G true
  | _ => false

/-! ## Dynamic -/

def XLen.v (c : Ctx) : XLen → Nat
  | .k n => n
  | .p i => (c.prm i).toNat

/-- The frame's `sp`: `top` bytes below `sp0`. -/
def Geo.fsp (G : Geo) (c : Ctx) : Word := c.sp0 - BitVec.ofNat 32 G.top

/-- The caller's window, `N` bytes below `sp0`. -/
def Geo.win (G : Geo) (c : Ctx) : Rgn := ⟨c.sp0 - BitVec.ofNat 32 G.N, G.N⟩

/-- The regions of a symbolic region: none when it is empty. -/
def SR.rgns (G : Geo) (c : Ctx) (r : SR) : List Rgn :=
  if r.len.v c = 0 then [] else [⟨r.loc.addr c (G.fsp c), r.len.v c⟩]

/-- A buffer as regions. -/
def XInfo.rgns (c : Ctx) (i : Nat) (x : XInfo) : List Rgn :=
  if x.len.v c = 0 then [] else [⟨c.ptr i, x.len.v c⟩]

/-- What a buffer satisfies: apart from the window, inside the caller's footprints as it may be
written or read, and aligned. -/
structure XOk (c : Ctx) (G : Geo) (Wc Rc : List Rgn) (i : Nat) (x : XInfo) : Prop where
  sep : x.len.v c = 0 ∨ Disj (c.ptr i) (x.len.v c) (c.sp0 - BitVec.ofNat 32 G.N) G.N
  w : x.w = true → Sub (x.rgns c i) Wc
  r : x.r = true → Sub (x.rgns c i) Rc
  al : x.al4 = true → (c.ptr i).toNat % 4 = 0

/-- **The dynamic facts of a run's geometry.** -/
structure GeoOk (c : Ctx) (G : Geo) (Wc Rc : List Rgn) : Prop where
  sp4 : c.sp0.toNat % 4 = 0
  room : G.N ≤ c.sp0.toNat
  top : G.top ≤ G.N
  top4 : G.top % 4 = 0
  wW : Sub [G.win c] Wc
  wR : Sub [G.win c] Rc
  xs : ∀ i x, G.xs[i]? = some x → XOk c G Wc Rc i x
  pm : ∀ i x, G.pm[i]? = some x → (c.prm i).toNat ≤ x
  cd : ∀ i s, G.cd.lookup i = some s → c.ptr i = c.base + BitVec.ofNat 32 s
  /-- A code buffer lies apart from the caller's writable memory. -/
  cdW : ∀ i s, G.cd.lookup i = some s → ∀ x, G.xs[i]? = some x → Sep (x.rgns c i) Wc

/-- An upper bound of a public length: a constant, or a parameter with a bound. -/
def SV.max (G : Geo) : SV → Option Nat
  | .k n => some n
  | .prm i => G.pm[i]?
  | _ => none

/-- An upper bound of a sum of public lengths. -/
def smax (G : Geo) (n : List SV) : Option Nat := (n.mapM (SV.max G)).map List.sum

theorem GeoOk.slen_le {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (g : GeoOk c G Wc Rc) (sp : Word) :
    ∀ {n : List SV} {x : Nat}, smax G n = some x → slen c sp n ≤ x
  | [], x, h => by simp [smax] at h; simp [slen, ← h]
  | v :: n, x, h => by
    simp only [smax, List.mapM_cons, Option.map_eq_some_iff, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, ⟨a, ha, l, hl, rfl⟩, rfl⟩ := h
    have ih := g.slen_le sp (n := n) (x := l.sum) (by simp [smax, hl])
    simp only [slen, List.map_cons, List.sum_cons] at ih ⊢
    have : (v.val c sp).toNat ≤ a := by
      cases v <;> simp only [SV.max, Option.some.injEq, reduceCtorEq] at ha
      · exact g.pm _ _ ha
      · subst ha; simp only [SV.val, BitVec.toNat_ofNat]; exact Nat.mod_le _ _
    omega

/-! ## Soundness -/

section
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn} (g : GeoOk c G Wc Rc)
include g

theorem GeoOk.fsp_toNat : (G.fsp c).toNat = c.sp0.toNat - G.top := by
  have := g.room; have := g.top; have := c.sp0.isLt
  simp only [Geo.fsp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem GeoOk.fr_toNat {o : Nat} (h : o ≤ G.top) :
    (G.fsp c + BitVec.ofNat 32 o).toNat = c.sp0.toNat - G.top + o := by
  have := g.room; have := g.top; have := c.sp0.isLt; have := g.fsp_toNat
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem GeoOk.win_toNat : (G.win c).a.toNat = c.sp0.toNat - G.N := by
  have := g.room; have := c.sp0.isLt
  simp only [Geo.win, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- The buffer facts of an `ok` buffer region: the buffer is nonempty and apart from the window,
and the region's address is `ptr + e` without wrapping. -/
theorem GeoOk.ex_facts {i e : Nat} {l : XLen} (ho : SR.ok G ⟨.ex i e, l⟩ = true) (hn : l.v c ≠ 0) :
    ∃ x, G.xs[i]? = some x ∧ XOk c G Wc Rc i x ∧ x.len.v c ≠ 0 ∧
      Disj (c.ptr i) (x.len.v c) (c.sp0 - BitVec.ofNat 32 G.N) G.N ∧ e + l.v c ≤ x.len.v c := by
  cases hx : G.xs[i]? with
  | none => simp [SR.ok, hx] at ho
  | some x =>
    have xo := g.xs i x hx
    have key : x.len.v c ≠ 0 ∧ e + l.v c ≤ x.len.v c := by
      cases l with
      | k n =>
        cases hL : x.len with
        | k L => simp only [SR.ok, hx, hL, decide_eq_true_eq] at ho; simp only [XLen.v] at hn ⊢; omega
        | p j => simp only [SR.ok, hx, hL, beq_iff_eq] at ho; simp only [XLen.v] at hn; omega
      | p j =>
        simp only [SR.ok, hx, Bool.and_eq_true, beq_iff_eq] at ho
        obtain ⟨rfl, hl⟩ := ho
        rw [hl]; exact ⟨hn, by omega⟩
    rcases xo.sep with h | h
    · exact absurd h key.1
    · exact ⟨x, rfl, xo, key.1, h, key.2⟩

omit g in
theorem ex_toNat {i e n L : Nat} (hd : Disj (c.ptr i) L (c.sp0 - BitVec.ofNat 32 G.N) G.N)
    (h : e + n ≤ L) (hn : 0 < n) : (c.ptr i + BitVec.ofNat 32 e).toNat = (c.ptr i).toNat + e := by
  obtain ⟨h1, -, -⟩ := hd
  have he : e < 2 ^ 32 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he]
  exact Nat.mod_eq_of_lt (by omega)

/-- **A region inside the window or its buffer**: an `ok` region lies in `Wc` and `Rc` as its
location permits. -/
theorem GeoOk.sub {r : SR} (ho : r.ok G = true) (w : Bool) (ha : r.acc G w = true) :
    Sub (r.rgns G c) (if w then Wc else Rc) := by
  unfold SR.rgns
  split
  · intro _ h; exact absurd h List.not_mem_nil
  rename_i hn
  obtain ⟨l, n⟩ := r
  cases l with
  | rg => simp [SR.ok] at ho
  | fr o =>
    cases n with
    | p _ => simp [SR.ok] at ho
    | k n =>
      simp only [SR.ok, decide_eq_true_eq] at ho
      simp only [XLen.v] at hn
      have hw : Sub [⟨Loc.addr c (G.fsp c) (.fr o), n⟩] [G.win c] := by
        have := g.fr_toNat (o := o) (by omega); have := g.win_toNat; have := g.room; have := g.top
        have := c.sp0.isLt
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩ <;> simp only [Loc.addr, Geo.win] at * <;> omega
      cases w
      · exact sub_trans hw g.wR
      · exact sub_trans hw g.wW
  | ex i e =>
    obtain ⟨x, hx, xo, hxn, hd, hle⟩ := g.ex_facts ho hn
    simp only [SR.acc, hx] at ha
    have hs : Sub [⟨Loc.addr c (G.fsp c) (.ex i e), n.v c⟩] (x.rgns c i) := by
      have := ex_toNat hd hle (Nat.pos_of_ne_zero hn)
      simp only [XInfo.rgns, hxn, ↓reduceIte]
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨h1, -, -⟩ := hd
      exact ⟨_, List.mem_singleton_self _, by simp only [Loc.addr]; omega,
        by simp only [Loc.addr]; omega, h1⟩
    cases w
    · exact sub_trans hs (xo.r ha)
    · exact sub_trans hs (xo.w ha)

/-- An `ok` region of buffer `i` lies in the buffer. -/
theorem GeoOk.sub_buf {i e : Nat} {n : XLen} (ho : SR.ok G ⟨.ex i e, n⟩ = true) {x : XInfo}
    (hx : G.xs[i]? = some x) : Sub (SR.rgns G c ⟨.ex i e, n⟩) (x.rgns c i) := by
  unfold SR.rgns
  split
  · intro _ h; exact absurd h List.not_mem_nil
  rename_i hn
  obtain ⟨x', hx', -, hxn, hd, hle⟩ := g.ex_facts ho hn
  rw [hx] at hx'; cases hx'
  have := ex_toNat hd hle (Nat.pos_of_ne_zero hn)
  simp only [XInfo.rgns, hxn, ↓reduceIte]
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  obtain ⟨h1, -, -⟩ := hd
  exact ⟨_, List.mem_singleton_self _, by simp only [Loc.addr]; omega, by simp only [Loc.addr]; omega, h1⟩

/-- **A code buffer's bytes are apart from every writable region**: an `ok` region of a code
buffer has no byte in an `ok` writable region. -/
theorem GeoOk.code_apart {i e s : Nat} {n : XLen} (ho : SR.ok G ⟨.ex i e, n⟩ = true)
    (hcd : G.cd.lookup i = some s) {r : SR} (hr : r.ok G = true) (ha : r.acc G true = true) {y : Word}
    (hy : Has (SR.rgns G c ⟨.ex i e, n⟩) y) : ¬ Has (r.rgns G c) y := by
  cases hx : G.xs[i]? with
  | none => simp [SR.ok, hx] at ho
  | some x =>
    intro hw
    have h1 := Sub.has (g.sub_buf ho hx) hy
    have h2 := Sub.has (g.sub hr true ha) hw
    exact Sep.not_has (g.cdW i s hcd x hx) h1 (by simpa using h2)

/-- **Two regions apart**: `ok` regions that `SR.apart` accepts are separated. -/
theorem GeoOk.sep {a b : SR} (ha : a.ok G = true) (hb : b.ok G = true) (h : a.apart b = true) :
    Sep (a.rgns G c) (b.rgns G c) := by
  intro r hr q hq
  unfold SR.rgns at hr hq
  split at hr
  · exact absurd hr List.not_mem_nil
  split at hq
  · exact absurd hq List.not_mem_nil
  rename_i hna hnb
  simp only [List.mem_singleton] at hr hq; subst hr hq
  obtain ⟨la, na⟩ := a; obtain ⟨lb, nb⟩ := b
  have he : ∀ {l : Loc} {n : XLen}, n.v c ≠ 0 → SR.empty ⟨l, n⟩ = false := by
    intro l n hn; cases n with
    | k n => cases n with
      | zero => simp [XLen.v] at hn
      | succ => rfl
    | p => rfl
  simp only [SR.apart, he hna, he hnb, Bool.false_or] at h
  have := c.sp0.isLt; have := g.room; have := g.top
  cases la with
  | rg => simp [SR.ok] at ha
  | fr o =>
    cases na with
    | p => simp [SR.ok] at ha
    | k n =>
      simp only [SR.ok, decide_eq_true_eq] at ha
      simp only [XLen.v] at hna
      have ho := g.fr_toNat (o := o) (by omega)
      cases lb with
      | rg => simp [SR.ok] at hb
      | fr p =>
        cases nb with
        | p => simp [SR.ok] at hb
        | k m =>
          simp only [SR.ok, decide_eq_true_eq] at hb
          simp only [XLen.v] at hnb ⊢
          have hp := g.fr_toNat (o := p) (by omega)
          simp only [far, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [Loc.addr, Disj]; omega
      | ex j f =>
        obtain ⟨x, -, -, -, hd, hle⟩ := g.ex_facts hb hnb
        have := ex_toNat hd hle (Nat.pos_of_ne_zero hnb); have := g.win_toNat
        obtain ⟨h1, -, h3⟩ := hd
        simp only [Loc.addr, Disj, Geo.win, XLen.v] at *; omega
  | ex i e =>
    obtain ⟨x, -, -, -, hd, hle⟩ := g.ex_facts ha hna
    have hi := ex_toNat hd hle (Nat.pos_of_ne_zero hna)
    cases lb with
    | rg => simp [SR.ok] at hb
    | fr p =>
      cases nb with
      | p => simp [SR.ok] at hb
      | k m =>
        simp only [SR.ok, decide_eq_true_eq] at hb
        simp only [XLen.v] at hnb
        have hp := g.fr_toNat (o := p) (by omega)
        have := g.win_toNat
        obtain ⟨h1, -, h3⟩ := hd
        simp only [Loc.addr, Disj, Geo.win, XLen.v] at *; omega
    | ex j f =>
      cases na with
      | p => simp at h
      | k n =>
        cases nb with
        | p => simp at h
        | k m =>
          simp only [Bool.and_eq_true, beq_iff_eq, far, Bool.or_eq_true, decide_eq_true_eq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨y, -, -, -, hd', hle'⟩ := g.ex_facts hb hnb
          have hj := ex_toNat hd' hle' (Nat.pos_of_ne_zero hnb)
          obtain ⟨h1, -, -⟩ := hd
          simp only [Loc.addr, Disj, XLen.v] at *; omega

/-- **The callee's window** of `st` bytes below the frame lies in the caller's window, apart from
every `ok` region. -/
theorem GeoOk.cwin {st : Nat} (hst : G.top + st ≤ G.N) :
    Sub [⟨G.fsp c - BitVec.ofNat 32 st, st⟩] [G.win c] ∧
    ∀ {r : SR}, r.ok G = true → Sep (r.rgns G c) [⟨G.fsp c - BitVec.ofNat 32 st, st⟩] := by
  have := g.fsp_toNat; have := g.win_toNat; have := g.room; have := g.top; have := c.sp0.isLt
  have hs : (G.fsp c - BitVec.ofNat 32 st).toNat = c.sp0.toNat - G.top - st := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ⟨fun r hr => ?_, fun {r} ho => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_, ?_, ?_⟩ <;> (try dsimp only) <;> simp only [Geo.win] at * <;> omega
  · intro q hq w hw
    simp only [List.mem_singleton] at hw; subst hw
    unfold SR.rgns at hq
    split at hq
    · exact absurd hq List.not_mem_nil
    rename_i hn
    simp only [List.mem_singleton] at hq; subst hq
    obtain ⟨l, n⟩ := r
    cases l with
    | rg => simp [SR.ok] at ho
    | fr o =>
      cases n with
      | p => simp [SR.ok] at ho
      | k n =>
        simp only [SR.ok, decide_eq_true_eq] at ho
        have := g.fr_toNat (o := o) (by omega)
        simp only [Loc.addr, Disj, XLen.v] at *; omega
    | ex i e =>
      obtain ⟨x, -, -, -, hd, hle⟩ := g.ex_facts ho hn
      have := ex_toNat hd hle (Nat.pos_of_ne_zero hn)
      obtain ⟨h1, -, h3⟩ := hd
      simp only [Loc.addr, Disj, Geo.win, XLen.v] at *; omega

/-- **A code buffer's region and a writable one are separated.** -/
theorem GeoOk.cd_sep {a b : SR} (ha : a.ok G = true) (hb : b.ok G = true) (h : a.cdSep G b = true) :
    Sep (a.rgns G c) (b.rgns G c) := by
  obtain ⟨l, n⟩ := a
  cases l with
  | ex i e =>
    simp only [SR.cdSep, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨s, hs⟩, hw⟩ := h
    cases hx : G.xs[i]? with
    | none => simp [SR.ok, hx] at ha
    | some x =>
      exact Sub.sep (g.sub_buf ha hx) (Sep.symm (Sub.sep (by simpa using g.sub hb true hw)
        (Sep.symm (g.cdW i s hs x hx))))
  | _ => simp [SR.cdSep] at h

/-- **Two regions apart**, by `SR.apart` or as a code buffer's region and a writable one. -/
theorem GeoOk.sepE {a b : SR} (ha : a.ok G = true) (hb : b.ok G = true)
    (h : (a.apart b || a.cdSep G b || b.cdSep G a) = true) : Sep (a.rgns G c) (b.rgns G c) := by
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact g.sep ha hb h
  · exact g.cd_sep ha hb h
  · exact Sep.symm (g.cd_sep hb ha h)

end

end M0Crypto.Release.Ed25519CallProg
