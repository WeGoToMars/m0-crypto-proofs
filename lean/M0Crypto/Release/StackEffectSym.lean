import M0Crypto.Release.StackEffect
import M0Crypto.Release.RoutineBlock

/-!
# Byte effects of a straight-line block, decided

`effChk ini is` decides, on the symbolic trace of the block `is`, that it keeps SP and that every
read lies in one of the regions `ini` (expressions of the entry state) or in an earlier write of
the block. `covChk wo is` decides that every byte of the regions `wo` is written. Then the
block's trace is `Good` from any effect state at the block's SP whose `U` holds the window bytes
of `ini`, and it adds the window bytes of `wo` to `U` (`block_good`), given that the block's
window accesses lie at or above SP.
-/

namespace M0Crypto.Release.StackEffect

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release.TraceSpec
open M0Crypto.Release.Routine (keepsSp addrE baseE blockTrE)

def wrsOf (acc : List SAccess) : List (SExpr × Nat) :=
  (acc.filter (·.kind == .write)).map fun a => (a.addr, a.width)

/-- Every read lies in `ini` or in an earlier write `w`. -/
def effGo (ini : List (SExpr × Nat)) : List (SExpr × Nat) → List (SExpr × Instr × List SAccess) → Bool
  | _, [] => true
  | w, (_, _, acc) :: es =>
    acc.all (fun a => a.kind == .write || (ini ++ w).any (inRgn a.addr a.width)) &&
      effGo ini (w ++ wrsOf acc) es

def effChk (ini : List (SExpr × Nat)) (is : List Instr) : Bool :=
  is.all Instr.falls && keepsSp is && effGo ini [] (symTrace is SState.init)

/-- `r` is covered by `x` at byte `k`: same base, and byte `k` of `r` lies in `x`. -/
def inRgnOff (r : SExpr) (k : Nat) (x : SExpr × Nat) : Bool :=
  (split (norm r)).1 == (split (norm x.1)).1 &&
    decide (((split (norm r)).2 + BitVec.ofNat 32 k - (split (norm x.1)).2).toNat + 1 ≤ x.2)

/-- Every byte of each region of `wo` lies in a write of the block. -/
def covChk (wo : List (SExpr × Nat)) (is : List Instr) : Bool :=
  wo.all fun r => (List.range r.2).all fun k =>
    ((symTrace is SState.init).flatMap fun e => wrsOf e.2.2).any
      (inRgnOff r.1 k)

/-- The bytes of the regions `rs` at the entry state `t`. -/
def InR (t : State) (rs : List (SExpr × Nat)) (y : Word) : Prop :=
  ∃ r ∈ rs, ∃ o < r.2, y = r.1.denote t + BitVec.ofNat 32 o

/-! A block's addresses may be valued by any `den` that is a function of an expression's base
plus its offset (`Spl`): the entry state's `denote`, or a block's atoms (`addrE`). -/

/-- The bytes of the regions `rs` under the valuation `den`. -/
def InRD (den : SExpr → Word) (rs : List (SExpr × Nat)) (y : Word) : Prop :=
  ∃ r ∈ rs, ∃ o < r.2, y = den r.1 + BitVec.ofNat 32 o

/-- `den` is a function of the base of an expression plus its offset. -/
def Spl (den : SExpr → Word) : Prop := ∃ B : SExpr → Word, ∀ e, den e = B (split (norm e)).1 + (split (norm e)).2

theorem spl_denote (t : State) : Spl (·.denote t) := ⟨(·.denote t), fun e => (base_split t e).symm⟩

theorem inRgn_den {den : SExpr → Word} (hd : Spl den) {a : SExpr} {w : Nat} {r : SExpr × Nat}
    (h : inRgn a w r = true) {k : Nat} (hk : k < w) :
    ∃ o < r.2, den a + BitVec.ofNat 32 k = den r.1 + BitVec.ofNat 32 o := by
  simp only [inRgn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨B, hB⟩ := hd
  refine ⟨((split (norm a)).2 - (split (norm r.1)).2).toNat + k, by omega, ?_⟩
  rw [hB a, hB r.1, h.1, BitVec.ofNat_add, BitVec.ofNat_toNat]
  exact add_sub_rearr _ _ _ _

/-- A symbolic event under the valuations `dpc` (its pc) and `den` (its addresses). -/
def evD (dpc den : SExpr → Word) (e : SExpr × Instr × List SAccess) : Event :=
  ⟨dpc e.1, e.2.1, e.2.2.map fun a => ⟨a.kind, den a.addr, a.width⟩⟩

theorem inR_append {den : SExpr → Word} {a b : List (SExpr × Nat)} {y : Word} :
    InRD den (a ++ b) y ↔ InRD den a y ∨ InRD den b y := by
  simp only [InRD, List.mem_append]
  exact ⟨fun ⟨r, hr, h⟩ => hr.imp (fun h' => ⟨r, h', h⟩) (fun h' => ⟨r, h', h⟩),
    fun h => h.elim (fun ⟨r, hr, h⟩ => ⟨r, .inl hr, h⟩) (fun ⟨r, hr, h⟩ => ⟨r, .inr hr, h⟩)⟩

theorem inR_wrs {den : SExpr → Word} {acc : List SAccess} {y : Word} :
    InRD den (wrsOf acc) y ↔ Writes (acc.map fun a => ⟨a.kind, den a.addr, a.width⟩) y := by
  simp only [InRD, wrsOf, List.mem_map, List.mem_filter, beq_iff_eq, Writes]
  constructor
  · rintro ⟨_, ⟨a, ⟨ha, hk⟩, rfl⟩, o, ho, rfl⟩; exact ⟨_, ⟨a, ha, rfl⟩, hk, o, ho, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, hk, o, ho, rfl⟩; exact ⟨_, ⟨a, ⟨ha, hk⟩, rfl⟩, o, ho, rfl⟩

theorem keep_sp {i : Instr} (h : (!(i.dsts.contains 13)) = true) (sp : Word) :
    spAfter i sp = sp ∧ spExact i = true := by
  cases i <;> simp_all [spAfter, spExact, Instr.dsts]

theorem symTrace_mem : ∀ {is : List Instr} {ss : SState} {e : SExpr × Instr × List SAccess},
    e ∈ symTrace is ss → e.2.1 ∈ is
  | [], _, _, h => absurd h List.not_mem_nil
  | i :: is, ss, e, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (symTrace_mem h)

variable {sp0 : Word} {n : Nat}

theorem effGo_good {ini : List (SExpr × Nat)} {dpc den : SExpr → Word} (hd : Spl den) {sp : Word} :
    ∀ (es : List (SExpr × Instr × List SAccess)) (w : List (SExpr × Nat)) (q : Ef),
    effGo ini w es = true → (∀ e ∈ es, (!(e.2.1.dsts.contains 13)) = true) → q.sp = sp →
    (∀ y, q.U y → AtOrAboveSp sp0 sp y) →
    (∀ y, InRD den (ini ++ w) y → BelowEntry sp0 n y → q.U y) →
    (∀ e ∈ es.map (evD dpc den), ∀ y, (Reads e.accesses y ∨ Writes e.accesses y) →
      BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) →
    Good sp0 n q (es.map (evD dpc den)) ∧ (q.run sp0 (es.map (evD dpc den))).sp = sp ∧
      (∀ y, q.U y → (q.run sp0 (es.map (evD dpc den))).U y) ∧
      ∀ y, InRD den (w ++ es.flatMap fun e => wrsOf e.2.2) y → BelowEntry sp0 n y →
        (q.run sp0 (es.map (evD dpc den))).U y
  | [], w, q, _, _, hs, _, hI, _ => ⟨trivial, hs, fun _ h => h, fun y hy hb =>
      hI y (inR_append.mpr (.inr (by simpa using hy))) hb⟩
  | (pc, i, acc) :: es, w, q, hg, hk, hs, hU, hI, hA => by
    simp only [effGo, Bool.and_eq_true, List.all_eq_true] at hg
    obtain ⟨hr, hg⟩ := hg
    subst hs
    obtain ⟨hsa, hx⟩ := keep_sp (i := i) (hk _ List.mem_cons_self) q.sp
    have hA0 := hA _ List.mem_cons_self
    simp only [evD] at hA0
    let q' := q.step sp0 ⟨dpc pc, i, acc.map fun a => ⟨a.kind, den a.addr, a.width⟩⟩
    have hs' : q'.sp = q.sp := by simp only [q', Ef.step, hsa]
    have hU' : ∀ y, q.U y → q'.U y := fun y h => ⟨by rw [hsa]; exact hU y h, .inl h⟩
    have hI' : ∀ y, InRD den (ini ++ (w ++ wrsOf acc)) y → BelowEntry sp0 n y → q'.U y := by
      intro y hy hb
      rw [← List.append_assoc, inR_append] at hy
      rcases hy with hy | hy
      · exact hU' y (hI y hy hb)
      · have hw := inR_wrs.mp hy
        exact ⟨by rw [hsa]; exact hA0 y (.inr hw) hb, .inr hw⟩
    obtain ⟨g, gs, gU, gW⟩ := effGo_good hd es _ q' hg (fun e he => hk e (List.mem_cons_of_mem _ he))
      hs' (fun y h => by have := h.1; rw [hsa] at this; exact this) hI'
      (fun e he => hA e (List.mem_cons_of_mem _ he))
    refine ⟨⟨⟨hx, fun y hy hb => .inl (hA0 y hy hb), ?_⟩, g⟩, gs, fun y h => gU y (hU' y h), ?_⟩
    · rintro y ⟨_, ha0, hk', o, ho, rfl⟩ hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha0
      have hr' := hr a ha
      rw [show a.kind = .read from hk', show (Kind.read == Kind.write) = false from rfl, Bool.false_or] at hr'
      obtain ⟨r, hr1, hr2⟩ := List.any_eq_true.mp hr'
      obtain ⟨o', ho', he⟩ := inRgn_den hd hr2 ho
      exact hI _ ⟨r, hr1, o', ho', he⟩ hb
    · intro y hy hb
      simp only [List.flatMap_cons, ← List.append_assoc] at hy
      exact gW y hy hb

theorem inRgnOff_den {den : SExpr → Word} (hd : Spl den) {r : SExpr} {k : Nat} {x : SExpr × Nat}
    (h : inRgnOff r k x = true) : ∃ o < x.2, den r + BitVec.ofNat 32 k = den x.1 + BitVec.ofNat 32 o := by
  simp only [inRgnOff, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨B, hB⟩ := hd
  refine ⟨((split (norm r)).2 + BitVec.ofNat 32 k - (split (norm x.1)).2).toNat, by omega, ?_⟩
  rw [hB r, hB x.1, h.1, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc, BitVec.add_assoc]
  congr 1; rw [BitVec.add_comm (split (norm x.1)).2, BitVec.sub_add_cancel]

/-- **The effect of a decided block** under the valuations `dpc` and `den`. -/
theorem block_good {is : List Instr} {ini wo : List (SExpr × Nat)} (hk : effChk ini is = true)
    (hc : covChk wo is = true) {dpc den : SExpr → Word} (hd : Spl den) (p : Ef)
    (hU : ∀ y, p.U y → AtOrAboveSp sp0 p.sp y) (hI : ∀ y, InRD den ini y → BelowEntry sp0 n y → p.U y)
    (hA : ∀ e ∈ (symTrace is SState.init).map (evD dpc den), ∀ y, (Reads e.accesses y ∨ Writes e.accesses y) →
      BelowEntry sp0 n y → AtOrAboveSp sp0 p.sp y) :
    Good sp0 n p ((symTrace is SState.init).map (evD dpc den)) ∧
      (p.run sp0 ((symTrace is SState.init).map (evD dpc den))).sp = p.sp ∧
      (∀ y, p.U y → (p.run sp0 ((symTrace is SState.init).map (evD dpc den))).U y) ∧
      ∀ y, InRD den wo y → BelowEntry sp0 n y → (p.run sp0 ((symTrace is SState.init).map (evD dpc den))).U y := by
  simp only [effChk, Bool.and_eq_true] at hk
  obtain ⟨⟨_, hks⟩, hg⟩ := hk
  obtain ⟨g, gs, gU, gW⟩ := effGo_good hd (sp := p.sp) _ [] p hg
    (fun e he => List.all_eq_true.mp hks _ (symTrace_mem he)) rfl hU
    (fun y hy hb => hI y (by simpa using hy) hb) hA
  refine ⟨g, gs, gU, fun y ⟨r, hr, o, ho, hy⟩ hb => gW y ?_ hb⟩
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hc r hr) o (List.mem_range.mpr ho)
  obtain ⟨x, hx, hxi⟩ := List.any_eq_true.mp h1
  obtain ⟨o', ho', he⟩ := inRgnOff_den hd hxi
  exact ⟨x, by simpa using hx, o', ho', by rw [hy, he]⟩

/-- Every access of the block lies in a region of `fp`. -/
def fpChk (fp : List (SExpr × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all fun a => fp.any (inRgn a.addr a.width)

theorem fp_acc {fp : List (SExpr × Nat)} {is : List Instr} (h : fpChk fp is = true) {dpc den : SExpr → Word}
    (hd : Spl den) : ∀ e ∈ (symTrace is SState.init).map (evD dpc den), ∀ y,
      (Reads e.accesses y ∨ Writes e.accesses y) → InRD den fp y := by
  intro e he y hy
  obtain ⟨se, hse, rfl⟩ := List.mem_map.mp he
  obtain ⟨x, hx, o, ho, rfl⟩ : ∃ x ∈ (evD dpc den se).accesses, ∃ o < x.width,
      y = x.addr + BitVec.ofNat 32 o := by
    rcases hy with ⟨x, hx, -, o, ho, rfl⟩ | ⟨x, hx, -, o, ho, rfl⟩ <;> exact ⟨x, hx, o, ho, rfl⟩
  obtain ⟨pc, i, acc⟩ := se
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨r, hr, hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h _ hse) a ha)
  obtain ⟨o', ho', he⟩ := inRgn_den hd hi ho
  exact ⟨r, hr, o', ho', he⟩

/-- The decided effect of a block: reads in `ini` or earlier writes, writes covering `wo`, and
every access in `fp`. -/
def blkChk (ini wo fp : List (SExpr × Nat)) (is : List Instr) : Bool :=
  effChk ini is && covChk wo is && fpChk fp is

/-! ## Segments that keep SP -/

/-- **A segment at SP `sp`**: from any effect state at `sp` whose `U` lies at or above `sp` and
holds the window bytes of `X`, `tr` is `Good`, stays at `sp`, keeps `U`, and adds those of `Y`. -/
def Seg (sp0 : Word) (n : Nat) (sp : Word) (X : Word → Prop) (tr : List Event) (Y : Word → Prop) : Prop :=
  ∀ q : Ef, q.sp = sp → (∀ y, q.U y → AtOrAboveSp sp0 sp y) → (∀ y, X y → BelowEntry sp0 n y → q.U y) →
    Good sp0 n q tr ∧ (q.run sp0 tr).sp = sp ∧ (∀ y, q.U y → (q.run sp0 tr).U y) ∧
      ∀ y, Y y → BelowEntry sp0 n y → (q.run sp0 tr).U y

theorem run_above : ∀ (q : Ef) (tr : List Event), (∀ y, q.U y → AtOrAboveSp sp0 q.sp y) →
    ∀ y, (q.run sp0 tr).U y → AtOrAboveSp sp0 (q.run sp0 tr).sp y
  | _, [], h => h
  | q, e :: tr, _ => run_above (q.step sp0 e) tr fun _ h => h.1

theorem Seg.append {sp : Word} {X Y Z : Word → Prop} {a b : List Event} (h1 : Seg sp0 n sp X a Y)
    (h2 : Seg sp0 n sp (fun y => X y ∨ Y y) b Z) : Seg sp0 n sp X (a ++ b) (fun y => Y y ∨ Z y) := by
  intro q hs hU hX
  obtain ⟨g1, s1, u1, w1⟩ := h1 q hs hU hX
  obtain ⟨g2, s2, u2, w2⟩ := h2 _ s1 (fun y h => s1 ▸ run_above q a (hs ▸ hU) y h)
    fun y h hb => h.elim (fun h => u1 y (hX y h hb)) (fun h => w1 y h hb)
  rw [run_append]
  exact ⟨(good_append q a b).mpr ⟨g1, g2⟩, s2, fun y h => u2 y (u1 y h),
    fun y h hb => h.elim (fun h => u2 y (w1 y h hb)) (fun h => w2 y h hb)⟩

theorem Seg.mono {sp : Word} {X X' Y Y' : Word → Prop} {tr : List Event} (h : Seg sp0 n sp X tr Y)
    (hX : ∀ y, X y → X' y) (hY : ∀ y, Y' y → Y y) : Seg sp0 n sp X' tr Y' := fun q hs hU hI =>
  let ⟨g, s, u, w⟩ := h q hs hU fun y hx hb => hI y (hX y hx) hb
  ⟨g, s, u, fun y hy hb => w y (hY y hy) hb⟩

/-- `Seg.append` with the requirement of the second segment met before the first. -/
theorem Seg.cat {sp : Word} {X Y Z : Word → Prop} {a b : List Event} (h1 : Seg sp0 n sp X a Y)
    (h2 : Seg sp0 n sp X b Z) : Seg sp0 n sp X (a ++ b) (fun y => Y y ∨ Z y) :=
  h1.append (h2.mono (fun _ h => .inl h) fun _ h => h)

/-- **A decided block is a segment** under the valuations `dpc` and `den`. -/
theorem blk_segD {is : List Instr} {ini wo fp : List (SExpr × Nat)} (h : blkChk ini wo fp is = true)
    {dpc den : SExpr → Word} (hd : Spl den) {sp : Word} {X : Word → Prop} (hI : ∀ y, InRD den ini y → X y)
    (hA : ∀ y, InRD den fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    Seg sp0 n sp X ((symTrace is SState.init).map (evD dpc den)) (InRD den wo) := by
  simp only [blkChk, Bool.and_eq_true] at h
  obtain ⟨⟨hk, hc⟩, hf⟩ := h
  intro q hs hU hX
  subst hs
  exact block_good hk hc hd q hU (fun y hy hb => hX y (hI y hy) hb)
    fun e he y hy hb => hA y (fp_acc hf hd e he y hy) hb

/-- A decided block at the entry state `t` is a segment. -/
theorem blk_seg {is : List Instr} {ini wo fp : List (SExpr × Nat)} (h : blkChk ini wo fp is = true)
    (t : State) {sp : Word} {X : Word → Prop} (hI : ∀ y, InR t ini y → X y)
    (hA : ∀ y, InR t fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    Seg sp0 n sp X (traceAll is t) (InR t wo) := by
  have hfa : is.all Instr.falls = true := by
    simp only [blkChk, effChk, Bool.and_eq_true] at h; exact h.1.1.1.1
  have hT := symTrace_sound is (sound_all hfa) t SState.init
  rw [SState.init_denote] at hT
  rw [← hT]
  exact blk_segD (dpc := (·.denote t)) h (spl_denote t) hI hA

theorem spl_addrE (pc : Word) (As : List SExpr) (vs : List Word) : Spl (addrE pc As vs) :=
  ⟨baseE pc As vs, fun _ => rfl⟩

/-- A decided block from its atoms is a segment. -/
theorem blkE_seg {is : List Instr} {ini wo fp : List (SExpr × Nat)} (h : blkChk ini wo fp is = true)
    {pc : Word} {As : List SExpr} {vs : List Word} {sp : Word} {X : Word → Prop}
    (hI : ∀ y, InRD (addrE pc As vs) ini y → X y)
    (hA : ∀ y, InRD (addrE pc As vs) fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    Seg sp0 n sp X (blockTrE is pc As vs) (InRD (addrE pc As vs) wo) :=
  blk_segD h (spl_addrE pc As vs) hI hA

/-- One event that keeps SP is a segment. -/
theorem ev_seg {e : Event} {sp : Word} {X : Word → Prop} (hx : spExact e.instr = true)
    (hs : spAfter e.instr sp = sp)
    (hA : ∀ y, (Reads e.accesses y ∨ Writes e.accesses y) → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y)
    (hR : ∀ y, Reads e.accesses y → BelowEntry sp0 n y → X y) :
    Seg sp0 n sp X [e] (Writes e.accesses) := by
  intro q hq hU hX
  subst hq
  refine ⟨⟨⟨hx, fun y hy hb => .inl (hA y hy hb), fun y hy hb => hX y (hR y hy hb) hb⟩, trivial⟩,
    hs, fun y h => ⟨by rw [hs]; exact hU y h, .inl h⟩,
    fun y hy hb => ⟨by rw [hs]; exact hA y (.inr hy) hb, .inr hy⟩⟩

theorem above_sub {sp y : Word} {k : Nat} (h : AtOrAboveSp sp0 sp y) (hk : (sp0 - sp).toNat + k < 2 ^ 32) :
    AtOrAboveSp sp0 (sp - BitVec.ofNat 32 k) y := by
  simp only [AtOrAboveSp, Region] at *
  bv_omega

/-! ## The effect of a call -/

/-- **The effect of a callee's trace** from entry SP `sp` with `stk` bytes of stack: from any
effect state at `sp` whose `U` holds the window bytes of `Rq`, in a window with room for `stk`
bytes below `sp`, where the bytes `Fp` it accesses outside its stack lie at or above SP, the trace
is `Good`, ends at `sp`, keeps `U`, and adds the window bytes of `Wd`. -/
def EffT (stk : Nat) (Fp Rq Wd : Word → Prop) (sp : Word) : M0Crypto.Release.TrP := fun tr =>
  ∀ sp0 n (p : Ef), p.sp = sp → (sp0 - sp).toNat + stk ≤ n → n < 2 ^ 32 →
    (∀ y, p.U y → AtOrAboveSp sp0 p.sp y) →
    (∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 p.sp y) →
    (∀ y, Rq y → BelowEntry sp0 n y → p.U y) →
    Good sp0 n p tr ∧ (p.run sp0 tr).sp = p.sp ∧ (∀ y, p.U y → (p.run sp0 tr).U y) ∧
      ∀ y, Wd y → BelowEntry sp0 n y → (p.run sp0 tr).U y

theorem word_above {sp y : Word} {k : Nat} (hk : (sp0 - sp).toNat + 4 * k < 2 ^ 32)
    (hy : ∃ a ∈ wordAccesses .write (sp - BitVec.ofNat 32 (4 * k)) k, ∃ o < a.width,
      y = a.addr + BitVec.ofNat 32 o) :
    AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * k)) y := by
  obtain ⟨_, ha, o, ho, rfl⟩ := hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_range] at hi
  simp only [AtOrAboveSp, Region] at *
  bv_omega

/-- **The effect of a framed routine**: `push` of `k` words, a body at the lowered SP that adds
`Wd`, then the `pop` of those words back to `sp`. -/
theorem eff_frame {stk k : Nat} {sp : Word} {Fp Rq Wd : Word → Prop} {e₁ e₂ : Event}
    {body : List Event} (hk : 4 * k ≤ stk) (hW : ∀ y, Wd y → Fp y)
    (x1 : spExact e₁.instr = true) (h1 : spAfter e₁.instr sp = sp - BitVec.ofNat 32 (4 * k))
    (a1 : e₁.accesses = wordAccesses .write (sp - BitVec.ofNat 32 (4 * k)) k)
    (x2 : spExact e₂.instr = true) (h2 : spAfter e₂.instr (sp - BitVec.ofNat 32 (4 * k)) = sp)
    (a2 : e₂.accesses = wordAccesses .read (sp - BitVec.ofNat 32 (4 * k)) k)
    (hb : ∀ sp0 n, (sp0 - sp).toNat + stk ≤ n → n < 2 ^ 32 →
      (∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) →
      Seg sp0 n (sp - BitVec.ofNat 32 (4 * k)) Rq body Wd) :
    EffT stk Fp Rq Wd sp (e₁ :: (body ++ [e₂])) := by
  intro sp0 n p hp hroom hn hU hF hR
  have hk' : (sp0 - sp).toNat + 4 * k < 2 ^ 32 := by omega
  have hw1 : ∀ y, Writes e₁.accesses y → AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * k)) y := by
    rw [a1]; rintro y ⟨a, ha, -, o, ho, rfl⟩; exact word_above hk' ⟨a, ha, o, ho, rfl⟩
  have hr1 : ∀ y, ¬ Reads e₁.accesses y := by
    rw [a1]; rintro y ⟨a, ha, hr, -⟩; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; cases hr
  let q := p.step sp0 e₁
  have qs : q.sp = sp - BitVec.ofNat 32 (4 * k) := by simp only [q, Ef.step, hp, h1]
  have pq : ∀ y, p.U y → q.U y := fun y h =>
    ⟨by rw [hp, h1]; exact above_sub (hp ▸ hU y h) hk', .inl h⟩
  obtain ⟨g, s, u, w⟩ := hb sp0 n hroom hn (hp ▸ hF) q qs (fun y h => qs ▸ h.1) fun y h hb => pq y (hR y h hb)
  have hr2 : ∀ y, Reads e₂.accesses y → (q.run sp0 body).U y := by
    rw [a2]; rintro y ⟨a, ha, -, o, ho, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have hy : Writes e₁.accesses (sp - BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (4 * i) +
        BitVec.ofNat 32 o) := by
      rw [a1]; exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, rfl, o, ho, rfl⟩
    exact u _ ⟨by rw [hp, h1]; exact hw1 _ hy, .inr hy⟩
  have hp2 : ∀ y, Reads e₂.accesses y → AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * k)) y := by
    rw [a2]; rintro y ⟨a, ha, -, o, ho, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact word_above hk' ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, o, ho, rfl⟩
  have hw2 : ∀ y, ¬ Writes e₂.accesses y := by
    rw [a2]; rintro y ⟨a, ha, hr, -⟩; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; cases hr
  have hrun : p.run sp0 (e₁ :: (body ++ [e₂])) = (q.run sp0 body).step sp0 e₂ := by
    simp only [Ef.run, List.foldl_cons, List.foldl_append, List.foldl_nil, q]
  have fs : spAfter e₂.instr (q.run sp0 body).sp = sp := by rw [s, h2]
  rw [hrun]
  refine ⟨⟨⟨x1, fun y hy hb => .inr (by rw [hp, h1]; exact hy.elim (fun h => absurd h (hr1 y)) (hw1 y)),
      fun y h => absurd h (hr1 y)⟩, (good_append _ body [e₂]).mpr ⟨g, ⟨x2, fun y hy hb => .inl
      (s ▸ hy.elim (hp2 y) fun h => absurd h (hw2 y)), fun y h _ => hr2 y h⟩, trivial⟩⟩,
    fs.trans hp.symm, fun y h => ⟨by rw [fs, ← hp]; exact hU y h, .inl (u y (pq y h))⟩,
    fun y hy hb => ⟨by rw [fs, ← hp]; exact hF y (hW y hy) hb, .inl (w y hy hb)⟩⟩

section
open M0Crypto.Release M0Crypto.Release.Routine
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **A routine with its trace as a function `T` of its public values**: the call lemma with that
trace, and the property `E` of `T` at every public value. -/
structure _root_.M0Crypto.Release.Routine.Routine.TE {α : Type} (f : Routine) (pub : Word → State → α)
    (E : Word → α → M0Crypto.Release.TrP) where
  T : Word → α → List Event
  spec : f.SpecT fun base s => Tr.is (T base (pub base s))
  eff : ∀ base p, E base p (T base p)

/-- `Routine.tspec_by` with the property `E`: one derivation whose trace condition admits exactly
one trace at every public value, and `E` of that trace. -/
noncomputable def _root_.M0Crypto.Release.Routine.Routine.te_by {α : Type} {f : Routine}
    {pub : Word → State → α} {E : Word → α → M0Crypto.Release.TrP} {Φ : Word → α → M0Crypto.Release.TrP}
    (h : ∀ base s, f.Entry base s → ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s
      (f.Ret s) (Φ base (pub base s)))
    (hu : ∀ b p, Tr.Uniq (Φ b p)) (hx : ∀ b p, ∃ tr, Φ b p tr) (he : ∀ b p tr, Φ b p tr → E b p tr) :
    f.TE pub E :=
  ⟨fun b p => (hx b p).choose, fun base s e =>
    ReachFT.mono (h base s e) (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (fun _ h => h) fun _ h => hu _ _ _ _ h (hx _ _).choose_spec,
    fun b p => he b p _ (hx b p).choose_spec⟩

end

end M0Crypto.Release.StackEffect
