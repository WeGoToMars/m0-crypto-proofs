import M0Crypto.Release.ConstantTime.HolesNext
import M0Crypto.Release.ConstantTime.EntryReads
import M0Crypto.Release.ConstantTime.LowEqLeft
import M0Crypto.Release.Interrupt

set_option linter.unusedSimpArgs false

/-!
# Stack discipline along a certified run

With a hole map that passes `certHoleFailure`, every run from a certified entry state keeps the
stack discipline of `TraceSpec.StackDiscipline` over the certificate's window below the entry SP,
provided the load sites read outside that window.

The proof follows the run step by step. At a state related to a certificate position, every window
byte at or above SP that is not a hole of the position's entry was written since it was allocated.
A step keeps this: `certPoint_next_pc` gives the next offset, the LR labels exclude every entry
there that the step cannot reach (`not_refuted`), and the check makes the holes of the others
cover the holes after the step (`holesAfter_testBit`).
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release

/-! ## Recorded runs by index -/

theorem runStates_get {stop : Word} {fuel : Nat} {s : State} {states : List State}
    {tr : List Event} (h : runStates stop fuel s = .ok (states, tr)) :
    states[0]? = some s ∧
      (∀ k e, tr[k]? = some e → ∃ u t, states[k]? = some u ∧ states[k + 1]? = some t ∧
        u.pc ≠ stop ∧ step u = .ok (t, e)) ∧
      (∀ k t, states[k + 1]? = some t → ∃ u e, states[k]? = some u ∧ tr[k]? = some e ∧
        u.pc ≠ stop ∧ step u = .ok (t, e)) := by
  induction fuel generalizing s states tr with
  | zero =>
    unfold runStates at h
    split at h
    · cases h; simp
    · contradiction
  | succ n ih =>
    unfold runStates at h
    split at h
    · cases h; simp
    · rename_i hne
      cases hs : step s with
      | error err => simp [hs] at h
      | ok pair =>
        obtain ⟨s', ev⟩ := pair
        simp only [hs] at h
        cases hr : runStates stop n s' with
        | error err => simp [hr] at h
        | ok pair =>
          obtain ⟨rest, es⟩ := pair
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h0, hf, hb⟩ := ih hr
          refine ⟨rfl, ?_, ?_⟩
          · intro k e he
            cases k with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at he
              subst he
              exact ⟨s, s', rfl, by simpa using h0, hne, hs⟩
            | succ k =>
              simp only [List.getElem?_cons_succ] at he ⊢
              exact hf k e he
          · intro k t ht
            cases k with
            | zero =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at ht ⊢
              rw [h0] at ht
              cases ht
              exact ⟨s, ev, rfl, rfl, hne, hs⟩
            | succ k =>
              simp only [List.getElem?_cons_succ] at ht ⊢
              exact hb k t ht

/-! ## Position facts -/

theorem blockPoint_holeFailure {env : Env} {ls : Nat → Option (Int × Int)} {m : HoleMap} {b : Blk}
    {off : Nat} {st : AbsState} {code : List Instr}
    (hc : walkHoleFailure env ls m b.ctx b.off b.st b.code = none)
    (hp : BlockPoint env b off st code) : walkHoleFailure env ls m b.ctx off st code = none := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkHoleFailure, hx, hs] at ih
    split at ih
    · cases ih
    · exact ih

theorem certPoint_hole {env : Env} {ls : Nat → Option (Int × Int)} {m : HoleMap} {cert : Cert}
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr}
    (hc : certHoleFailure env ls m cert = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is)) :
    posHoleOk env ls m off b.ctx st i = true := by
  have hb := (List.findSome?_eq_none_iff.mp hc) b hm
  have hw : walkHoleFailure env ls m b.ctx b.off b.st b.code = none := by
    cases h : walkHoleFailure env ls m b.ctx b.off b.st b.code with
    | none => rfl
    | some x => simp [h] at hb
  have := blockPoint_holeFailure hw hp
  simp only [walkHoleFailure] at this
  cases hpos : posHoleOk env ls m off b.ctx st i
  · simp [hpos] at this
  · rfl

/-- The facts a successful check gives at one position. -/
theorem posHoleOk_facts {env : Env} {ls : Nat → Option (Int × Int)} {m : HoleMap} {off : Nat}
    {ctx : Option Nat} {st : AbsState} {i : Instr} {out : Out}
    (h : posHoleOk env ls m off ctx st i = true) (hx : xfer env off ctx i st = .ok out) :
    ∃ e, m.find off ctx = some e ∧ e.o = st.spOff ∧ lrOk e.lr st = true ∧ pcSafe i = true ∧
      (∀ a ∈ stackAccs st i, saccOk env.win.below env.win.above i st.spOff e.h a = true) ∧
      (loadSite st i = true → ∀ a b, ls off = some (a, b) → st.spOff ≤ a ∧
        -(env.win.below : Int) ≤ a ∧ b ≤ env.win.above ∧
        (e.h &&& rangeMask env.win.below a b == 0) = true) ∧
      ∀ tgt ∈ succOffs off i out, tgt < env.size ∧ ∀ e' ∈ m.get tgt,
        refuted off e i e' = true ∨ (-(env.win.below : Int) ≤ e'.o ∧
          (holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h &&& e'.h ==
            holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h) = true) := by
  unfold posHoleOk at h
  cases hg : m.find off ctx with
  | none => simp [hg] at h
  | some e =>
    simp only [hg, hx, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ho, hlr⟩, hs⟩, ha⟩, hls⟩, ht⟩ := h
    rw [ho] at ha hls ht
    refine ⟨e, rfl, ho, hlr, hs, ha, fun hl a b hab => ?_, fun tgt htg => ?_⟩
    · simp only [hl, Bool.not_true, Bool.false_or, hab, Bool.and_eq_true, decide_eq_true_eq] at hls
      exact ⟨hls.1.1.1, hls.1.1.2, hls.1.2, hls.2⟩
    · have := ht tgt htg
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at this
      exact ⟨this.1, fun e' he' => (this.2 e' he').imp id (fun h => ⟨h.1, h.2⟩)⟩

/-! ## Window arithmetic -/

theorem ofNat_inj_base {base : Word} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : base + BitVec.ofNat 32 a = base + BitVec.ofNat 32 b) : a = b := by
  have h2 : BitVec.ofNat 32 a = BitVec.ofNat 32 b := by
    generalize BitVec.ofNat 32 a = x at h ⊢
    generalize BitVec.ofNat 32 b = y at h ⊢
    bv_omega
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem sp_ofInt_zero {sp0 : Word} {o : Int} {below : Nat} (hb : below < 2 ^ 32)
    (hlo : -(below : Int) ≤ o) (hhi : o ≤ 0) (h : sp0 + BitVec.ofInt 32 o = sp0) : o = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, o = -(n : Int) := ⟨(-o).toNat, by omega⟩
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast] at h
  have h0 : BitVec.ofNat 32 n = 0#32 := by
    generalize BitVec.ofNat 32 n = x at h ⊢
    bv_omega
  have := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)] at this
  simp at this
  omega

/-- A window offset with its byte below the entry SP is negative. -/
theorem neg_of_belowEntry {sp0 : Word} {below above : Nat} {q : Int}
    (hw : below + above < 2 ^ 32) (hlo : -(below : Int) ≤ q) (hhi : q < above)
    (h : TraceSpec.BelowEntry sp0 below (sp0 + BitVec.ofInt 32 q)) : q < 0 := by
  unfold TraceSpec.BelowEntry Region at h
  rw [stack_offset_rebase sp0 below q hlo] at h
  rw [show sp0 - BitVec.ofNat 32 below + BitVec.ofNat 32 (q + (below : Int)).toNat -
      (sp0 - BitVec.ofNat 32 below) = BitVec.ofNat 32 (q + (below : Int)).toNat by
    generalize sp0 - BitVec.ofNat 32 below = a
    generalize BitVec.ofNat 32 (q + (below : Int)).toNat = x
    bv_omega] at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  omega

/-- A byte at a window offset between SP and the entry SP is allocated. -/
theorem atOrAbove_of_off {sp0 : Word} {below : Nat} {o q : Int} (hb : below < 2 ^ 32)
    (hlo : -(below : Int) ≤ o) (hoq : o ≤ q) (hq : q < 0) :
    TraceSpec.AtOrAboveSp sp0 (sp0 + BitVec.ofInt 32 o) (sp0 + BitVec.ofInt 32 q) := by
  obtain ⟨d, rfl⟩ : ∃ d : Nat, q = o + d := ⟨(q - o).toNat, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n : Nat, o = -(n : Int) := ⟨(-o).toNat, by omega⟩
  unfold TraceSpec.AtOrAboveSp Region
  rw [BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  have e1 : sp0 + (-BitVec.ofNat 32 n + BitVec.ofNat 32 d) - (sp0 + -BitVec.ofNat 32 n) =
      BitVec.ofNat 32 d := by
    generalize BitVec.ofNat 32 n = x
    generalize BitVec.ofNat 32 d = y
    bv_omega
  have e2 : sp0 - (sp0 + -BitVec.ofNat 32 n) = BitVec.ofNat 32 n := by
    generalize BitVec.ofNat 32 n = x
    bv_omega
  rw [e1, e2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Bytes below the entry SP lie in the window region. -/
theorem region_of_belowEntry {sp0 y : Word} {below above : Nat}
    (h : TraceSpec.BelowEntry sp0 below y) :
    Region (sp0 - BitVec.ofNat 32 below) (below + above) y := by
  unfold TraceSpec.BelowEntry Region at h
  show _ < _
  omega

theorem not_code_of_belowEntry {p : Params} {env : Env} {bytes : List (BitVec 8)} {y : Word}
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hc : CodeRdAt p env.size y)
    (hy : TraceSpec.BelowEntry p.sp0 env.win.below y) : False := by
  obtain ⟨o, ho, rfl⟩ := hc
  obtain ⟨q, hq, e⟩ := Region.exists (region_of_belowEntry (above := env.win.above) hy)
  obtain ⟨h1, h2, h3⟩ := hdisj
  exact M0Crypto.Release.Frame.ne_of_disj h1 h2 h3 (by omega) hq e

/-- A byte of a region separated from another is not in it. -/
theorem not_region_of_disj {a b y : Word} {n m : Nat} (hd : M0Crypto.Release.Frame.Disj a n b m)
    (hy : Region a n y) : ¬ Region b m y := by
  intro hb
  obtain ⟨o, ho, rfl⟩ := Region.exists hy
  obtain ⟨q, hq, e⟩ := Region.exists hb
  obtain ⟨h1, h2, h3⟩ := hd
  exact M0Crypto.Release.Frame.ne_of_disj h1 h2 h3 ho hq e

theorem saccOk_facts {below above : Nat} {i : Instr} {o : Int} {h : Nat} {a : SAcc}
    (hok : saccOk below above i o h a = true) :
    -(below : Int) ≤ a.lo ∧ a.hi ≤ above ∧
      (a.read = true → o ≤ a.lo ∧ (h &&& rangeMask below a.lo a.hi == 0) = true) ∧
      (a.read = false → o ≤ a.lo ∨ isPush i = true) := by
  unfold saccOk at hok
  cases hr : a.read <;> simp_all

/-- Two return labels with even offsets below `2 ^ 32` are equal only for equal offsets. -/
theorem ret_label_inj {base : Word} {r r' : Nat} (hb : base.toNat % 2 = 0) (hr : r % 2 = 0)
    (hr' : r' % 2 = 0) (h1 : r < 2 ^ 32) (h2 : r' < 2 ^ 32)
    (h : (base + BitVec.ofNat 32 r) ||| 1#32 = (base + BitVec.ofNat 32 r') ||| 1#32) : r = r' := by
  have e1 := clear_thumb_bit _ (pc_even base r hb hr)
  have e2 := clear_thumb_bit _ (pc_even base r' hb hr')
  rw [h] at e1
  exact ofNat_inj_base h1 h2 (e1.symm.trans e2)

/-- The LR labels of a position's entry bound LR there. -/
theorem lrOk_label {p : Params} {bytes : List (BitVec 8)} {off : Nat} {st : AbsState} {s : State}
    {ls : List Nat} (hlr : lrOk (some ls) st = true) (h : LowEq p bytes off st s s) :
    ∃ r ∈ ls, r % 2 = 0 ∧ r < 2 ^ 32 ∧ s.regs 14 = (p.base + BitVec.ofNat 32 r) ||| 1#32 := by
  simp only [lrOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hlr
  obtain ⟨hev, hst⟩ := hlr
  have hreg := h.regs 14 (by decide) (by decide)
  cases hg : st.get 14 with
  | ret rs =>
    rw [hg] at hst hreg
    simp only [List.all_eq_true, List.contains_iff_mem] at hst
    obtain ⟨⟨r, hr, hx⟩, -⟩ := hreg
    exact ⟨r, hst r hr, (hev r (hst r hr)).1, (hev r (hst r hr)).2, by simpa [regAt] using hx⟩
  | _ => rw [hg] at hst; cases hst

/-- **A certified step reaches no entry it refutes.** If `u` steps by `i` to `t`, and `t` is at a
position whose entry is `e'`, then the step from the entry `e` of `u` does not refute `e'`. -/
theorem not_refuted {p : Params} {bytes : List (BitVec 8)} {off off' : Nat} {st st' : AbsState}
    {u t : State} {i : Instr} {e e' : HEnt} (hb : p.base.toNat % 2 = 0) (hoff : off % 2 = 0)
    (hlow : LowEq p bytes off st u u) (hlr : lrOk e.lr st = true)
    (hlow' : LowEq p bytes off' st' t t) (hlr' : lrOk e'.lr st' = true)
    (hex : i.exec u = .ok t) : refuted off e i e' = false := by
  unfold refuted
  cases hl' : e'.lr with
  | none => rfl
  | some ls =>
    rw [hl'] at hlr'
    obtain ⟨r', hr', hev', hlt', ht14⟩ := lrOk_label hlr' hlow'
    by_cases hbl : isBl i = true
    · obtain ⟨imm, rfl⟩ : ∃ imm, i = .bl imm := by cases i <;> simp_all [isBl]
      simp only [Instr.exec, Except.ok.injEq] at hex
      subst hex
      have h14 : ((u.setReg 14 ((u.pc + 4#32) ||| 1#32)).setReg 15
          (u.pc + 4#32 + imm.signExtend 32)).regs 14 = (u.pc + 4#32) ||| 1#32 := by
        simp [State.setReg]
      rw [h14, hlow.pc] at ht14
      simp only [hbl, ↓reduceIte, Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false']
      by_cases hlt : off + 4 < 2 ^ 32
      · have e4 : p.base + BitVec.ofNat 32 off + 4#32 = p.base + BitVec.ofNat 32 (off + 4) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add]
        rw [e4] at ht14
        have := ret_label_inj hb (by omega) hev' hlt hlt' ht14
        subst this
        exact Or.inr (List.contains_iff_mem.mpr hr')
      · exact Or.inl hlt
    · simp only [hbl, Bool.false_eq_true, ↓reduceIte]
      by_cases h14 : (14 : Nat) ∈ i.dsts
      · simp [h14]
      · have hu : t.regs 14 = u.regs 14 := by
          have := next_regs_other (i := i) u 14 (by decide) h14
          simpa [Instr.next, hex] using this
        cases hl : e.lr with
        | none => simp
        | some ls0 =>
          rw [hl] at hlr
          obtain ⟨r, hr, hev, hlt, hu14⟩ := lrOk_label hlr hlow
          rw [hu, hu14] at ht14
          have := ret_label_inj hb hev hev' hlt hlt' ht14
          subst this
          have hc : ls.contains r = true := List.contains_iff_mem.mpr hr'
          have hall : (ls0.all fun r => !ls.contains r) = false := by
            rw [List.all_eq_false]; exact ⟨r, hr, by rw [hc]; decide⟩
          show (_ && (ls0.all fun r => !ls.contains r)) = false
          rw [hall, Bool.and_false]

/-! ## The run theorem -/

/-- At every certificate position related to `u`, window bytes at or above SP that are not holes
of the position's entry were written since they were allocated. -/
def HoleInv (env : Env) (cert : Cert) (p : Params) (bytes : List (BitVec 8)) (m : HoleMap)
    (states : List State) (tr : List Event) (k : Nat) (u : State) : Prop :=
  ∀ b off st i is e, b ∈ cert → BlockPoint env b off st (i :: is) → LowEq p bytes off st u u →
    m.find off b.ctx = some e → ∀ q : Int, e.o ≤ q → q < 0 →
      e.h.testBit (holeBit env.win.below q) = false →
      TraceSpec.WrittenSinceAllocated p.sp0 states tr k (p.sp0 + BitVec.ofInt 32 q)

section
variable {env : Env} {bytes : List (BitVec 8)} {entry : Nat} {init : AbsState} {cert : Cert}
  {p : Params} {s : State}


abbrev EarlierHoles (m : HoleMap) (states : List State) (tr : List Event) (k : Nat) :=
  ∀ j, j < k → ∀ u, states[j]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
    HoleInv env cert p bytes m states tr j u

/-- The pointwise stack claims supplied by a verified fragment for a recorded
state between certificate positions. -/
structure FragmentDisciplineAt (m : HoleMap) (states : List State) (tr : List Event)
    (k : Nat) (u : State) : Prop where
  code : Interrupt.CodePos p.base bytes u
  access : ∀ ev t, tr[k]? = some ev → states[k+1]? = some t →
    ∀ y, (Reads ev.accesses y ∨ Writes ev.accesses y) → TraceSpec.BelowEntry p.sp0 env.win.below y →
      TraceSpec.AtOrAboveSp p.sp0 u.sp y ∨ TraceSpec.AtOrAboveSp p.sp0 t.sp y
  reads : EarlierHoles (env := env) (cert := cert) (p := p) (bytes := bytes) m states tr k →
    ∀ ev, tr[k]? = some ev → ∀ y, Reads ev.accesses y → TraceSpec.BelowEntry p.sp0 env.win.below y →
      TraceSpec.WrittenSinceAllocated p.sp0 states tr k y

/-- A recorded state before the stop has a certificate position, related to itself, with its
buffer obligation. -/
theorem run_position
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s s) {u : State} (hu : BeforeStop (p.lr0 &&& ~~~1#32) s u)
    (hne : u.pc ≠ p.lr0 &&& ~~~1#32) (hplain : env.frameCall = none := by rfl) :
    ∃ b off st i is, b ∈ cert ∧ BlockPoint env b off st (i :: is) ∧ LowEq p bytes off st u u ∧
      BufferStoreOk env p bytes st u i := by
  obtain ⟨u₂, hrel, hb₂⟩ := certificate_reachable_partner hc hi ha hslots hwidth hdisj hsize hbase
    hnowrap hlr hlocal h hplain u hu
  rcases hrel with ⟨b, off, st, code, hm, hp, hnil, hlow⟩ | ⟨hpc, _⟩
  · cases code with
    | nil => exact absurd rfl hnil
    | cons i is =>
      exact ⟨b, off, st, i, is, hm, hp, hlow.left,
        (hlocal u u₂ hu hb₂ ⟨b, off, st, _, hm, hp, hnil, hlow⟩ b off st i is hm hp hlow).1⟩
  · exact absurd hpc hne

/-- Stack discipline with separately justified fragments between certificate positions. -/
theorem certificate_run_discipline_with_fragments
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hsp : s.regs 13 = p.sp0)
    {ok : Nat → Bool} (hl : certLoadFailure ok env cert = none) (R : Word → Prop)
    {ls : Nat → Option (Int × Int)}
    (hsite : ∀ u t ev, BeforeStop (p.lr0 &&& ~~~1#32) s u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → ∀ off, u.pc = p.base + BitVec.ofNat 32 off → ok off = true →
      ∀ i, instrAt bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → R y ∨ ∃ a b, ls off = some (a, b) ∧
        ∃ q : Int, a ≤ q ∧ q < b ∧ y = p.sp0 + BitVec.ofInt 32 q)
    (hR : ∀ y, R y → ¬ TraceSpec.BelowEntry p.sp0 env.win.below y)
    {m : HoleMap} (hh : certHoleFailure env ls m cert = none)
    {fuel : Nat} {states : List State} {tr : List Event}
    (hrun : runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, tr))
    (hpos : ∀ k u, states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      (∃ b off st i is, b ∈ cert ∧ BlockPoint env b off st (i :: is) ∧ LowEq p bytes off st u u ∧
        BufferStoreOk env p bytes st u i) ∨
      FragmentDisciplineAt (env := env) (cert := cert) (p := p) (bytes := bytes) m states tr k u)
    (hAdvance : ∀ k u t ev, states[k]? = some u → states[k+1]? = some t → tr[k]? = some ev →
      u.pc ≠ p.lr0 &&& ~~~1#32 → step u = .ok (t,ev) → t.pc ≠ p.lr0 &&& ~~~1#32 →
      (∃ b off st i is, b ∈ cert ∧ BlockPoint env b off st (i :: is) ∧ LowEq p bytes off st u u ∧
        env.frameCallAt off = none) ∨
      (EarlierHoles (env := env) (cert := cert) (p := p) (bytes := bytes) m states tr (k+1) →
        HoleInv env cert p bytes m states tr (k+1) t)) :
    TraceSpec.StackDiscipline p.sp0 env.win.below states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
        Interrupt.CodePos p.base bytes u := by
  obtain ⟨h0, hfwd, hbwd⟩ := runStates_get hrun
  have hbs : ∀ k u, states[k]? = some u → BeforeStop (p.lr0 &&& ~~~1#32) s u :=
    fun k u hk => runStates_beforeStop hrun u (List.mem_of_getElem? hk)
  have hbase2 : p.base.toNat % 2 = 0 := by omega
  have hb32 : env.win.below < 2 ^ 32 := by omega
  -- the facts at one position
  have hat : ∀ {b off st i is u}, b ∈ cert → BlockPoint env b off st (i :: is) →
      LowEq p bytes off st u u → ∃ out e, xfer env off b.ctx i st = .ok out ∧
        m.find off b.ctx = some e ∧ e.o = st.spOff ∧ lrOk e.lr st = true ∧ pcSafe i = true ∧
        (∀ a ∈ stackAccs st i, saccOk env.win.below env.win.above i st.spOff e.h a = true) ∧
        (loadSite st i = true → ∀ lo hi, ls off = some (lo, hi) → st.spOff ≤ lo ∧
          -(env.win.below : Int) ≤ lo ∧ hi ≤ env.win.above ∧
          (e.h &&& rangeMask env.win.below lo hi == 0) = true) ∧
        ∀ tgt ∈ succOffs off i out, tgt < env.size ∧ ∀ e' ∈ m.get tgt,
          refuted off e i e' = true ∨ (-(env.win.below : Int) ≤ e'.o ∧
            (holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h &&& e'.h ==
              holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h) = true) := by
    intro b off st i is u hm hp _
    obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
    exact ⟨out, posHoleOk_facts (certPoint_hole hh hm hp) hx |>.elim fun e he => ⟨e, hx, he⟩⟩
  -- the invariant
  have inv : ∀ k u, states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      HoleInv env cert p bytes m states tr k u := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      cases k with
      | zero =>
        intro u hu hne
        rw [h0] at hu
        cases hu
        intro b off st i is e hm hp hlow hfind q hq hq0 _
        obtain ⟨out, e', hx, hf, ho, -⟩ := hat hm hp hlow
        rw [hfind] at hf
        cases hf
        have hb := xfer_sp_bounds hx
        have h0' : st.spOff = 0 := sp_ofInt_zero hb32 hb.1 hb.2.1 (hlow.sp.symm.trans hsp)
        omega
      | succ k =>
        intro t ht htne b' off' st' i' is' e' hm' hp' hlow' hfind' q hq hq0 hbit
        obtain ⟨u, ev, hu, he, hune, hst⟩ := hbwd k t ht
        rcases hAdvance k u t ev hu ht he hune hst htne with hposU | hJump
        · obtain ⟨b, off, st, i, is, hm, hp, hlow, hplain⟩ := hposU
          obtain ⟨out, e, hx, hfind, ho, hlre, hsafe, hacc, -, hsucc⟩ := hat hm hp hlow
          have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
          obtain ⟨hexec, hev⟩ := step_exec_of hlow.code₁ off i hlow.pc hdecode hlen hst
          rcases certPoint_next_pc hc hi ha hbase2 hm hp hlow hx hsafe hst hplain with hts | ⟨tgt, htgt, htpc⟩
          · exact absurd hts htne
          obtain ⟨htsz, hall⟩ := hsucc tgt htgt
          obtain ⟨out', e'', -, hfind'', ho', hlr', -⟩ := hat hm' hp' hlow'
          rw [hfind'] at hfind''
          cases hfind''
          have hlen' := (certPoint_instrAt hc hm' hp').2
          have hsz' := instr_size_pos i'
          have hoff' : off' = tgt := ofNat_inj_base (by omega) (by omega) (hlow'.pc.symm.trans htpc)
          subst hoff'
          have hmem : e' ∈ m.get off' := List.mem_of_find?_eq_some hfind'
          have hoffe : off % 2 = 0 := blockPoint_aligned hp (certAligned_head ha hm)
          rcases hall e' hmem with hrf | ⟨hlo', hsub⟩
          · rw [not_refuted hbase2 hoffe hlow hlre hlow' hlr' hexec] at hrf
            cases hrf
          have hspt : t.sp = p.sp0 + BitVec.ofInt 32 e'.o := by
            rw [ho']; simpa [State.sp] using hlow'.sp
          have hlo : ∀ a ∈ stackAccs st i, -(env.win.below : Int) ≤ a.lo :=
            fun a ha => (saccOk_facts (hacc a ha)).1
          have hha : (holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h).testBit
              (holeBit env.win.below q) = false := by
            cases hb : (holesAfter env.win.below st.spOff e'.o (stackAccs st i) e.h).testBit
                (holeBit env.win.below q)
            · rfl
            · rw [sub_testBit hsub hb] at hbit
              cases hbit
          have hnew : ∀ i' u', i' ≤ k + 1 → ¬ i' ≤ k → states[i']? = some u' →
              TraceSpec.AtOrAboveSp p.sp0 u'.sp (p.sp0 + BitVec.ofInt 32 q) := by
            intro i' u' h1 h2 hu'
            have : i' = k + 1 := by omega
            subst this
            rw [ht] at hu'
            cases hu'
            rw [hspt]
            exact atOrAbove_of_off hb32 hlo' hq hq0
          rcases holesAfter_testBit hlo' hq hlo hha with ⟨a, ha, hr, hex, hal, hah⟩ | ⟨hbit', hoq⟩
          · have hw := stackAccs_exact i hlow a ha hr hex q hal hah
            refine ⟨k, Nat.lt_succ_self k, ⟨ev, he, by rw [hev]; exact hw⟩, ?_⟩
            intro i' u' h1 h2 hu'
            exact hnew i' u' h2 (by omega) hu'
          · obtain ⟨j, hj, hw, hold⟩ := ih k (Nat.lt_succ_self k) u hu hune b off st i is e hm hp hlow hfind q
              (by omega) hq0 hbit'
            refine ⟨j, by omega, hw, ?_⟩
            intro i' u' h1 h2 hu'
            by_cases hik : i' ≤ k
            · exact hold i' u' h1 hik hu'
            · exact hnew i' u' h2 hik hu'
        · exact hJump ih b' off' st' i' is' e' hm' hp' hlow' hfind' q hq hq0 hbit
  -- a load-site byte below the entry SP lies in the checked range
  have hsiteW : ∀ (k : Nat) (u t : State) (ev : Event) (b : Blk) (off : Nat) (st : AbsState)
      (i : Instr) (is : List Instr), states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → b ∈ cert → BlockPoint env b off st (i :: is) →
      LowEq p bytes off st u u → loadSite st i = true → ∀ y, Reads ev.accesses y →
      TraceSpec.BelowEntry p.sp0 env.win.below y →
      ∃ lo hi q e, ls off = some (lo, hi) ∧ m.find off b.ctx = some e ∧ st.spOff ≤ lo ∧
        lo ≤ q ∧ q < 0 ∧ -(env.win.below : Int) ≤ lo ∧ y = p.sp0 + BitVec.ofInt 32 q ∧
        e.h.testBit (holeBit env.win.below q) = false := by
    intro k u t ev b off st i is hu hune hst hm hp hlow hls y hy hyw
    obtain ⟨out, e, -, hfind, -, -, -, -, hlsf, -⟩ := hat hm hp hlow
    have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
    have hev := (step_exec_of hlow.code₁ off i hlow.pc hdecode hlen hst).2
    rcases hsite u t ev (hbs k u hu) hune hst off hlow.pc (certPoint_loadSite hl hm hp hls) i
        hdecode (by rw [hev]) y hy with hr | ⟨lo, hi, hab, q, haq, hqb, rfl⟩
    · exact (hR _ hr hyw).elim
    · obtain ⟨h1, h2, h3, h4⟩ := hlsf hls lo hi hab
      have hq0 := neg_of_belowEntry hwidth (by omega) (by omega) hyw
      exact ⟨lo, hi, q, e, hab, hfind, h1, haq, hq0, h2, rfl,
        meets_testBit h4 ((rangeMask_testBit h2 (by omega)).2 ⟨haq, hqb⟩)⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  rotate_right
  · -- instruction positions
    intro k u hu hune
    rcases hpos k u hu hune with ⟨b, off, st, i, is, hm, hp, hlow, -⟩ | hFragment
    · have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
      exact ⟨off, i, hlow.pc, hdecode, hlen, hlow.code₁⟩
    · exact hFragment.code
  · -- accesses at or above SP
    intro k e u u' he hu hu' y hy hyw
    obtain ⟨u0, t, hu0, ht, hune, hst⟩ := hfwd k e he
    rw [hu] at hu0; cases hu0
    rw [hu'] at ht; cases ht
    rcases hpos k u hu hune with ⟨b, off, st, i, is, hm, hp, hlow, hbuf⟩ | hFragment
    · obtain ⟨out, en, hx, -, -, -, -, hacc, -, -⟩ := hat hm hp hlow
      have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
      obtain ⟨hexec, hev⟩ := step_exec_of hlow.code₁ off i hlow.pc hdecode hlen hst
      have hspu : u.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using hlow.sp
      have hacc' : ∃ a ∈ i.accesses u, ∃ j, j < a.width ∧ y = a.addr + BitVec.ofNat 32 j ∧
          (a.kind = .read → Reads e.accesses y) := by
        rcases hy with ⟨a, ha, hk, j, hj, rfl⟩ | ⟨a, ha, hk, j, hj, rfl⟩
        · exact ⟨a, by rw [hev] at ha; exact ha, j, hj, rfl, fun _ => ⟨a, ha, hk, j, hj, rfl⟩⟩
        · exact ⟨a, by rw [hev] at ha; exact ha, j, hj, rfl, fun hr => by rw [hr] at hk; cases hk⟩
      obtain ⟨a, ha, j, hj, rfl, hrd⟩ := hacc'
      rcases xfer_stack_access i hlow hx hsize hbase hnowrap a ha j hj with
        hcode | ⟨hls, hk⟩ | ⟨hss, hk⟩ | ⟨sa, hsa, hkind, q, hql, hqh, hyq⟩
      · exact (not_code_of_belowEntry hdisj hsize hcode hyw).elim
      · obtain ⟨a', b', q, e', -, -, h1, h2, hq0, h3, hyq, -⟩ :=
          hsiteW k u u' e b off st i is hu hune hst hm hp hlow hls _ (hrd hk) hyw
        left; rw [hspu, hyq]; exact atOrAbove_of_off hb32 (xfer_sp_bounds hx).1 (by omega) hq0
      · exact (storeSite_outside i hbuf hss a ha j hj (region_of_belowEntry hyw)).elim
      · obtain ⟨hlo, hhi, hrdf, hwrf⟩ := saccOk_facts (hacc sa hsa)
        rw [hyq] at hyw ⊢
        have hq0 := neg_of_belowEntry hwidth (by omega) (by omega) hyw
        cases hr : sa.read
        · rcases hwrf hr with hle | hpush
          · left; rw [hspu]; exact atOrAbove_of_off hb32 (xfer_sp_bounds hx).1 (by omega) hq0
          · right
            cases i with
            | push l lr =>
              simp only [stackAccs, List.mem_singleton] at hsa
              subst hsa
              simp only [Instr.exec, Except.ok.injEq] at hexec
              subst hexec
              have : ({ u.setReg 15 (u.pc + BitVec.ofNat 32 (Instr.push l lr).size) with
                  mem := storeWords u.mem (u.sp - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)))
                    ((listRegs l).map u.reg ++ if lr = true then [u.regs 14] else []) }.setReg 13
                  (u.sp - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)))).sp =
                  u.sp - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)) := by
                simp [State.sp, State.setReg]
              rw [this, hspu, sp_sub_ofInt]
              exact atOrAbove_of_off hb32 hlo (by omega) hq0
            | _ => simp [isPush] at hpush
        · left; rw [hspu]; exact atOrAbove_of_off hb32 (xfer_sp_bounds hx).1 (by have := (hrdf hr).1; omega) hq0
    · exact hFragment.access e _ he hu' y hy hyw
  · -- reads of written bytes
    intro k e he y hy hyw
    obtain ⟨u, t, hu, ht, hune, hst⟩ := hfwd k e he
    rcases hpos k u hu hune with ⟨b, off, st, i, is, hm, hp, hlow, -⟩ | hFragment
    · obtain ⟨out, en, hx, hfind, ho, -, -, hacc, -, -⟩ := hat hm hp hlow
      have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
      have hev := (step_exec_of hlow.code₁ off i hlow.pc hdecode hlen hst).2
      have hy' := hy
      obtain ⟨a, ha, hk, j, hj, rfl⟩ := hy
      rw [hev] at ha
      rcases xfer_stack_access i hlow hx hsize hbase hnowrap a ha j hj with
        hcode | ⟨hls, -⟩ | ⟨-, hk'⟩ | ⟨sa, hsa, hkind, q, hql, hqh, hyq⟩
      · exact (not_code_of_belowEntry hdisj hsize hcode hyw).elim
      · obtain ⟨a', b', q, e', -, hf', h1, h2, hq0, h3, hyq, hbit⟩ :=
          hsiteW k u t e b off st i is hu hune hst hm hp hlow hls _ hy' hyw
        rw [hfind] at hf'
        cases hf'
        rw [hyq]
        exact inv k u hu hune b off st i is en hm hp hlow hfind q (by omega) hq0 hbit
      · rw [hk] at hk'; cases hk'
      · obtain ⟨hlo, hhi, hrdf, -⟩ := saccOk_facts (hacc sa hsa)
        rw [hyq] at hyw ⊢
        have hq0 := neg_of_belowEntry hwidth (by omega) (by omega) hyw
        obtain ⟨hle, hz⟩ := hrdf (hkind.2 hk)
        have hbit := meets_testBit hz ((rangeMask_testBit hlo (by omega)).2 ⟨hql, hqh⟩)
        exact inv k u hu hune b off st i is en hm hp hlow hfind q (by omega) hq0 hbit

    · exact hFragment.reads (fun j _ => inv j) e he y hy hyw

/-- **Stack discipline of a certified run**, from a certificate position of each recorded state
before the stop. If the hole map passes the check and every load site reads outside the window
below the entry SP or in its checked stack range, the run keeps the stack discipline over the
window's `below` bytes, and each of its states before the stop address is at an instruction of the
artifact. -/
theorem certificate_run_discipline_of
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hsp : s.regs 13 = p.sp0)
    {ok : Nat → Bool} (hl : certLoadFailure ok env cert = none) (R : Word → Prop)
    {ls : Nat → Option (Int × Int)}
    (hsite : ∀ u t ev, BeforeStop (p.lr0 &&& ~~~1#32) s u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → ∀ off, u.pc = p.base + BitVec.ofNat 32 off → ok off = true →
      ∀ i, instrAt bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → R y ∨ ∃ a b, ls off = some (a, b) ∧
        ∃ q : Int, a ≤ q ∧ q < b ∧ y = p.sp0 + BitVec.ofInt 32 q)
    (hR : ∀ y, R y → ¬ TraceSpec.BelowEntry p.sp0 env.win.below y)
    {m : HoleMap} (hh : certHoleFailure env ls m cert = none)
    {fuel : Nat} {states : List State} {tr : List Event}
    (hrun : runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, tr))
    (hpos : ∀ u ∈ states, u.pc ≠ p.lr0 &&& ~~~1#32 → ∃ b off st i is, b ∈ cert ∧
      BlockPoint env b off st (i :: is) ∧ LowEq p bytes off st u u ∧ BufferStoreOk env p bytes st u i)
    (hplain : env.frameCall = none := by rfl) :
    TraceSpec.StackDiscipline p.sp0 env.win.below states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
        Interrupt.CodePos p.base bytes u := by
  apply certificate_run_discipline_with_fragments hc hi ha hwidth hdisj hsize hbase hnowrap
    hsp hl R hsite hR hh hrun
  · intro k u hu hn
    exact .inl (hpos u (List.mem_of_getElem? hu) hn)
  · intro k u t ev hu _ _ hn _ _
    obtain ⟨b,off,st,i,is,hm,hp,hrel,_⟩ := hpos u (List.mem_of_getElem? hu) hn
    exact .inl ⟨b,off,st,i,is,hm,hp,hrel,by simp [Env.frameCallAt,hplain]⟩

/-- **Stack discipline of a certified run** whose local obligations hold at every pair of
related reachable states. -/
theorem certificate_run_discipline
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hslots : certSlotsCheck env cert = true)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hlr : p.lr0.getLsbD 0 = true)
    (hlocal : ∀ u₁ u₂, BeforeStop (p.lr0 &&& ~~~1#32) s u₁ →
      BeforeStop (p.lr0 &&& ~~~1#32) s u₂ → CertAt env cert p bytes u₁ u₂ →
      PositionObligations env cert p bytes u₁ u₂)
    (h : CertAt env cert p bytes s s) (hsp : s.regs 13 = p.sp0)
    {ok : Nat → Bool} (hl : certLoadFailure ok env cert = none) (R : Word → Prop)
    {ls : Nat → Option (Int × Int)}
    (hsite : ∀ u t ev, BeforeStop (p.lr0 &&& ~~~1#32) s u → u.pc ≠ p.lr0 &&& ~~~1#32 →
      step u = .ok (t, ev) → ∀ off, u.pc = p.base + BitVec.ofNat 32 off → ok off = true →
      ∀ i, instrAt bytes off = some i → ev.instr = i →
      ∀ y, Reads ev.accesses y → R y ∨ ∃ a b, ls off = some (a, b) ∧
        ∃ q : Int, a ≤ q ∧ q < b ∧ y = p.sp0 + BitVec.ofInt 32 q)
    (hR : ∀ y, R y → ¬ TraceSpec.BelowEntry p.sp0 env.win.below y)
    {m : HoleMap} (hh : certHoleFailure env ls m cert = none)
    {fuel : Nat} {states : List State} {tr : List Event}
    (hrun : runStates (p.lr0 &&& ~~~1#32) fuel s = .ok (states, tr))
    (hplain : env.frameCall = none := by rfl) :
    TraceSpec.StackDiscipline p.sp0 env.win.below states tr ∧
      ∀ (k : Nat) (u : State), states[k]? = some u → u.pc ≠ p.lr0 &&& ~~~1#32 →
        Interrupt.CodePos p.base bytes u :=
  certificate_run_discipline_of hc hi ha hwidth hdisj hsize hbase hnowrap hsp hl R hsite hR hh hrun
    (fun u hu hne => run_position hc hi ha hslots hwidth hdisj hsize hbase hnowrap hlr hlocal h
      (runStates_beforeStop hrun u hu) hne hplain) hplain

end

end M0Crypto.Release.ConstantTime
