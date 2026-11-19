import M0Crypto.Release.StackEffectSym

set_option linter.unusedSimpArgs false

/-!
# Byte effects: trace conditions from effect states

`GP sp0 n I Φ J`: from every effect state with `I`, a trace of `Φ` is `Good` and ends with `J`.
Its rules follow the trace combinators (`cat`, `cond`, `rep`, a segment). `SIR sp R` is the
invariant of code that moves SP or keeps it outside a frame body: SP at `sp`, the bytes `R`
written, the written bytes at or above SP; `sir_ev` is its rule for one event.
-/

namespace M0Crypto.Release.StackEffect

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)

/-! ## Trace conditions from effect states -/

section gp
variable {sp0 : Word} {n : Nat}

/-- From every effect state with `I`, a trace of `Φ` is `Good` and ends with `J`. -/
def GP (sp0 : Word) (n : Nat) (I : Ef → Prop) (Φ : TrP) (J : Ef → Prop) : Prop :=
  ∀ q, I q → ∀ tr, Φ tr → Good sp0 n q tr ∧ J (q.run sp0 tr)

theorem GP.cat {I K J : Ef → Prop} {Φ Ψ : TrP} (h1 : GP sp0 n I Φ K) (h2 : GP sp0 n K Ψ J) :
    GP sp0 n I (Tr.cat Φ Ψ) J := by
  rintro q hq _ ⟨a, b, rfl, ha, hb⟩
  obtain ⟨g1, k1⟩ := h1 q hq a ha
  obtain ⟨g2, k2⟩ := h2 _ k1 b hb
  rw [run_append]; exact ⟨(good_append q a b).mpr ⟨g1, g2⟩, k2⟩

theorem GP.cond {I J : Ef → Prop} {b : Bool} {Φ Ψ : TrP} (h1 : b = true → GP sp0 n I Φ J)
    (h2 : b = false → GP sp0 n I Ψ J) : GP sp0 n I (Tr.cond b Φ Ψ) J := fun q hq tr h => by
  cases b
  · exact h2 rfl q hq tr (h.2 rfl)
  · exact h1 rfl q hq tr (h.1 rfl)

theorem GP.nil {I J : Ef → Prop} (h : ∀ q, I q → J q) : GP sp0 n I (Tr.is []) J := by
  rintro q hq _ rfl; exact ⟨trivial, h q hq⟩

/-- A segment at `sp` as a trace condition. -/
theorem GP.seg {I K : Ef → Prop} {sp : Word} {X Y : Word → Prop} {a : List Event}
    (h : Seg sp0 n sp X a Y)
    (hI : ∀ q, I q → q.sp = sp ∧ (∀ y, q.U y → AtOrAboveSp sp0 sp y) ∧ ∀ y, X y → BelowEntry sp0 n y → q.U y)
    (hK : ∀ q q' : Ef, I q → q'.sp = sp → (∀ y, q.U y → q'.U y) → (∀ y, Y y → BelowEntry sp0 n y → q'.U y) →
      (∀ y, q'.U y → AtOrAboveSp sp0 sp y) → K q') : GP sp0 n I (Tr.is a) K := by
  intro q hq tr htr
  subst htr
  obtain ⟨s, u, x⟩ := hI q hq
  obtain ⟨g, s', u', w⟩ := h q s u x
  have ha := run_above (sp0 := sp0) q tr (fun y hy => by rw [s]; exact u y hy)
  exact ⟨g, hK q _ hq s' u' w fun y hy => by rw [← s']; exact ha y hy⟩

theorem GP.pre {I I' J : Ef → Prop} {Φ : TrP} (h : ∀ q, I q → I' q)
    (g : GP sp0 n I' Φ J) : GP sp0 n I Φ J := fun q hq => g q (h q hq)

end gp

/-! ## Events by their instructions and accesses -/

/-- What `Good` sees of an event. -/
def ia (e : Event) : Instr × List Access := (e.instr, e.accesses)

/-- An event with instruction `i` and accesses `a`. -/
def ev (i : Instr) (a : List Access) : Event := ⟨0, i, a⟩

section
variable {sp0 : Word} {n : Nat}

theorem good_ia : ∀ {q : Ef} {a b : List Event}, a.map ia = b.map ia →
    (Good sp0 n q a ↔ Good sp0 n q b) ∧ q.run sp0 a = q.run sp0 b
  | _, [], [], _ => ⟨Iff.rfl, rfl⟩
  | q, x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, ia, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hs : q.step sp0 x = q.step sp0 y := by simp only [Ef.step, h1, h2]
    obtain ⟨i1, i2⟩ := good_ia (q := q.step sp0 y) h3
    refine ⟨by simp only [Good, EvOk, h1, h2, hs, i1], ?_⟩
    show (q.step sp0 x).run sp0 a = (q.step sp0 y).run sp0 b
    rw [hs]; exact i2
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp at h

theorem GP.ia {I J : Ef → Prop} {a b : List Event} (h : a.map ia = b.map ia) (g : GP sp0 n I (Tr.is b) J) :
    GP sp0 n I (Tr.is a) J := by
  rintro q hq _ rfl
  obtain ⟨g1, g2⟩ := g q hq b rfl
  obtain ⟨i1, i2⟩ := good_ia (n := n) (q := q) h
  exact ⟨i1.mpr g1, i2 ▸ g2⟩

theorem GP.cons {I K J : Ef → Prop} {e : Event} {l : List Event} (h1 : GP sp0 n I (Tr.is [e]) K)
    (h2 : GP sp0 n K (Tr.is l) J) : GP sp0 n I (Tr.is (e :: l)) J := by
  have := GP.cat h1 h2; rwa [Tr.cat_is_is] at this

theorem GP.rep {I J : Ef → Prop} {Φ : Nat → TrP} {Ψ : TrP} (hΨ : GP sp0 n I Ψ J) :
    ∀ k j, (∀ i, i < j + k → GP sp0 n I (Φ i) I) → GP sp0 n I (Tr.rep Φ j k Ψ) J
  | 0, _, _ => hΨ
  | k + 1, j, h => GP.cat (h j (by omega)) (GP.rep hΨ k (j + 1) fun i hi => h i (by omega))

/-! ## The invariant outside the body -/

/-- SP at `sp`, the bytes `R` written, and the written bytes at or above SP. -/
structure SIR (sp0 sp : Word) (R : Word → Prop) (q : Ef) : Prop where
  hs : q.sp = sp
  r : ∀ y, R y → q.U y
  ab : ∀ y, q.U y → AtOrAboveSp sp0 sp y

/-- **One event** outside the body: its accesses at or above SP, its reads written. -/
theorem sir_ev {sp sp' : Word} {R R' : Word → Prop} {e : Event} (hx : spExact e.instr = true)
    (hs : spAfter e.instr sp = sp')
    (hA : ∀ y, (Reads e.accesses y ∨ Writes e.accesses y) → AtOrAboveSp sp0 sp y ∨ AtOrAboveSp sp0 sp' y)
    (hR : ∀ y, Reads e.accesses y → R y) (hR' : ∀ y, R' y → AtOrAboveSp sp0 sp' y ∧ (R y ∨ Writes e.accesses y)) :
    GP sp0 n (SIR sp0 sp R) (Tr.is [e]) (SIR sp0 sp' R') := by
  rintro q ⟨s, r, -⟩ _ rfl
  subst s
  exact ⟨⟨⟨hx, fun y hy _ => by rw [hs]; exact hA y hy, fun y hy _ => r y (hR y hy)⟩, trivial⟩,
    ⟨hs, fun y hy => ⟨by rw [hs]; exact (hR' y hy).1, (hR' y hy).2.imp (r y) id⟩, fun y hy => hs ▸ hy.1⟩⟩

theorem acc_nil {y : Word} : ¬ (Reads [] y ∨ Writes [] y) := by rintro (⟨_, h, _⟩ | ⟨_, h, _⟩) <;> cases h

theorem sir_quiet {sp sp' : Word} {R R' : Word → Prop} {e : Event} (hx : spExact e.instr = true)
    (hs : spAfter e.instr sp = sp') (ha : e.accesses = []) (hR' : ∀ y, R' y → AtOrAboveSp sp0 sp' y ∧ R y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is [e]) (SIR sp0 sp' R') :=
  sir_ev hx hs (fun _ h => absurd (ha ▸ h) acc_nil) (fun _ h => absurd (.inl (ha ▸ h)) acc_nil)
    fun y hy => ⟨(hR' y hy).1, .inl (hR' y hy).2⟩

/-! ## Address facts -/

theorem reg_above {a m d : Nat} {y : Word} (h : Region (sp0 - BitVec.ofNat 32 a) m y) (hm : m ≤ a) (had : a ≤ d)
    (hd : d < 2 ^ 32) : AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 d) y := by
  simp only [AtOrAboveSp, Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at h ⊢
  have := sp0.isLt; have := y.isLt; omega

theorem reg_above2 {D d m : Nat} {y : Word} (h : Region (sp0 - BitVec.ofNat 32 D + BitVec.ofNat 32 d) m y)
    (hm : d + m ≤ D) (hD : D < 2 ^ 32) : AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 D) y := by
  simp only [AtOrAboveSp, Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢
  have := sp0.isLt; have := y.isLt; omega

theorem sp_add {d k : Nat} (h : k ≤ d) :
    sp0 - BitVec.ofNat 32 d + BitVec.ofNat 32 k = sp0 - BitVec.ofNat 32 (d - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega

theorem words_reg {kd : Kind} {x y : Word} {k : Nat} (hk : 4 * k < 2 ^ 32)
    (h : ∃ a ∈ wordAccesses kd x k, ∃ o, o < a.width ∧ y = a.addr + BitVec.ofNat 32 o) : Region x (4 * k) y := by
  obtain ⟨a, ha, o, ho, rfl⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_range] at hi
  dsimp only at ho ⊢
  show ((x + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 o) - x).toNat < 4 * k
  rw [BitVec.add_assoc, BitVec.add_comm x, BitVec.add_sub_cancel]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem reads_words {x y : Word} {k : Nat} (hk : 4 * k < 2 ^ 32) (h : Reads (wordAccesses .read x k) y) :
    Region x (4 * k) y := let ⟨a, ha, _, h⟩ := h; words_reg hk ⟨a, ha, h⟩

theorem writes_words {x y : Word} {k : Nat} (hk : 4 * k < 2 ^ 32) (h : Writes (wordAccesses .write x k) y) :
    Region x (4 * k) y := let ⟨a, ha, _, h⟩ := h; words_reg hk ⟨a, ha, h⟩

theorem no_writes {x y : Word} {k : Nat} : ¬ Writes (wordAccesses .read x k) y := by
  rintro ⟨a, ha, hk, -⟩; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; cases hk

theorem no_reads {x y : Word} {k : Nat} : ¬ Reads (wordAccesses .write x k) y := by
  rintro ⟨a, ha, hk, -⟩; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; cases hk

theorem words_of {x y : Word} {k : Nat} (h : Region x (4 * k) y) : Writes (wordAccesses .write x k) y := by
  have ht : (y - x).toNat < 4 * k := h
  refine ⟨_, List.mem_map.mpr ⟨(y - x).toNat / 4, List.mem_range.mpr (by omega), rfl⟩, rfl,
    (y - x).toNat % 4, by dsimp only; omega, ?_⟩
  have e : BitVec.ofNat 32 (4 * ((y - x).toNat / 4)) + BitVec.ofNat 32 ((y - x).toNat % 4) = y - x := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (y - x).isLt; omega
  dsimp only; rw [BitVec.add_assoc, e, BitVec.add_comm, BitVec.sub_add_cancel]

end

/-! ## Leaf routines -/

section leaf
open M0Crypto.Sym (SExpr)
variable {sp0 : Word} {n : Nat}

/-- **A routine's effect from a GP** from the written set `U` of its caller. -/
theorem effT_of_gp {stk : Nat} {Fp Rq Wd : Word → Prop} {sp : Word} {tr : List Event}
    (h : ∀ sp0 n (U : Word → Prop), (sp0 - sp).toNat + stk ≤ n → n < 2 ^ 32 →
      (∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) → (∀ y, Rq y → BelowEntry sp0 n y → U y) →
      GP sp0 n (SIR sp0 sp U) (Tr.is tr) (SIR sp0 sp fun y => U y ∨ Wd y ∧ BelowEntry sp0 n y)) :
    EffT stk Fp Rq Wd sp tr := fun sp0 n p hp h1 h2 hU hF hR => by
  subst hp
  obtain ⟨g, s, r, -⟩ := h sp0 n p.U h1 h2 hF hR p ⟨rfl, fun _ h => h, hU⟩ tr rfl
  exact ⟨g, s, fun y hy => r y (.inl hy), fun y hy hb => r y (.inr ⟨hy, hb⟩)⟩

/-- **A callee's trace** from its effect, under `SIR`. -/
theorem gp_effT {stk : Nat} {Fp Rq Wd R : Word → Prop} {sp : Word} {tr : List Event}
    (h : EffT stk Fp Rq Wd sp tr) (hroom : (sp0 - sp).toNat + stk ≤ n) (hn : n < 2 ^ 32)
    (hF : ∀ y, Fp y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) (hR : ∀ y, Rq y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is tr) (SIR sp0 sp fun y => R y ∨ Wd y ∧ BelowEntry sp0 n y) := by
  intro q ⟨hs, r, ab⟩ x hx
  rw [show x = tr from hx]
  subst hs
  obtain ⟨g, s, u, w⟩ := h sp0 n q rfl hroom hn ab hF fun y hy hb => r y (hR y hy hb)
  exact ⟨g, s, fun y hy => hy.elim (fun h => u y (r y h)) fun h => w y h.1 h.2,
    fun y hy => s ▸ run_above q tr ab y hy⟩

/-- A segment at `sp` under `SIR`. -/
theorem sir_seg {sp : Word} {X Y R R' : Word → Prop} {a : List Event} (h : Seg sp0 n sp X a Y)
    (hX : ∀ y, X y → BelowEntry sp0 n y → R y) (hR : ∀ y, R' y → R y ∨ Y y ∧ BelowEntry sp0 n y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is a) (SIR sp0 sp R') :=
  GP.seg h (fun _ hq => ⟨hq.hs, hq.ab, fun y hy hb => hq.r y (hX y hy hb)⟩)
    fun _ _ hq s u w ab => ⟨s, fun y hy => (hR y hy).elim (fun h => u y (hq.r y h)) fun h => w y h.1 h.2, ab⟩

/-- A loop's passes with an invariant at each index. -/
theorem GP.repI {I : Nat → Ef → Prop} {J : Ef → Prop} {Φ : Nat → TrP} {Ψ : TrP} :
    ∀ k j, (∀ i, j ≤ i → i < j + k → GP sp0 n (I i) (Φ i) (I (i + 1))) → GP sp0 n (I (j + k)) Ψ J →
      GP sp0 n (I j) (Tr.rep Φ j k Ψ) J
  | 0, _, _, hΨ => hΨ
  | k + 1, j, h, hΨ => GP.cat (h j (Nat.le_refl _) (by omega))
      (GP.repI k (j + 1) (fun i h1 h2 => h i (by omega) (by omega)) (by rwa [show j + 1 + k = j + (k + 1) by omega]))

theorem reg_sub_above {sp y : Word} {d e : Nat} (h : Region (sp - BitVec.ofNat 32 d) e y) (he : e ≤ d)
    (hd : (sp0 - sp).toNat + d < 2 ^ 32) : AtOrAboveSp sp0 (sp - BitVec.ofNat 32 d) y := by
  simp only [AtOrAboveSp, Region] at h ⊢
  bv_omega

/-! ## Code that keeps its written set

Once every byte a stretch of code accesses below the entry is written, it keeps `SIR sp R`: a
loop body, a cut, a branch. -/

theorem catI {I J : Ef → Prop} {Φ Ψ : TrP} (h1 : GP sp0 n I Φ I) (h2 : GP sp0 n I Ψ J) :
    GP sp0 n I (Tr.cat Φ Ψ) J := GP.cat h1 h2

theorem sir_closed {sp : Word} {X R : Word → Prop} {a : List Event} {Y : Word → Prop}
    (h : (∀ y, X y → BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) → Seg sp0 n sp X a Y)
    (hX : ∀ y, X y → BelowEntry sp0 n y → R y) : GP sp0 n (SIR sp0 sp R) (Tr.is a) (SIR sp0 sp R) :=
  fun q hq => sir_seg (h fun y hy hb => hq.ab y (hq.r y (hX y hy hb))) hX (fun _ h => .inl h) q hq

/-- A block whose accesses lie in the regions `rs` of its atoms. -/
theorem sir_blkE {is : List Instr} {rs : List (SExpr × Nat)} (h : blkChk rs [] rs is = true)
    {pc : Word} {As : List SExpr} {vs : List Word} {sp : Word} {R : Word → Prop}
    (hX : ∀ y, InRD (addrE pc As vs) rs y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is (blockTrE is pc As vs)) (SIR sp0 sp R) :=
  sir_closed (fun hA => blkE_seg h (fun _ h => h) hA) hX

/-- A glue block whose accesses lie in the regions `rs` of its registers. -/
theorem sir_blk {is : List Instr} {rs : List (SExpr × Nat)} (h : blkChk rs [] rs is = true)
    {pc : Word} {L : List Reg} {vs : List Word} {sp : Word} {R : Word → Prop}
    (hX : ∀ y, InR (regState pc L vs) rs y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is (blockTr is pc L vs)) (SIR sp0 sp R) :=
  sir_closed (fun hA => blk_seg h _ (fun _ h => h) hA) hX

/-- An event that keeps SP and accesses nothing. -/
theorem sir_quietC {sp : Word} {R : Word → Prop} {e : Event} (hx : spExact e.instr = true)
    (hs : spAfter e.instr sp = sp) (ha : e.accesses = []) : GP sp0 n (SIR sp0 sp R) (Tr.is [e]) (SIR sp0 sp R) :=
  fun q hq => sir_quiet hx hs ha (fun y hy => ⟨hq.ab y (hq.r y hy), hy⟩) q hq

theorem reg_in {a y : Word} {c w N : Nat} (h : Region (a + BitVec.ofNat 32 c) w y) (hc : c + w ≤ N)
    (hN : N < 2 ^ 32) : Region a N y := by
  simp only [Region] at h ⊢
  bv_omega

theorem GP.is_of {I J : Ef → Prop} {Φ : TrP} {tr : List Event} (g : GP sp0 n I Φ J) (h : Φ tr) :
    GP sp0 n I (Tr.is tr) J := fun q hq _ hx => hx ▸ g q hq tr h

/-- A segment at `sp` whose accesses below the entry lie at or above SP once they lie in `R`. -/
theorem sir_segR {sp : Word} {X Y R R' : Word → Prop} {a : List Event}
    (h : (∀ y, R y → AtOrAboveSp sp0 sp y) → Seg sp0 n sp X a Y)
    (hX : ∀ y, X y → BelowEntry sp0 n y → R y) (hR : ∀ y, R' y → R y ∨ Y y ∧ BelowEntry sp0 n y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is a) (SIR sp0 sp R') :=
  fun q hq => sir_seg (h fun y hy => hq.ab y (hq.r y hy)) hX hR q hq

/-- **A framed non-entry routine**: `push {mask, lr}; sub sp, #4k`, a body at the lowered SP that
keeps the saved words, then `add sp, #4k; pop {mask, pc}`. The bytes `R'` after it are those of `U`
or bytes at or above SP that the body wrote. -/
theorem frameK_gp {mask : BitVec 8} {k : Nat} {sp pc1 pc2 pc3 pc4 : Word} {U R2 R' : Word → Prop} {Ψ : TrP}
    (hk : k < 128) (hroom : (sp0 - sp).toNat + (4 * nSaved mask + 4 * k) < 2 ^ 32)
    (hB : GP sp0 n (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k))
      (fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)) Ψ
      (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k)) R2))
    (hS : ∀ y, Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y → R2 y)
    (hR' : ∀ y, R' y → U y ∨ AtOrAboveSp sp0 sp y ∧ R2 y) (hUR : ∀ y, U y → R2 y) :
    GP sp0 n (SIR sp0 sp U)
      (Tr.cat (Tr.is [⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat (Tr.cat (Tr.is [⟨pc2, .subSp (BitVec.ofNat 7 k), []⟩])
            (Tr.cat Ψ (Tr.is [⟨pc3, .addSp (BitVec.ofNat 7 k), []⟩])))
          (Tr.is [⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])))
      (SIR sp0 sp R') := fun q hq => by
  have hU : ∀ y, U y → AtOrAboveSp sp0 sp y := fun y hy => hq.ab y (hq.r y hy)
  have h4 : 4 * nSaved mask < 2 ^ 32 := by omega
  have r1 : (sp0 - sp).toNat + 4 * nSaved mask < 2 ^ 32 := by omega
  have r2 : (sp0 - (sp - BitVec.ofNat 32 (4 * nSaved mask))).toNat + 4 * k < 2 ^ 32 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hroom ⊢; have := sp.isLt; have := sp0.isLt; omega
  have a1 : ∀ y, (U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) →
      AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y :=
    fun y hy => hy.elim (fun h => above_sub (hU y h) r1) fun h => reg_sub_above h (Nat.le_refl _) r1
  have hks : (BitVec.ofNat 7 k).toNat * 4 = 4 * k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mul_comm]
  have s1 : spAfter (.push mask true) sp = sp - BitVec.ofNat 32 (4 * nSaved mask) := by
    simp only [spAfter, nSaved, Bool.toNat_true]
  have s2 : spAfter (.subSp (BitVec.ofNat 7 k)) (sp - BitVec.ofNat 32 (4 * nSaved mask)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k) := by simp only [spAfter, hks]
  have s3 : spAfter (.addSp (BitVec.ofNat 7 k)) (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) := by simp only [spAfter, hks, BitVec.sub_add_cancel]
  have s4 : spAfter (.pop mask true) (sp - BitVec.ofNat 32 (4 * nSaved mask)) = sp := by
    show _ + BitVec.ofNat 32 (4 * nSaved mask) = sp; exact BitVec.sub_add_cancel _ _
  have e1 := sir_ev (sp0 := sp0) (n := n) (R := U)
    (e := ⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩) (R' := fun y => U y ∨
      Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) rfl s1
    (fun y hy => .inr (hy.elim (fun h => absurd h no_reads)
      fun h => reg_sub_above (writes_words h4 h) (Nat.le_refl _) r1)) (fun y h => absurd h no_reads)
    (fun y hy => ⟨a1 y hy, hy.imp_right words_of⟩)
  have e2 := sir_quiet (sp0 := sp0) (n := n) (e := ⟨pc2, .subSp (BitVec.ofNat 7 k), []⟩) rfl s2 rfl
    (R' := fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)
    fun y hy => ⟨above_sub (a1 y hy) r2, hy⟩
  have e3 := sir_quiet (sp0 := sp0) (n := n) (R := R2) (e := ⟨pc3, .addSp (BitVec.ofNat 7 k), []⟩) rfl s3 rfl
    (R' := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y ∧ R2 y) fun y hy => ⟨hy.1, hy.2⟩
  have e4 := sir_ev (sp0 := sp0) (n := n) (R' := R')
    (R := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y ∧ R2 y)
    (e := ⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩) rfl s4
    (fun y hy => .inl (hy.elim (fun h => reg_sub_above (reads_words h4 h) (Nat.le_refl _) r1)
      fun h => absurd h no_writes))
    (fun y h => ⟨reg_sub_above (reads_words h4 h) (Nat.le_refl _) r1, hS y (reads_words h4 h)⟩)
    fun y hy => (hR' y hy).elim (fun h => ⟨hU y h, .inl ⟨above_sub (hU y h) r1, hUR y h⟩⟩)
      fun h => ⟨h.1, .inl ⟨above_sub h.1 r1, h.2⟩⟩
  exact GP.cat e1 (GP.cat (GP.cat e2 (GP.cat hB e3)) e4) q hq

/-- The atom `i0` at `a`, as a window of `m` bytes. -/
theorem hv_at {vs : List Word} {i0 m : Nat} {a : Word} (h : vs[i0]? = some a) :
    ∀ i v, (i == i0) = true → vs[i]? = some v → ∃ k ≤ m, v = a + BitVec.ofNat 32 k := by
  intro i v hi hv
  simp only [beq_iff_eq] at hi; subst hi
  rw [h] at hv; cases hv; exact ⟨0, Nat.zero_le _, by simp⟩

theorem reg_split {a y : Word} {x w : Nat} (h : Region a (x + w) y) :
    Region a x y ∨ Region (a + BitVec.ofNat 32 x) w y := by
  simp only [Region] at h ⊢; bv_omega

theorem reg_off {a : Word} {k o N : Nat} (h : k + o < N) : Region a N (a + BitVec.ofNat 32 k + BitVec.ofNat 32 o) := by
  simp only [Region]; bv_omega

/-- One region's bytes, from the value of its expression. -/
theorem inR_one {t : State} {e : SExpr} {w : Nat} {y : Word} (h : Region (e.denote t) w y) : InR t [(e, w)] y :=
  ⟨_, List.mem_singleton.2 rfl, _, h, by bv_omega⟩

/-! A PC-relative literal's address `((pc + c) & ~3) + k` lies within `c + k` bytes of the code. -/

theorem and_not3 (x : Word) : (x &&& ~~~3#32) + (x &&& 3#32) = x := by
  have h0 : (x &&& ~~~3#32) &&& (x &&& 3#32) = 0#32 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases (3#32)[i] <;> rfl
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ h0, ← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]
theorem and3_lt (x : Word) : (x &&& 3#32).toNat < 4 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
theorem al_reg {b y : Word} {c k o N : Nat} (h : y = ((b + BitVec.ofNat 32 c) &&& ~~~3#32) + BitVec.ofNat 32 k + BitVec.ofNat 32 o)
    (hc : 3 ≤ c) (hN : c + k + o < N) (h32 : N < 2 ^ 32) : Region b N y := by
  have e := and_not3 (b + BitVec.ofNat 32 c); have r4 := and3_lt (b + BitVec.ofNat 32 c)
  generalize (b + BitVec.ofNat 32 c) &&& ~~~3#32 = z at e h
  generalize (b + BitVec.ofNat 32 c) &&& 3#32 = r at e r4
  subst h; simp only [Region]; bv_omega

end leaf

/-! ## Regions of a block's atoms -/

section
open M0Crypto.Sym

/-- The atom `i` with `e`'s base, and `e`'s offset from it: the atom `addrE` values `e` by. -/
def atomOf : List SExpr → SExpr → Option (Nat × Word)
  | [], _ => none
  | x :: As, e => if (split (norm x)).1 == (split (norm e)).1 then some (0, (split (norm e)).2 - (split (norm x)).2)
    else (atomOf As e).map fun p => (p.1 + 1, p.2)

theorem sub_add_sub (v a b : Word) : v - a + b = v + (b - a) := by bv_omega

theorem addrE_atom {pc : Word} : ∀ {As : List SExpr} {vs : List Word} {e : SExpr} {i : Nat} {d : Word},
    vs.length = As.length → atomOf As e = some (i, d) → ∃ v, vs[i]? = some v ∧ addrE pc As vs e = v + d
  | [], _, _, _, _, _, h => by simp [atomOf] at h
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | x :: As, v :: vs, e, i, d, hl, h => by
    unfold atomOf at h
    simp only [addrE, baseE, List.zip_cons_cons, List.find?_cons] at h ⊢
    split at h
    · next hx =>
      simp only [hx, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, rfl, sub_add_sub _ _ _⟩
    · next hx =>
      simp only [hx] at ⊢
      obtain ⟨⟨i', d'⟩, h', he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simpa [addrE, baseE] using addrE_atom (pc := pc) (by simpa using hl) h'

/-- Every region of `rs` has an atom `i` with `ok i`, and lies within `N` bytes of `a` once each
such atom lies within `m` bytes of `a`. -/
def winChk (As : List SExpr) (ok : Nat → Bool) (m N : Nat) (rs : List (SExpr × Nat)) : Bool :=
  rs.all fun r => match atomOf As r.1 with
    | some (i, d) => ok i && decide (m + d.toNat + r.2 ≤ N)
    | none => false

theorem win_arith {a d : Word} {k o N : Nat} (h : k + d.toNat + o < N) :
    Region a N (a + BitVec.ofNat 32 k + d + BitVec.ofNat 32 o) := by
  simp only [Region]; bv_omega

/-- **A block's regions in a window**: from the checked offsets of its atoms' regions. -/
theorem inRD_win {pc a y : Word} {As : List SExpr} {vs : List Word} {rs : List (SExpr × Nat)}
    {ok : Nat → Bool} {m N : Nat} (hl : vs.length = As.length) (hc : winChk As ok m N rs = true)
    (hv : ∀ i v, ok i = true → vs[i]? = some v → ∃ k ≤ m, v = a + BitVec.ofNat 32 k)
    (hy : InRD (addrE pc As vs) rs y) : Region a N y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  have hr' := List.all_eq_true.1 hc r hr
  revert hr'
  split
  · next i d hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hi, hm⟩
    obtain ⟨v, hvi, hav⟩ := addrE_atom (pc := pc) hl hd
    obtain ⟨k, hk, rfl⟩ := hv i v hi hvi
    rw [hav]; exact win_arith (by omega)
  · simp

/-- SP-relative regions `(offset, width)`. -/
def spRg (l : List (Nat × Nat)) : List (SExpr × Nat) :=
  l.map fun x => (.add (.reg0 13) (.const (BitVec.ofNat 32 x.1)), x.2)

/-- **A glue block's SP-relative regions in its frame.** -/
theorem inR_sp {pc v y : Word} {l : List (Nat × Nat)} {N : Nat} (hc : (l.all fun x => decide (x.1 + x.2 ≤ N)) = true)
    (hy : InR (regState pc [13] [v]) (spRg l) y) : Region v N y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have h := List.all_eq_true.1 hc x hx
  simp only [decide_eq_true_eq] at h
  have := win_arith (a := v) (d := 0#32) (k := x.1) (o := o) (N := N) (by simp only at ho; exact show _ + 0 + o < N by omega)
  simpa [SExpr.denote, regState] using this


theorem addrE_none {pc : Word} : ∀ {As : List SExpr} {vs : List Word} {e : SExpr},
    atomOf As e = none → addrE pc As vs e = e.denote (regState pc [] [])
  | [], vs, e, _ => by
    cases vs <;> simp only [addrE, baseE, List.zip_nil_left, List.find?_nil] <;> exact base_split _ e
  | _ :: _, [], e, _ => by simp only [addrE, baseE, List.zip_nil_right, List.find?_nil]; exact base_split _ e
  | x :: As, v :: vs, e, h => by
    unfold atomOf at h
    split at h
    · cases h
    · next hx =>
      have := addrE_none (pc := pc) (vs := vs) (Option.map_eq_none_iff.1 h)
      simp only [addrE, baseE, List.zip_cons_cons, List.find?_cons, hx] at this ⊢
      exact this

/-- The bytes of one region of atom `i`. -/
theorem inRD_atom1 {pc v y d : Word} {As : List SExpr} {vs : List Word} {e : SExpr} {w i : Nat}
    (hl : vs.length = As.length) (ha : atomOf As e = some (i, d)) (hv : vs[i]? = some v)
    (hy : InRD (addrE pc As vs) [(e, w)] y) : Region (v + d) w y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  simp only [List.mem_singleton] at hr; subst hr
  obtain ⟨v', h', e'⟩ := addrE_atom (pc := pc) hl ha
  rw [hv] at h'; cases h'
  rw [e']; simp only [Region]; bv_omega

theorem inRD_of {pc v y d : Word} {As : List SExpr} {vs : List Word} {rs : List (SExpr × Nat)} {r : SExpr × Nat}
    {i : Nat} (hl : vs.length = As.length) (hr : r ∈ rs) (ha : atomOf As r.1 = some (i, d))
    (hv : vs[i]? = some v) (hy : Region (v + d) r.2 y) : InRD (addrE pc As vs) rs y := by
  obtain ⟨v', h', e'⟩ := addrE_atom (pc := pc) hl ha
  rw [hv] at h'; cases h'
  exact ⟨r, hr, _, hy, by rw [e']; bv_omega⟩

theorem inR_sp_of {pc v y : Word} {l : List (Nat × Nat)} {c w : Nat} (hc : (c, w) ∈ l)
    (hy : Region (v + BitVec.ofNat 32 c) w y) : InR (regState pc [13] [v]) (spRg l) y :=
  ⟨_, List.mem_map.2 ⟨_, hc, rfl⟩, _, hy, by simp only [SExpr.denote, regState]; simp; bv_omega⟩

end

end M0Crypto.Release.StackEffect
