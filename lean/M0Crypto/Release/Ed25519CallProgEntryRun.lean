import M0Crypto.Release.Ed25519CallProgEntry
import M0Crypto.Release.Ed25519CallProgClaim

set_option linter.unusedSimpArgs false

/-!
# Call programs: an entry

An entry is `abi_enter fs`, a checked body program and `abi_leave fs w` with `fs + w = N` the
body's window. `entry_run` composes `enter_run`, `prog_run` and `leave_run`: from the entry state
the entry returns with `sp` and `r4`-`r11` restored, `r1`-`r3` and `r12` zero, the window below the
saved words zero, the saved words in place, and the body's final values in the memory below the
wipe. The footprints are the body's with the 36 saved bytes added; the trace is `entryTr`, a
function of the public context.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

/-- The memory after `abi_enter`'s two pushes. -/
def enterMem (s : State) (sp0 : Word) : Mem :=
  storeWords (storeWords s.mem (sp0 - 20#32) [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14])
    (sp0 - 36#32) [s.regs 8, s.regs 9, s.regs 10, s.regs 11]

/-- The 36 saved bytes. -/
def savedR (sp0 : Word) : Rgn := ⟨sp0 - 36#32, 36⟩

theorem ad_sub36 (x : Word) (fs : Nat) : x - 36#32 - BitVec.ofNat 32 fs = x - BitVec.ofNat 32 (36 + fs) := by
  rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, sub_sub_ofNat]

theorem enterMem_saved (s : State) {sp0 : Word} (h : 36 ≤ sp0.toNat) :
    ∀ i < 9, read32 (enterMem s sp0) (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) =
      s.regs Ed25519.savedRegs[i]! := by
  have hs := sp0.isLt
  intro i hi
  by_cases h4 : i < 4
  · rw [enterMem, Frame.read32_storeWords_same _ _ _ i (by simpa using h4) (by simp)]
    obtain _ | _ | _ | _ | i := i <;> first | rfl | omega
  · obtain ⟨k, rfl⟩ : ∃ k, i = 4 + k := ⟨i - 4, by omega⟩
    rw [enterMem, ← ad_hi,
      Field25519Slot.read32_storeWords_disj (n := 20) _ _ _ _ ?_ k (by omega),
      Frame.read32_storeWords_same _ _ _ k (by simp; omega) (by simp)]
    · obtain _ | _ | _ | _ | _ | k := k <;> first | rfl | omega
    · have : (sp0 - 20#32).toNat = sp0.toNat - 20 := by rw [BitVec.toNat_sub]; simp; omega
      refine ⟨by omega, by simp; omega, Or.inr (by simp; omega)⟩

theorem ad_off (x : Word) (d i k : Nat) :
    x - 36#32 + BitVec.ofNat 32 d + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k - (x - 36#32) =
      BitVec.ofNat 32 (d + 4 * i + k) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (x - 36#32),
    BitVec.add_sub_cancel, BitVec.add_assoc]

theorem enterMem_other (s : State) (sp0 : Word) {y : Word}
    (hy : ¬ Region (sp0 - 36#32) 36 y) : enterMem s sp0 y = s.mem y := by
  have ne : ∀ (a : Word) (d : Nat), a = sp0 - 36#32 + BitVec.ofNat 32 d →
      ∀ i k, d + 4 * i + k < 36 → y ≠ a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k := by
    rintro a d rfl i k hik rfl
    apply hy
    simp only [Region, ad_off, BitVec.toNat_ofNat]
    omega
  rw [enterMem, storeWords_other _ (sp0 - 36#32) _ y fun i k hi hk =>
      ne _ 0 (by simp) i k (by simp at hi; omega),
    storeWords_other _ (sp0 - 20#32) _ y fun i k hi hk =>
      ne _ 16 (ad_sp sp0).symm i k (by simp at hi; omega)]

/-! ## Region arithmetic, each in its own context -/

theorem rgn_region {a y : Word} {n : Nat} (h : Rgn.Has ⟨a, n⟩ y) (hn : n < 2 ^ 32) : Region a n y := by
  obtain ⟨o, ho, rfl⟩ := h
  dsimp only at ho
  simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega

theorem region_add (a : Word) {j n : Nat} (h : j < n) (hn : n < 2 ^ 32) : Region a n (a + BitVec.ofNat 32 j) := by
  simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega

/-- The saved bytes lie above the `N`-byte window below them. -/
theorem saved_not_win {sp0 y : Word} {N : Nat} (h : 36 + N ≤ sp0.toNat) (hy : Region (sp0 - 36#32) 36 y) :
    ¬ Region (sp0 - BitVec.ofNat 32 (36 + N)) N y := by
  have := sp0.isLt; have := y.isLt
  simp only [Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega

/-- The saved bytes lie in the entry's whole window. -/
theorem saved_in_all {sp0 y : Word} {N : Nat} (hy : Region (sp0 - 36#32) 36 y) :
    Region (sp0 - BitVec.ofNat 32 (36 + N)) (36 + N) y := by
  have := sp0.isLt; have := y.isLt
  simp only [Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega

theorem win_in_all {sp0 y : Word} {N : Nat}
    (hy : Region (sp0 - BitVec.ofNat 32 (36 + N)) N y) : Region (sp0 - BitVec.ofNat 32 (36 + N)) (36 + N) y := by
  simp only [Region] at *; omega

/-- Word `i < 9` of the saved bytes. -/
theorem word_in_saved {x y : Word} {i : Nat} (hi : i < 9) (h : Region (x + BitVec.ofNat 32 (4 * i)) 4 y) :
    Region x 36 y := by
  have := x.isLt; have := y.isLt
  simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at *; omega

/-- Memory that agrees with `enterMem` on the saved bytes holds the saved registers. -/
theorem saved_of {m : Mem} {s : State} {sp0 : Word} (h36 : 36 ≤ sp0.toNat)
    (h : ∀ y, Region (sp0 - 36#32) 36 y → m y = enterMem s sp0 y) :
    ∀ i < 9, read32 m (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) = s.regs Ed25519.savedRegs[i]! := by
  intro i hi
  rw [← enterMem_saved s h36 i hi]
  exact Frame.read32_congr fun k hk => h _ (word_in_saved hi (region_add _ hk (by omega)))

theorem callee_of {u s : State}
    (h : ∀ i < 8, u.regs Ed25519.savedRegs[i]! = s.regs Ed25519.savedRegs[i]!) :
    ∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = s.regs r := by
  intro ⟨v, hv⟩ h1 h2
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v := v
  all_goals first | (simp only [Fin.val_mk] at h1 h2; omega) | exact h 4 (by decide) | exact h 5 (by decide) |
    exact h 6 (by decide) | exact h 7 (by decide) | exact h 0 (by decide) | exact h 1 (by decide) |
    exact h 2 (by decide) | exact h 3 (by decide)

/-! ## Zero words -/

theorem write32_zero_in {m : Mem} {a y : Word} (h : Region a 4 y) : write32 m a 0#32 y = 0#8 := by
  have : y = a ∨ y = a + 1#32 ∨ y = a + 2#32 ∨ y = a + 3#32 := by simp only [Region] at h; bv_omega
  rcases this with e | e | e | e <;> simp [write32, e]

theorem zeros_in : ∀ (k : Nat) (m : Mem) (a y : Word), a.toNat + 4 * k ≤ 2 ^ 32 →
    Region a (4 * k) y → storeWords m a (List.replicate k 0#32) y = 0#8
  | 0, _, _, _, _, h => absurd h (by simp [Region])
  | k + 1, m, a, y, hw, h => by
    simp only [List.replicate_succ, storeWords]
    have ha := a.isLt; have hy := y.isLt
    by_cases h4 : Region a 4 y
    · rw [storeWords_other _ _ _ _ fun i j hi hj e => ?_]
      · exact write32_zero_in h4
      · subst e; simp only [List.length_replicate] at hi
        simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h4; omega
    · exact zeros_in k _ _ _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by
        simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h h4 ⊢; omega)

/-- `k` zero words from `a`. -/
theorem zeros_at (k : Nat) (m : Mem) (a y : Word) (hw : a.toNat + 4 * k ≤ 2 ^ 32) :
    storeWords m a (List.replicate k 0#32) y = if Region a (4 * k) y then 0#8 else m y := by
  by_cases h : Region a (4 * k) y
  · simp only [h, ↓reduceIte]; exact zeros_in k m a y hw h
  · simp only [h, ↓reduceIte]
    refine storeWords_other _ _ _ _ fun i j hi hj e => h ?_
    subst e; simp only [List.length_replicate] at hi
    simp only [Region]
    rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel, ← BitVec.ofNat_add]
    simp only [BitVec.toNat_ofNat]; omega

theorem Has.tail {r : Rgn} {l : List Rgn} {y : Word} (h : Has l y) : Has (r :: l) y :=
  let ⟨q, hq, hy⟩ := h; ⟨q, List.mem_cons_of_mem _ hq, hy⟩

/-- The pcs of `[lo, lo + n)` lie in the code ranges. -/
theorem inRegion_of {base : Word} {cs : List (Nat × Nat)} {lo n : Nat} (h : rangesSub [(lo, lo + n)] cs = true) :
    InRegion (PcIn base cs) base lo n := fun j hj =>
  PcIn.mono h (PcIn.at List.mem_cons_self (by omega) (by omega))

theorem win_mono {sp0 y : Word} {N : Nat} (h : InStackWindow (sp0 - 36#32) N y) :
    InStackWindow sp0 (36 + N) y := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨36 + o, by omega, by rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, sub_sub_ofNat]⟩

section
variable {A Bk : Type} (cE : A → CalleeS) (bE : Bk → BlockS)

/-- The body's offset after `abi_enter` at `oE`. -/
def bodyAt (G : Geo) (oE : Nat) : Nat := oE + seqSize (abiEnter G.top)

/-- `abi_leave` after the body `P` at `oE`'s entry. -/
def leaveOf (G : Geo) (P : Prog A Bk) (oE : Nat) : List Piece :=
  abiLeave G.top (G.N - G.top) (bodyAt G oE + P.size cE bE)

/-- **The decided facts of an entry**: the frame's shape (word steps, a wipe of whole pairs, at
most 255 of them), the parities, the code ranges of the enter and the leave, and the wipe loop's
back branch. -/
def entryOk (G : Geo) (P : Prog A Bk) (oE : Nat) : Bool :=
  let ol := bodyAt G oE + P.size cE bE
  let ow := ol + 2 * (chunks (G.N - G.top) (G.N - G.top)).length + 10
  G.xv.isEmpty && G.top % 4 == 0 && G.N % 8 == 0 && decide (G.top < G.N) && decide (G.N < 2048) && oE % 2 == 0 &&
    ol % 2 == 0 && rangesSub [(oE, oE + seqSize (abiEnter G.top))] G.cs &&
    rangesSub [(ol, ol + piecesSize (leaveOf cE bE G P oE))] G.cs &&
    BitVec.ofNat 32 (ow + 4) + 4#32 + (brImm8 (ow + 4) ow ++ 0#1).signExtend 32 == BitVec.ofNat 32 ow

/-- **The trace of an entry** at `oE`: the enter, the body from `st0`, the leave. -/
def entryTr (G : Geo) (T : A → Word → (Nat → Word) → List Event) (c : Ctx) (sp0 : Word) (oE : Nat)
    (P : Prog A Bk) (st0 : St) : TrP :=
  Tr.cat (Tr.is (blockTr saveHi (c.base + BitVec.ofNat 32 oE) [13] [sp0]))
    (Tr.cat (Tr.is (spTr c.base false (oE + 12) (chunks G.top G.top)))
      (Tr.cat (Prog.tr cE bE G T c P (bodyAt G oE) st0 (Tr.is []) [] [])
        (leaveTr c.base sp0 G.top (G.N - G.top) (bodyAt G oE + P.size cE bE) (Tr.is []))))

end

/-! ## One trace -/

section uniq
open Tr
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {G : Geo}
variable {T : A → Word → (Nat → Word) → List Event} {c : Ctx}

/-- Closes `Uniq` goals built from `is`, `cat` and `cond` over assumptions. -/
local macro "uniq" : tactic =>
  `(tactic| repeat (first | assumption | exact uniq_is _ | apply uniq_cat | apply uniq_cond))

theorem loopTr_uniq {bt : TrP → TrP} (hb : ∀ Ψ, Uniq Ψ → Uniq (bt Ψ)) {D : List Event} {bc bb : Event}
    {Ψk : TrP} (hk : Uniq Ψk) : ∀ n, Uniq (loopTr bt D bc bb Ψk n)
  | 0 => uniq_is _
  | n + 1 => hb _ (by have := loopTr_uniq hb (D := D) (bc := bc) (bb := bb) hk n; uniq)

theorem getD_uniq : ∀ {Ψs : List TrP}, (∀ Ψ ∈ Ψs, Uniq Ψ) → ∀ l, Uniq (Ψs.getD l (is []))
  | [], _, _ => uniq_is _
  | _ :: _, h, 0 => h _ List.mem_cons_self
  | _ :: Ψs, h, l + 1 => getD_uniq (Ψs := Ψs) (fun Ψ hΨ => h Ψ (List.mem_cons_of_mem _ hΨ)) l

theorem whTr_uniq {tb : St → Option St} {bt : St → TrP → List TrP → TrP} {kt : St → TrP} {back : TrP → TrP}
    {Ψs : List TrP} (hb : ∀ s Ψ Ψs', Uniq Ψ → (∀ x ∈ Ψs', Uniq x) → Uniq (bt s Ψ Ψs'))
    (hk : ∀ s, Uniq (kt s)) (hback : ∀ Ψ, Uniq Ψ → Uniq (back Ψ)) (hs : ∀ x ∈ Ψs, Uniq x) :
    ∀ n st, Uniq (whTr tb bt kt back Ψs n st)
  | 0, _ => uniq_is _
  | n + 1, st => by
    simp only [whTr]
    split
    · exact hb _ _ _ (hback _ (whTr_uniq hb hk hback hs n _)) fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hk _
        · exact hs x hx
    · exact uniq_is _

/-- **A program's trace condition admits one trace.** -/
theorem Prog.tr_uniq : ∀ (P : Prog A Bk) (o : Nat) (st : St) {Ψ : TrP} {J : List Nat} {Ψs : List TrP}, Uniq Ψ →
    (∀ x ∈ Ψs, Uniq x) → Uniq (Prog.tr cE bE G T c P o st Ψ J Ψs)
  | .nil, _, _, _, _, _, h, _ => h
  | .op x k, o, st, _, J, _, h, hs => by
    have := Prog.tr_uniq k (o + x.size cE bE) ((x.ty cE bE G st).getD st) (J := J) h hs
    cases x with
    | ld r l => cases l <;> simp only [Prog.tr, Op.tr] <;> uniq
    | _ => simp only [Prog.tr, Op.tr] <;> uniq
  | .loop cnt n b k, o, st, _, _, _, h, hs => by
    simp only [Prog.tr]
    exact uniq_cat (uniq_is _) (loopTr_uniq (fun Ψ hΨ => Prog.tr_uniq b _ _ hΨ (fun _ h => absurd h List.not_mem_nil))
      (Prog.tr_uniq k _ _ h hs) n)
  | .sel w i p₀ p₁ k, o, st, _, _, _, h, hs => by
    simp only [Prog.tr]
    have hn : ∀ x ∈ ([] : List TrP), Uniq x := fun _ h => absurd h List.not_mem_nil
    exact uniq_cat (uniq_is _) (uniq_cat (uniq_is _) (uniq_cond
      (Prog.tr_uniq p₀ _ _ (uniq_cat (uniq_is _) (Prog.tr_uniq k _ _ h hs)) hn) (uniq_cat (uniq_is _)
        (Prog.tr_uniq p₁ _ _ (uniq_cat (uniq_is _) (Prog.tr_uniq k _ _ h hs)) hn))))
  | .xit g s cc sh l k, o, st, _, J, Ψs, h, hs => by
    have hk : ∀ st', Uniq (Prog.tr cE bE G T c k (o + xitSz g s + xbSz sh) st' _ J Ψs) :=
      fun st' => Prog.tr_uniq k _ st' h hs
    have := getD_uniq hs l
    simp only [Prog.tr]
    cases s <;> cases sh <;> simp only [xitT, Op.tr, ↓reduceIte, Bool.false_eq_true] <;>
      repeat (first | assumption | exact hk _ | exact uniq_is _ | apply uniq_cat | apply uniq_cond)
  | .hd b h k, o, st, _, J, Ψs, hΨ, hs => by
    simp only [Prog.tr]
    split
    · refine Prog.tr_uniq b _ _ ?_ fun x hx => ?_
      · split
        · exact Prog.tr_uniq k _ _ hΨ hs
        · exact uniq_cat (uniq_is _) (Prog.tr_uniq k _ _ hΨ hs)
      · rcases List.mem_cons.mp hx with rfl | hx
        · split
          · exact Prog.tr_uniq h _ _ (Prog.tr_uniq k _ _ hΨ hs) hs
          · exact uniq_is _
        · exact hs x hx
    · exact uniq_is _
  | .wh n b k, o, st, _, J, Ψs, h, hs => by
    simp only [Prog.tr]
    exact whTr_uniq (fun _ _ _ h1 h2 => Prog.tr_uniq b _ _ h1 h2) (fun _ => Prog.tr_uniq k _ _ h hs)
      (fun _ h1 => uniq_cat (uniq_is _) h1) hs n st

theorem leaveTr_uniq {base sp0 : Word} {fs w o : Nat} {Ψ : TrP} (h : Uniq Ψ) :
    Uniq (leaveTr base sp0 fs w o Ψ) := by
  simp only [leaveTr]
  refine uniq_cat (uniq_is _) (uniq_cat (uniq_is _) (uniq_rep (fun _ => ?_) ?_ _ _))
  · simp only [wipeTr]; uniq
  · uniq

/-- **An entry's trace condition admits one trace.** -/
theorem entryTr_uniq {sp0 : Word} {oE : Nat} {P : Prog A Bk} {st0 : St} :
    Uniq (entryTr cE bE G T c sp0 oE P st0) :=
  uniq_cat (uniq_is _) (uniq_cat (uniq_is _) (uniq_cat (Prog.tr_uniq P _ _ (uniq_is _)
    (fun _ h => absurd h List.not_mem_nil))
    (leaveTr_uniq (uniq_is _))))

end uniq

section
variable (Rs : Rels)
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS}
variable (ads : ∀ a, Ad Rs B BS (cE a)) (bds : ∀ b, Bd Rs (bE b))
variable {c : Ctx} {G : Geo} {Wc Rc : List Rgn}

/-- The decided facts of an entry whose body has `bsz` bytes. -/
def entryOkB (G : Geo) (bsz oE : Nat) : Bool :=
  let ol := bodyAt G oE + bsz
  let ow := ol + 2 * (chunks (G.N - G.top) (G.N - G.top)).length + 10
  G.xv.isEmpty && G.top % 4 == 0 && G.N % 8 == 0 && decide (G.top < G.N) && decide (G.N < 2048) && oE % 2 == 0 &&
    ol % 2 == 0 && rangesSub [(oE, oE + seqSize (abiEnter G.top))] G.cs &&
    rangesSub [(ol, ol + piecesSize (abiLeave G.top (G.N - G.top) ol))] G.cs &&
    BitVec.ofNat 32 (ow + 4) + 4#32 + (brImm8 (ow + 4) ow ++ 0#1).signExtend 32 == BitVec.ofNat 32 ow

/-- The trace of an entry at `oE` whose body of `bsz` bytes has the trace `Ψ`. -/
def entryTrB (G : Geo) (c : Ctx) (sp0 : Word) (oE bsz : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is (blockTr saveHi (c.base + BitVec.ofNat 32 oE) [13] [sp0]))
    (Tr.cat (Tr.is (spTr c.base false (oE + 12) (chunks G.top G.top)))
      (Tr.cat Ψ (leaveTr c.base sp0 G.top (G.N - G.top) (bodyAt G oE + bsz) (Tr.is []))))

/-- An entry's trace condition with a body admitting one trace admits one trace. -/
theorem entryTrB_uniq {sp0 : Word} {oE bsz : Nat} {Ψ : TrP} (h : Tr.Uniq Ψ) : Tr.Uniq (entryTrB G c sp0 oE bsz Ψ) :=
  Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat h (leaveTr_uniq (Tr.uniq_is _))))

/-- The saved words stay in place while the program state's regions keep out of them. -/
theorem saved_inv {s : State} {sp0 : Word} {st : St} {E : Loc → V} {m : Mem} (hsp : c.sp0 = sp0 - 36#32)
    (hroom : 36 + G.N ≤ sp0.toNat) (hsv : ∀ y, Region (sp0 - 36#32) 36 y → ∀ r ∈ st.X, ¬ Has (r.rgns G c) y)
    (hI : Inv Rs c G (enterMem s sp0) st E m) : ∀ y, Region (sp0 - 36#32) 36 y → m y = enterMem s sp0 y :=
  fun y hy => hI.2.1 y (fun hw => saved_not_win hroom hy (by
    simp only [Geo.win] at hw
    have := rgn_region hw (by omega); rwa [hsp, ad_sub36] at this)) (hsv y hy)

/-- **An entry with a given body**: from its entry state, an entry whose body of `bsz` bytes
runs from the program state `st0` to the leave with the trace `Ψ`, keeping the saved words, with
`R`, returns with `sp` and `r4`-`r11` restored, `r0` the body's, `r1`-`r3` and `r12` zero, the
window below the saved words zero and the saved words in place; elsewhere memory is the body's
final memory. -/
theorem entry_runB {bsz : Nat} {Ψ : TrP} {st0 : St} {oE : Nat} {s : State} {sp0 : Word} {R Q : State → Prop}
    (F : Caller c.base c.sp0 G.N Wc) (hok : entryOkB G bsz oE = true) (hen : seqAt B oE (abiEnter G.top) = true)
    (hsp : c.sp0 = sp0 - 36#32) (hroom : 36 + G.N ≤ sp0.toNat) (hs13 : s.regs 13 = sp0) (hpc : s.pc = c.base + BitVec.ofNat 32 oE)
    (hc : CodeAt s.mem c.base B) (hcs : ∀ i < B.length, ¬ Region (sp0 - 36#32) 36 (c.base + BitVec.ofNat 32 i))
    (hΓ : st0.Γ = []) (hρ0 : st0.ρ = []) (hσ : ∀ p ∈ st0.σ, (p.1.val < 4 ∧ s.regs p.1 = p.2.val c (G.fsp c)) ∨ p = (13, .sp 0))
    (hwW : Sub [G.win c] Wc) (hlr : (s.regs 14).getLsbD 0 = true)
    (hbody : ∀ t, At Rs B c G (enterMem s sp0) (bodyAt G oE) st0 (fun _ => .none) t →
      ReachFT c.base (PcIn c.base G.cs) (Has Rc) (Has Wc) (InStackWindow c.sp0 G.N) t
        (fun u => u.pc = c.base + BitVec.ofNat 32 (bodyAt G oE + bsz) ∧ u.regs 13 = G.fsp c ∧
          piecesAt B (bodyAt G oE + bsz) (abiLeave G.top (G.N - G.top) (bodyAt G oE + bsz)) = true ∧
          (∀ y, Region (sp0 - 36#32) 36 y → u.mem y = enterMem s sp0 y) ∧ R u) Ψ)
    (k : ∀ u1 u, R u1 →
      u.pc = s.regs 14 &&& ~~~1#32 → u.regs 13 = sp0 → u.regs 0 = u1.regs 0 →
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = s.regs r) →
      u.regs 1 = 0 → u.regs 2 = 0 → u.regs 3 = 0 → u.regs 12 = 0 →
      (∀ i < 9, read32 u.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) = s.regs Ed25519.savedRegs[i]!) →
      (∀ y, Region (sp0 - BitVec.ofNat 32 (36 + G.N)) G.N y → u.mem y = 0) →
      (∀ y, ¬ Region (sp0 - BitVec.ofNat 32 (36 + G.N)) (36 + G.N) y → u.mem y = u1.mem y) →
      Q u) :
    ReachFT c.base (PcIn c.base G.cs) (Has (savedR sp0 :: Rc)) (Has (savedR sp0 :: Wc))
      (InStackWindow sp0 (36 + G.N)) s Q (entryTrB G c sp0 oE bsz Ψ) := by
  simp only [entryOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxv, h4⟩, h8⟩, hlt⟩, h2048⟩, hoE⟩, hol⟩, hrE⟩, hrL⟩, ht⟩ := hok
  have hb : c.base.toNat % 2 = 0 := by have := F.b4; omega
  have hsp4 : sp0.toNat % 4 = 0 := by
    have := F.sp4; rw [hsp, BitVec.toNat_sub] at this; simp at this; omega
  have hfw : G.top + (G.N - G.top) = G.N := by omega
  have hwin : ∀ y, Region (sp0 - BitVec.ofNat 32 (36 + G.N)) G.N y → Has Wc y := fun y hy =>
    Sub.has hwW ⟨G.win c, List.mem_singleton_self _, by
      simp only [Geo.win]; rw [hsp, ad_sub36]; exact Rgn.of_region hy⟩
  refine enter_run hb hpc hoE hen (inRegion_of hrE) hs13 hsp4 h4 (by omega)
    (fun j hj => Has.cons ⟨j, hj, rfl⟩ _) fun t hpt ht13 htr htm => ?_
  have hat : At Rs B c G (enterMem s sp0) (bodyAt G oE) st0 (fun _ => .none) t := by
    refine ⟨hpt, by rw [ht13, Geo.fsp, hsp, ad_sub36], ?_, fun p hp => ?_, ⟨fun p hp => ?_,
      fun y _ _ => by rw [htm]; rfl, fun p hp => by simp [List.isEmpty_iff.mp hxv] at hp⟩,
      fun r h => by rw [hρ0] at h; cases h⟩
    · intro i hi; rw [htm, show storeWords _ _ _ = enterMem s sp0 from rfl, enterMem_other _ _ (hcs i hi)]
      exact hc i hi
    · rcases hσ p hp with ⟨h4', hv⟩ | rfl
      · exact ⟨by omega, by rw [htr p.1 (Or.inl h4'), hv]⟩
      · refine ⟨by decide, ?_⟩
        simp only [SV.val, ht13, Geo.fsp, hsp, ad_sub36]; simp
    · simp [hΓ] at hp
  refine ReachT.seq (ReachT.mono (hbody t hat)
      (fun x e ⟨a1, a2, a3, a4⟩ => ⟨a1, fun y hy => Has.tail (a2 y hy), fun y hy => Has.tail (a3 y hy),
        win_mono (hsp ▸ a4)⟩) (fun _ h => h) (fun _ h => h)) fun u1 hu1 => ?_
  obtain ⟨hp1, h131, hpl, hsv1, hR1⟩ := hu1
  have hs1 := saved_of (by omega) hsv1
  refine leave_run hb hp1 hol hpl ht (inRegion_of hrL)
    (by rw [h131, Geo.fsp, hsp, ad_sub36]) hsp4 (by omega) h4 (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun j hj => by
      rw [show 36 + G.top + (G.N - G.top) = 36 + G.N by omega]
      exact Has.tail (hwin _ (region_add _ (by omega) (by omega))))
    (fun j hj => Has.cons ⟨j, hj, rfl⟩ _)
    (by rw [← ad_lr', hs1 8 (by omega)]; exact hlr) fun u hpu hu13 hr0 hr1 hr2 hr3 hr12 _ hcal hum => ?_
  have hz := zeros_at (2 * ((G.top + (G.N - G.top)) / 8)) u1.mem
    (sp0 - BitVec.ofNat 32 (36 + G.top + (G.N - G.top)))
  rw [show 36 + G.top + (G.N - G.top) = 36 + G.N by omega, show 4 * (2 * ((G.top + (G.N - G.top)) / 8)) = G.N by
    omega] at hz
  rw [show 36 + G.top + (G.N - G.top) = 36 + G.N by omega] at hum
  have hzs : ∀ y, u.mem y = if Region (sp0 - BitVec.ofNat 32 (36 + G.N)) G.N y then 0 else u1.mem y := by
    intro y; rw [hum]; exact hz y (by rw [BitVec.toNat_sub]; simp; omega)
  have hsu : ∀ y, Region (sp0 - 36#32) 36 y → u.mem y = enterMem s sp0 y := fun y hy => by
    rw [hzs]; simp only [saved_not_win hroom hy, ↓reduceIte]; exact hsv1 y hy
  refine ReachT.done (k u1 u hR1 ?_ hu13 hr0 (callee_of fun i hi => ?_) hr1 hr2 hr3 hr12
    (saved_of (by omega) hsu) (fun y hy => by rw [hzs]; simp only [hy, ↓reduceIte]) fun y hy => by
      have hn : ¬ Region (sp0 - BitVec.ofNat 32 (36 + G.N)) G.N y := fun h => hy (win_in_all h)
      rw [hzs]; simp only [hn, ↓reduceIte])
  · rw [hpu, ← ad_lr', hs1 8 (by omega)]; rfl
  · rw [hcal i hi, hs1 i (by omega)]

/-- **An entry**: from its entry state, an entry whose body is the checked program `P` returns
with `sp` and `r4`-`r11` restored, `r1`-`r3` and `r12` zero, the window below the saved words zero
and the saved words in place; elsewhere memory is the body's final memory `mb`, which holds the
body's values. Its footprints are the body's with the 36 saved bytes. -/
theorem entry_run (g : GeoOk c G Wc Rc) (F : Caller c.base c.sp0 G.N Wc) (hcR : Sub [codeR c.base] Rc)
    (P : Prog A Bk) {st0 st' : St} {oE : Nat} {s : State} {sp0 : Word} {Q : State → Prop}
    (hok : entryOk cE bE G P oE = true) (hty : P.ty cE bE G st0 = some st') (hex0 : st0.ex = none)
    (hexf : st'.ex = none)
    (hbok : P.bok cE bE G [] (bodyAt G oE) = true) (hen : seqAt B oE (abiEnter G.top) = true)
    (hpb : piecesAt B (bodyAt G oE) (P.emit cE bE [] (bodyAt G oE) ++ leaveOf cE bE G P oE) = true)
    (hsp : c.sp0 = sp0 - 36#32) (hroom : 36 + G.N ≤ sp0.toNat) (hs13 : s.regs 13 = sp0) (hpc : s.pc = c.base + BitVec.ofNat 32 oE)
    (hc : CodeAt s.mem c.base B) (hcs : ∀ i < B.length, ¬ Region (sp0 - 36#32) 36 (c.base + BitVec.ofNat 32 i))
    (hΓ : st0.Γ = []) (hρ0 : st0.ρ = []) (hσ : ∀ p ∈ st0.σ, (p.1.val < 4 ∧ s.regs p.1 = p.2.val c (G.fsp c)) ∨ p = (13, .sp 0))
    (hsv : ∀ y, Region (sp0 - 36#32) 36 y → ∀ r ∈ st'.X, ¬ Has (r.rgns G c) y)
    (hlr : (s.regs 14).getLsbD 0 = true)
    (k : ∀ mb u, Inv Rs c G (enterMem s sp0) st'
        (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c (enterMem s sp0) P st0
          fun _ => .none) mb →
      u.pc = s.regs 14 &&& ~~~1#32 → u.regs 13 = sp0 →
      (∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = s.regs r) →
      u.regs 1 = 0 → u.regs 2 = 0 → u.regs 3 = 0 → u.regs 12 = 0 →
      (∀ i < 9, read32 u.mem (sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) = s.regs Ed25519.savedRegs[i]!) →
      (∀ y, Region (sp0 - BitVec.ofNat 32 (36 + G.N)) G.N y → u.mem y = 0) →
      (∀ y, ¬ Region (sp0 - BitVec.ofNat 32 (36 + G.N)) (36 + G.N) y → u.mem y = mb y) →
      Q u) :
    ReachFT c.base (PcIn c.base G.cs) (Has (savedR sp0 :: Rc)) (Has (savedR sp0 :: Wc))
      (InStackWindow sp0 (36 + G.N)) s Q
      (entryTr cE bE G (fun a => (ads a).T) c sp0 oE P st0) :=
  entry_runB Rs (R := fun u => Inv Rs c G (enterMem s sp0) st'
      (Prog.ev cE bE G (fun a => (ads a).sem) (fun b => (bds b).sem) c (enterMem s sp0) P st0 fun _ => .none) u.mem)
    F hok hen hsp hroom hs13 hpc hc hcs hΓ hρ0 hσ g.wW hlr
    (fun t hat => prog_run Rs ads bds (enterMem s sp0) g F hcR P (J := []) (Ψs := []) hty hex0 hbok hpb hat
      (fun _ u hu hr => ReachT.done ⟨hu.1, hu.2.1, hr, saved_inv Rs hsp hroom hsv hu.2.2.2.2.1, hu.2.2.2.2.1⟩)
      (fun l hl => by rw [hexf] at hl; cases hl))
    fun u1 u hI hpu hu13 _ hcal hr1 hr2 hr3 hr12 hsw hz hum => k u1.mem u hI hpu hu13 hcal hr1 hr2 hr3 hr12 hsw hz hum

end

end M0Crypto.Release.Ed25519CallProg
