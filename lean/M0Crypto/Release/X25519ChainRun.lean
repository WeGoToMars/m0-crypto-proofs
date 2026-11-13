import M0Crypto.Release.X25519ChainStep

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
The inversion chain segment of `m0c_x25519`.

`chain_run` folds `stepChain_w` over a list of steps whose destination is not the frame slot
`Z2` (offsets threaded as in `chainAt`): the values before and after form an
`X25519Chain.Run`, and only the chain slots and `LV_T` change. `chain_w` runs
`chainAt oChain invChain` from `oChain` to `oFinish`: all steps but the last by `chain_run`,
the last (`dst`, which shares `Z2` with the input `z`) by `stepChain_w` alone, so the aliasing
is handled by stating the last value map with `upd`. `invChain_correct` then gives
`Z2 ≡ Z2_old ^ (2 ^ 255 - 21)`.

The segment's bytes come from `entry_at` by `seqAt_append`; its size bound from `entry_size`.
-/

namespace M0Crypto.Release.X25519ChainRun
open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Congr (ModP)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519ChainLoop
open M0Crypto.Release.X25519ChainStep
open M0Crypto.Release.X25519Chain (CSlot CStep Run invChain upd invChain_correct)

/-! ## Lists -/

theorem chainAt_append : ∀ (o : Nat) (l₁ l₂ : List CStep),
    chainAt o (l₁ ++ l₂) = chainAt o l₁ ++ chainAt (o + seqSize (chainAt o l₁)) l₂
  | o, [], l₂ => by simp [chainAt, seqSize]
  | o, st :: l₁, l₂ => by
    simp only [List.cons_append, chainAt, chainAt_append _ l₁ l₂, List.append_assoc, seqSize_append,
      Nat.add_assoc]

theorem Run.append : ∀ {l₁ l₂ : List CStep} {f g h : CSlot → Int},
    Run l₁ f g → Run l₂ g h → Run (l₁ ++ l₂) f h
  | [], _, _, _, _, .nil _, h2 => h2
  | _ :: _, _, _, _, _, .cons hs hr, h2 => .cons hs (Run.append hr h2)

/-- Chain slots are distinct frame slots, except `z` and `dst`. -/
theorem cslot_ne : ∀ x d : CSlot, x ≠ d → cslot d ≠ sZ2 → cslot x ≠ cslot d := by
  intro x d; cases x <;> cases d <;> decide

/-! ## Frame regions -/

section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

theorem slot_disj {a b : Nat} (ha : SlotOk a) (hb : SlotOk b) (hab : a ≠ b) {y : Word}
    (h : Region (slotAt c a) 32 y) : ¬ Region (slotAt c b) 32 y := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  simp only [LFRAME] at ha2 hb2
  rw [slot_iff hv (by simp only [SAVED, LFRAME]; omega)] at h
  rw [slot_iff hv (by simp only [SAVED, LFRAME]; omega)]
  omega

theorem slot_frame {a : Nat} (ha : SlotOk a) {y : Word} (h : Region (slotAt c a) 32 y) :
    Region (E c) LFRAME y ∧ ¬ Region (slotAt c lvT) 4 y := by
  obtain ⟨ha1, ha2⟩ := ha
  simp only [LFRAME] at ha2
  rw [slot_iff hv (by simp only [SAVED, LFRAME]; omega)] at h
  refine ⟨?_, ?_⟩
  · have := (slot_iff hv (o := 0) (n := LFRAME) (by decide) (y := y)).mpr (by simp only [LFRAME]; omega)
    rwa [show slotAt c 0 = E c by simp [slotAt]] at this
  · rw [slot_iff hv (by decide)]; simp only [lvT]; omega

/-- A byte outside the four temporaries and `Z2` is outside every chain slot. -/
theorem chain_slots {y : Word} (hA : ¬ Region (slotAt c sA) 128 y) (hZ : ¬ Region (slotAt c sZ2) 32 y) :
    ∀ x, ¬ Region (slotAt c (cslot x)) 32 y := by
  have key : ∀ i, i < 4 → ¬ Region (slotAt c (sA + 32 * i)) 32 y := fun i hi h => hA (by
    rw [slot_iff hv (by simp only [sA, SAVED, LFRAME]; omega)] at h
    rw [slot_iff hv (by decide)]; omega)
  intro x
  cases x
  · exact key 0 (by decide)
  · exact key 1 (by decide)
  · exact key 2 (by decide)
  · exact key 3 (by decide)
  · exact hZ
  · exact hZ

/-- Frame bytes kept by a run of chain steps: those outside every chain slot and `LV_T`. -/
def KeepC (c : X25519.Ctx) (s t : State) : Prop :=
  ∀ y, Region (E c) LFRAME y → (∀ x, ¬ Region (slotAt c (cslot x)) 32 y) →
    ¬ Region (slotAt c lvT) 4 y → t.mem y = s.mem y

/-- A step whose destination is not `Z2` is a `CStep.Rel` of the slot values. -/
theorem rel_of {st : CStep} {s u : State} (hdz : cslot st.dst ≠ sZ2)
    (uv : ModP (cv c u.mem st.dst) (st.rhs (cv c s.mem))) (uk : KeepDT c (cslot st.dst) s u) :
    CStep.Rel (cv c s.mem) (cv c u.mem) st := by
  have hk : ∀ x, x ≠ st.dst → cv c u.mem x = cv c s.mem x := fun x hx => by
    unfold cv
    congr 1
    refine feVal_congr fun y hy => ?_
    obtain ⟨h1, h2⟩ := slot_frame hv (cslot_ok x) hy
    exact uk y h1 (slot_disj hv (cslot_ok x) (cslot_ok _) (cslot_ne x _ hx hdz) hy) h2
  cases st with
  | sqr d a n => exact ⟨uv, hk⟩
  | mul d a b => exact ⟨uv, hk⟩

end

/-- Any step relates the values before it to those with only its destination replaced. -/
theorem rel_upd {f : CSlot → Int} {v : Int} {st : CStep} (h : ModP v (st.rhs f)) :
    CStep.Rel f (upd f st.dst v) st := by
  cases st with
  | sqr d a n =>
    refine ⟨by simpa [upd, CStep.dst, CStep.rhs] using h, fun x hx => ?_⟩
    simp [upd, CStep.dst, hx]
  | mul d a b =>
    refine ⟨by simpa [upd, CStep.dst, CStep.rhs] using h, fun x hx => ?_⟩
    simp [upd, CStep.dst, hx]

/-! ## The fold -/

section
variable {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
  {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
  {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
include hv hcode hWr hPO

/-- Chain steps not writing `Z2`, from `o`. -/
theorem chain_run {Q : State → Prop} : ∀ (sts : List CStep) (o : Nat) (s : State),
    sts.all (fun st => st.ok && cslot st.dst != sZ2) = true →
    seqAt B o (chainAt o sts) = true → o % 2 = 0 → lo ≤ o →
    o + seqSize (chainAt o sts) ≤ hi →
    s.pc = c.base + BitVec.ofNat 32 o → Body c m1 s →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (chainAt o sts)) → Body c m1 t →
      Run sts (cv c s.mem) (cv c t.mem) → KeepC c s t →
      ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q
  | [], o, s, _, _, _, _, _, hpc, hs, k =>
    k s (by simpa [chainAt, seqSize] using hpc) hs (.nil _) fun _ _ _ _ => rfl
  | st :: sts, o, s, hall, hseq, ho, hlo, hend, hpc, hs, k => by
    simp only [chainAt] at hseq hend k
    rw [seqAt_append, Bool.and_eq_true] at hseq
    rw [seqSize_append] at hend
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hall
    obtain ⟨⟨hok, hdz⟩, hall⟩ := hall
    have he := seqSize_even (stepChainAt o st)
    refine stepChain_w hv hcode hWr hPO st hok hseq.1 ho hlo (by omega) hpc hs ?_
    intro u upc ub uv uk
    refine chain_run sts _ u (by simpa using hall) hseq.2 (by omega) (by omega) (by omega) upc ub ?_
    intro t tpc tb tr tk
    refine k t (by rw [tpc, seqSize_append, Nat.add_assoc]) tb (.cons (rel_of hv hdz uv uk) tr) ?_
    intro y h1 h2 h3
    rw [tk y h1 h2 h3]; exact uk y h1 (h2 _) h3

end

/-! ## The segment in the entry -/

theorem chain_at : seqAt B oChain (chainAt oChain invChain) = true := by
  have h := entry_at
  simp only [entryList, seqAt_append, Bool.and_eq_true] at h
  have e : Artifacts.Release.x25519 + seqSize (prologue ++ ladderAt oLadder ++ swapAt oSwap ++ dblAt oDbl) =
      oChain := by
    have e1 : oLadder = Artifacts.Release.x25519 + seqSize prologue := rfl
    have e2 : oSwap = oLadder + seqSize (ladderAt oLadder) := rfl
    have e3 : oDbl = oSwap + seqSize (swapAt oSwap) := rfl
    have e4 : oChain = oDbl + seqSize (dblAt oDbl) := rfl
    simp only [seqSize_append]
    omega
  have h5 := h.1.1.1.1.2
  rwa [e] at h5

theorem chain_bounds : oChain % 2 = 0 ∧ Artifacts.Release.x25519 ≤ oChain ∧
    oChain + seqSize (chainAt oChain invChain) ≤ Artifacts.Release.size := by
  have h := entry_size
  simp only [entryList, seqSize_append] at h
  have e1 : oLadder = Artifacts.Release.x25519 + seqSize prologue := rfl
  have e2 : oSwap = oLadder + seqSize (ladderAt oLadder) := rfl
  have e3 : oDbl = oSwap + seqSize (swapAt oSwap) := rfl
  have e4 : oChain = oDbl + seqSize (dblAt oDbl) := rfl
  have h0 : Artifacts.Release.x25519 % 2 = 0 := by decide
  have := seqSize_even prologue
  have := seqSize_even (ladderAt oLadder)
  have := seqSize_even (swapAt oSwap)
  have := seqSize_even (dblAt oDbl)
  omega

/-! ## Main theorem -/

/-- All steps but the last. -/
def initSteps : List CStep := invChain.dropLast

/-- The last step, the only one writing `dst`. -/
def lastStep : CStep := invChain.getLast (by decide)

theorem invChain_split : invChain = initSteps ++ [lastStep] := by decide

theorem initSteps_ok : initSteps.all (fun st => st.ok && cslot st.dst != sZ2) = true := by decide

theorem lastStep_ok : lastStep.ok = true ∧ lastStep.dst = .dst := by decide

/-- The inversion chain: from `oChain` to `oFinish`, slot `Z2` is raised to the power
`2 ^ 255 - 21 = p - 2` modulo p; of the frame only the temporaries `A..D` (128 bytes from
`sA`), `Z2` and `LV_T` change. -/
theorem chain_w {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
    {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
    (hL0 : lo ≤ oLadder) (hH0 : oStore ≤ hi)
    {s : State} {Q : State → Prop}
    (hpc : s.pc = c.base + BitVec.ofNat 32 oChain) (hs : Body c m1 s)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 oFinish → Body c m1 t →
      ModP (feVal t.mem (slotAt c sZ2)) ((feVal s.mem (slotAt c sZ2) : Int) ^ (2 ^ 255 - 21)) →
      (∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sA) 128 y → ¬ Region (slotAt c sZ2) 32 y →
        ¬ Region (slotAt c lvT) 4 y → t.mem y = s.mem y) →
      ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hL : lo ≤ oChain := Nat.le_trans hL0 (by decide +kernel)
  have hH : oFinish ≤ hi := Nat.le_trans (by decide +kernel) hH0
  have hsplit := invChain_split
  have hinit := initSteps_ok
  obtain ⟨hokl, hlast⟩ := lastStep_ok
  generalize initSteps = init at hsplit hinit
  generalize lastStep = last at hsplit hlast hokl
  obtain ⟨ho, hlo, hend⟩ := chain_bounds
  have hseq := chain_at
  have hfin : oFinish = oChain + seqSize (chainAt oChain invChain) := rfl
  rw [hsplit, chainAt_append, seqAt_append, Bool.and_eq_true] at hseq
  rw [hsplit, chainAt_append, seqSize_append] at hend hfin
  simp only [chainAt, List.append_nil] at hseq hend hfin
  have he := seqSize_even (chainAt oChain init)
  refine chain_run hv hcode hWr hPO init oChain s hinit hseq.1 ho hL (by omega) hpc hs ?_
  intro u upc ub ur uk
  refine stepChain_w hv hcode hWr hPO last hokl hseq.2 (by omega) (by omega) (by omega) upc ub ?_
  intro t tpc tb tv tk
  refine k t (by rw [tpc, hfin, Nat.add_assoc]) tb ?_ ?_
  · have hr : Run invChain (cv c s.mem) (upd (cv c u.mem) last.dst (cv c t.mem last.dst)) := by
      rw [hsplit]; exact Run.append ur (.cons (rel_upd tv) (.nil _))
    have := invChain_correct (cv c s.mem .z) _ _ (ModP.refl _) hr
    simpa [upd, hlast, cv, cslot] using this
  · intro y h1 hA hZ h3
    have hx := chain_slots hv hA hZ
    rw [tk y h1 (hx _) h3]; exact uk y h1 hx h3

end M0Crypto.Release.X25519ChainRun
