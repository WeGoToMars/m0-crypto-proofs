import M0Crypto.Release.Ed25519Sha512Sched
import M0Crypto.Release.Ed25519PcFree
import M0Crypto.Release.Ed25519Lookup
import M0Crypto.Release.StackEffectGP

set_option linter.unusedSimpArgs false

/-!
# One group pass of `m0c_sha512_block`

The pieces of the code at their offsets (`Lay`, from `blockAt`), the frame of a pass (`Inv`: the
slots, the variables and the buffer), and the fragments of the group loop's body, each a
`Tr.HasK` whose trace depends on public values alone:

* `sched_frag`: the sixteen passes of macro `schedule` (`sched_run`), its footprint decided at
  the masked addresses (`sAt`);
* `skip_frag`: from `oSkip`, the half of the buffer and the `K` pointer (`gSel`), the eight
  rounds cut by the literal pool (`group_run` through `execAll_setPc`), and the counter (`gTail`);
* `pass_frag`: the branches on the public counter that choose whether the schedule runs.
-/

namespace M0Crypto.Release.Ed25519Sha512Pass

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Exec
open M0Crypto.Release.Ed25519Sha512Round
open M0Crypto.Release.Ed25519Sha512Group
open M0Crypto.Release.Ed25519Sha512Sched
open M0Crypto.Release.Ed25519Sha512Rounds (schedRun schedStep codeGroups codeGroup)
open M0Crypto.Release.StackEffect (Ef GP SIR catI sir_blkE sir_blk sir_quietC winChk inRD_win blkChk spRg inR_sp)
open M0Crypto.Release.TraceSpec (BelowEntry)

/-- The offset of `m0c_sha512_block`. -/
abbrev O : Nat := M0Crypto.Artifacts.Ed25519Compact.sha512_block

/-! ## The pieces at their offsets -/

/-- The pieces of `blockAt` that the proofs run, at their offsets. -/
structure Lay (B : List (BitVec 8)) : Prop where
  pre : seqAt B O pre = true
  wl : seqAt B (oWL O) wload = true
  wlb : instrAt B (oWL O + seqSize wload) = some (.bcond 1 (brImm8 (oWL O + seqSize wload) (oWL O)))
  vc : seqAt B (oCopy O) vcopy = true
  lit : seqAt B (oLit O) [.ldrLit 7 (Ed25519Sha512Code.litImm O pool)] = true
  ki : seqAt B (oLit O + 2) kinit = true
  gh : seqAt B (oG O) gHead = true
  ghb : instrAt B (oG O + seqSize gHead) = some (.bcond 3 (brImm8 (oG O + seqSize gHead) (oSkip O)))
  go : seqAt B (oOdd O) gOdd = true
  gob : instrAt B (oOdd O + seqSize gOdd) = some (.bcond 2 (brImm8 (oOdd O + seqSize gOdd) (oSkip O)))
  sp : seqAt B (oOdd O + seqSize gOdd + brSize) sPre = true
  sb : seqAt B (oS O) schedBody = true
  sbb : instrAt B (oS O + seqSize schedBody) = some (.bcond 1 (brImm8 (oS O + seqSize schedBody) (oS O)))
  gs : seqAt B (oSkip O) gSel = true
  tk : seqAt B (oR O) (groupI.take (kPool O pool)) = true
  pb : instrAt B (oR O + seqSize (groupI.take (kPool O pool))) =
    some (.b (brImm11 (oR O + seqSize (groupI.take (kPool O pool))) (oR2 pool)))
  dr : seqAt B (oR2 pool) (groupI.drop (kPool O pool)) = true
  gt : seqAt B (oT O pool) gTail = true
  gtb : instrAt B (oT O pool + seqSize gTail) =
    some (.bcond 0 (brImm8 (oT O pool + seqSize gTail) (oEnd O pool)))
  gtj : instrAt B (oT O pool + seqSize gTail + brSize) =
    some (.b (brImm11 (oT O pool + seqSize gTail + brSize) (oG O)))
  ha : seqAt B (oEnd O pool) hAdd = true
  po : seqAt B (oPost O pool) post = true

theorem lay_of {B : List (BitVec 8)} (h : blockAt O pool B size = true) : Lay B := by
  simp only [blockAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hA, hB⟩, -⟩, -⟩ := h
  simp only [piecesA, piecesAt, Piece.instrs, Piece.size, Bool.and_eq_true] at hA
  simp only [piecesB, piecesAt, Piece.instrs, Piece.size, Bool.and_eq_true] at hB
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, -⟩ := hA
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hB
  replace a3 := instrAt_of_seqAt a3
  replace a8 := instrAt_of_seqAt a8; replace a10 := instrAt_of_seqAt a10
  replace a13 := instrAt_of_seqAt a13; replace a16 := instrAt_of_seqAt a16
  replace b3 := instrAt_of_seqAt b3; replace b4 := instrAt_of_seqAt b4
  have e : ∀ x, seqSize [Instr.ldrLit 7 x] = 2 := fun _ => rfl
  simp only [e] at a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  constructor <;> (try simp only [oWL, oCopy, oLit, oG, oOdd, oS, oSkip, oR, oT, oEnd, oPost, Nat.two_mul,
    ← Nat.add_assoc] at *) <;> with_reducible assumption

/-! ## The frame of a pass -/

open M0Crypto.Release.Ed25519Lookup (kS)

/-- The code of `m0c_sha512_block`. -/
def cs : List (Nat × Nat) := [(O, O + size)]

/-- Bytes of stack below the entry `sp`: the saved `lr` and the frame. -/
def D : Nat := 4 + BFRAME

/-- The frame's base for the entry `sp0`. -/
abbrev fsp (sp0 : Word) : Word := sp0 - BitVec.ofNat 32 D

theorem vp_pair (m : Mem) (sp : Word) (i : Nat) : vp m sp i = pairAt m (sp + BitVec.ofNat 32 (VOFF + 8 * i)) := by
  have e : ∀ x y : Nat, x = y → sp + BitVec.ofNat 32 x = sp + BitVec.ofNat 32 y := fun _ _ h => by rw [h]
  simp only [vp, pairAt, slot, BitVec.add_assoc, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl,
    ← BitVec.ofNat_add]
  rw [e (4 * vw i true) (VOFF + 8 * i + 4) (by simp only [vw, VOFF, ↓reduceIte]; omega),
    e (4 * vw i false) (VOFF + 8 * i) (by simp only [vw, VOFF, Bool.false_eq_true, ↓reduceIte]; omega)]

theorem wAt_pair (m : Mem) (b : Word) (j : Nat) : wAt m b j = pairAt m (b + BitVec.ofNat 32 (8 * j)) := by
  have e : ∀ x y : Nat, x = y → b + BitVec.ofNat 32 x = b + BitVec.ofNat 32 y := fun _ _ h => by rw [h]
  simp only [wAt, pairAt, BitVec.add_assoc, ← BitVec.ofNat_add, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl]
  rw [e ((2 * j + 1) * 4) (8 * j + 4) (by omega), e (2 * j * 4) (8 * j) (by omega)]

/-- A frame fact keeps a pair outside its footprint (a reader for `keep_simp`). -/
theorem MemEq.pairAt {f : List Rgn} {m m' : Mem} (h : MemEq f m m') {a : Word} (hs : Sep [⟨a, 8⟩] f) :
    pairAt m' a = pairAt m a := by
  have h4 : ∀ k < 4, ∀ y, y = a + BitVec.ofNat 32 k → ¬ Has f y := fun k hk y hy hf =>
    Sep.not_has hs ⟨⟨a, 8⟩, List.mem_singleton.mpr rfl, ⟨k, show k < 8 by omega, hy⟩⟩ hf
  have h8 : ∀ k < 4, ∀ y, y = a + 4#32 + BitVec.ofNat 32 k → ¬ Has f y := fun k hk y hy hf =>
    Sep.not_has hs ⟨⟨a, 8⟩, List.mem_singleton.mpr rfl, ⟨4 + k, show 4 + k < 8 by omega, by
      rw [hy, BitVec.add_assoc, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]⟩⟩ hf
  simp only [Ed25519Sha512Exec.pairAt]
  rw [Frame.read32_congr fun k hk => h _ (h4 k hk _ rfl), Frame.read32_congr fun k hk => h _ (h8 k hk _ rfl)]


/-- The frame's constants as numerals, for `fp_tac`. -/
macro "nrm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [fsp, D, VB, VOFF, WOFF, HP, GRP, KP, BFRAME, GROUPS, HALF, HALF_SHIFT, Nat.add_zero, Nat.zero_add, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append] $[$loc]?)

/-- The frame of a pass over group `g`: memory outside the frame as `m1`, the saved `H` pointer
`hp`, the counter, the `K` pointer, the variables `V` and the buffer `W`. -/
def Inv (sp kb hp : Word) (m1 : Mem) (g : Nat) (V W : Nat → BitVec 64) (m : Mem) : Prop :=
  MemEq [⟨sp, BFRAME⟩] m1 m ∧ read32 m (sp + BitVec.ofNat 32 HP) = hp ∧
  read32 m (sp + BitVec.ofNat 32 GRP) = BitVec.ofNat 32 g ∧
  read32 m (sp + BitVec.ofNat 32 KP) = kb + BitVec.ofNat 32 (8 * 8 * g) ∧
  (∀ i < 8, pairAt m (sp + BitVec.ofNat 32 (VOFF + 8 * i)) = V i) ∧
  ∀ i < 16, pairAt m (sp + BitVec.ofNat 32 (WOFF + 8 * i)) = W i

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- What a pass needs of its caller: the layout, the frame and the `K` table in the footprints,
the `K` table apart from the frame, and its words. -/
structure Env (base sp0 kb : Word) (Rc Wc : List Rgn) : Prop where
  F : Caller base sp0 D Wc
  L : Lay B
  bs : O + size ≤ BS
  wc : Sub [⟨fsp sp0, BFRAME⟩] Wc
  rc : Sub [⟨fsp sp0, BFRAME⟩, ⟨kb, 8 * 80⟩] Rc
  kn : kb.toNat + 8 * 80 ≤ 2 ^ 32
  k4 : kb.toNat % 4 = 0
  ksep : Frame.Disj kb (8 * 80) (fsp sp0) BFRAME
  ktab : ∀ m, CodeAt m base B → ∀ i < 80,
    pairAt m (kb + BitVec.ofNat 32 (8 * i)) = M0Crypto.Spec.Sha512.K[i]!

theorem SGlueSides.mono {t : State} {Rc Wc Rc' Wc' : List Rgn} {al wg rg : List (SExpr × Nat)}
    (h : SGlueSides t Rc' Wc' al wg rg) (hR : Sub Rc' Rc) (hW : Sub Wc' Wc) : SGlueSides t Rc Wc al wg rg :=
  ⟨h.1, sub_trans h.2.1 hW, sub_trans h.2.2 hR⟩

/-- **A fragment's byte effect**: once the frame and the `K` table are written below the entry
`e0`, the fragment's trace keeps `SIR` at the frame. -/
def FragE (sp0 kb : Word) (Θ : TrP → TrP) : Prop :=
  ∀ (e0 : Word) (n : Nat) (R : Word → Prop) (Ψ : TrP) (J : Ef → Prop),
    (∀ y, (Region (fsp sp0) BFRAME y ∨ Region kb (8 * 80) y) → BelowEntry e0 n y → R y) →
    GP e0 n (SIR e0 (fsp sp0) R) Ψ J → GP e0 n (SIR e0 (fsp sp0) R) (Θ Ψ) J

/-! ## Macro `schedule` -/

/-- The taps of `W[j] + σ0(W[j+1]) + W[j+9] + σ1(W[j+14])`, in the order the code loads them. -/
def taps : List Nat := [1, 0, 9, 14]

/-- `(r7 + 8a) & MASK` as the executor forms it. -/
def ixr (a : Nat) : SExpr :=
  if a = 0 then .and (kS MASK) (.reg0 7) else .and (.awc (.reg0 7) (kS (8 * a)) (.const false)) (kS MASK)

/-- The addresses of word `j + a` of the buffer at `r6`, and of its high half. -/
def loA (a : Nat) : SExpr := .add (.reg0 6) (ixr a)
def hiA (a : Nat) : SExpr := .add (.reg0 6) (.add (ixr a) (kS 4))
def sAt : List SExpr := taps.flatMap fun a => [loA a, hiA a]
def w4 (l : List SExpr) : List (SExpr × Nat) := l.map (·, 4)

/-- The footprint and the trace of `schedBody` at the masked addresses. -/
theorem sched_ok : sglueOk cs schedBody (oS O) D D (w4 sAt) (w4 [loA 0, hiA 0]) (w4 sAt) = true ∧
    schedBody.all Instr.falls = true ∧ traceOkE schedBody sAt = true := by decide +kernel

theorem sched_blk : blkChk (w4 sAt) [] (w4 sAt) schedBody = true ∧
    winChk sAt (fun _ => true) (WOFF + 124) BFRAME (w4 sAt) = true := by decide +kernel

theorem ixr_val (t : State) {j : Nat} (a : Nat) (hj : j < 16) (h7 : t.regs 7 = BitVec.ofNat 32 (8 * j))
    (ha : a < 16 := by decide) : (ixr a).denote t = BitVec.ofNat 32 (8 * ((j + a) % 16)) := by
  have hm : BitVec.ofNat 32 MASK = 0x78#32 := rfl
  unfold ixr; split
  · subst a; simp only [SExpr.denote, kS, h7, hm, BitVec.and_comm (0x78#32)]
    have := Ed25519Sha512Rounds.sched_index j 0 hj (by omega); simpa using this
  · simp only [SExpr.denote, SBool.denote, kS, add_flags, h7, hm]
    exact Ed25519Sha512Rounds.sched_index j a hj ha

/-- The values of `sAt` for `r6 = w`, `r7 = 8 j`. -/
def sVals (w : Word) (j : Nat) : List Word := taps.flatMap fun a =>
  [w + BitVec.ofNat 32 (8 * ((j + a) % 16)), w + (BitVec.ofNat 32 (8 * ((j + a) % 16)) + BitVec.ofNat 32 4)]

theorem sVals_win (sp : Word) (j : Nat) : ∀ (i : Nat) (v : Word), (fun _ => true) i = true →
    (sVals (sp + BitVec.ofNat 32 WOFF) j)[i]? = some v → ∃ k ≤ WOFF + 124, v = sp + BitVec.ofNat 32 k := by
  intro i v _ h
  have hm := List.mem_of_getElem? h
  simp only [sVals, taps, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hm
  obtain h|h|h|h|h|h|h|h := hm <;> subst h <;> simp only [BitVec.add_assoc, ← BitVec.ofNat_add] <;>
    exact ⟨_, by omega, rfl⟩

theorem sAt_vals (t : State) {w : Word} {j : Nat} (hj : j < 16) (h6 : t.regs 6 = w)
    (h7 : t.regs 7 = BitVec.ofNat 32 (8 * j)) : sAt.map (·.denote t) = sVals w j := by
  simp only [sAt, sVals, taps, List.flatMap_cons, List.flatMap_nil, List.map_append, List.map_cons,
    List.map_nil, List.append_nil, loA, hiA, SExpr.denote, kS, h6, ixr_val t 1 hj h7,
    ixr_val t 0 hj h7, ixr_val t 9 hj h7, ixr_val t 14 hj h7]

theorem schedStep_congr {f f' : Nat → BitVec 64} (h : ∀ i < 16, f i = f' i) {j : Nat} (hj : j < 16) :
    ∀ i < 16, schedStep f j i = schedStep f' j i := by
  intro i hi
  simp only [schedStep, Ed25519Sha512Rounds.upd, h i hi, h j hj, h _ (Nat.mod_lt _ (by omega : 16 > 0))]

/-- The schedule loop's frame before pass `j`. -/
def SI (sp kb hp : Word) (m1 : Mem) (g : Nat) (V buf : Nat → BitVec 64) (j : Nat) (v : State) : Prop :=
  Inv sp kb hp m1 g V (schedRun buf j) v.mem ∧ v.regs 6 = sp + BitVec.ofNat 32 WOFF ∧
    v.regs 7 = BitVec.ofNat 32 (8 * j)


theorem SI_pc {sp kb hp : Word} {m1 : Mem} {g : Nat} {V buf : Nat → BitVec 64} {j : Nat} {t : State}
    {v : Word} (h : SI sp kb hp m1 g V buf j t) : SI sp kb hp m1 g V buf j (t.setReg 15 v) :=
  ⟨h.1, by rw [RoutineBranch.setReg15_regs _ _ _ (by decide)]; exact h.2.1,
    by rw [RoutineBranch.setReg15_regs _ _ _ (by decide)]; exact h.2.2⟩

theorem sides_w4 {t : State} {Rc Wc : List Rgn} {la lw lr : List SExpr} :
    SGlueSides t Rc Wc (w4 la) (w4 lw) (w4 lr) ↔ (∀ a ∈ la.map (·.denote t), a.toNat % 4 = 0) ∧
      Sub ((lw.map (·.denote t)).map fun a => (⟨a, 4⟩ : Rgn)) Wc ∧
      Sub ((lr.map (·.denote t)).map fun a => (⟨a, 4⟩ : Rgn)) Rc := by
  unfold SGlueSides sregions w4; simp only [List.map_map, List.forall_mem_map]; exact Iff.rfl

theorem sregions_w4 (t : State) (l : List SExpr) :
    sregions t (w4 l) = (l.map (·.denote t)).map fun a => (⟨a, 4⟩ : Rgn) := by
  simp [sregions, w4]

theorem bs_le {base sp0 kb : Word} {Rc Wc : List Rgn} (E : Env (B := B) base sp0 kb Rc Wc) {x : Nat}
    (hx : x ≤ O + size := by decide) : x ≤ BS := Nat.le_trans hx E.bs

/-- **The sixteen passes of macro `schedule`** from `oS` with the frame `SI … 0`; the loop leaves
at `oSkip` with the buffer `schedRun buf 16`. -/
theorem sched_frag (base sp0 : Word) : Tr.HasK fun Θ => (∀ {kb : Word} {Rc Wc : List Rgn},
    Env (B := B) base sp0 kb Rc Wc → ∀ {Q : State → Prop} {Ψ : TrP} {hp : Word} {m1 : Mem} {g : Nat}
    {V buf : Nat → BitVec 64} (t : State), t.pc = base + BitVec.ofNat 32 (oS O) →
    SI (fsp sp0) kb hp m1 g V buf 0 t → t.regs 13 = fsp sp0 → CodeAt t.mem base B →
    (∀ u : State, u.pc = base + BitVec.ofNat 32 (oSkip O) → u.regs 13 = fsp sp0 → CodeAt u.mem base B →
      Inv (fsp sp0) kb hp m1 g V (schedRun buf 16) u.mem →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) u Q Ψ) →
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) t Q (Θ Ψ)) ∧ ∀ kb, FragE sp0 kb Θ := by
  trefine Tr.HasK.intro ⟨?_, ?_⟩ ?_ ?_
  · intro kb Rc Wc E Q Ψ hp m1 g V buf t hpc hI h13 hc k
    have hroom := E.F.room; have := E.F.sp4; have := sp0.isLt
    simp only [D, BFRAME] at hroom
    obtain ⟨ok, hf, htr⟩ := sched_ok
    trefine ReachFT.loop (o := oS O) (ob := oS O + seqSize schedBody) (d := D) E.F 1 _ E.L.sbb 16
      (SI (fsp sp0) kb hp m1 g V buf) (fun _ _ _ h => SI_pc h) ?body ?exit ?lok 0 t (by decide) hpc hI
      h13 hc
    case lok =>
      simp only [loopOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨⟨by decide, by decide⟩, bs_le E⟩, by decide⟩, Nat.le_refl _⟩
    case exit =>
      intro u hpu hIu h13u hcu
      exact k u (by rw [hpu]; rfl) h13u hcu hIu.1
    case body =>
      intro j v hj hpv ⟨⟨hm1, hHP, hG, hK, hV, hW⟩, h6, h7⟩ h13v hcv
      have vals := sAt_vals v hj h6 h7
      have wv : [loA 0, hiA 0].map (·.denote v) = [fsp sp0 + BitVec.ofNat 32 WOFF + BitVec.ofNat 32 (8 * ((j + 0) % 16)),
          fsp sp0 + BitVec.ofNat 32 WOFF + (BitVec.ofNat 32 (8 * ((j + 0) % 16)) + BitVec.ofNat 32 4)] := by
        simp only [List.map_cons, List.map_nil, loA, hiA, SExpr.denote, kS, h6, ixr_val v 0 hj h7]
      trefine ReachFT.sglue E.F schedBody _ _ _ E.L.sb hpv h13v hcv ?sides
        (traceAll_blockTrE hf htr hpv vals) (fun hpA h13A hcA hmA => ?_) ok
      case sides =>
        refine SGlueSides.mono ?_ E.rc E.wc
        rw [sides_w4, vals, wv]
        simp only [sVals, taps, List.flatMap_cons, List.flatMap_nil, List.map_append, List.map_cons,
          List.map_nil, List.append_nil, List.cons_append, List.nil_append, List.forall_mem_cons,
          List.not_mem_nil, false_implies, implies_true, and_true]
        nrm
        repeat' apply And.intro
        all_goals fp_tac
      obtain ⟨m, r7, z, kp⟩ := sched_run v hj h7
      rw [sregions_w4, wv] at hmA
      have hw' : ∀ i < 16, wAt v.mem (fsp sp0 + BitVec.ofNat 32 WOFF) i = schedRun buf j i := fun i hi => by
        rw [wAt_pair, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hW i hi
      have h6' := kp 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      refine ReachT.done ⟨hpA, h13A, hcA, ⟨⟨?_, ?_, ?_, ?_, fun i hi => ?_,
        fun i hi => ?_⟩, ?_, ?_⟩, ?_⟩
      · refine (hm1.trans hmA).mono ?_
        nrm at hmA ⊢; fp_tac
      · nrm at hmA hHP ⊢; keep_simp; exact hHP
      · nrm at hmA hG ⊢; keep_simp; exact hG
      · nrm at hmA hK ⊢; keep_simp; exact hK
      · have := hV i hi; nrm at hmA this ⊢; keep_simp with [MemEq.pairAt]; exact this
      · rw [m, h6, show fsp sp0 + BitVec.ofNat 32 (WOFF + 8 * i) = fsp sp0 + BitVec.ofNat 32 WOFF +
          BitVec.ofNat 32 (8 * i) by rw [BitVec.add_assoc, ← BitVec.ofNat_add], ← wAt_pair, wAt_wset _ _ hi hj,
          Ed25519Sha512Rounds.schedRun, ← schedStep_congr hw' hj i hi]
        by_cases hij : i = j
        · subst hij; simp only [↓reduceIte, schedStep, Ed25519Sha512Rounds.upd]
        · simp only [hij, ↓reduceIte, schedStep, Ed25519Sha512Rounds.upd]
      · rw [h6']; exact h6
      · rw [r7]
      · rw [RoutineBranch.cond_ne, z]; by_cases h : j + 1 = 16 <;> simp [h] <;> omega
  · intro kb e0 n R Ψ J hG hΨ
    refine GP.rep hΨ _ _ fun j _ => catI (catI (sir_blkE sched_blk.1 fun y hy hb => hG y (.inl ?_) hb)
      (GP.nil fun _ h => h)) (sir_quietC rfl rfl rfl)
    exact inRD_win (by simp [sVals, sAt, taps]) sched_blk.2 (sVals_win _ j) hy
  · intro Ψ hu; uniq_tac
  · intro Ψ hx; ex_tac


/-! ## The rounds of a group, cut by the literal pool -/

/-- `r7` after the rounds before the pool, from the executor. -/
abbrev r7S : SExpr := (symExec (groupI.take (kPool O pool)) SState.init).regs 7
/-- The `K` pointer's advance in the rounds before the pool. -/
def adv : Word := (split (norm r7S)).2
/-- The atoms of the rounds' addresses: the variables at `sp`, `W` at `r6`, `K` at `r7`. -/
def at3 : List SExpr := [.reg0 13, .reg0 6, .reg0 7]
/-- The variables' region at `sp + VOFF`. -/
def vS : SExpr := .add (.reg0 13) (kS VOFF)

/-- The two halves' footprints and traces, the `K` pointer's advance in the first, and the facts
`execAll_setPc` needs. -/
theorem grp_ok : (split (norm r7S)).1 = .reg0 7 ∧ adv.toNat < VB ∧ adv.toNat % 4 = 0 ∧
    sglueOk cs (groupI.take (kPool O pool)) (oR O) D D (w4 at3) [(vS, VB)]
      [(vS, VB), (.reg0 6, VB), (.reg0 7, VB)] = true ∧
    sglueOk cs (groupI.drop (kPool O pool)) (oR2 pool) D D (w4 at3) [(vS, VB)]
      [(vS, VB), (.reg0 6, VB), (.reg0 7, VB - adv.toNat)] = true ∧
    traceOkE (groupI.take (kPool O pool)) at3 = true ∧ traceOkE (groupI.drop (kPool O pool)) at3 = true ∧
    (groupI.take (kPool O pool)).all Instr.falls = true ∧ (groupI.drop (kPool O pool)).all Instr.falls = true ∧
    groupI.all PcFree.pcFree = true ∧ (groupI.take (kPool O pool)).all (fun i => !(i.dsts.contains 6)) = true := by
  decide +kernel

/-- The variables and `W` (atoms 0, 1), and the `K` table (atom 2), as windows of the groups. -/
abbrev rgF : List (SExpr × Nat) := [(vS, VB), (.reg0 6, VB)]

theorem skip_blk : blkChk (spRg [(GRP, 4), (KP, 4)]) [] (spRg [(GRP, 4), (KP, 4)]) gSel = true ∧
    blkChk (spRg [(KP, 4), (GRP, 4)]) [] (spRg [(KP, 4), (GRP, 4)]) gTail = true ∧
    blkChk (rgF ++ [(.reg0 7, VB)]) [] (rgF ++ [(.reg0 7, VB)]) (groupI.take (kPool O pool)) = true ∧
    blkChk (rgF ++ [(.reg0 7, VB - adv.toNat)]) [] (rgF ++ [(.reg0 7, VB - adv.toNat)])
      (groupI.drop (kPool O pool)) = true ∧
    winChk at3 (fun i => decide (i < 2)) (WOFF + HALF) BFRAME rgF = true ∧
    winChk at3 (· == 2) (8 * 8 * 9) (8 * 80) [(.reg0 7, VB)] = true ∧
    winChk at3 (· == 2) (8 * 8 * 9 + adv.toNat) (8 * 80) [(.reg0 7, VB - adv.toNat)] = true := by
  decide +kernel

theorem at3_fr (sp x : Word) (g : Nat) : ∀ (i : Nat) (v : Word), decide (i < 2) = true →
    [sp, sp + BitVec.ofNat 32 WOFF + BitVec.ofNat 32 (HALF * (g % 2)), x][i]? = some v →
      ∃ k ≤ WOFF + HALF, v = sp + BitVec.ofNat 32 k
  | 0, _, _, h => ⟨0, Nat.zero_le _, by simp at h; simp [← h]⟩
  | 1, _, _, h => ⟨WOFF + HALF * (g % 2), by rcases Nat.mod_two_eq_zero_or_one g with e | e <;> rw [e] <;> simp,
      by simp at h; rw [← h, BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  | _ + 2, _, hi, _ => by simp at hi; omega

theorem at3_k (a b kb x : Word) {k m : Nat} (hk : k ≤ m) (hx : x = kb + BitVec.ofNat 32 k) :
    ∀ (i : Nat) (v : Word), (i == 2) = true → [a, b, x][i]? = some v → ∃ k' ≤ m, v = kb + BitVec.ofNat 32 k'
  | 2, _, _, h => ⟨k, hk, by simp at h; rw [← h, hx]⟩
  | 0, _, hi, _ | 1, _, hi, _ | _ + 3, _, hi, _ => by simp at hi

theorem add_ofNat_toNat (a d : Word) (k : Nat) : a + BitVec.ofNat 32 k + d = a + BitVec.ofNat 32 (k + d.toNat) := by
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem all_drop {α : Type} {l : List α} {p : α → Bool} (h : l.all p = true) (k : Nat) :
    (l.drop k).all p = true :=
  List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_drop hx)

/-- The rounds after the pool, run from the rounds before it with the pc replaced, are the group. -/
theorem cut_run (X : State) (v : Word) (k : Nat) (hp : groupI.all PcFree.pcFree = true) :
    execAll (groupI.drop k) ((execAll (groupI.take k) X).setReg 15 v) =
      (execAll groupI X).setReg 15 (v + BitVec.ofNat 32 (seqSize (groupI.drop k))) := by
  rw [PcFree.execAll_setPc _ _ _ (all_drop hp k), ← execAll_append, List.take_append_drop]

theorem outV_of_sep {sp a : Word} (h : Sep [⟨a, 1⟩] [⟨sp + BitVec.ofNat 32 VOFF, VB⟩]) : OutV sp a :=
  fun k hk e => Sep.not_has h (y := a) ⟨⟨a, 1⟩, List.mem_singleton.mpr rfl, ⟨0, Nat.one_pos, by simp⟩⟩
    ⟨_, List.mem_singleton.mpr rfl, ⟨k, hk, by rw [e, add_ofNat]⟩⟩

theorem memEq_of_out {sp : Word} {m m' : Mem} (h : ∀ a, OutV sp a → m' a = m a) :
    MemEq [⟨sp + BitVec.ofNat 32 VOFF, VB⟩] m m' :=
  fun y hy => h y fun k hk e => hy ⟨_, List.mem_singleton.mpr rfl, ⟨k, hk, by rw [e, add_ofNat]⟩⟩

theorem GlueSides.mono {t : State} {Rc Wc Rc' Wc' : List Rgn} {al : List (Reg × Nat)}
    {wg rg : List (Reg × Word × Nat)} (h : GlueSides t Rc' Wc' al wg rg) (hR : Sub Rc' Rc)
    (hW : Sub Wc' Wc) : GlueSides t Rc Wc al wg rg :=
  ⟨h.1, sub_trans h.2.1 hW, sub_trans h.2.2 hR⟩

theorem wd_ofs {n : Nat} (h : n % 4 = 0 ∧ n < 1024) : (wd n).toNat * 4 = n := by
  simp only [wd, BitVec.toNat_ofNat]; omega

theorem slot_ofs (sp : Word) {n : Nat} (h : n % 4 = 0) : slot sp (n / 4) = sp + BitVec.ofNat 32 n := by
  rw [slot, show 4 * (n / 4) = n by omega]

theorem gsel_idx (g : Nat) (hg : g < GROUPS) :
    (BitVec.ofNat 32 g <<< (BitVec.ofNat 5 HALF_SHIFT).toNat) &&& BitVec.ofNat 32 (BitVec.ofNat 8 HALF).toNat =
      BitVec.ofNat 32 (HALF * (g % 2)) := by
  have h : ∀ x : Fin GROUPS, (BitVec.ofNat 32 x.val <<< (BitVec.ofNat 5 HALF_SHIFT).toNat) &&&
      BitVec.ofNat 32 (BitVec.ofNat 8 HALF).toNat = BitVec.ofNat 32 (HALF * (x.val % 2)) := by decide +kernel
  exact h ⟨g, hg⟩

/-- `gSel`: `r6` at the group's half of the buffer, `r7` the `K` pointer. -/
theorem gsel_run (t : State) {sp kb hp : Word} {m1 : Mem} {g : Nat} {V W : Nat → BitVec 64}
    (hg : g < GROUPS) (hI : Inv sp kb hp m1 g V W t.mem) (h13 : t.regs 13 = sp) :
    (execAll gSel t).regs 6 = sp + BitVec.ofNat 32 WOFF + BitVec.ofNat 32 (HALF * (g % 2)) ∧
    (execAll gSel t).regs 7 = kb + BitVec.ofNat 32 (8 * 8 * g) ∧ (execAll gSel t).mem = t.mem := by
  obtain ⟨-, -, hG, hK, -⟩ := hI
  simp only [gSel]
  refine ⟨?_, ?_, ?_⟩ <;> rsimp [nx_addRdSp, add_flags, wd_ofs, h13, hG, hK, gsel_idx g hg]

/-- `gTail`: the `K` pointer and the counter stored, `Z` when the counter reaches `GROUPS`. -/
theorem gtail_run (u : State) {sp : Word} {g : Nat} (hg : g < GROUPS) (h13 : u.regs 13 = sp)
    (hG : read32 u.mem (sp + BitVec.ofNat 32 GRP) = BitVec.ofNat 32 g) :
    read32 (execAll gTail u).mem (sp + BitVec.ofNat 32 KP) = u.regs 7 ∧
    read32 (execAll gTail u).mem (sp + BitVec.ofNat 32 GRP) = BitVec.ofNat 32 (g + 1) ∧
    (execAll gTail u).z = decide (g + 1 = GROUPS) := by
  have e : gTail = gTail.dropLast ++ [.cmpImm 0 (BitVec.ofNat 8 GROUPS)] := rfl
  have one : (1 : BitVec 8).toNat = 1 := rfl
  have hs : ∀ n, n % 4 = 0 → n < 1024 → sp + BitVec.ofNat 32 ((wd n).toNat * 4) = slot sp (n / 4) :=
    fun n h1 h2 => by rw [wd_ofs ⟨h1, h2⟩, slot_ofs sp h1]
  have hG' : read32 u.mem (slot sp (GRP / 4)) = BitVec.ofNat 32 g := by rw [slot_ofs sp (by decide)]; exact hG
  have r0 : (execAll gTail.dropLast u).regs 0 = BitVec.ofNat 32 (g + 1) := by
    simp only [gTail, List.dropLast]
    rsimp [h13, hs, read32_write32_slotN, hG', one, ← BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [← slot_ofs sp (show KP % 4 = 0 by decide)]
    simp only [gTail]; rsimp [h13, hs, read32_write32_slotN, hG']
  · rw [← slot_ofs sp (show GRP % 4 = 0 by decide)]
    simp only [gTail]; rsimp [h13, hs, read32_write32_slotN, hG', one, ← BitVec.ofNat_add]
  · rw [e, execAll_append]; simp only [execAll]
    rw [(RoutineBranch.cmpImm_flags _ _ _).2, M0Crypto.Proofs.toReg_0, r0]
    simp only [GROUPS] at hg ⊢; simp only [BitVec.toNat_ofNat]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The trace of the rounds' first half for `r6 = w`, `r7 = k`. -/
theorem take_r7 (s : State) (hf : (groupI.take (kPool O pool)).all Instr.falls = true)
    (h1 : (split (norm r7S)).1 = .reg0 7) :
    (execAll (groupI.take (kPool O pool)) s).regs 7 = s.regs 7 + adv := by
  have e := congrArg (fun x : State => x.regs 7) (symExec_sound _ (sound_all hf) s SState.init)
  simp only [SState.init_denote, denote_regs] at e
  rw [← e, ← base_split s r7S, h1]; rfl


/-- **From `oSkip` to the counter's test**: `gSel`, the eight rounds of group `g` over the buffer
`W`, cut by the literal pool, and `gTail`. -/
theorem skip_frag (base sp0 kb : Word) (g : Nat) : Tr.HasK fun Θ => (∀ {Rc Wc : List Rgn},
    Env (B := B) base sp0 kb Rc Wc → g < GROUPS → ∀ {Q : State → Prop} {Ψ : TrP} {hp : Word} {m1 : Mem}
    {V W : Nat → BitVec 64} (t : State), t.pc = base + BitVec.ofNat 32 (oSkip O) →
    Inv (fsp sp0) kb hp m1 g V W t.mem → t.regs 13 = fsp sp0 → CodeAt t.mem base B →
    (∀ u : State, u.pc = base + BitVec.ofNat 32 (oT O pool + seqSize gTail) → u.regs 13 = fsp sp0 →
      CodeAt u.mem base B → Inv (fsp sp0) kb hp m1 (g + 1) (codeGroup g W V) W u.mem →
      u.z = decide (g + 1 = GROUPS) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) u Q Ψ) →
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) t Q (Θ Ψ)) ∧ (g < GROUPS → FragE sp0 kb Θ) := by
  trefine Tr.HasK.intro ⟨?_, ?_⟩ ?_ ?_
  · intro Rc Wc E hg Q Ψ hp m1 V W t hpc hI h13 hc k
    have hroom := E.F.room; have := E.F.sp4; have := sp0.isLt; have hkn := E.kn; have hk4 := E.k4
    have hks := E.ksep; have hg' := hg
    nrm at hroom hks hg'
    fp_simp at hks
    have hb2 : base.toNat % 2 = 0 := by have := E.F.b4; omega
    obtain ⟨h7a, hadv, hadv4, okT, okD, trT, trD, fT, fD, pcf, n6⟩ := grp_ok
    nrm at hadv
    obtain ⟨X6, X7, XM⟩ := gsel_run t hg hI h13
    obtain ⟨hm1, hHP, hG, hK, hV, hW⟩ := hI
    -- `gSel`
    trefine ReachFT.glue E.F gSel [((13 : Reg), 4)] []
      [((13 : Reg), BitVec.ofNat 32 GRP, 4), ((13 : Reg), BitVec.ofNat 32 KP, 4)] E.L.gs hpc h13 hc ?gs
      (tr_block [13] hpc [h13]) (fun hpX h13X hcX _ => ?_) (by decide)
    case gs =>
      refine GlueSides.mono ?_ E.rc E.wc
      glue_tac [h13, fsp, D, BFRAME, GRP, KP]
    generalize execAll gSel t = X at hpX h13X hcX X6 X7 XM
    have hpX' : X.pc = base + BitVec.ofNat 32 (oR O) := hpX
    -- the rounds before the pool
    trefine ReachFT.sglue E.F (groupI.take (kPool O pool)) _ _ _ E.L.tk hpX' h13X hcX ?ts
      (traceAll_blockTrE fT trT hpX' (vs := [fsp sp0, fsp sp0 + BitVec.ofNat 32 WOFF +
        BitVec.ofNat 32 (HALF * (g % 2)), kb + BitVec.ofNat 32 (8 * 8 * g)])
        (by simp only [at3, List.map_cons, List.map_nil, SExpr.denote, h13X, X6, X7]))
      (fun hpY h13Y hcY _ => ?_) okT
    case ts =>
      refine SGlueSides.mono ?_ E.rc E.wc
      simp only [SGlueSides, sregions, w4, at3, vS, kS, List.map_cons, List.map_nil, SExpr.denote, h13X, X6, X7,
        List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      nrm; repeat' apply And.intro
      all_goals fp_tac
    have Y6 : (execAll (groupI.take (kPool O pool)) X).regs 6 = X.regs 6 := execAll_regs_other _ _ 6 (by decide) n6
    have Y7 := take_r7 X fT h7a
    generalize hY : execAll (groupI.take (kPool O pool)) X = Y at hpY h13Y hcY Y6 Y7
    -- the jump over the pool
    trefine ReachT.b hb2 (oR O + seqSize (groupI.take (kPool O pool))) (oR2 pool) _ hpY (by decide +kernel)
      E.L.pb (bs_le E (by decide +kernel)) (by decide +kernel)
      ⟨by rw [hpY]; exact PcIn.at List.mem_cons_self (by decide +kernel) (by decide +kernel),
        fun y hy => absurd hy (writes_nil y), fun y hy => absurd hy (reads_nil y),
        by rw [h13Y]; exact ⟨D, Nat.le_refl _, rfl⟩⟩ ?_
    have hpZ := RoutineBranch.setReg15_pc Y (base + BitVec.ofNat 32 (oR2 pool))
    have rZ : ∀ r : Reg, r.val ≠ 15 → (Y.setReg 15 (base + BitVec.ofNat 32 (oR2 pool))).regs r = Y.regs r :=
      fun r h => RoutineBranch.setReg15_regs _ _ _ h
    -- the rounds after the pool
    trefine ReachFT.sglue E.F (groupI.drop (kPool O pool)) _ _ _ E.L.dr hpZ
      ((rZ 13 (by decide)).trans h13Y) hcY ?ds
      (traceAll_blockTrE fD trD hpZ (vs := [fsp sp0, fsp sp0 + BitVec.ofNat 32 WOFF +
        BitVec.ofNat 32 (HALF * (g % 2)), kb + BitVec.ofNat 32 (8 * 8 * g) + adv])
        (by simp only [at3, List.map_cons, List.map_nil, SExpr.denote, rZ 13 (by decide), rZ 6 (by decide),
          rZ 7 (by decide), h13Y, Y6, Y7, X6, X7]))
      (fun hpU h13U hcU _ => ?_) okD
    case ds =>
      refine SGlueSides.mono ?_ E.rc E.wc
      simp only [SGlueSides, sregions, w4, at3, vS, kS, List.map_cons, List.map_nil, SExpr.denote, rZ 13 (by decide),
        rZ 6 (by decide), rZ 7 (by decide), h13Y, Y6, Y7, X6, X7, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true, and_true]
      nrm; repeat' apply And.intro
      all_goals fp_tac
    -- the group's effect
    have hU : execAll (groupI.drop (kPool O pool)) (Y.setReg 15 (base + BitVec.ofNat 32 (oR2 pool))) =
        (execAll groupI X).setReg 15 (base + BitVec.ofNat 32 (oR2 pool) +
          BitVec.ofNat 32 (seqSize (groupI.drop (kPool O pool)))) := by rw [← hY]; exact cut_run X _ _ pcf
    rw [hU] at hpU h13U hcU ⊢
    obtain ⟨gV, gO, g7, gkp⟩ := group_run X (fun r => M0Crypto.Spec.Sha512.K[8 * g + r]!)
      (fun r => W (8 * (g % 2) + r)) V (fun i hi => by rw [vp_pair, XM, h13X]; exact hV i hi)
      (fun r hr => by
        rw [X7, add_ofNat, show 8 * 8 * g + 8 * r = 8 * (8 * g + r) by omega]
        exact E.ktab X.mem hcX _ (by omega))
      (fun r hr => by
        rw [wAt_pair, X6, XM, add_ofNat, add_ofNat]
        rw [show WOFF + (HALF * (g % 2) + 8 * r) = WOFF + 8 * (8 * (g % 2) + r) by simp only [HALF, HALF_SHIFT]; omega]
        exact hW _ (by omega))
      (fun q hq => outV_of_sep (by rw [h13X, X7]; nrm; fp_tac))
      (fun q hq => outV_of_sep (by rw [h13X, X6]; nrm; fp_tac))
    rw [h13X] at gV gO
    have hGM := memEq_of_out gO
    generalize execAll groupI X = G at hpU h13U hcU gV gO g7 gkp hGM
    have hUm : (G.setReg 15 (base + BitVec.ofNat 32 (oR2 pool) +
        BitVec.ofNat 32 (seqSize (groupI.drop (kPool O pool))))).mem = G.mem := rfl
    rw [hUm] at hcU
    have hpU' : (G.setReg 15 (base + BitVec.ofNat 32 (oR2 pool) +
        BitVec.ofNat 32 (seqSize (groupI.drop (kPool O pool))))).pc = base + BitVec.ofNat 32 (oT O pool) := hpU
    -- `gTail`
    trefine ReachFT.glue E.F gTail [((13 : Reg), 4)]
      [((13 : Reg), BitVec.ofNat 32 KP, 4), ((13 : Reg), BitVec.ofNat 32 GRP, 4)]
      [((13 : Reg), BitVec.ofNat 32 GRP, 4)] E.L.gt hpU' h13U hcU ?gt (tr_block [13] hpU' [h13U])
      (fun hpR h13R hcR hmR => ?_) (by decide +kernel)
    case gt =>
      refine GlueSides.mono ?_ E.rc E.wc
      glue_tac [h13U, fsp, D, BFRAME, GRP, KP]
    have hmR' : MemEq _ G.mem _ := hmR
    clear hmR
    simp only [regions, List.map_cons, List.map_nil, h13U] at hmR'
    have hGU : read32 G.mem (fsp sp0 + BitVec.ofNat 32 GRP) = BitVec.ofNat 32 g := by
      have := hG; nrm at this hGM ⊢; keep_simp; rw [XM]; exact this
    obtain ⟨tK, tG, tZ⟩ := gtail_run _ hg h13U hGU
    refine k _ hpR h13R hcR ⟨?_, ?_, tG, ?_, fun i hi => ?_, fun i hi => ?_⟩ tZ
    · refine (((hm1.trans (MemEq.of_eq (f := []) XM)).trans hGM).trans hmR').mono ?_
      nrm at hmR' ⊢; fp_tac
    · have := hHP; nrm at this hmR' hGM ⊢; keep_simp; rw [XM]; exact this
    · rw [tK, RoutineBranch.setReg15_regs _ _ _ (by decide), g7, X7, add_ofNat,
        show 8 * 8 * g + 8 * 8 = 8 * 8 * (g + 1) by omega]
    · have := gV i hi; rw [vp_pair] at this; nrm at this hmR' ⊢; keep_simp with [MemEq.pairAt]; exact this
    · have := hW i hi; nrm at this hmR' hGM ⊢; keep_simp with [MemEq.pairAt]; rw [XM]; exact this
  · intro hg e0 n R Ψ J hG hΨ
    obtain ⟨b1, b2, b3, b4, w1, w2, w3⟩ := skip_blk
    have hF : ∀ y, Region (fsp sp0) BFRAME y → BelowEntry e0 n y → R y := fun y h => hG y (.inl h)
    have hK : ∀ y, Region kb (8 * 80) y → BelowEntry e0 n y → R y := fun y h => hG y (.inr h)
    have hg' : 8 * 8 * g ≤ 8 * 8 * 9 := by simp only [GROUPS] at hg; omega
    refine catI (sir_blk b1 fun y hy => hF y (inR_sp (by decide) hy)) (catI (sir_blkE b3 fun y hy => ?_)
      (catI (sir_quietC rfl rfl rfl) (catI (sir_blkE b4 fun y hy => ?_)
        (catI (sir_blk b2 fun y hy => hF y (inR_sp (by decide) hy)) hΨ))))
    · rcases StackEffect.inR_append.1 hy with h | h
      · exact hF y (inRD_win rfl w1 (at3_fr _ _ g) h)
      · exact hK y (inRD_win rfl w2 (at3_k _ _ _ _ hg' rfl) h)
    · rcases StackEffect.inR_append.1 hy with h | h
      · exact hF y (inRD_win rfl w1 (at3_fr _ _ g) h)
      · exact hK y (inRD_win rfl w3 (at3_k _ _ _ _ (Nat.add_le_add_right hg' _) (add_ofNat_toNat _ _ _)) h)
  · intro Ψ hu; uniq_tac
  · intro Ψ hx; ex_tac


/-! ## A pass of the group loop -/

theorem pass_blk : blkChk (spRg [(GRP, 4)]) [] (spRg [(GRP, 4)]) gHead = true ∧ blkChk [] [] [] gOdd = true ∧
    blkChk [] [] [] sPre = true := by decide +kernel

/-- The buffer group `g` runs over: refreshed by macro `schedule` before even groups from 2 on. -/
def bufOf (g : Nat) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  if 2 ≤ g ∧ g % 2 = 0 then schedRun W 16 else W

theorem lsb_odd (g : Nat) : (BitVec.ofNat 32 g)[0] = decide (g % 2 = 1) := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp [Nat.testBit_zero]

/-- **A pass of the group loop** from `oG`: `cmp g, #2; blo; lsrs g; bcs` on the public counter,
macro `schedule` for even groups from 2 on, then `skip_frag`. -/
theorem pass_frag (base sp0 kb : Word) (g : Nat) : Tr.HasK fun Θ => (∀ {Rc Wc : List Rgn},
    Env (B := B) base sp0 kb Rc Wc → g < GROUPS → ∀ {Q : State → Prop} {Ψ : TrP} {hp : Word} {m1 : Mem}
    {V W : Nat → BitVec 64} (t : State), t.pc = base + BitVec.ofNat 32 (oG O) →
    Inv (fsp sp0) kb hp m1 g V W t.mem → t.regs 13 = fsp sp0 → CodeAt t.mem base B →
    (∀ u : State, u.pc = base + BitVec.ofNat 32 (oT O pool + seqSize gTail) → u.regs 13 = fsp sp0 →
      CodeAt u.mem base B → Inv (fsp sp0) kb hp m1 (g + 1) (codeGroup g (bufOf g W) V) (bufOf g W) u.mem →
      u.z = decide (g + 1 = GROUPS) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) u Q Ψ) →
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) t Q (Θ Ψ)) ∧ (g < GROUPS → FragE sp0 kb Θ) := by
  trefine Tr.HasK.intro ⟨?_, ?_⟩ ?_ ?_
  · intro Rc Wc E hg Q Ψ hp m1 V W t hpc hI h13 hc k
    have hb2 : base.toNat % 2 = 0 := by have := E.F.b4; omega
    have hG := hI.2.2.1
    -- `ldr r0, [sp, #GRP]; cmp r0, #2`
    have e0 : ((Instr.ldrSp 0 (wd GRP)).next t).regs 0 = BitVec.ofNat 32 g := by
      rsimp [wd_ofs, h13, hG]
    have ec : (execAll gHead t).c = decide (2 ≤ g) := by
      simp only [gHead, execAll]
      rw [(RoutineBranch.cmpImm_flags _ _ _).1, M0Crypto.Proofs.toReg_0, e0]
      have : g < 2 ^ 32 := by simp only [GROUPS] at hg; omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]; rfl
    have e0' : (execAll gHead t).regs 0 = BitVec.ofNat 32 g := by
      simp only [gHead, execAll]; rw [nx_cmpImm _ _ (by decide)]; exact e0
    have em : (execAll gHead t).mem = t.mem := by simp only [gHead]; rsimp []
    trefine ReachFT.glue E.F gHead [((13 : Reg), 4)] [] [((13 : Reg), BitVec.ofNat 32 GRP, 4)] E.L.gh hpc
      h13 hc ?gh (tr_block [13] hpc [h13]) (fun hp1 h131 hc1 _ => ?_) (by decide)
    case gh =>
      refine GlueSides.mono ?_ E.rc E.wc
      have := E.F.room; have := E.F.sp4; have := sp0.isLt
      nrm at *; glue_tac [h13, fsp, D, BFRAME, GRP]
    generalize execAll gHead t = t1 at hp1 h131 hc1 ec e0' em
    rw [← em] at hI
    -- `blo oSkip`: groups 0 and 1 use the loaded words
    have hc2 : condPassed 3 t1 = decide (g < 2) := by
      rw [RoutineBranch.cond_lo, ec]; by_cases h : g < 2 <;> simp [h] <;> omega
    trefine ReachFT.bcond (b := decide (g < 2)) hb2 (oSkip O) 3 _ hp1 (by decide +kernel) E.L.ghb
      (bs_le E (by decide +kernel)) (by decide +kernel)
      (PcIn.at (lo := O) (hi := O + size) List.mem_cons_self (by decide +kernel) (by decide +kernel))
      (by rw [h131]; exact ⟨D, Nat.le_refl _, rfl⟩)
      hc2 (fun hT => ?_) (fun hF1 => ?_)
    · rw [hc2] at hT
      have hb : bufOf g W = W := by simp only [bufOf]; split <;> first | rfl | (simp at hT; omega)
      rw [hb] at k
      exact (skip_frag (B := B) base sp0 kb g).run.1 E hg _ (RoutineBranch.setReg15_pc _ _) hI
        ((RoutineBranch.setReg15_regs _ _ _ (by decide)).trans h131) hc1 k
    -- `lsrs r1, r0, #1; bcs oSkip`: odd groups use the half the last refresh wrote
    have hp2 : (t1.setReg 15 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2))).pc =
        base + BitVec.ofNat 32 (oOdd O) := RoutineBranch.setReg15_pc _ _
    have h132 := (RoutineBranch.setReg15_regs t1 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2)) 13
      (by decide)).trans h131
    have e2 : (t1.setReg 15 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2))).regs 0 = BitVec.ofNat 32 g :=
      (RoutineBranch.setReg15_regs _ _ _ (by decide)).trans e0'
    trefine ReachFT.glue E.F gOdd [] [] [] E.L.go hp2 h132 hc1 ⟨fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      (tr_block [] hp2 []) (fun hp3 h133 hc3 _ => ?_) (by decide)
    have ec3 : (execAll gOdd (t1.setReg 15 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2)))).c =
        decide (g % 2 = 1) := by
      simp [gOdd, execAll, Instr.next, Instr.exec, lsrC, State.setNZC, State.setNZ, State.reg,
        M0Crypto.Proofs.toReg_0, e2, lsb_odd g]
    have em3 : (execAll gOdd (t1.setReg 15 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2)))).mem = t1.mem := by
      simp only [gOdd]; rsimp []; rfl
    generalize execAll gOdd (t1.setReg 15 (base + BitVec.ofNat 32 (oG O + seqSize gHead + 2))) = t3
      at hp3 h133 hc3 ec3 em3
    rw [← em3] at hI
    have hc4 : condPassed 2 t3 = decide (g % 2 = 1) := by rw [show condPassed 2 t3 = t3.c from rfl, ec3]
    trefine ReachFT.bcond (b := decide (g % 2 = 1)) hb2 (oSkip O) 2 _ hp3 (by decide +kernel) E.L.gob
      (bs_le E (by decide +kernel)) (by decide +kernel)
      (PcIn.at (lo := O) (hi := O + size) List.mem_cons_self (by decide +kernel) (by decide +kernel))
      (by rw [h133]; exact ⟨D, Nat.le_refl _, rfl⟩)
      hc4 (fun hT => ?_) (fun hF2 => ?_)
    · rw [hc4] at hT
      have hb : bufOf g W = W := by simp only [bufOf]; split <;> first | rfl | (simp at hT; omega)
      rw [hb] at k
      exact (skip_frag (B := B) base sp0 kb g).run.1 E hg _ (RoutineBranch.setReg15_pc _ _) hI
        ((RoutineBranch.setReg15_regs _ _ _ (by decide)).trans h133) hc3 k
    -- `add r6, sp, #WOFF; movs r7, #0`, then the schedule
    rw [hc2] at hF1; rw [hc4] at hF2
    have hb : bufOf g W = schedRun W 16 := by simp only [bufOf]; split <;> first | rfl | (simp at hF1 hF2; omega)
    rw [hb] at k
    have hp4 : (t3.setReg 15 (base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + 2))).pc =
        base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + brSize) := RoutineBranch.setReg15_pc _ _
    have h134 := (RoutineBranch.setReg15_regs t3 (base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + 2)) 13
      (by decide)).trans h133
    trefine ReachFT.glue E.F sPre [] [] [] E.L.sp hp4 h134 hc3 ⟨fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      (tr_block [] hp4 []) (fun hp5 h135 hc5 _ => ?_) (by decide)
    have r6 : (execAll sPre (t3.setReg 15 (base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + 2)))).regs 6 =
        fsp sp0 + BitVec.ofNat 32 WOFF := by
      simp only [sPre]; rsimp [nx_addRdSp, wd_ofs, RoutineBranch.setReg15_regs, h133]
    have r7 : (execAll sPre (t3.setReg 15 (base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + 2)))).regs 7 =
        BitVec.ofNat 32 (8 * 0) := by
      simp only [sPre]; rsimp []
    have em5 : (execAll sPre (t3.setReg 15 (base + BitVec.ofNat 32 (oOdd O + seqSize gOdd + 2)))).mem = t3.mem := by
      simp only [sPre]; rsimp [nx_addRdSp]; rfl
    exact (sched_frag (B := B) base sp0).run.1 E _ hp5 ⟨by rw [em5]; exact hI, r6, r7⟩ h135 hc5
      fun u hpu h13u hcu hIu => (skip_frag (B := B) base sp0 kb g).run.1 E hg u hpu hIu h13u hcu k
  · intro hg e0 n R Ψ J hG hΨ
    have sk := (skip_frag (B := B) base sp0 kb g).run.2 hg e0 n R Ψ J hG hΨ
    obtain ⟨b1, b2, b3⟩ := pass_blk
    have h0 : ∀ t y, ¬ StackEffect.InR t [] y := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil
    refine catI (sir_blk b1 fun y hy => hG y (.inl (inR_sp (by decide) hy))) (catI (sir_quietC rfl rfl rfl)
      (GP.cond (fun _ => sk) fun _ => catI (sir_blk b2 fun y hy => absurd hy (h0 _ y)) (catI (sir_quietC rfl rfl rfl)
        (GP.cond (fun _ => sk) fun _ => catI (sir_blk b3 fun y hy => absurd hy (h0 _ y))
          ((sched_frag (B := B) base sp0).run.2 kb e0 n R _ J hG sk)))))
  · intro Ψ hu; uniq_tac
  · intro Ψ hx; ex_tac


/-! ## The group loop -/

theorem codeGroups_succ (M S : Nat → BitVec 64) (g : Nat) : codeGroups M S (g + 1) =
    (bufOf g (codeGroups M S g).1, codeGroup g (bufOf g (codeGroups M S g).1) (codeGroups M S g).2) := rfl

/-- **The `GROUPS` passes** from `oG` with the frame of group 0 over the variables `S` and the
loaded words `M`; the loop leaves at `oEnd` with `codeGroups M S GROUPS`. -/
theorem loop_frag (base sp0 kb : Word) : Tr.HasK fun Θ => (∀ {Rc Wc : List Rgn},
    Env (B := B) base sp0 kb Rc Wc → ∀ {Q : State → Prop} {Ψ : TrP} {hp : Word} {m1 : Mem}
    {M S : Nat → BitVec 64} (t : State), t.pc = base + BitVec.ofNat 32 (oG O) →
    Inv (fsp sp0) kb hp m1 0 S M t.mem → t.regs 13 = fsp sp0 → CodeAt t.mem base B →
    (∀ u : State, u.pc = base + BitVec.ofNat 32 (oEnd O pool) → u.regs 13 = fsp sp0 →
      CodeAt u.mem base B →
      Inv (fsp sp0) kb hp m1 GROUPS (codeGroups M S GROUPS).2 (codeGroups M S GROUPS).1 u.mem →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) u Q Ψ) →
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 D) t Q (Θ Ψ)) ∧ FragE sp0 kb Θ := by
  trefine Tr.HasK.intro ⟨?_, ?_⟩ ?_ ?_
  · intro Rc Wc E Q Ψ hp m1 M S t hpc hI h13 hc k
    have hj := E.L.gtj
    rw [show brSize = 2 from rfl] at hj
    trefine Ed25519Lookup.loopJ (o := oG O) (ob := oT O pool + seqSize gTail) (ex := oEnd O pool) (d := D)
      (Φb := fun j => (pass_frag (B := B) base sp0 kb j).tr (Tr.is [])) (Ψx := Ψ)
      E.F 0 _ _ E.L.gtb hj GROUPS
      (fun j u => Inv (fsp sp0) kb hp m1 j (codeGroups M S j).2 (codeGroups M S j).1 u.mem)
      (fun _ _ _ h => h) ?body ?exit ?ok 0 t (by decide) hpc hI h13 hc
    case ok =>
      simp only [Ed25519Lookup.loopJOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨⟨⟨by decide +kernel, by decide +kernel⟩, bs_le E (by decide +kernel)⟩, by decide +kernel⟩,
        by decide +kernel⟩, Nat.le_refl _⟩
    case exit =>
      intro u hpu hIu h13u hcu
      exact k u hpu h13u hcu hIu
    case body =>
      intro j u hj hpu hIu h13u hcu
      exact (pass_frag (B := B) base sp0 kb j).run.1 E hj (Ψ := Tr.is []) u hpu hIu h13u hcu
        fun v hpv h13v hcv hIv hz => ReachT.done ⟨hpv, h13v, hcv, by rw [codeGroups_succ]; exact hIv, hz⟩
  · intro e0 n R Ψ J hG hΨ
    refine GP.rep hΨ _ _ fun j hj => catI ((pass_frag (B := B) base sp0 kb j).run.2 (by omega) e0 n R _ _ hG
      (GP.nil fun _ h => h)) (catI (sir_quietC rfl rfl rfl)
        (GP.cond (fun _ => GP.nil fun _ h => h) fun _ => sir_quietC rfl rfl rfl))
  · intro Ψ hu
    refine Tr.uniq_rep (fun j => ?_) hu _ _
    simp only [Ed25519Lookup.passTr]; uniq_tac
  · intro Ψ hx
    refine Tr.ex_rep (fun j => ?_) hx _ _
    simp only [Ed25519Lookup.passTr]; ex_tac

end

end M0Crypto.Release.Ed25519Sha512Pass
