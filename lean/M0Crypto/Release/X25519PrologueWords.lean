import M0Crypto.Release.X25519PrologueFrame
import M0Crypto.Release.X25519ReadBlock

set_option linter.unusedSimpArgs false

/-!
The input loads of the prologue of `m0c_x25519`.

* `scalarWord_w`, `pointWord_w`: one word of the scalar (clamped) or of the u-coordinate
  (bit 255 masked), loaded with `X25519Bytes.loadLe32_run_w` and stored in the frame, for any
  word index `i < 8`. The loaded bytes are those of `c.m0`: the inputs are disjoint from the
  stack window (`Valid.scalarS`, `Valid.pointS`) and the prologue writes only that window.
* `words_loop`: a loop over the eight copies of a per-word block in `words f`; `scalar_w` and
  `point_w` are the two loops, with the frame after them described slot by slot.

Code bytes come from the offsets of `words f` (`word_at`), never from new byte checks.
-/

namespace M0Crypto.Release.X25519Prologue
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW ReachS InRegion Region B)
open M0Crypto.Release.Frame (Disj InFrame)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Bytes (loadLe32)

/-! ## Generic facts -/

theorem upd1_ne (F : Nat → Word) {k x : Nat} (v : Word) (h : x ≠ k) : upd F k [v] x = F x := by
  simp only [upd, List.length_singleton, show ¬ (k ≤ x ∧ x < k + 1) by omega, ↓reduceIte]

theorem upd1_eq (F : Nat → Word) (k : Nat) (v : Word) : upd F k [v] k = v := by
  simp [upd]

theorem seqSize_even' : ∀ is : List Instr, seqSize is % 2 = 0
  | [] => rfl
  | i :: is => by
    have := seqSize_even' is
    have : i.size % 2 = 0 := by cases i <;> simp [Instr.size]
    simp only [seqSize, List.map_cons, List.sum_cons] at *
    omega

/-- Code offsets below the end of the artifact are in the executed-PC region. -/
theorem code_reg {base : Word} {o n : Nat} (h : o + n ≤ Artifacts.Release.size) :
    InRegion (Region base Artifacts.Release.size) base o n := fun j hj => by
  have := X25519MulcFacts.inReg (base := base) (F := 0) (S := Artifacts.Release.size) (off := o) (n := n)
    ⟨Nat.zero_le _, by omega, by have := X25519Op.size_lt; omega⟩ j hj
  rwa [BitVec.add_zero] at this

/-- Word `i` of `words f`, at its offset. -/
theorem word_at (f : Nat → List Instr) {i off0 : Nat} (hi : i < 8) (hseq : seqAt B off0 (words f) = true) :
    seqAt B (off0 + seqSize ((List.range i).flatMap f)) (f i) = true ∧
      off0 + seqSize ((List.range i).flatMap f) + seqSize (f i) ≤ off0 + seqSize (words f) := by
  rw [words_split f hi] at hseq ⊢
  simp only [seqAt_append, seqSize_append, Bool.and_eq_true] at hseq ⊢
  exact ⟨hseq.1.2, by omega⟩

/-- A loop over the eight blocks of `words f`, with invariant `I i` before block `i`. -/
theorem words_loop {base : Word} {P : State → Event → Prop} {Q : State → Prop} (f : Nat → List Instr)
    (off0 : Nat) (I : Nat → State → Prop)
    (step : ∀ i < 8, ∀ s : State, s.pc = base + BitVec.ofNat 32 (off0 + seqSize ((List.range i).flatMap f)) →
      I i s → (∀ t : State, t.pc = base + BitVec.ofNat 32 (off0 + seqSize ((List.range (i + 1)).flatMap f)) →
        I (i + 1) t → ReachS base P t Q) → ReachS base P s Q)
    (k : ∀ t : State, t.pc = base + BitVec.ofNat 32 (off0 + seqSize (words f)) → I 8 t → ReachS base P t Q)
    (s : State) (hpc : s.pc = base + BitVec.ofNat 32 off0) (hs : I 0 s) : ReachS base P s Q := by
  have main : ∀ n i, i + n = 8 → ∀ s : State,
      s.pc = base + BitVec.ofNat 32 (off0 + seqSize ((List.range i).flatMap f)) → I i s →
      ReachS base P s Q := by
    intro n
    induction n with
    | zero =>
      intro i hi s hpc hs
      obtain rfl : i = 8 := by omega
      exact k s hpc hs
    | succ n ih =>
      intro i hi s hpc hs
      exact step i (by omega) s hpc hs fun t ht hi' => ih (i + 1) (by omega) t ht hi'
  exact main 8 0 rfl s (by simpa [seqSize] using hpc) hs

/-! ## One input word -/

/-- The two input buffers. The prologue reads nothing else. -/
def InpR (c : X25519.Ctx) (y : Word) : Prop := Region c.scalar 32 y ∨ Region c.point 32 y

/-- The byte loads of input words read only their input. -/
theorem loadLe32_chk : ∀ i < 8,
    M0Crypto.Sym.readChk (fun _ => true) [(1, BitVec.ofNat 32 (4 * i), 4)] (loadLe32 4 3 1 (4 * i)) = true ∧
    M0Crypto.Sym.readChk (fun _ => true) [(2, BitVec.ofNat 32 (4 * i), 4)] (loadLe32 4 3 2 (4 * i)) = true := by
  decide +kernel

theorem loadLe32_reads {c : X25519.Ctx} {t : State} {i : Nat} (hi : i < 8) {rb : LowReg} {p : Word}
    (hrb : rb = 1 ∧ p = c.scalar ∨ rb = 2 ∧ p = c.point) (hp : t.regs rb.toReg = p) :
    BlockReads (InpR c) (loadLe32 4 3 rb (4 * i)) t := by
  have hreg : ∀ o < 4, InpR c (p + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 o) := fun o ho => by
    rcases hrb with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl (region_add (by omega) (by decide))
    · exact Or.inr (region_add (by omega) (by decide))
  rcases hrb with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · refine blockReads_chk _ (X25519Bytes.loadLe32_falls _ _ _ _) (loadLe32_chk i hi).1 fun q hq o ho => ?_
    rcases List.mem_singleton.mp hq with rfl
    rw [← X25519Mem.toReg1, hp]; exact hreg o ho
  · refine blockReads_chk _ (X25519Bytes.loadLe32_falls _ _ _ _) (loadLe32_chk i hi).2 fun q hq o ho => ?_
    rcases List.mem_singleton.mp hq with rfl
    rw [← X25519Mem.toReg2, hp]; exact hreg o ho

/-- `X25519Bytes.loadLe32_run_w` with the read bound. -/
theorem loadLe32_run_r {base p : Word} (hb : base.toNat % 2 = 0) {Pc Wr Rd : Word → Prop} {t : State}
    {off k : Nat} {rd rt rb : LowReg} (hdt : rd ≠ rt) (hdb : rd ≠ rb) (htb : rt ≠ rb)
    (hk : k + 3 < 32) (hseq : seqAt B off (loadLe32 rd rt rb k) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hp : t.regs rb.toReg = p)
    (hrd : BlockReads Rd (loadLe32 rd rt rb k) t)
    (hr : InRegion Pc base off (seqSize (loadLe32 rd rt rb k))) {Q : State → Prop}
    (cont : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (loadLe32 rd rt rb k)) →
      t'.mem = t.mem →
      (∀ r : Reg, r ≠ rd.toReg → r ≠ rt.toReg → r.val ≠ 15 → t'.regs r = t.regs r) →
      (t'.regs rd.toReg).toNat = (t.mem (p + BitVec.ofNat 32 k)).toNat +
        2 ^ 8 * (t.mem (p + BitVec.ofNat 32 (k + 1))).toNat +
        2 ^ 16 * (t.mem (p + BitVec.ofNat 32 (k + 2))).toNat +
        2 ^ 24 * (t.mem (p + BitVec.ofNat 32 (k + 3))).toNat →
      ReachR base Pc Wr Rd t' Q) :
    ReachR base Pc Wr Rd t Q := by
  apply ReachR.blockAcc hb (loadLe32 rd rt rb k) off hpc ho hseq (X25519Bytes.loadLe32_falls rd rt rb k)
    (accAll_of (X25519Bytes.loadLe32_aligned t rd rt rb k)
      (Release.WritesTo.of_noWritesMem _ _ (X25519Bytes.loadLe32_noW rd rt rb k) Wr)) hrd hr
  apply cont
  · rw [execAll_pc _ _ (X25519Bytes.loadLe32_falls rd rt rb k), hpc, ofNat_add_assoc]
  · exact execAll_mem _ _ (X25519Bytes.loadLe32_noW rd rt rb k)
  · intro r h1 h2 h15
    exact X25519Bytes.loadLe32_regs_other t k h1 h2 h15
  · rw [← hp]; exact X25519Bytes.loadLe32_exec t hdt hdb htb hk

section
variable {c : X25519.Ctx} {Wr : Word → Prop} (hv : X25519.Valid c)
  (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y) {Pc : Word → Prop}
  (hPc : ∀ o n, Artifacts.Release.x25519 ≤ o → o + n ≤ oLadder → InRegion Pc c.base o n)

/-- An input byte (outside the stack window) reads as in `c.m0` while the frame is `FrameOk`. -/
theorem in_byte {p : Word} (hd : Disj p 32 c.fp X25519.stackBytes) {F : Nat → Word} {m : Mem}
    (fr : FrameOk (E c) NW (mP c) F m) {j : Nat} (hj : j < 32) :
    m (p + BitVec.ofNat 32 j) = c.m0 (p + BitVec.ofNat 32 j) := by
  have hn : ¬ Region c.fp X25519.stackBytes (p + BitVec.ofNat 32 j) :=
    fun h => X25519MulcFacts.region_ne hd h j hj rfl
  rw [fr.out _ fun hi => hn (frame_inwin hi), mP_out hn]

/-- The four loaded bytes of input word `i` are `leWord` of the input bytes. -/
theorem load_word {p : Word} (hd : Disj p 32 c.fp X25519.stackBytes) {F : Nat → Word} {m : Mem}
    (fr : FrameOk (E c) NW (mP c) F m) {i : Nat} (hi : i < 8) :
    (m (p + BitVec.ofNat 32 (4 * i))).toNat + 2 ^ 8 * (m (p + BitVec.ofNat 32 (4 * i + 1))).toNat +
      2 ^ 16 * (m (p + BitVec.ofNat 32 (4 * i + 2))).toNat +
      2 ^ 24 * (m (p + BitVec.ofNat 32 (4 * i + 3))).toNat =
      X25519Decode.leWord (Frame.Ctx.bytesAt c.m0 p 32) i := by
  rw [X25519Decode.leWord, bytesAt_getD _ _ (show 4 * i < 32 by omega),
    bytesAt_getD _ _ (show 4 * i + 1 < 32 by omega), bytesAt_getD _ _ (show 4 * i + 2 < 32 by omega),
    bytesAt_getD _ _ (show 4 * i + 3 < 32 by omega), in_byte hd fr (by omega),
    in_byte hd fr (by omega), in_byte hd fr (by omega), in_byte hd fr (by omega)]

include hv hWr hPc

/-- Scalar word `i`: load, clamp (words 0 and 7), store at `sK/4 + i`. -/
theorem scalarWord_w {i : Nat} (hi : i < 8) {off : Nat} {s : State} {F : Nat → Word} {Q : State → Prop}
    (hseq : seqAt B off (scalarWord i) = true) (ho : off % 2 = 0)
    (hend : off + seqSize (scalarWord i) ≤ oLadder) (hlo : Artifacts.Release.x25519 ≤ off)
    (hpc : s.pc = c.base + BitVec.ofNat 32 off) (sp : s.regs 13 = E c) (r1 : s.regs 1 = c.scalar)
    (fr : FrameOk (E c) NW (mP c) F s.mem)
    (cont : ∀ (t : State) (v : Word), t.pc = c.base + BitVec.ofNat 32 (off + seqSize (scalarWord i)) →
      v.toNat = (kWords c).getD i 0 → t.regs 13 = E c →
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 15 → t.regs r = s.regs r) →
      FrameOk (E c) NW (mP c) (upd F (sK / 4 + i) [v]) t.mem →
      ReachR c.base Pc Wr (InpR c) t Q) :
    ReachR c.base Pc Wr (InpR c) s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  rw [scalarWord_eq] at hseq hend cont
  rw [seqAt_append, Bool.and_eq_true] at hseq
  rw [seqSize_append] at hend
  obtain ⟨hL, hA⟩ := hseq
  refine loadLe32_run_r hb0 (by decide) (by decide) (by decide) (by omega) hL ho hpc
    (p := c.scalar) (by rw [X25519Mem.toReg1]; exact r1)
    (loadLe32_reads hi (Or.inl ⟨rfl, rfl⟩) (by rw [X25519Mem.toReg1]; exact r1))
    (hPc _ _ (by omega) (by omega)) fun t1 pc1 m1 o1 v1 => ?_
  have hw : (t1.regs 4).toNat = X25519Decode.leWord c.scalarB i := by
    rw [X25519Mem.toReg4] at v1; rw [v1]; exact load_word hv.scalarS fr hi
  have ho1 : (off + seqSize (loadLe32 4 3 1 (4 * i))) % 2 = 0 := by
    have := seqSize_even' (loadLe32 4 3 1 (4 * i)); omega
  have o1' : ∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 15 → t1.regs r = s.regs r := fun r h3 h4 h15 =>
    o1 r (by rw [X25519Mem.toReg4]; exact h4) (by rw [X25519Mem.toReg3]; exact h3) fun e => h15 (Fin.ext e)
  have sp1 : (execAll (adjK i) t1).regs 13 = E c := by
    rw [adjK_other _ _ (by decide) (by decide) (by decide), o1' 13 (by decide) (by decide) (by decide), sp]
  refine ReachR.blockRuns hb0 _ _ pc1 ho1 hA (by rw [List.all_append, adjK_falls]; rfl)
    (R := fun t => t.regs 13 = E c ∧ (∀ r : Reg, r ≠ 15 → t.regs r = (execAll (adjK i) t1).regs r) ∧
      FrameOk (E c) NW (mP c) (upd F (sK / 4 + i) [(execAll (adjK i) t1).regs 4]) t.mem)
    (Runs.append (Runs.reg (Q := fun u => u = execAll (adjK i) t1) (adjK_reg i).1 (adjK_reg i).2 rfl)
      fun u hu => ?_) (blockReads_noRd _ _ _ (by rw [List.all_append, all_noRd (adjK_reg i).1]; rfl))
    (hPc _ _ (by omega) (by omega)) fun t pct ⟨spt, ot, frt⟩ => ?_
  · subst hu
    exact strE hv hWr _ fr (by rw [execAll_mem _ _ (adjK_reg i).2, m1]) 4 (k := sK / 4 + i) (is := [])
      (by simp only [sK, NW, LFRAME]; omega) sp1 (by rw [X25519Mem.toReg4])
      fun t spt frt ot => ⟨accAll_nil _ _, spt, ot, frt⟩
  · refine cont t _ ?_ ?_ spt ?_ frt
    · rw [seqSize_append, ← Nat.add_assoc]; exact pct
    · rw [adjK_val, hw, adjKv_words c hi]
    · intro r h3 h4 h15
      rw [ot r h15, adjK_other _ _ h3 h4 h15, o1' r h3 h4 h15]

/-- Point word `i`: load, mask bit 255 (word 7), store at `sX1/4 + i` and `sX3/4 + i`. -/
theorem pointWord_w {i : Nat} (hi : i < 8) {off : Nat} {s : State} {F : Nat → Word} {Q : State → Prop}
    (hseq : seqAt B off (pointWord i) = true) (ho : off % 2 = 0)
    (hend : off + seqSize (pointWord i) ≤ oLadder) (hlo : Artifacts.Release.x25519 ≤ off)
    (hpc : s.pc = c.base + BitVec.ofNat 32 off) (sp : s.regs 13 = E c) (r2 : s.regs 2 = c.point)
    (fr : FrameOk (E c) NW (mP c) F s.mem)
    (cont : ∀ (t : State) (v : Word), t.pc = c.base + BitVec.ofNat 32 (off + seqSize (pointWord i)) →
      v.toNat = (uWords c).getD i 0 → t.regs 13 = E c →
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 15 → t.regs r = s.regs r) →
      FrameOk (E c) NW (mP c) (upd (upd F (sX1 / 4 + i) [v]) (sX3 / 4 + i) [v]) t.mem →
      ReachR c.base Pc Wr (InpR c) t Q) :
    ReachR c.base Pc Wr (InpR c) s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  rw [pointWord_eq] at hseq hend cont
  rw [seqAt_append, Bool.and_eq_true] at hseq
  rw [seqSize_append] at hend
  obtain ⟨hL, hA⟩ := hseq
  refine loadLe32_run_r hb0 (by decide) (by decide) (by decide) (by omega) hL ho hpc
    (p := c.point) (by rw [X25519Mem.toReg2]; exact r2)
    (loadLe32_reads hi (Or.inr ⟨rfl, rfl⟩) (by rw [X25519Mem.toReg2]; exact r2))
    (hPc _ _ (by omega) (by omega)) fun t1 pc1 m1 o1 v1 => ?_
  have hw : (t1.regs 4).toNat = X25519Decode.leWord c.pointB i := by
    rw [X25519Mem.toReg4] at v1; rw [v1]; exact load_word hv.pointS fr hi
  have ho1 : (off + seqSize (loadLe32 4 3 2 (4 * i))) % 2 = 0 := by
    have := seqSize_even' (loadLe32 4 3 2 (4 * i)); omega
  have o1' : ∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 15 → t1.regs r = s.regs r := fun r h3 h4 h15 =>
    o1 r (by rw [X25519Mem.toReg4]; exact h4) (by rw [X25519Mem.toReg3]; exact h3) fun e => h15 (Fin.ext e)
  have sp1 : (execAll (adjU i) t1).regs 13 = E c := by
    rw [adjU_other _ _ (by decide) (by decide), o1' 13 (by decide) (by decide) (by decide), sp]
  refine ReachR.blockRuns hb0 _ _ pc1 ho1 hA (by rw [List.all_append, adjU_falls]; rfl)
    (R := fun t => t.regs 13 = E c ∧ (∀ r : Reg, r ≠ 15 → t.regs r = (execAll (adjU i) t1).regs r) ∧
      FrameOk (E c) NW (mP c) (upd (upd F (sX1 / 4 + i) [(execAll (adjU i) t1).regs 4]) (sX3 / 4 + i)
        [(execAll (adjU i) t1).regs 4]) t.mem)
    (Runs.append (Runs.reg (Q := fun u => u = execAll (adjU i) t1) (adjU_reg i).1 (adjU_reg i).2 rfl)
      fun u hu => ?_) (blockReads_noRd _ _ _ (by rw [List.all_append, all_noRd (adjU_reg i).1]; rfl))
    (hPc _ _ (by omega) (by omega)) fun t pct ⟨spt, ot, frt⟩ => ?_
  · subst hu
    refine strE hv hWr _ fr (by rw [execAll_mem _ _ (adjU_reg i).2, m1]) 4 (k := sX1 / 4 + i)
      (by simp only [sX1, NW, LFRAME]; omega) sp1 (by rw [X25519Mem.toReg4])
      fun t2 sp2 fr2 o2 => ?_
    exact strE hv hWr _ fr2 rfl 4 (k := sX3 / 4 + i) (is := [])
      (by simp only [sX3, NW, LFRAME]; omega) sp2 (by rw [X25519Mem.toReg4, o2 4 (by decide)])
      fun t spt frt ot => ⟨accAll_nil _ _, spt, fun r h15 => by show t.regs r = _; rw [ot r h15, o2 r h15], frt⟩
  · refine cont t _ ?_ ?_ spt ?_ frt
    · rw [seqSize_append, ← Nat.add_assoc]; exact pct
    · rw [adjU_val, hw, adjUv_words c hi]
    · intro r h3 h4 h15
      rw [ot r h15, adjU_other _ _ h4 h15, o1' r h3 h4 h15]

/-! ## The two loops -/

/-- Before scalar word `i`: the words below `i` are stored, every other slot is as in `F1`. -/
def IK (c : X25519.Ctx) (F1 : Nat → Word) (i : Nat) (s : State) : Prop :=
  s.regs 13 = E c ∧ s.regs 1 = c.scalar ∧ s.regs 2 = c.point ∧
    ∃ F, FrameOk (E c) NW (mP c) F s.mem ∧ (∀ j < i, (F (sK / 4 + j)).toNat = (kWords c).getD j 0) ∧
      ∀ x, (x < sK / 4 ∨ sK / 4 + i ≤ x) → F x = F1 x

/-- Before point word `i`: the words below `i` are stored twice, every other slot is as in `F2`. -/
def IU (c : X25519.Ctx) (F2 : Nat → Word) (i : Nat) (s : State) : Prop :=
  s.regs 13 = E c ∧ s.regs 2 = c.point ∧
    ∃ F, FrameOk (E c) NW (mP c) F s.mem ∧
      (∀ j < i, (F (sX1 / 4 + j)).toNat = (uWords c).getD j 0 ∧ (F (sX3 / 4 + j)).toNat = (uWords c).getD j 0) ∧
      ∀ x, (x < sX1 / 4 ∨ sX1 / 4 + i ≤ x) → (x < sX3 / 4 ∨ sX3 / 4 + i ≤ x) → F x = F2 x

theorem scalar_w {off0 : Nat} (hseq : seqAt B off0 (words scalarWord) = true) (ho : off0 % 2 = 0)
    (hend : off0 + seqSize (words scalarWord) ≤ oLadder) (hlo : Artifacts.Release.x25519 ≤ off0) {F1 : Nat → Word} {Q : State → Prop}
    (k : ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (off0 + seqSize (words scalarWord)) → IK c F1 8 t →
      ReachR c.base Pc Wr (InpR c) t Q)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off0) (hs : IK c F1 0 s) :
    ReachR c.base Pc Wr (InpR c) s Q := by
  refine words_loop scalarWord off0 (IK c F1) (fun i hi s hpc ⟨sp, r1, r2, F, fr, hk, hF⟩ kk => ?_) k s hpc hs
  obtain ⟨hw, he⟩ := word_at scalarWord hi hseq
  have hsk : sK / 4 = 72 := rfl
  refine scalarWord_w hv hWr hPc hi hw (by have := seqSize_even' ((List.range i).flatMap scalarWord); omega)
    (by omega) (by omega) hpc sp r1 fr fun t v pct vv spt ot frt => kk t ?_ ⟨spt, ?_, ?_, _, frt, fun j hj => ?_, fun x hx => ?_⟩
  · rw [words_succ, seqSize_append, ← Nat.add_assoc]; exact pct
  · rw [ot 1 (by decide) (by decide) (by decide)]; exact r1
  · rw [ot 2 (by decide) (by decide) (by decide)]; exact r2
  · by_cases e : j = i
    · subst e; rw [upd1_eq]; exact vv
    · rw [upd1_ne _ _ (by omega)]; exact hk j (by omega)
  · rw [upd1_ne _ _ (by omega)]; exact hF x (by omega)

theorem point_w {off0 : Nat} (hseq : seqAt B off0 (words pointWord) = true) (ho : off0 % 2 = 0)
    (hend : off0 + seqSize (words pointWord) ≤ oLadder) (hlo : Artifacts.Release.x25519 ≤ off0) {F2 : Nat → Word} {Q : State → Prop}
    (k : ∀ t : State, t.pc = c.base + BitVec.ofNat 32 (off0 + seqSize (words pointWord)) → IU c F2 8 t →
      ReachR c.base Pc Wr (InpR c) t Q)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off0) (hs : IU c F2 0 s) :
    ReachR c.base Pc Wr (InpR c) s Q := by
  refine words_loop pointWord off0 (IU c F2) (fun i hi s hpc ⟨sp, r2, F, fr, hk, hF⟩ kk => ?_) k s hpc hs
  obtain ⟨hw, he⟩ := word_at pointWord hi hseq
  have hx1 : sX1 / 4 = 0 := rfl
  have hx3 : sX3 / 4 = 24 := rfl
  refine pointWord_w hv hWr hPc hi hw (by have := seqSize_even' ((List.range i).flatMap pointWord); omega)
    (by omega) (by omega) hpc sp r2 fr fun t v pct vv spt ot frt => kk t ?_ ⟨spt, ?_, _, frt, fun j hj => ?_, fun x h1 h3 => ?_⟩
  · rw [words_succ, seqSize_append, ← Nat.add_assoc]; exact pct
  · rw [ot 2 (by decide) (by decide) (by decide)]; exact r2
  · by_cases e : j = i
    · subst e
      rw [upd1_ne _ _ (by omega), upd1_eq, upd1_eq]; exact ⟨vv, vv⟩
    · rw [upd1_ne _ _ (by omega), upd1_ne _ _ (by omega), upd1_ne _ _ (by omega), upd1_ne _ _ (by omega)]
      exact hk j (by omega)
  · rw [upd1_ne _ _ (by omega), upd1_ne _ _ (by omega)]; exact hF x (by omega) (by omega)

end

end M0Crypto.Release.X25519Prologue
