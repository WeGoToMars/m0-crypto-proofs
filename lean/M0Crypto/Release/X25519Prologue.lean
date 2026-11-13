import M0Crypto.Release.X25519PrologueWords

set_option linter.unusedSimpArgs false

/-!
The prologue of `m0c_x25519` (plan `x25519-proofs.md`, phase 9, step 2).

`prologue_w`: from an entry state satisfying `X25519.Pre c s`, the segment
`X25519EntryCode.prologue` (register save, scalar words, point words, initial ladder state)
runs to `c.base + oLadder` and writes only the stack window (through the first disjunct of
`X25519.WrOk`). The state there satisfies `PrologueOut c`.

The code bytes come from `entry_at` through `entryList` and `seqAt_append`; no segment is
checked against the bytes again.
-/

namespace M0Crypto.Release.X25519Prologue
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region B)
open M0Crypto.Release.Frame (Disj InFrame)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Val (val Words)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Op (Body)

/-! ## The state at the ladder

Choice of value statements, for the ladder proof (`X25519Ladder`, `X25519Decode`):

* scalar: word `i` of the frame at `sK + 4 i` has value `(kWords c).getD i 0`, with
  `val (kWords c) = decodeScalar25519 c.scalarB` (`kWords_val`), `Words (kWords c)` and length 8
  (`kWords_words`, `kWords_length`). The ladder reads word `t / 32` at `sK + 4 (t / 32)`
  (`word_index`), and `scalar_bit` turns bit `t % 32` of that word into bit `t` of
  `val (kWords c)`.
* u-coordinate: `feVal` at `sX1` and at `sX3` equals `decodeUCoordinate c.pointB` (exact value,
  bit 255 masked; `uWords_val`, through `decodeU_val`).
* `X2 = 1`, `Z2 = 0`, `Z3 = 1` as `feVal`; `swap = 0`, `t = 254`, `out = c.out` as words.
* saved registers: word `j` at `saveLo c + 4 j` (`saveLo c = sp0 - SAVED`) is `(savedList c)[j]`,
  that is `r8, r9, r10, r11` at `sp0 - 36 .. sp0 - 24` and `r4, r5, r6, r7, lr` at
  `sp0 - 20 .. sp0 - 4` (entry values `c.regs0`).
-/

/-- The state at `c.base + oLadder`. -/
structure PrologueOut (c : X25519.Ctx) (t : State) : Prop where
  /-- SP = `E c`; later segments take `m1 := t.mem`. -/
  body : Body c t.mem t
  /-- Outside the stack window the memory is the entry memory. -/
  outside : ∀ y, ¬ Region c.fp X25519.stackBytes y → t.mem y = c.m0 y
  saved : ∀ j (hj : j < (savedList c).length),
    read32 t.mem (saveLo c + BitVec.ofNat 32 (4 * j)) = (savedList c)[j]
  scalar : ∀ i < 8, (read32 t.mem (E c + BitVec.ofNat 32 (sK + 4 * i))).toNat = (kWords c).getD i 0
  x1 : feVal t.mem (E c + BitVec.ofNat 32 sX1) = Spec.X25519.decodeUCoordinate c.pointB
  x3 : feVal t.mem (E c + BitVec.ofNat 32 sX3) = Spec.X25519.decodeUCoordinate c.pointB
  x2 : feVal t.mem (E c + BitVec.ofNat 32 sX2) = 1
  z2 : feVal t.mem (E c + BitVec.ofNat 32 sZ2) = 0
  z3 : feVal t.mem (E c + BitVec.ofNat 32 sZ3) = 1
  swap : read32 t.mem (E c + BitVec.ofNat 32 lvSwap) = 0
  tctr : read32 t.mem (E c + BitVec.ofNat 32 lvT) = 254
  out : read32 t.mem (E c + BitVec.ofNat 32 lvOut) = c.out

theorem kWords_length (c : X25519.Ctx) : (kWords c).length = 8 := rfl

theorem leWord_lt (bs : List X25519Decode.Byte) (i : Nat) : X25519Decode.leWord bs i < 2 ^ 32 := by
  unfold X25519Decode.leWord
  have := (bs.getD (4 * i) 0).isLt; have := (bs.getD (4 * i + 1) 0).isLt
  have := (bs.getD (4 * i + 2) 0).isLt; have := (bs.getD (4 * i + 3) 0).isLt
  omega

theorem kWords_words (c : X25519.Ctx) : Words (kWords c) := by
  intro w hw
  simp only [kWords, X25519Decode.words, List.mem_cons, List.not_mem_nil, or_false] at hw
  have h := leWord_lt c.scalarB
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := h 0; have := Nat.div_mul_le_self (X25519Decode.leWord c.scalarB 0) 8; omega
  all_goals first | exact h _ | (have := Nat.mod_lt (X25519Decode.leWord c.scalarB 7) (show 0 < 2 ^ 30 by decide); omega)

/-! ## The frame after `initState` -/

theorem initF_keep (F : Nat → Word) {x : Nat} (h1 : x < sX2 / 4 ∨ sX2 / 4 + 16 ≤ x)
    (h2 : x < sZ3 / 4 ∨ sZ3 / 4 + 8 ≤ x) (h3 : x ≠ lvSwap / 4) (h4 : x ≠ lvT / 4) : initF F x = F x := by
  obtain ⟨-, a2, -, -, a5, -, a7, a8, -⟩ := X25519Layout.lay
  simp only [initF, upd, List.length_cons, List.length_nil]
  repeat' split
  all_goals first | rfl | omega

theorem initF_x2 (F : Nat → Word) {j : Nat} (hj : j < 8) :
    (initF F (sX2 / 4 + j)).toNat = [1, 0, 0, 0, 0, 0, 0, 0].getD j 0 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [initF, upd, sX2, sZ3, lvSwap, lvT]

theorem initF_z2 (F : Nat → Word) {j : Nat} (hj : j < 8) :
    (initF F (sZ2 / 4 + j)).toNat = [0, 0, 0, 0, 0, 0, 0, 0].getD j 0 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [initF, upd, sX2, sZ2, sZ3, lvSwap, lvT]

theorem initF_z3 (F : Nat → Word) {j : Nat} (hj : j < 8) :
    (initF F (sZ3 / 4 + j)).toNat = [1, 0, 0, 0, 0, 0, 0, 0].getD j 0 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [initF, upd, sX2, sZ3, lvSwap, lvT]

theorem initF_swap (F : Nat → Word) : initF F (lvSwap / 4) = 0 := by
  simp [initF, upd, sX2, sZ3, lvSwap, lvT]

theorem initF_t (F : Nat → Word) : initF F (lvT / 4) = 254 := by
  simp [initF, upd, lvT]

section
variable {c : X25519.Ctx} {m0 : Mem}

theorem frame_read {F : Nat → Word} {m : Mem} (fr : FrameOk (E c) NW m0 F m) {o : Nat} (ho : o % 4 = 0)
    (hk : o / 4 < NW) : read32 m (E c + BitVec.ofNat 32 o) = F (o / 4) := by
  rw [← fr.slots _ hk, slot, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ho)]

theorem frame_feVal {F : Nat → Word} {m : Mem} (fr : FrameOk (E c) NW m0 F m) {b : Nat} (hb : b % 4 = 0)
    (hn : b / 4 + 8 ≤ NW) (ws : List Nat) (hl : ws.length = 8)
    (h : ∀ j < 8, (F (b / 4 + j)).toNat = ws.getD j 0) : feVal m (E c + BitVec.ofNat 32 b) = val ws :=
  feVal_words _ _ ws hl fun j hj => by
    rw [ofNat_add_assoc, frame_read fr (by omega) (by omega), show (b + 4 * j) / 4 = b / 4 + j by omega]
    exact h j hj

end

/-! ## The prologue -/

/-- The prologue: `Pre` to `PrologueOut` at `c.base + oLadder`, writing only the stack window. -/
theorem prologue_w {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s) {Wr : Word → Prop}
    (hWr : ∀ y, X25519.WrOk c y → Wr y) {Pc : Word → Prop}
    (hPc : ∀ o n, Artifacts.Release.x25519 ≤ o → o + n ≤ oLadder → InRegion Pc c.base o n)
    {Q : State → Prop}
    (k : ∀ t : State, t.pc = c.base + BitVec.ofNat 32 oLadder → PrologueOut c t →
      ReachR c.base Pc Wr (InpR c) t Q) :
    ReachR c.base Pc Wr (InpR c) s Q := by
  have hv := hp.valid
  have en := hp.entry
  have hW : ∀ y, Region c.fp X25519.stackBytes y → Wr y := fun y h => hWr y (Or.inl h)
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨rest, hE⟩ : ∃ rest, entryList = prologue ++ rest := ⟨_, by simp only [entryList, List.append_assoc]; exact rfl⟩
  have hseq := entry_at
  rw [hE, seqAt_append, Bool.and_eq_true] at hseq
  have hsz := entry_size
  rw [hE, seqSize_append] at hsz
  have hP := hseq.1
  simp only [prologue, seqAt_append, seqSize_append, Bool.and_eq_true] at hP hsz
  obtain ⟨⟨⟨hS, hK⟩, hU⟩, hI⟩ := hP
  have hx : Artifacts.Release.x25519 % 2 = 0 := by decide
  have e1 := seqSize_even' saveRegs
  have e2 := seqSize_even' (words scalarWord)
  have e3 := seqSize_even' (words pointWord)
  have hpc : s.pc = c.base + BitVec.ofNat 32 Artifacts.Release.x25519 := by
    show s.regs 15 = _; rw [en.regs, en.pc]
  have hOL : oLadder = Artifacts.Release.x25519 + (seqSize saveRegs + seqSize (words scalarWord) +
      seqSize (words pointWord) + seqSize initState) := by
    simp only [oLadder, prologue, seqSize_append]
  refine ReachR.blockRuns hb0 saveRegs _ hpc hx hS (by decide) (saveRegs_run hv hW s en.regs en.mem en.sp)
    (blockReads_noRd _ _ _ rfl) (hPc _ _ (Nat.le_refl _) (by omega)) fun t1 pc1 ⟨sp1, fr1, r11, r21⟩ => ?_
  refine scalar_w hv hW hPc hK (by omega) (by omega) (by omega) (F1 := upd (F0 c) (lvOut / 4) [c.regs0 0]) ?_ t1 pc1
    ⟨sp1, by rw [r11, en.r1], by rw [r21, en.r2], _, fr1, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  rintro t2 pc2 ⟨sp2, -, r22, F2, fr2, hk2, hF2⟩
  refine point_w hv hW hPc hU (by omega) (by omega) (by omega) (F2 := F2) ?_ t2 pc2
    ⟨sp2, r22, F2, fr2, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  rintro t3 pc3 ⟨sp3, -, F3, fr3, hu3, hF3⟩
  refine ReachR.blockRuns hb0 initState _ pc3 (by omega) hI (by decide) (initState_run hv hW t3 sp3 fr3)
    (blockReads_noRd _ _ _ rfl) (hPc _ _ (by omega) (by omega)) fun t pct ⟨spt, frt⟩ => k t ?_ ?_
  · rw [pct, oLadder, prologue]; simp only [seqSize_append, Nat.add_assoc]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := X25519Layout.lay
  have a11 : NW = LFRAME / 4 := rfl
  -- slots the initial state does not write, through both loops
  have keep : ∀ x, x < NW → (x < sX2 / 4 ∨ sX2 / 4 + 16 ≤ x) → (x < sZ3 / 4 ∨ sZ3 / 4 + 8 ≤ x) →
      x ≠ lvSwap / 4 → x ≠ lvT / 4 → read32 t.mem (E c + BitVec.ofNat 32 (4 * x)) = F3 x := by
    intro x hx h1 h2 h3 h4
    rw [frame_read frt (by omega) (by omega), show 4 * x / 4 = x by omega, initF_keep F3 h1 h2 h3 h4]
  refine ⟨⟨spt, fun _ _ => rfl⟩, fun y hy => ?_, fun j hj => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frt.out y fun h => hy (frame_inwin h), mP_out hy]
  · have h9 : (savedList c).length = 9 := rfl
    refine (Frame.read32_congr (m := mP c) fun q hq => ?_).trans (mP_saved hv hj)
    rw [ofNat_add_assoc]
    exact frt.out _ (saved_notFrame hv (by simp only [SAVED]; omega))
  · rw [show sK + 4 * i = 4 * (sK / 4 + i) by omega, keep _ (by omega) (by omega) (by omega) (by omega) (by omega),
      hF3 _ (by omega) (by omega)]
    exact hk2 i hi
  · rw [frame_feVal frt (by omega) (by omega) (uWords c) rfl fun j hj => ?_, uWords_val]
    rw [initF_keep F3 (by omega) (by omega) (by omega) (by omega)]; exact (hu3 j hj).1
  · rw [frame_feVal frt (by omega) (by omega) (uWords c) rfl fun j hj => ?_, uWords_val]
    rw [initF_keep F3 (by omega) (by omega) (by omega) (by omega)]; exact (hu3 j hj).2
  · rw [frame_feVal frt (by omega) (by omega) _ rfl fun j hj => initF_x2 F3 hj]; rfl
  · rw [frame_feVal frt (by omega) (by omega) _ rfl fun j hj => initF_z2 F3 hj]; rfl
  · rw [frame_feVal frt (by omega) (by omega) _ rfl fun j hj => initF_z3 F3 hj]; rfl
  · rw [frame_read frt (by omega) (by omega), initF_swap]
  · rw [frame_read frt (by omega) (by omega), initF_t]
  · rw [show lvOut = 4 * (lvOut / 4) by omega, keep _ (by omega) (by omega) (by omega) (by omega) (by omega),
      hF3 _ (by omega) (by omega), hF2 _ (by omega), upd1_eq, en.r0]

end M0Crypto.Release.X25519Prologue
