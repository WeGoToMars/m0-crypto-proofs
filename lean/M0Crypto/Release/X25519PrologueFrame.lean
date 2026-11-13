import M0Crypto.Release.X25519PrologueBase

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
The memory side of the prologue of `m0c_x25519` (plan `x25519-proofs.md`, phase 9, step 2).

* `push_run`, `stm_run`: `push {r4-r7[, lr]}` and `stm r3!, {r4-r7}` as `Runs`.
* `str_step`, `stm_step`: stores into a `FrameOk` frame of any size, in continuation form.
* `saveRegs_run`: the register save, `sub sp` and `str r0, [sp, #LV_OUT]`. The pushed words
  are `savedList c` at `saveLo c = sp0 - SAVED` (`mP c` is the memory after the pushes).
* `initState_run`: `X2 = 1`, `Z2 = 0`, `Z3 = 1`, `swap = 0`, `t = 254`, as the frame update
  `initF`.

Every write is to the stack window (`Region c.fp stackBytes`), so the write set is any `Wr`
containing it.
-/

namespace M0Crypto.Release.X25519Prologue
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region)
open M0Crypto.Release.Frame (Disj InFrame)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519FeSteps (cons one)

/-! ## Single instructions -/

section
variable {Wr : Word → Prop}

theorem toNat_sub_al (a : Word) (n : Nat) (ha : a.toNat % 4 = 0) (hn : n % 4 = 0) (hn' : n < 2 ^ 32) :
    (a - BitVec.ofNat 32 n).toNat % 4 = 0 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn']
  have := a.isLt
  omega

theorem push_run (s : State) (lr : Bool) (hsp : s.sp.toNat % 4 = 0)
    (hW : ∀ i < 4 + lr.toNat, ∀ q < 4,
      Wr (s.sp - BitVec.ofNat 32 (4 * (4 + lr.toNat)) + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    Runs (AccOk Wr) [.push 0xf0 lr] s fun t =>
      t.mem = storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * (4 + lr.toNat)))
        ([s.regs 4, s.regs 5, s.regs 6, s.regs 7] ++ if lr then [s.regs 14] else []) ∧
      t.regs 13 = s.sp - BitVec.ofNat 32 (4 * (4 + lr.toNat)) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 13 → t.regs r = s.regs r := by
  have hl : lr.toNat ≤ 1 := by cases lr <;> decide
  refine ⟨accAll_cons (fun a ha => ?_) (accAll_nil _ _), ?_⟩
  · simp only [Instr.accesses, Frame.bitCount_f0] at ha
    exact wordAccesses_ok (toNat_sub_al _ _ hsp (by omega) (by omega)) (fun _ i hi q hq => hW i hi q hq) a ha
  · simp only [execAll, Instr.next, Instr.exec, Frame.bitCount_f0, Frame.listRegs_f0]
    refine ⟨?_, ?_, fun r h15 h13 => ?_⟩
    · simp [State.setReg, State.reg, X25519Mem.toReg4, X25519Mem.toReg5, X25519Mem.toReg6,
        X25519Mem.toReg7]
    · simp [State.setReg]
    · simp [State.setReg, h15, h13]

theorem stm_run (s : State) (hal : (s.regs 3).toNat % 4 = 0)
    (hW : ∀ i < 4, ∀ q < 4, Wr (s.regs 3 + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    Runs (AccOk Wr) [.stm 3 0xf0] s fun t =>
      t.mem = storeWords s.mem (s.regs 3) [s.regs 4, s.regs 5, s.regs 6, s.regs 7] ∧
      t.regs 3 = s.regs 3 + BitVec.ofNat 32 (4 * 4) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 3 → t.regs r = s.regs r := by
  refine ⟨accAll_cons (fun a ha => ?_) (accAll_nil _ _), ?_⟩
  · simp only [Instr.accesses, Frame.bitCount_f0, State.reg, X25519Mem.toReg3] at ha
    exact wordAccesses_ok hal (fun _ i hi q hq => hW i hi q hq) a ha
  · simp only [execAll]
    refine ⟨?_, ?_, fun r h15 h3 => ?_⟩
    · rw [X25519Mem.mem_stm]
      simp [Frame.listRegs_f0, Frame.listRegs_240, State.reg, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5,
        X25519Mem.toReg6, X25519Mem.toReg7]
    · rw [X25519Mem.regs_stm _ _ _ _ (by decide)]
      simp [X25519Mem.toReg3, Frame.bitCount_f0, show bitCount 240#8 = 4 from by decide, State.reg]
    · rw [X25519Mem.regs_stm _ _ _ _ h15]
      simp [X25519Mem.toReg3, h3]

variable {is : List Instr} {Q : State → Prop}

theorem str_step {P : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} (s : State) (d : LowReg) {k : Nat}
    (hk : k < n) (hk' : k < 256) (sp : s.regs 13 = P) (fr : FrameOk P n m0 F s.mem)
    (hP : P.toNat % 4 = 0) (hW : ∀ q < 4, Wr (slot P k + BitVec.ofNat 32 q))
    (cont : ∀ t : State, t.regs 13 = P → FrameOk P n m0 (upd F k [s.reg d]) t.mem →
      (∀ r : Reg, r ≠ 15 → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.strSp d (BitVec.ofNat 8 k) :: is) s Q := by
  have sp' : s.sp = P := sp
  refine cons (X25519FeCommon.strSp_run s d hk' (by rw [sp']; exact hP) (by rw [sp']; exact hW))
    fun t ⟨tm, to⟩ => cont t ?_ ?_ to
  · rw [to 13 (by decide)]; exact sp
  · rw [tm, sp']; exact fr.write hk _

theorem stm_step {P : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} (s : State) {k : Nat}
    {v0 v1 v2 v3 : Word} (hk : k + 4 ≤ n) (sp : s.regs 13 = P) (fr : FrameOk P n m0 F s.mem)
    (hP : P.toNat % 4 = 0) (h3 : s.regs 3 = slot P k) (h4 : s.regs 4 = v0) (h5 : s.regs 5 = v1)
    (h6 : s.regs 6 = v2) (h7 : s.regs 7 = v3)
    (hW : ∀ i < 4, ∀ q < 4, Wr (slot P (k + i) + BitVec.ofNat 32 q))
    (cont : ∀ t : State, t.regs 13 = P → FrameOk P n m0 (upd F k [v0, v1, v2, v3]) t.mem →
      t.regs 3 = slot P (k + 4) → (∀ r : Reg, r ≠ 15 → r ≠ 3 → t.regs r = s.regs r) →
      Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.stm 3 0xf0 :: is) s Q := by
  have hal : (s.regs 3).toNat % 4 = 0 := by
    rw [h3]; exact word_add_aligned hP (by omega)
  refine cons (stm_run s hal fun i hi q hq => ?_) fun t ⟨tm, t3, to⟩ => cont t ?_ ?_ ?_ to
  · rw [h3, X25519FeCommon.slot_add]; exact hW i hi q hq
  · rw [to 13 (by decide) (by decide)]; exact sp
  · rw [tm, h3, h4, h5, h6, h7]; exact fr.storeWords [v0, v1, v2, v3] (by simpa using hk)
  · rw [t3, h3, X25519FeCommon.slot_add]

end

/-! ## The frame of the entry -/

/-- Words of the entry frame. -/
abbrev NW : Nat := LFRAME / 4

/-- Lowest saved word: `sp0 - SAVED`. -/
def saveLo (c : X25519.Ctx) : Word := c.sp0 - BitVec.ofNat 32 SAVED

/-- The words the two pushes save, from `saveLo c` up: r8-r11, then r4-r7 and lr. -/
def savedList (c : X25519.Ctx) : List Word :=
  [c.regs0 8, c.regs0 9, c.regs0 10, c.regs0 11, c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7,
    c.regs0 14]

/-- Memory after the two pushes. -/
def mP (c : X25519.Ctx) : Mem :=
  storeWords (storeWords c.m0 (saveLo c + BitVec.ofNat 32 (4 * 4))
    [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14]) (saveLo c)
    [c.regs0 8, c.regs0 9, c.regs0 10, c.regs0 11]

section
variable {c : X25519.Ctx} (hv : X25519.Valid c)
include hv

omit hv in
theorem E_eq : E c = c.fp + BitVec.ofNat 32 CALLEE := by
  simp only [E, X25519.Ctx.fp, SAVED, LFRAME, CALLEE, X25519.stackBytes]; bv_omega

omit hv in
theorem saveLo_eq : saveLo c = c.fp + BitVec.ofNat 32 (CALLEE + LFRAME) := by
  simp only [saveLo, X25519.Ctx.fp, SAVED, LFRAME, CALLEE, X25519.stackBytes]; bv_omega

theorem E_al : (E c).toNat % 4 = 0 := by
  have := X25519Op.E_toNat hv; have := hv.sp4; have := hv.spLo
  simp only [SAVED, LFRAME, X25519.stackBytes] at *; omega

theorem fp_fits : c.fp.toNat + X25519.stackBytes ≤ 2 ^ 32 := by
  have := X25519Op.fp_toNat hv; have := hv.spLo; have := c.sp0.isLt
  simp only [X25519.stackBytes] at *; omega

omit hv in
/-- Byte `o` of the window. -/
theorem win (o : Nat) (ho : o < X25519.stackBytes) : Region c.fp X25519.stackBytes (c.fp + BitVec.ofNat 32 o) :=
  Region.mk ho rfl

theorem frame_fits : (E c).toNat + 4 * NW ≤ 2 ^ 32 := by
  have := X25519Op.E_toNat hv; have := hv.spLo; have := c.sp0.isLt
  simp only [NW, SAVED, LFRAME, X25519.stackBytes] at *; omega

omit hv in
/-- Frame bytes are window bytes. -/
theorem frame_win {k q : Nat} (hk : k < NW) (hq : q < 4) :
    Region c.fp X25519.stackBytes (slot (E c) k + BitVec.ofNat 32 q) := by
  rw [slot_byte, E_eq (c := c), ofNat_add_assoc]
  exact win _ (by simp only [NW, LFRAME, CALLEE, X25519.stackBytes] at hk ⊢; omega)

omit hv in
theorem frame_inwin {y : Word} (h : InFrame (E c) NW y) : Region c.fp X25519.stackBytes y := by
  obtain ⟨o, ho, rfl⟩ := h
  rw [E_eq (c := c), ofNat_add_assoc]
  exact win _ (by simp only [NW, LFRAME, CALLEE, X25519.stackBytes] at ho ⊢; omega)

omit hv in
/-- Saved-register bytes are window bytes. -/
theorem saved_win {o : Nat} (ho : o < SAVED) : Region c.fp X25519.stackBytes (saveLo c + BitVec.ofNat 32 o) := by
  rw [saveLo_eq (c := c), ofNat_add_assoc]
  exact win _ (by simp only [SAVED, LFRAME, CALLEE, X25519.stackBytes] at ho ⊢; omega)

/-- Saved-register bytes are not frame bytes. -/
theorem saved_notFrame {o : Nat} (ho : o < SAVED) : ¬ InFrame (E c) NW (saveLo c + BitVec.ofNat 32 o) := by
  rintro ⟨p, hp, e⟩
  rw [saveLo_eq (c := c), E_eq (c := c), ofNat_add_assoc, ofNat_add_assoc] at e
  have := congrArg BitVec.toNat e
  have hf := fp_fits hv
  simp only [NW, SAVED, LFRAME, CALLEE, X25519.stackBytes] at *
  rw [Frame.toNat_add_ofNat _ _ (by omega), Frame.toNat_add_ofNat _ _ (by omega)] at this
  omega

omit hv in
/-- Outside the window, the pushes changed nothing. -/
theorem mP_out {y : Word} (hy : ¬ Region c.fp X25519.stackBytes y) : mP c y = c.m0 y := by
  unfold mP
  rw [storeWords_other, storeWords_other]
  · intro i k hi hk e
    rw [ofNat_add_assoc, ofNat_add_assoc] at e
    exact hy (e ▸ saved_win (by simp only [List.length_cons, List.length_nil, SAVED] at hi ⊢; omega))
  · intro i k hi hk e
    rw [ofNat_add_assoc] at e
    exact hy (e ▸ saved_win (by simp only [List.length_cons, List.length_nil, SAVED] at hi ⊢; omega))

/-- Saved word `j` of `mP`. -/
theorem mP_saved {j : Nat} (hj : j < (savedList c).length) :
    read32 (mP c) (saveLo c + BitVec.ofNat 32 (4 * j)) = (savedList c)[j] := by
  have hj9 : j < 9 := hj
  unfold mP
  by_cases h4 : j < 4
  · rw [Frame.read32_storeWords_same _ _ _ j (by simpa using h4) (by simp)]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [Frame.read32_congr (m := storeWords c.m0 (saveLo c + BitVec.ofNat 32 (4 * 4))
      [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])]
    · rw [show 4 * j = 4 * 4 + 4 * (j - 4) by omega, ← ofNat_add_assoc,
        Frame.read32_storeWords_same _ _ _ (j - 4) (by simp; omega) (by simp)]
      rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro q hq
      apply storeWords_other
      intro i p hi hp e
      rw [ofNat_add_assoc, ofNat_add_assoc, saveLo_eq (c := c), ofNat_add_assoc, ofNat_add_assoc] at e
      have := congrArg BitVec.toNat e
      have hf := fp_fits hv
      simp only [List.length_cons, List.length_nil] at hi
      simp only [SAVED, LFRAME, CALLEE, X25519.stackBytes] at *
      rw [Frame.toNat_add_ofNat _ _ (by omega), Frame.toNat_add_ofNat _ _ (by omega)] at this
      omega

end

/-! ## The register save -/

theorem push1_addr (c : X25519.Ctx) :
    c.sp0 - BitVec.ofNat 32 (4 * (4 + true.toNat)) = saveLo c + BitVec.ofNat 32 (4 * 4) := by
  simp only [saveLo, SAVED, Bool.toNat_true]; bv_omega

theorem push2_addr (c : X25519.Ctx) :
    saveLo c + BitVec.ofNat 32 (4 * 4) - BitVec.ofNat 32 (4 * (4 + false.toNat)) = saveLo c := by
  simp only [Bool.toNat_false]; bv_omega

theorem subSp_addr (c : X25519.Ctx) :
    saveLo c - BitVec.ofNat 32 ((BitVec.ofNat 7 (LFRAME / 4)).toNat * 4) = E c := by
  simp only [saveLo, E, SAVED, LFRAME]; bv_omega

/-- The frame right after the pushes: every word as in `mP`. -/
def F0 (c : X25519.Ctx) (i : Nat) : Word := read32 (mP c) (slot (E c) i)

section
variable {c : X25519.Ctx} {Wr : Word → Prop} (hv : X25519.Valid c)
  (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
include hWr

omit hv in
theorem frame_wr {k : Nat} (hk : k < NW) : ∀ q < 4, Wr (slot (E c) k + BitVec.ofNat 32 q) :=
  fun _ hq => hWr _ (frame_win hk hq)

include hv in
theorem saveRegs_run (s : State) (hr : s.regs = c.regs0) (hm : s.mem = c.m0) (h13 : c.regs0 13 = c.sp0) :
    Runs (AccOk Wr) saveRegs s fun t => t.regs 13 = E c ∧
      FrameOk (E c) NW (mP c) (upd (F0 c) (lvOut / 4) [c.regs0 0]) t.mem ∧
      t.regs 1 = c.regs0 1 ∧ t.regs 2 = c.regs0 2 := by
  have hsp : s.sp = c.sp0 := by show s.regs 13 = _; rw [hr, h13]
  unfold saveRegs
  refine cons (push_run s true (by rw [hsp]; exact hv.sp4) fun i hi q hq => hWr _ ?_)
    fun s1 ⟨m1, sp1, o1⟩ => ?_
  · rw [hsp, push1_addr]; simp only [ofNat_add_assoc]
    exact saved_win (by simp only [Bool.toNat_true, SAVED] at hi ⊢; omega)
  refine cons (one _ s1 rfl rfl) fun s2 e2 => ?_
  refine cons (one _ s2 rfl rfl) fun s3 e3 => ?_
  refine cons (one _ s3 rfl rfl) fun s4 e4 => ?_
  refine cons (one _ s4 rfl rfl) fun s5 e5 => ?_
  subst e2 e3 e4 e5
  have r5 : ∀ r : Reg, r ≠ 15 → r ≠ 13 → r.val < 4 ∨ 7 < r.val →
      ((Instr.movHi 7 11).next ((Instr.movHi 6 10).next ((Instr.movHi 5 9).next
        ((Instr.movHi 4 8).next s1)))).regs r = s.regs r := fun r h15 h13 hr => by
    have a4 : r ≠ 4 := fun e => by subst e; exact absurd hr (by decide)
    have a5 : r ≠ 5 := fun e => by subst e; exact absurd hr (by decide)
    have a6 : r ≠ 6 := fun e => by subst e; exact absurd hr (by decide)
    have a7 : r ≠ 7 := fun e => by subst e; exact absurd hr (by decide)
    simp [Instr.next, Instr.exec, State.setReg, h15, a4, a5, a6, a7, o1 r h15 h13]
  generalize hs5 : (Instr.movHi 7 11).next ((Instr.movHi 6 10).next ((Instr.movHi 5 9).next
    ((Instr.movHi 4 8).next s1))) = s5 at r5
  have v5 : s5.regs 4 = s.regs 8 ∧ s5.regs 5 = s.regs 9 ∧ s5.regs 6 = s.regs 10 ∧ s5.regs 7 = s.regs 11 ∧
      s5.mem = s1.mem ∧ s5.regs 13 = s1.regs 13 := by
    subst hs5
    simp [Instr.next, Instr.exec, State.setReg, o1 8 (by decide) (by decide), o1 9 (by decide) (by decide),
      o1 10 (by decide) (by decide), o1 11 (by decide) (by decide)]
  obtain ⟨v4, v5', v6, v7, vm, v13⟩ := v5
  have hsp5 : s5.sp = saveLo c + BitVec.ofNat 32 (4 * 4) := by
    show s5.regs 13 = _; rw [v13, sp1, hsp, push1_addr]
  refine cons (push_run s5 false (by
      rw [hsp5]; exact word_add_aligned (by rw [saveLo]; exact toNat_sub_al _ _ hv.sp4 (by decide) (by decide))
        (by omega)) fun i hi q hq => hWr _ ?_)
    fun s6 ⟨m6, sp6, o6⟩ => ?_
  · rw [hsp5, push2_addr]; simp only [ofNat_add_assoc]
    exact saved_win (by simp only [Bool.toNat_false, SAVED] at hi ⊢; omega)
  refine cons (one _ s6 rfl rfl) fun s7 e7 => ?_
  subst e7
  have sp7 : ((Instr.subSp (BitVec.ofNat 7 (LFRAME / 4))).next s6).regs 13 = E c := by
    rw [X25519FeSteps.regs_subSp _ _ _ (by decide), if_pos rfl, sp6, hsp5, push2_addr, subSp_addr]
  have m7 : ((Instr.subSp (BitVec.ofNat 7 (LFRAME / 4))).next s6).mem = mP c := by
    show s6.mem = _
    rw [m6, vm, m1, hsp5, push2_addr, hsp, push1_addr, hm, v4, v5', v6, v7, hr]
    rfl
  have o7 : ∀ r : Reg, r.val < 4 →
      ((Instr.subSp (BitVec.ofNat 7 (LFRAME / 4))).next s6).regs r = s.regs r := fun r hr4 => by
    have h15 : r ≠ 15 := fun e => by subst e; exact absurd hr4 (by decide)
    have h13 : r ≠ 13 := fun e => by subst e; exact absurd hr4 (by decide)
    rw [X25519FeSteps.regs_subSp _ _ _ h15, if_neg h13, o6 r h15 h13, r5 r h15 h13 (Or.inl hr4)]
  have fr0 : FrameOk (E c) NW (mP c) (F0 c) ((Instr.subSp (BitVec.ofNat 7 (LFRAME / 4))).next s6).mem := by
    rw [m7]; exact ⟨frame_fits hv, fun _ _ => rfl, fun _ _ => rfl⟩
  refine str_step _ 0 (k := lvOut / 4) (by simp only [NW, lvOut, LFRAME]; omega)
    (by simp only [lvOut]; omega) sp7 fr0 (E_al hv)
    (frame_wr hWr (by simp only [NW, lvOut, LFRAME]; omega)) fun t tsp tfr to => ?_
  refine ⟨accAll_nil _ _, tsp, ?_, ?_, ?_⟩
  · have e0 : ((Instr.subSp (BitVec.ofNat 7 (LFRAME / 4))).next s6).reg 0 = c.regs0 0 := by
      show _ = c.regs0 (LowReg.toReg 0)
      rw [← hr]; exact o7 _ (by decide)
    rw [e0] at tfr; exact tfr
  · show t.regs 1 = _; rw [to 1 (by decide), o7 1 (by decide), hr]
  · show t.regs 2 = _; rw [to 2 (by decide), o7 2 (by decide), hr]

end

/-! ## The initial ladder state -/

/-- The frame update of `initState`: `X2` and `Z2` (one `stm` run from `X2`), `Z3`, `swap`, `t`. -/
def initF (F : Nat → Word) : Nat → Word :=
  upd (upd (upd (upd (upd (upd (upd (upd F (sX2 / 4) [1, 0, 0, 0]) (sX2 / 4 + 4) [0, 0, 0, 0])
    (sX2 / 4 + 8) [0, 0, 0, 0]) (sX2 / 4 + 12) [0, 0, 0, 0]) (sZ3 / 4) [1, 0, 0, 0])
    (sZ3 / 4 + 4) [0, 0, 0, 0]) (lvSwap / 4) [0]) (lvT / 4) [254]

theorem regs_addRdSp' (s : State) (d : LowReg) (i : BitVec 8) :
    ((Instr.addRdSp d i).next s).regs d.toReg = s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) := by
  rw [X25519Mem.regs_addRdSp _ _ _ _ (toReg_ne_15 d), if_pos rfl]; rfl

theorem slot_sp (P : Word) (k : Nat) (hk : k < 256) : P + BitVec.ofNat 32 ((BitVec.ofNat 8 k).toNat * 4) = slot P k := by
  simp only [BitVec.toNat_ofNat, slot, Nat.mod_eq_of_lt hk, Nat.mul_comm]

theorem mov_val (n : Nat) (h : n < 256) : (BitVec.ofNat 8 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt h]

section
variable {c : X25519.Ctx} {Wr : Word → Prop} (hv : X25519.Valid c)
  (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
include hv hWr

theorem stmE (s : State) {F : Nat → Word} {m : Mem} (fr : FrameOk (E c) NW (mP c) F m) (hm : s.mem = m)
    {k : Nat} {v0 v1 v2 v3 : Word} {is : List Instr} {Q : State → Prop} (hk : k + 4 ≤ NW)
    (sp : s.regs 13 = E c) (h3 : s.regs 3 = slot (E c) k) (h4 : s.regs 4 = v0) (h5 : s.regs 5 = v1)
    (h6 : s.regs 6 = v2) (h7 : s.regs 7 = v3)
    (cont : ∀ t : State, t.regs 13 = E c → FrameOk (E c) NW (mP c) (upd F k [v0, v1, v2, v3]) t.mem →
      t.regs 3 = slot (E c) (k + 4) → (∀ r : Reg, r ≠ 15 → r ≠ 3 → t.regs r = s.regs r) →
      Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.stm 3 0xf0 :: is) s Q :=
  stm_step s hk sp (hm ▸ fr) (E_al hv) h3 h4 h5 h6 h7 (fun _ hi => frame_wr hWr (by omega)) cont

theorem strE (s : State) {F : Nat → Word} {m : Mem} (fr : FrameOk (E c) NW (mP c) F m) (hm : s.mem = m)
    (d : LowReg) {k : Nat} {v : Word} {is : List Instr} {Q : State → Prop} (hk : k < NW)
    (sp : s.regs 13 = E c) (hd : s.regs d.toReg = v)
    (cont : ∀ t : State, t.regs 13 = E c → FrameOk (E c) NW (mP c) (upd F k [v]) t.mem →
      (∀ r : Reg, r ≠ 15 → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.strSp d (BitVec.ofNat 8 k) :: is) s Q :=
  str_step s d hk (by simp only [NW, LFRAME] at hk; omega) sp (hm ▸ fr) (E_al hv) (frame_wr hWr hk)
    fun t a b o => cont t a (hd ▸ b) o

attribute [local simp] X25519Mem.toReg0 X25519Mem.toReg1 X25519Mem.toReg2 X25519Mem.toReg3
  X25519Mem.toReg4 X25519Mem.toReg5 X25519Mem.toReg6 X25519Mem.toReg7 in
theorem initState_run (s : State) {F : Nat → Word} (sp : s.regs 13 = E c)
    (fr : FrameOk (E c) NW (mP c) F s.mem) :
    Runs (AccOk Wr) initState s fun t => t.regs 13 = E c ∧ FrameOk (E c) NW (mP c) (initF F) t.mem := by
  have hal := E_al hv
  have hw : ∀ k, k + 4 ≤ NW → ∀ i < 4, ∀ q < 4, Wr (slot (E c) (k + i) + BitVec.ofNat 32 q) :=
    fun k hk i hi => frame_wr hWr (by omega)
  have hx2 : sX2 / 4 + 16 ≤ NW := by simp only [sX2, NW, LFRAME]; omega
  have hz3 : sZ3 / 4 + 8 ≤ NW := by simp only [sZ3, NW, LFRAME]; omega
  unfold initState setT
  simp only [List.cons_append, List.nil_append]
  refine cons (one _ s rfl rfl) fun s1 e1 => ?_
  refine cons (one _ s1 rfl rfl) fun s2 e2 => ?_
  refine cons (one _ s2 rfl rfl) fun s3 e3 => ?_
  refine cons (one _ s3 rfl rfl) fun s4 e4 => ?_
  refine cons (one _ s4 rfl rfl) fun s5 e5 => ?_
  subst e1 e2 e3 e4 e5
  have sx : sX2 / 4 < 256 := by simp only [sX2]; omega
  have sz : sZ3 / 4 < 256 := by simp only [sZ3]; omega
  -- `X2[0..3] = 1, 0, 0, 0`
  refine stm_step _ (P := E c) (n := NW) (m0 := mP c) (F := F) (k := sX2 / 4) (v0 := 1) (v1 := 0)
    (v2 := 0) (v3 := 0) (by omega) ?_ ?_ hal ?_ ?_ ?_ ?_ ?_ (hw _ (by omega)) fun t1 sp1 fr1 r31 o1 => ?_
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, sp]
  · simpa [Instr.next, Instr.exec, State.setReg, State.setNZ] using fr
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, sp, slot, Nat.mod_eq_of_lt sx, Nat.mul_comm]
  all_goals try (simp [Instr.next, Instr.exec, State.setReg, State.setNZ]; done)
  -- `X2[4..7] = 0`, `Z2 = 0`
  have z1 : ∀ r : Reg, r.val = 5 ∨ r.val = 6 ∨ r.val = 7 → t1.regs r = 0 := fun r hr => by
    have h15 : r ≠ 15 := fun e => by subst e; exact absurd hr (by decide)
    have h3 : r ≠ 3 := fun e => by subst e; exact absurd hr (by decide)
    rw [o1 r h15 h3]
    obtain rfl | rfl | rfl : r = 5 ∨ r = 6 ∨ r = 7 := by
      rcases hr with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    all_goals simp [Instr.next, Instr.exec, State.setReg, State.setNZ]
  refine cons (one _ t1 rfl rfl) fun u1 e1 => ?_
  subst e1
  refine stmE hv hWr _ fr1 (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ]) (k := sX2 / 4 + 4)
    (v0 := 0) (v1 := 0) (v2 := 0) (v3 := 0) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ fun t2 sp2 fr2 r32 o2 => ?_
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, sp1]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, r31]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z1 5 (by decide)]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z1 6 (by decide)]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z1 7 (by decide)]
  have z2 : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 7 → t2.regs r = 0 := fun r h1 h2 => by
    have h15 : r ≠ 15 := fun e => by subst e; exact absurd h2 (by decide)
    have h3 : r ≠ 3 := fun e => by subst e; exact absurd h1 (by decide)
    rw [o2 r h15 h3]
    by_cases h4 : r = 4
    · subst h4; simp [Instr.next, Instr.exec, State.setReg, State.setNZ]
    · rw [regs_movImm _ _ _ _ h15, if_neg (by simpa using h4)]
      exact z1 r (by have : r.val ≠ 4 := fun e => h4 (Fin.ext e); omega)
  refine stmE hv hWr _ fr2 rfl (k := sX2 / 4 + 8) (v0 := 0) (v1 := 0) (v2 := 0) (v3 := 0) (by omega)
    sp2 (by rw [r32]) (z2 4 (by decide) (by decide)) (z2 5 (by decide) (by decide))
    (z2 6 (by decide) (by decide)) (z2 7 (by decide) (by decide)) fun t3 sp3 fr3 r33 o3 => ?_
  refine stmE hv hWr _ fr3 rfl (k := sX2 / 4 + 12) (v0 := 0) (v1 := 0) (v2 := 0) (v3 := 0) (by omega)
    sp3 (by rw [r33]) (by rw [o3 4 (by decide) (by decide)]; exact z2 4 (by decide) (by decide))
    (by rw [o3 5 (by decide) (by decide)]; exact z2 5 (by decide) (by decide))
    (by rw [o3 6 (by decide) (by decide)]; exact z2 6 (by decide) (by decide))
    (by rw [o3 7 (by decide) (by decide)]; exact z2 7 (by decide) (by decide)) fun t4 sp4 fr4 _ o4 => ?_
  have z4 : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 7 → t4.regs r = 0 := fun r h1 h2 => by
    have h15 : r ≠ 15 := fun e => by subst e; exact absurd h2 (by decide)
    have h3 : r ≠ 3 := fun e => by subst e; exact absurd h1 (by decide)
    rw [o4 r h15 h3, o3 r h15 h3]; exact z2 r h1 h2
  -- `Z3 = 1`
  refine cons (one _ t4 rfl rfl) fun u4 e4 => ?_
  refine cons (one _ u4 rfl rfl) fun u5 e5 => ?_
  subst e4 e5
  refine stmE hv hWr _ fr4 (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ]) (k := sZ3 / 4)
    (v0 := 1) (v1 := 0) (v2 := 0) (v3 := 0) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ fun t5 sp5 fr5 r35 o5 => ?_
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, sp4]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.sp, sp4, slot, Nat.mod_eq_of_lt sz,
      Nat.mul_comm]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z4 5 (by decide) (by decide)]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z4 6 (by decide) (by decide)]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, z4 7 (by decide) (by decide)]
  refine cons (one _ t5 rfl rfl) fun u6 e6 => ?_
  subst e6
  have z6 : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 7 → ((Instr.movImm 4 0).next t5).regs r = 0 := fun r h1 h2 => by
    have h15 : r ≠ 15 := fun e => by subst e; exact absurd h2 (by decide)
    have h3 : r ≠ 3 := fun e => by subst e; exact absurd h1 (by decide)
    by_cases h4 : r = 4
    · subst h4; simp [Instr.next, Instr.exec, State.setReg, State.setNZ]
    · have h13 : r ≠ 13 := fun e => by subst e; exact absurd h2 (by decide)
      rw [regs_movImm _ _ _ _ h15, if_neg (by simpa using h4), o5 r h15 h3]
      have a3 : r ≠ LowReg.toReg 3 := by simpa using h3
      have a4 : r ≠ LowReg.toReg 4 := by simpa using h4
      simp [Instr.next, Instr.exec, State.setReg, State.setNZ, h15, a3, a4]
      rw [if_neg h4, if_neg h3]
      exact z4 r h1 h2
  refine stmE hv hWr _ fr5 (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ]) (k := sZ3 / 4 + 4)
    (v0 := 0) (v1 := 0) (v2 := 0) (v3 := 0) (by omega) ?_ ?_ (z6 4 (by decide) (by decide))
    (z6 5 (by decide) (by decide)) (z6 6 (by decide) (by decide)) (z6 7 (by decide) (by decide))
    fun t6 sp6 fr6 _ o6 => ?_
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, sp5]
  · simp [Instr.next, Instr.exec, State.setReg, State.setNZ, r35]
  -- `swap = 0`, `t = 254`
  refine strE hv hWr _ fr6 rfl 4 (k := lvSwap / 4) (v := 0) (by simp only [lvSwap, NW, LFRAME]; omega) sp6
    (by simp only [X25519Mem.toReg4]; rw [o6 4 (by decide) (by decide)]; exact z6 4 (by decide) (by decide)) fun t7 sp7 fr7 _ => ?_
  refine cons (one _ t7 rfl rfl) fun u8 e8 => ?_
  subst e8
  refine strE hv hWr _ fr7 (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ]) 0 (k := lvT / 4)
    (v := 254) (by simp only [lvT, NW, LFRAME]; omega) (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ, sp7])
    (by simp [Instr.next, Instr.exec, State.setReg, State.setNZ]) fun t8 sp8 fr8 _ => ?_
  exact ⟨accAll_nil _ _, sp8, fr8⟩

end

end M0Crypto.Release.X25519Prologue
