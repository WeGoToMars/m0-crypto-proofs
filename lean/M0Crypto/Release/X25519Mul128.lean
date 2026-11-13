import M0Crypto.Release.X25519Slot
import M0Crypto.Release.X25519Absd

set_option linter.unusedSimpArgs false

/-!
Macro `mul128` of `m0c_fe_mul` (plan `x25519-proofs.md`, phase 8): one level of Karatsuba
multiplication of the 4-word operands at `r1` and `r2`. `L` (low halves) and `H` (high halves)
are stored at slot `k`; the middle product `|aL - aH| * |bL - bH|` and the sign mask go to
`combine128`.

The macro is cut into pieces (`mul128_split`). Each piece is a `Runs` lemma: its accesses and
its effect from its own start state. `Runs.append` composes them, so the macro is one `ReachW`
block (`mul128_run_w`). The operand words are read again after `L` and `H` are stored, so
the operands must not overlap the 8 slots from `k`.
-/

namespace M0Crypto.Release.X25519Mul128
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion WritesTo)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Macros (combine128 mul128 sl)
open M0Crypto.Release.X25519Mul (mul64 mul64_exec mul64_regOnly mul64_noW High Dist8)
open M0Crypto.Release.X25519Absd (absd64 absd64_exec)
open M0Crypto.Release.X25519Comb
open M0Crypto.Release.X25519Slot (ld read32_storeWords_disj ld_store_same storeWords_frame SlotOut slotOut_store)
open M0Crypto.Release.InstrNext (toReg_ne15 regs_eors regs_movHi)

def m1 : List Instr := [.movHi 12 1, .movHi 11 2, .ldm 1 0x50, .ldm 2 0xa0]

theorem listRegs_50 : listRegs 0x50 = [4, 6] := by decide
theorem listRegs_a0 : listRegs 0xa0 = [5, 7] := by decide

theorem m1_run {Wr : Word → Prop} (s : State) (ha : (s.regs 1).toNat % 4 = 0)
    (hb : (s.regs 2).toNat % 4 = 0) :
    Runs (AccOk Wr) m1 s fun t => t.regs 12 = s.regs 1 ∧ t.regs 11 = s.regs 2 ∧
      t.regs 4 = ld s.mem (s.regs 1) 0 ∧ t.regs 6 = ld s.mem (s.regs 1) 1 ∧
      t.regs 5 = ld s.mem (s.regs 2) 0 ∧ t.regs 7 = ld s.mem (s.regs 2) 1 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 11 → r ≠ 12 → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [m1, alignedAll, Instr.accesses, List.all_nil,
      Bool.true_and, Bool.and_true, regs_movHi, State.reg, toReg1, toReg2, ite_true, ite_false,
      next_mem, Bool.and_eq_true]
    exact ⟨wordAccesses_aligned ha, wordAccesses_aligned hb⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 h11 h12 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp (config := {decide := true}) only [m1, execAll, regs_ldm, regs_movHi, listRegs_50,
        listRegs_a0, List.map, List.mem_cons, State.reg, toReg1, toReg2, toReg4, toReg5, toReg6,
        toReg7, h15, h11, h12, n 1 (by decide), n 2 (by decide), n 4 (by decide), n 5 (by decide),
        n 6 (by decide), n 7 (by decide), ne_eq, not_false_eq_true, ite_false, or_self,
        List.not_mem_nil]
    all_goals
      simp (config := {decide := true}) only [m1, execAll, regs_ldm, regs_movHi, listRegs_50,
        listRegs_a0, List.map, List.mem_cons, State.reg, toReg1, toReg2, toReg4, toReg5, toReg6,
        toReg7, ite_true, ite_false, next_mem, mem_ldm, List.idxOf, ld, List.findIdx_cons,
        List.findIdx_nil]
      try rfl

theorem reg_ne_toReg {d : LowReg} {r : Reg} (h : d.val < r.val) : r ≠ d.toReg := by
  intro e; subst e; exact Nat.lt_irrefl _ h

/-- `add d, sp, #4k; stm d!, {r4-r7}`: `r4`-`r7` to slot `k`. -/
def sstore (d : LowReg) (k : Nat) : List Instr := [.addRdSp d (sl k), .stm d 0xf0]

theorem sstore_run {Wr : Word → Prop} (s : State) (d : LowReg) (k : Nat) (hd : d.val < 4)
    (hsp : s.sp.toNat % 4 = 0) (hW : ∀ j < 16, Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + j))) :
    Runs (AccOk Wr) (sstore d k) s fun t =>
      t.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4))
        [s.regs 4, s.regs 5, s.regs 6, s.regs 7] ∧
      ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → t.regs r = s.regs r := by
  have h4 : (4 : Reg) ≠ d.toReg := reg_ne_toReg (show d.val < 4 by omega)
  have h5 : (5 : Reg) ≠ d.toReg := reg_ne_toReg (show d.val < 5 by omega)
  have h6 : (6 : Reg) ≠ d.toReg := reg_ne_toReg (show d.val < 6 by omega)
  have h7 : (7 : Reg) ≠ d.toReg := reg_ne_toReg (show d.val < 7 by omega)
  refine ⟨accAll_cons (fun a ha => by simp [Instr.accesses] at ha) (accAll_cons ?_ (accAll_nil _ _)), ?_, ?_⟩
  · intro a ha
    simp only [Instr.accesses, State.reg, regs_addRdSp _ _ _ _ (toReg_ne15 d), ite_true,
      X25519Diff.listRegs_f0, X25519Diff.bitCount_f0] at ha
    refine wordAccesses_ok (word_add_aligned hsp (by omega)) (fun _ i hi q hq => ?_) a ha
    rw [ofNat_add_assoc, ofNat_add_assoc]
    exact hW _ (by omega)
  · simp only [sstore, execAll, mem_stm, mem_addRdSp, State.reg, X25519Diff.listRegs_f0, List.map,
      regs_addRdSp _ _ _ _ (toReg_ne15 d), ite_true, toReg4, toReg5, toReg6, toReg7,
      regs_addRdSp _ _ _ _ (by decide : (4 : Reg) ≠ 15), regs_addRdSp _ _ _ _ (by decide : (5 : Reg) ≠ 15),
      regs_addRdSp _ _ _ _ (by decide : (6 : Reg) ≠ 15), regs_addRdSp _ _ _ _ (by decide : (7 : Reg) ≠ 15),
      h4, h5, h6, h7, ite_false, State.sp]
  · intro r h15 hr
    simp only [sstore, execAll, regs_stm _ _ _ _ h15, regs_addRdSp _ _ _ _ h15, hr, ite_false]

def m2r : List Instr :=
  [.movHi 0 12, .memImm .ldr 4 0 2, .memImm .ldr 6 0 3, .movHi 1 11, .memImm .ldr 5 1 2,
   .memImm .ldr 7 1 3]

theorem m2r_run {Wr : Word → Prop} (s : State) (ha : (s.regs 12).toNat % 4 = 0)
    (hb : (s.regs 11).toNat % 4 = 0) :
    Runs (AccOk Wr) m2r s fun t =>
      t.regs 4 = ld s.mem (s.regs 12) 2 ∧ t.regs 6 = ld s.mem (s.regs 12) 3 ∧
      t.regs 5 = ld s.mem (s.regs 11) 2 ∧ t.regs 7 = ld s.mem (s.regs 11) 3 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [m2r, alignedAll, Instr.accesses, List.all_cons,
      List.all_nil, Bool.true_and, Bool.and_true, regs_movHi, regs_ldrImm, State.reg, toReg0,
      toReg1, toReg4, toReg5, toReg6, ite_true, ite_false, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [MemOp.width] <;>
      exact aligned_word (word_add_aligned (by assumption) (by decide))
  · refine ⟨?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp only [m2r, execAll, regs_ldrImm _ _ _ _ _ h15, regs_movHi _ _ _ _ h15, toReg0, toReg1,
        toReg4, toReg5, toReg6, toReg7, n 0 (by decide), n 1 (by decide), n 4 (by decide),
        n 5 (by decide), n 6 (by decide), n 7 (by decide), ite_false]
    all_goals
      simp (config := {decide := true}) only [m2r, execAll, regs_ldrImm, regs_movHi, State.reg,
        toReg0, toReg1, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false, next_mem, mem_ldrImm,
        ld]
      rfl

def m3r : List Instr := [.movHi 7 12, .ldm 7 0x65]

theorem listRegs_65 : listRegs 0x65 = [0, 2, 5, 6] := by decide
theorem listRegs_5a : listRegs 0x5a = [1, 3, 4, 6] := by decide

theorem m3r_run {Wr : Word → Prop} (s : State) (ha : (s.regs 12).toNat % 4 = 0) :
    Runs (AccOk Wr) m3r s fun t =>
      t.regs 0 = ld s.mem (s.regs 12) 0 ∧ t.regs 2 = ld s.mem (s.regs 12) 1 ∧
      t.regs 5 = ld s.mem (s.regs 12) 2 ∧ t.regs 6 = ld s.mem (s.regs 12) 3 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [m3r, alignedAll, Instr.accesses, List.all_nil,
      Bool.true_and, Bool.and_true, regs_movHi, State.reg, toReg7, ite_true]
    exact wordAccesses_aligned ha
  · refine ⟨?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp (config := {decide := true}) only [m3r, execAll, regs_ldm, regs_movHi, listRegs_65,
        List.map, List.mem_cons, State.reg, toReg0, toReg2, toReg5, toReg6, toReg7, h15,
        n 0 (by decide), n 2 (by decide), n 5 (by decide), n 6 (by decide), n 7 (by decide), ne_eq,
        not_false_eq_true, ite_false, or_self, List.not_mem_nil]
    all_goals
      simp (config := {decide := true}) only [m3r, execAll, regs_ldm, regs_movHi, listRegs_65,
        List.map, List.mem_cons, State.reg, toReg0, toReg2, toReg5, toReg6, toReg7, ite_true,
        ite_false, next_mem, List.idxOf, ld, List.findIdx_cons, List.findIdx_nil]
      try rfl

def m3b : List Instr := [.movHi 4 11, .ldm 4 0x5a]

theorem m3b_run {Wr : Word → Prop} (s : State) (hb : (s.regs 11).toNat % 4 = 0) :
    Runs (AccOk Wr) m3b s fun t =>
      t.regs 1 = ld s.mem (s.regs 11) 0 ∧ t.regs 3 = ld s.mem (s.regs 11) 1 ∧
      t.regs 4 = ld s.mem (s.regs 11) 2 ∧ t.regs 6 = ld s.mem (s.regs 11) 3 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 6 → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [m3b, alignedAll, Instr.accesses, List.all_nil,
      Bool.true_and, Bool.and_true, regs_movHi, State.reg, toReg4, ite_true]
    exact wordAccesses_aligned hb
  · refine ⟨?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h1 h3 h4 h6 => ?_⟩
    rotate_right
    · simp (config := {decide := true}) only [m3b, execAll, regs_ldm, regs_movHi, listRegs_5a,
        List.map, List.mem_cons, State.reg, toReg1, toReg3, toReg4, toReg6, h15, h1, h3, h4, h6,
        ne_eq, not_false_eq_true, ite_false, or_self, List.not_mem_nil]
    all_goals
      simp (config := {decide := true}) only [m3b, execAll, regs_ldm, regs_movHi, listRegs_5a,
        List.map, List.mem_cons, State.reg, toReg1, toReg3, toReg4, toReg6, ite_true,
        ite_false, next_mem, List.idxOf, ld, List.findIdx_cons, List.findIdx_nil]
      try rfl

/-! Memory and register helpers. -/

theorem storeWords_append (m : M0Crypto.Armv6M.Mem) (a : Word) (xs ys : List Word) :
    storeWords m a (xs ++ ys) =
      storeWords (storeWords m a xs) (a + BitVec.ofNat 32 (4 * xs.length)) ys := by
  induction xs generalizing m a with
  | nil => simp [storeWords]
  | cons x xs ih =>
    simp only [List.cons_append, storeWords, ih, List.length_cons]
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
    congr 3; omega

theorem hi_ne {r : Reg} (h : 8 ≤ r.val) (x : LowReg) : r ≠ x.toReg := by
  intro e; subst e; have := x.isLt; simp only [LowReg.toReg] at h; omega

theorem high8 : High 8 := ⟨fun x => hi_ne (by decide) x, by decide⟩
theorem high10 : High 10 := ⟨fun x => hi_ne (by decide) x, by decide⟩

/-- `mul64` with the high scratch registers `r8`, `r10`. -/
theorem mul64_runs {Wr : Word → Prop} (s : State) (a0 a1 b0 b1 t1 t2 t3 t4 : LowReg)
    (hd : Dist8 a0 a1 b0 b1 t1 t2 t3 t4) :
    Runs (AccOk Wr) (mul64 a0 a1 b0 b1 t1 t2 t3 t4 8 10) s fun t =>
      (t.reg a0).toNat + 2 ^ 32 * (t.reg b0).toNat + 2 ^ 64 * (t.reg a1).toNat +
          2 ^ 96 * (t.reg b1).toNat =
        ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) *
          ((s.reg b0).toNat + 2 ^ 32 * (s.reg b1).toNat) ∧
      t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → t.regs r = s.regs r := by
  obtain ⟨e1, e2, e3⟩ := mul64_exec s a0 a1 b0 b1 t1 t2 t3 t4 8 10 high8 high10 (by decide) hd
  exact Runs.reg (mul64_regOnly ..) (mul64_noW ..) ⟨e1, e2, fun r h15 h8 n8 n10 =>
    e3 r h15 (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _)
      (hi_ne h8 _) (hi_ne h8 _) n8 n10⟩

theorem absd64_runs {Wr : Word → Prop} (s : State) (x0 x1 y0 y1 m : LowReg) (h01 : x0.val ≠ x1.val)
    (h0m : x0.val ≠ m.val) (h1m : x1.val ≠ m.val) (h0y : x0.val ≠ y1.val) :
    Runs (AccOk Wr) (absd64 x0 x1 y0 y1 m) s fun t =>
      let X : Nat := (s.reg x0).toNat + 2 ^ 32 * (s.reg x1).toNat
      let Y : Nat := (s.reg y0).toNat + 2 ^ 32 * (s.reg y1).toNat
      let R : Nat := (t.reg x0).toNat + 2 ^ 32 * (t.reg x1).toNat
      t.reg m = mask (decide (X < Y)) ∧
        (X : Int) - Y = (if X < Y then -(R : Int) else R) ∧
        t.mem = s.mem ∧
        ∀ r : Reg, r ≠ 15 → r ≠ x0.toReg → r ≠ x1.toReg → r ≠ m.toReg → t.regs r = s.regs r :=
  Runs.reg (by simp [absd64, X25519Mul.regOnly]) (by simp [absd64, Instr.writesMem])
    (absd64_exec s x0 x1 y0 y1 m h01 h0m h1m h0y)

theorem not_xor_mask (p q : Bool) : ~~~(mask p ^^^ mask q) = mask (p == q) := by
  cases p <;> cases q <;> decide

def m3c : List Instr := [.dp .eors 6 5, .dp .mvns 6 6, .movHi 12 6]

theorem m3c_runs {Wr : Word → Prop} (s : State) :
    Runs (AccOk Wr) m3c s fun t =>
      t.regs 12 = ~~~(s.regs 6 ^^^ s.regs 5) ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 6 → r ≠ 12 → t.regs r = s.regs r := by
  refine Runs.reg (by decide) (by decide) ⟨?_, execAll_mem _ _ (by decide), fun r h15 h6 h12 => ?_⟩
  · simp (config := {decide := true}) only [m3c, execAll, regs_movHi, regs_mvns, regs_eors,
      State.reg, toReg5, toReg6, ite_true, ite_false]
  · simp only [m3c, execAll, regs_movHi _ _ _ _ h15, regs_mvns _ _ _ _ h15, regs_eors _ _ _ _ h15,
      toReg6, h6, h12, ite_false]

theorem mul128_split (k : Nat) (direct : Bool) :
    mul128 k direct = m1 ++ (mul64 4 6 5 7 0 1 2 3 8 10 ++ (sstore 0 k ++ (m2r ++
      (mul64 4 6 5 7 0 1 2 3 8 10 ++ (sstore 0 (k + 4) ++ (m3r ++ (absd64 0 2 5 6 5 ++ (m3b ++
      (absd64 1 3 4 6 6 ++ (m3c ++ (mul64 0 2 1 3 4 5 6 7 8 10 ++
      ([.movHi 4 12] ++ combine128 k direct)))))))))))) := by
  simp only [mul128, m1, sstore, m2r, m3r, absd64, m3b, m3c, List.append_assoc, List.cons_append,
    List.nil_append]

/-- Value of four words from `p`. -/
def opv (m : M0Crypto.Armv6M.Mem) (p : Word) : Nat := w4 (ld m p 0) (ld m p 1) (ld m p 2) (ld m p 3)

theorem disjLo {p a : Word} (h : Frame.Disj p 16 a 32) : Frame.Disj p 16 a 16 := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by omega⟩

theorem disjHi {p a : Word} (h : Frame.Disj p 16 a 32) :
    Frame.Disj p 16 (a + BitVec.ofNat 32 16) 16 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩ <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem ld_past {m : M0Crypto.Armv6M.Mem} {p b : Word} (h : Frame.Disj p 16 b 16) (ws : List Word)
    (hl : ws.length = 4) (i : Nat) (hi : i < 4) : ld (storeWords m b ws) p i = ld m p i := by
  unfold ld
  exact read32_storeWords_disj (n := 16) m p b ws (by rw [hl]; exact h) i (by omega)

theorem sl_add4 {k : Nat} (hk : k + 4 < 256) : (sl (k + 4)).toNat * 4 = (sl k).toNat * 4 + 16 := by
  simp only [sl, BitVec.toNat_ofNat]; omega

theorem lt64 {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x * y < 2 ^ 128 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

theorem lt128 {x y : Nat} (hx : x < 2 ^ 128) (hy : y < 2 ^ 128) : x * y < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

/-- The arithmetic of `mul128`: the halves' products, the absolute differences and their
signs give `combine128`'s precondition and the full product. -/
theorem mul128_nat (AL AH BL BH RA RB L H P : Nat) (hAL : AL < 2 ^ 64) (hAH : AH < 2 ^ 64)
    (hBL : BL < 2 ^ 64) (hBH : BH < 2 ^ 64) (hL : L = AL * BL) (hH : H = AH * BH)
    (hP : P = RA * RB)
    (hA : (AL : Int) - AH = if AL < AH then -(RA : Int) else RA)
    (hB : (BL : Int) - BH = if BL < BH then -(RB : Int) else RB) :
    (if (decide (BL < BH) == decide (AL < AH)) then AL * BH + AH * BL + P = L + H
      else AL * BH + AH * BL = L + H + P) ∧
    AL * BH + AH * BL < 2 ^ 160 ∧
    L + 2 ^ 64 * (AL * BH + AH * BL) + 2 ^ 128 * H = (AL + 2 ^ 64 * AH) * (BL + 2 ^ 64 * BH) ∧
    (AL + 2 ^ 64 * AH) * (BL + 2 ^ 64 * BH) < 2 ^ 256 := by
  have b1 := lt64 hAL hBH; have b2 := lt64 hAH hBL
  have ks := X25519Kara.kara_split (2 ^ 64) AL AH BL BH
  refine ⟨?_, by omega, by subst hL hH; omega, lt128 (by omega) (by omega)⟩
  have c := X25519Kara.cross AL AH BL BH RA RB (if AL < AH then 1 else 0) (if BL < BH then 1 else 0)
    (by by_cases h : AL < AH <;> simp [h] at hA ⊢ <;> exact hA)
    (by by_cases h : BL < BH <;> simp [h] at hB ⊢ <;> exact hB)
    (by split <;> omega) (by split <;> omega)
  subst hL hH hP
  by_cases h1 : AL < AH <;> by_cases h2 : BL < BH <;> simp [h1, h2] at c ⊢ <;> omega

theorem mul128_runs {Wr : Word → Prop} (s : State) (k : Nat) (direct : Bool) (hk : k + 4 < 256)
    (hsp : s.sp.toNat % 4 = 0) (ha : (s.regs 1).toNat % 4 = 0) (hb : (s.regs 2).toNat % 4 = 0)
    (hda : Frame.Disj (s.regs 1) 16 (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 32)
    (hdb : Frame.Disj (s.regs 2) 16 (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 32)
    (hW : ∀ j < 32, Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + j))) :
    Runs (AccOk Wr) (mul128 k direct) s fun t =>
      ∃ l0 l1 : Word,
        SlotOut s.mem t.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) direct l0 l1 t ∧
        l0.toNat + 2 ^ 32 * l1.toNat + 2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) +
            2 ^ 192 * (t.regs 4).toNat + 2 ^ 224 * (t.regs 5).toNat =
          opv s.mem (s.regs 1) * opv s.mem (s.regs 2) ∧
        ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
          t.regs r = s.regs r := by
  have d8 : Dist8 4 6 5 7 0 1 2 3 := by simp only [Dist8]; decide
  rw [mul128_split]
  -- `L`
  refine Runs.append (m1_run s ha hb) fun s1 ⟨p12, p11, p4, p6, p5, p7, pm, pf⟩ => ?_
  refine Runs.append (mul64_runs s1 4 6 5 7 0 1 2 3 d8) fun s2 ⟨qv, qm, qf⟩ => ?_
  have f2 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
      s2.regs r = s.regs r := fun r a b c d e f => by rw [qf r a b c d, pf r a b e f]
  have a2 : s2.regs 12 = s.regs 1 := by rw [qf 12 (by decide) (by decide) (by decide) (by decide), p12]
  have b2 : s2.regs 11 = s.regs 2 := by rw [qf 11 (by decide) (by decide) (by decide) (by decide), p11]
  have sp2 : s2.sp = s.sp := f2 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [State.reg, toReg4, toReg5, toReg6, toReg7, p4, p5, p6, p7] at qv
  refine Runs.append (sstore_run s2 0 k (by decide) (by rw [sp2]; exact hsp)
    (fun j hj => by rw [sp2]; exact hW j (by omega))) fun s3 ⟨sm3, sf3⟩ => ?_
  have g3 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s3.regs r = s2.regs r := fun r h h8 => sf3 r h (hi_ne h8 0)
  have a3 : s3.regs 12 = s.regs 1 := by rw [g3 12 (by decide) (by decide), a2]
  have b3 : s3.regs 11 = s.regs 2 := by rw [g3 11 (by decide) (by decide), b2]
  rw [qm, pm, sp2] at sm3
  -- `H`
  refine Runs.append (m2r_run s3 (by rw [a3]; exact ha) (by rw [b3]; exact hb))
    fun s4 ⟨u4, u6, u5, u7, um, uf⟩ => ?_
  rw [a3, sm3, ld_past (disjLo hda) _ rfl _ (by decide)] at u4 u6
  rw [b3, sm3, ld_past (disjLo hdb) _ rfl _ (by decide)] at u5 u7
  refine Runs.append (mul64_runs s4 4 6 5 7 0 1 2 3 d8) fun s5 ⟨qv5, qm5, qf5⟩ => ?_
  simp only [State.reg, toReg4, toReg5, toReg6, toReg7, u4, u5, u6, u7] at qv5
  have f5 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → s5.regs r = s3.regs r :=
    fun r a b c d => by rw [qf5 r a b c d, uf r a b]
  have sp5 : s5.sp = s.sp := by
    show s5.regs 13 = s.regs 13
    rw [f5 13 (by decide) (by decide) (by decide) (by decide), g3 13 (by decide) (by decide)]; exact sp2
  have a5 : s5.regs 12 = s.regs 1 := by rw [f5 12 (by decide) (by decide) (by decide) (by decide), a3]
  have b5 : s5.regs 11 = s.regs 2 := by rw [f5 11 (by decide) (by decide) (by decide) (by decide), b3]
  refine Runs.append (sstore_run s5 0 (k + 4) (by decide) (by rw [sp5]; exact hsp)
    (fun j hj => by rw [sp5, sl_add4 hk, Nat.add_assoc]; exact hW (16 + j) (by omega))) fun s6 ⟨sm6, sf6⟩ => ?_
  have g6 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s6.regs r = s5.regs r := fun r h h8 => sf6 r h (hi_ne h8 0)
  rw [qm5, um, sm3, sp5, sl_add4 hk, ← ofNat_add_assoc] at sm6
  -- operands again: `aL - aH`
  refine Runs.append (m3r_run s6 (by rw [g6 12 (by decide) (by decide), a5]; exact ha))
    fun s7 ⟨w0, w2, w5, w6, wm, wf⟩ => ?_
  rw [g6 12 (by decide) (by decide), a5, sm6, ld_past (disjHi hda) _ rfl _ (by decide),
    ld_past (disjLo hda) _ rfl _ (by decide)] at w0 w2 w5 w6
  refine Runs.append (absd64_runs s7 0 2 5 6 5 (by decide) (by decide) (by decide) (by decide))
    fun s8 ⟨v5, vd, vm, vf⟩ => ?_
  simp only [State.reg, toReg0, toReg2, toReg5, toReg6, w0, w2, w5, w6] at v5 vd
  have h8 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s8.regs r = s7.regs r :=
    fun r h h8 => vf r h (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _)
  -- `bL - bH`
  refine Runs.append (m3b_run s8 (by
      rw [h8 11 (by decide) (by decide), wf 11 (by decide) (by decide), g6 11 (by decide) (by decide), b5]
      exact hb)) fun s9 ⟨x1, x3, x4, x6, xm, xf⟩ => ?_
  rw [h8 11 (by decide) (by decide), wf 11 (by decide) (by decide), g6 11 (by decide) (by decide), b5,
    vm, wm, sm6, ld_past (disjHi hdb) _ rfl _ (by decide), ld_past (disjLo hdb) _ rfl _ (by decide)]
    at x1 x3 x4 x6
  refine Runs.append (absd64_runs s9 1 3 4 6 6 (by decide) (by decide) (by decide) (by decide))
    fun s10 ⟨y6, yd, ym, yf⟩ => ?_
  simp only [State.reg, toReg1, toReg3, toReg4, toReg6, x1, x3, x4, x6] at y6 yd
  -- the sign of the middle product
  refine Runs.append (m3c_runs s10) fun s11 ⟨z12, zm, zf⟩ => ?_
  have r5 : s10.regs 5 = s8.regs 5 := by
    rw [yf 5 (by decide) (by decide) (by decide) (by decide),
      xf 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [y6, r5, v5, not_xor_mask] at z12
  -- `|aL - aH| * |bL - bH|`
  refine Runs.append (mul64_runs s11 0 2 1 3 4 5 6 7 (by simp only [Dist8]; decide))
    fun s12 ⟨pv, pm12, pf12⟩ => ?_
  refine Runs.append (Runs.reg (Wr := Wr) (is := [Instr.movHi 4 12]) (s := s12) (by decide) (by decide)
      (Q := fun t => t.regs 4 = s12.regs 12 ∧ t.mem = s12.mem ∧
        ∀ r : Reg, r ≠ 15 → r ≠ 4 → t.regs r = s12.regs r)
      ⟨by simp [execAll, regs_movHi], execAll_mem _ _ (by decide),
        fun r h15 h4 => by simp [execAll, regs_movHi, h15, h4]⟩) fun s13 ⟨o4, om, of⟩ => ?_
  -- the state before `combine128`
  have F : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
      s13.regs r = s.regs r := by
    intro r a b c d e f
    have nl : ∀ q : Reg, q.val < 8 → r ≠ q := fun q hq h => by subst h; omega
    rw [of r a (nl 4 (by decide)), pf12 r a b c d, zf r a (nl 6 (by decide)) f,
      yf r a (hi_ne b _) (hi_ne b _) (hi_ne b _),
      xf r a (nl 1 (by decide)) (nl 3 (by decide)) (nl 4 (by decide)) (nl 6 (by decide)), h8 r a b,
      wf r a b, g6 r a b, f5 r a b c d, g3 r a b, f2 r a b c d e f]
  have sp13 : s13.sp = s.sp :=
    F 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have mem13 : s13.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4))
      ([s2.regs 4, s2.regs 5, s2.regs 6, s2.regs 7] ++ [s5.regs 4, s5.regs 5, s5.regs 6, s5.regs 7]) := by
    rw [om, pm12, zm, ym, xm, vm, wm, sm6, storeWords_append]; rfl
  have cwj : ∀ j (hj : j < 8), cw s13 k j =
      ([s2.regs 4, s2.regs 5, s2.regs 6, s2.regs 7] ++ [s5.regs 4, s5.regs 5, s5.regs 6, s5.regs 7])[j]'(by simp; omega) := by
    intro j hj
    unfold cw
    rw [mem13, sp13, ← ofNat_add_assoc]
    exact Frame.read32_storeWords_same _ _ _ _ _ (by simp)
  -- values for `combine128`
  simp only [State.reg, toReg0, toReg1, toReg2, toReg3] at pv
  have e0 : s11.regs 0 = s8.regs 0 := by
    rw [zf 0 (by decide) (by decide) (by decide), yf 0 (by decide) (by decide) (by decide) (by decide),
      xf 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e2 : s11.regs 2 = s8.regs 2 := by
    rw [zf 2 (by decide) (by decide) (by decide), yf 2 (by decide) (by decide) (by decide) (by decide),
      xf 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [e0, e2, zf 1 (by decide) (by decide) (by decide), zf 3 (by decide) (by decide) (by decide),
    ← of 0 (by decide) (by decide), ← of 1 (by decide) (by decide), ← of 2 (by decide) (by decide),
    ← of 3 (by decide) (by decide)] at pv
  have m4 : s13.regs 4 = s11.regs 12 := by
    rw [o4, pf12 12 (by decide) (by decide) (by decide) (by decide)]
  rw [z12] at m4
  have hx : ∀ w : Word, w.toNat < 2 ^ 32 := fun w => w.isLt
  have qv' : w4 (s2.regs 4) (s2.regs 5) (s2.regs 6) (s2.regs 7) = _ := qv
  have qv5' : w4 (s5.regs 4) (s5.regs 5) (s5.regs 6) (s5.regs 7) = _ := qv5
  have pv' : w4 (s13.regs 0) (s13.regs 1) (s13.regs 2) (s13.regs 3) = _ := pv
  obtain ⟨hmid, hM, hval, hlt⟩ := mul128_nat _ _ _ _ _ _ _ _ _
    (by have := hx (ld s.mem (s.regs 1) 0); have := hx (ld s.mem (s.regs 1) 1); omega)
    (by have := hx (ld s.mem (s.regs 1) 2); have := hx (ld s.mem (s.regs 1) 3); omega)
    (by have := hx (ld s.mem (s.regs 2) 0); have := hx (ld s.mem (s.regs 2) 1); omega)
    (by have := hx (ld s.mem (s.regs 2) 2); have := hx (ld s.mem (s.regs 2) 3); omega)
    qv' qv5' pv' vd yd
  have c0 : cw s13 k 0 = s2.regs 4 := cwj 0 (by decide)
  have c1 : cw s13 k 1 = s2.regs 5 := cwj 1 (by decide)
  have c2 : cw s13 k 2 = s2.regs 6 := cwj 2 (by decide)
  have c3 : cw s13 k 3 = s2.regs 7 := cwj 3 (by decide)
  have c4 : cw s13 k 4 = s5.regs 4 := cwj 4 (by decide)
  have c5 : cw s13 k 5 = s5.regs 5 := cwj 5 (by decide)
  have c6 : cw s13 k 6 = s5.regs 6 := cwj 6 (by decide)
  have c7 : cw s13 k 7 = s5.regs 7 := cwj 7 (by decide)
  have pre : CombPre s13 k _ _ := ⟨m4, by simp only [c0, c1, c2, c3, c4, c5, c6, c7]; exact hmid, hM,
    by simp only [c0, c1, c2, c3, c4, c5, c6, c7]; rw [hval]; exact hlt⟩
  refine ⟨combine128_acc s13 k direct (by rw [sp13]; exact hsp) (fun j hj => by
    rw [sp13, Nat.add_assoc]; exact hW _ (by cases direct <;> simp only [coff] at hj ⊢ <;> simp at hj ⊢ <;> omega)), ?_⟩
  obtain ⟨cv, cmem, cf⟩ := combine128_exec s13 k direct _ _ pre
  generalize execAll (combine128 k direct) s13 = t at cv cmem cf
  refine ⟨s2.regs 4, s2.regs 5, ?_, ?_, fun r a b c d e f => by rw [cf r a b, F r a b c d e f]⟩
  · rw [cmem, mem13, sp13, ← ofNat_add_assoc]
    refine slotOut_store _ _ _ hda.2.1 _ _ _ _ (ld_store_same _ _ _ 0 (by simp) (by simp))
      (ld_store_same _ _ _ 1 (by simp) (by simp)) fun y hy => ?_
    have := storeWords_frame s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 0
      ([s2.regs 4, s2.regs 5, s2.regs 6, s2.regs 7] ++ [s5.regs 4, s5.regs 5, s5.regs 6, s5.regs 7])
      (by simp) y hy
    simpa using this
  · rw [c0, c1, c2, c3, c4, c5, c6, c7] at cv
    have oA : opv s.mem (s.regs 1) = (ld s.mem (s.regs 1) 0).toNat + 2 ^ 32 * (ld s.mem (s.regs 1) 1).toNat +
        2 ^ 64 * ((ld s.mem (s.regs 1) 2).toNat + 2 ^ 32 * (ld s.mem (s.regs 1) 3).toNat) := by
      unfold opv w4; omega
    have oB : opv s.mem (s.regs 2) = (ld s.mem (s.regs 2) 0).toNat + 2 ^ 32 * (ld s.mem (s.regs 2) 1).toNat +
        2 ^ 64 * ((ld s.mem (s.regs 2) 2).toNat + 2 ^ 32 * (ld s.mem (s.regs 2) 3).toNat) := by
      unfold opv w4; omega
    rw [cv, hval, oA, oB]

end M0Crypto.Release.X25519Mul128
