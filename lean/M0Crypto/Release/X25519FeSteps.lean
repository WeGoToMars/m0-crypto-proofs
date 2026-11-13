import M0Crypto.Release.X25519FeCommon
import M0Crypto.Release.X25519Sqr128
import M0Crypto.Release.X25519Diff
import M0Crypto.Release.X25519CombRed

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
Step lemmas for the routine proofs of `m0c_fe_mul` and `m0c_fe_sqr`, in continuation form over
`Runs`: each takes the frame (`FrameOk` over 37 slots from `P`, SP at `P`) and hands the next
state, the updated frame and the step's facts to the rest of the block.

* `cons`, `one`: a single instruction; a register-only one runs to `i.next s`.
* `enter_step`: `push {lr}; sub sp, #144`, building the frame.
* `str_step`, `ldr_step`: `str`/`ldr rd, [sp, #4k]`.
* `mul_step`, `sqr_step`: `mul128` / `sqr128` at slot `k`, the product in the frame.
* `diff_step`: `diff256 p o`.
-/

namespace M0Crypto.Release.X25519FeSteps
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (Region)
open M0Crypto.Release.Frame (Disj InFrame)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Slot (ld SlotOut)
open M0Crypto.Release.X25519Comb (coff cregs)
open M0Crypto.Release.X25519Macros (sl SFRAME mul128 sqr128 diff256)
open M0Crypto.Release.X25519Mul128 (opv mul128_runs)
open M0Crypto.Release.X25519Sqr128 (sqr128_runs)
open M0Crypto.Release.X25519W4 (w4 mask)
open M0Crypto.Release.X25519FeCommon
open M0Crypto.Release.X25519Routines (Call mulFrame)

theorem cons {P : Access → Prop} {i : Instr} {is : List Instr} {s : State} {Q1 Q2 : State → Prop}
    (h1 : Runs P [i] s Q1) (h2 : ∀ t, Q1 t → Runs P is t Q2) : Runs P (i :: is) s Q2 :=
  Runs.append h1 h2

theorem one {Wr : Word → Prop} (i : Instr) (s : State) (h1 : X25519Mul.regOnly i = true)
    (h2 : i.writesMem = false) : Runs (AccOk Wr) [i] s (· = i.next s) :=
  Runs.reg (by simp [h1]) (by simp [h2]) rfl

theorem regs_subSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subSp i).next s).regs r = if r = 13 then s.regs 13 - BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem ne_low (d : LowReg) {r : Reg} (h : 8 ≤ r.val) : r ≠ d.toReg := fun e => by
  have h1 : r.val = d.val := congrArg Fin.val e
  have := d.isLt
  omega

section
variable {Wr : Word → Prop} {is : List Instr} {Q : State → Prop}

theorem enter_step (c : Call) (s : State) (h13 : s.regs 13 = c.sp0) (hm : s.mem = c.m0)
    (h4 : c.sp0.toNat % 4 = 0) (hlo : mulFrame ≤ c.sp0.toNat)
    (hW : ∀ y, Region (fp c) mulFrame y → Wr y)
    (k : ∀ t : State, t.sp = fp c →
      FrameOk (fp c) 37 c.m0 (upd (fun i => read32 c.m0 (slot (fp c) i)) 36 [s.regs 14]) t.mem →
      (∀ r : Reg, r ≠ 15 → r ≠ 13 → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.push 0 true :: .subSp (BitVec.ofNat 7 SFRAME) :: is) s Q := by
  have hs : s.sp = c.sp0 := h13
  refine cons (push_run s (by rw [hs]; exact h4) fun q hq => hW _ ?_) fun s1 ⟨m1, sp1, o1⟩ => ?_
  · rw [hs, ← slot36 c]; exact wr_slot c (by omega) hq
  refine cons (one _ s1 rfl rfl) fun s2 e2 => ?_
  subst e2
  refine k _ ?_ ?_ fun r h15 h13' => ?_
  · show ((Instr.subSp _).next s1).regs 13 = _
    rw [regs_subSp _ _ _ (by decide), if_pos rfl, sp1, hs, fp_sub]
  · rw [show ((Instr.subSp (BitVec.ofNat 7 SFRAME)).next s1).mem = s1.mem from rfl, m1, hs, hm,
      ← slot36 c]
    exact (frame_init c hlo).write (by omega) _
  · rw [regs_subSp _ _ _ h15, if_neg h13', o1 r h15 h13']

theorem str_step {P : Word} {m0 : Mem} {F : Nat → Word} (s : State) (d : LowReg) {k : Nat}
    (hk : k < 37) (sp : s.sp = P) (fr : FrameOk P 37 m0 F s.mem) (hP : P.toNat % 4 = 0)
    (hW : ∀ q < 4, Wr (slot P k + BitVec.ofNat 32 q))
    (cont : ∀ t : State, t.sp = P → FrameOk P 37 m0 (upd F k [s.reg d]) t.mem →
      (∀ r : Reg, r ≠ 15 → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.strSp d (sl k) :: is) s Q := by
  refine cons (strSp_run s d (by omega) (by rw [sp]; exact hP) (by rw [sp]; exact hW))
    fun t ⟨tm, to⟩ => cont t ?_ ?_ to
  · show t.regs 13 = P; rw [to 13 (by decide)]; exact sp
  · rw [tm, sp]; exact fr.write hk _

theorem ldr_step {P : Word} {m0 : Mem} {F : Nat → Word} (s : State) (d : LowReg) {k : Nat}
    (hk : k < 37) (sp : s.sp = P) (fr : FrameOk P 37 m0 F s.mem) (hP : P.toNat % 4 = 0)
    (cont : ∀ t : State, t.sp = P → FrameOk P 37 m0 F t.mem → t.regs d.toReg = F k →
      (∀ r : Reg, r ≠ 15 → r ≠ d.toReg → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (.ldrSp d (sl k) :: is) s Q := by
  refine cons (ldrSp_run s d (by omega) (by rw [sp]; exact hP)) fun t ⟨tm, td, to⟩ => cont t ?_ ?_ ?_ to
  · show t.regs 13 = P
    rw [to 13 (by decide) (ne_low d (by decide))]; exact sp
  · rw [tm]; exact fr
  · rw [td, sp, fr.slots k hk]

/-- `mul128 k direct`: the product of the 16-byte inputs at `r1`, `r2` into slots `k ..`. -/
theorem mul_step {P : Word} {m0 : Mem} {F : Nat → Word} (s : State) {k : Nat} (direct : Bool)
    (hk : k + 8 ≤ 37) (sp : s.sp = P) (fr : FrameOk P 37 m0 F s.mem) (hP : P.toNat % 4 = 0)
    (ha : (s.regs 1).toNat % 4 = 0) (hb : (s.regs 2).toNat % 4 = 0)
    (hda : Disj (s.regs 1) 16 (slot P k) 32) (hdb : Disj (s.regs 2) 16 (slot P k) 32)
    (hW : ∀ j < 32, Wr (slot P k + BitVec.ofNat 32 j))
    (cont : ∀ (t : State) (F' : Nat → Word) (l0 l1 : Word), t.sp = P →
      FrameOk P 37 m0 F' t.mem → (∀ i, (i < k ∨ k + 8 ≤ i) → F' i = F i) → F' k = l0 →
      F' (k + 1) = l1 →
      (∀ j (hj : j < (cregs direct t).length), F' (k + coff direct / 4 + j) = (cregs direct t)[j]) →
      l0.toNat + 2 ^ 32 * l1.toNat + 2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) +
          2 ^ 192 * (t.regs 4).toNat + 2 ^ 224 * (t.regs 5).toNat =
        opv s.mem (s.regs 1) * opv s.mem (s.regs 2) →
      Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (mul128 k direct ++ is) s Q := by
  have hk' : k < 256 := by omega
  have e : s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) = slot P k := by rw [sp, sl_slot _ hk']
  refine Runs.append (mul128_runs s k direct (by omega) (by rw [sp]; exact hP) ha hb
    (by rw [e]; exact hda) (by rw [e]; exact hdb) (fun j hj => by
      rw [← ofNat_add_assoc, e]; exact hW j hj)) fun t ⟨l0, l1, so, v, tf⟩ => ?_
  rw [e] at so
  have tsp : t.sp = P := by
    show t.regs 13 = P
    rw [tf 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp
  rw [← sl_slot P hk'] at so
  obtain ⟨F', f1, f2, f3, f4, f5⟩ := slotOut fr hk hk' so
  exact cont t F' l0 l1 tsp f1 f2 f3 f4 f5 v

/-- `sqr128 k direct`: the square of the 16-byte input at `r1` into slots `k ..`. -/
theorem sqr_step {P : Word} {m0 : Mem} {F : Nat → Word} (s : State) {k : Nat} (direct : Bool)
    (hk : k + 8 ≤ 37) (sp : s.sp = P) (fr : FrameOk P 37 m0 F s.mem) (hP : P.toNat % 4 = 0)
    (ha : (s.regs 1).toNat % 4 = 0) (hda : Disj (s.regs 1) 16 (slot P k) 32)
    (hW : ∀ j < 32, Wr (slot P k + BitVec.ofNat 32 j))
    (cont : ∀ (t : State) (F' : Nat → Word) (l0 l1 : Word), t.sp = P →
      FrameOk P 37 m0 F' t.mem → (∀ i, (i < k ∨ k + 8 ≤ i) → F' i = F i) → F' k = l0 →
      F' (k + 1) = l1 →
      (∀ j (hj : j < (cregs direct t).length), F' (k + coff direct / 4 + j) = (cregs direct t)[j]) →
      l0.toNat + 2 ^ 32 * l1.toNat + 2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) +
          2 ^ 192 * (t.regs 4).toNat + 2 ^ 224 * (t.regs 5).toNat =
        opv s.mem (s.regs 1) * opv s.mem (s.regs 1) →
      Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (sqr128 k direct ++ is) s Q := by
  have hk' : k < 256 := by omega
  have e : s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) = slot P k := by rw [sp, sl_slot _ hk']
  refine Runs.append (sqr128_runs s k direct (by omega) (by rw [sp]; exact hP) ha
    (by rw [e]; exact hda) (fun j hj => by
      rw [← ofNat_add_assoc, e]; exact hW j hj)) fun t ⟨l0, l1, so, v, tf⟩ => ?_
  rw [e] at so
  have tsp : t.sp = P := by
    show t.regs 13 = P
    rw [tf 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp
  rw [← sl_slot P hk'] at so
  obtain ⟨F', f1, f2, f3, f4, f5⟩ := slotOut fr hk hk' so
  exact cont t F' l0 l1 tsp f1 f2 f3 f4 f5 v

/-- `diff256 p o`: `|X0 - X1|` of the buffer whose pointer is in slot `p`, into slots `o ..`. -/
theorem diff_step {P : Word} {m0 : Mem} {F : Nat → Word} (s : State) (p o : Nat) (hp : p < 37)
    (ho : o + 4 ≤ 37) (sp : s.sp = P) (fr : FrameOk P 37 m0 F s.mem) (hP : P.toNat % 4 = 0)
    (hA : (F p).toNat % 4 = 0) (hW : ∀ j < 16, Wr (slot P o + BitVec.ofNat 32 j))
    (cont : ∀ t : State, t.sp = P →
      FrameOk P 37 m0 (upd F o [t.regs 4, t.regs 5, t.regs 6, t.regs 7]) t.mem →
      t.regs 0 = mask (decide (opv s.mem (F p) < opv s.mem (F p + BitVec.ofNat 32 16))) →
      (opv s.mem (F p) : Int) - opv s.mem (F p + BitVec.ofNat 32 16) =
        (if opv s.mem (F p) < opv s.mem (F p + BitVec.ofNat 32 16)
          then -(w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7) : Int)
          else w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7)) →
      (∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r) → Runs (AccOk Wr) is t Q) :
    Runs (AccOk Wr) (diff256 p o ++ is) s Q := by
  have epp : s.sp + BitVec.ofNat 32 (p % 256 * 4) = slot P p := by
    rw [sp, Nat.mod_eq_of_lt (by omega)]; simp only [slot, Nat.mul_comm]
  have hA' : read32 s.mem (s.sp + BitVec.ofNat 32 (p % 256 * 4)) = F p := by
    rw [epp, fr.slots p hp]
  have hD := X25519Diff.diff256_exec s p o (by omega)
  rw [hA'] at hD
  have ex : w4 (read32 s.mem (F p + BitVec.ofNat 32 (4 * 0))) (read32 s.mem (F p + BitVec.ofNat 32 (4 * 1)))
      (read32 s.mem (F p + BitVec.ofNat 32 (4 * 2))) (read32 s.mem (F p + BitVec.ofNat 32 (4 * 3))) =
      opv s.mem (F p) := rfl
  have ey := (opv_hi s.mem (F p)).symm
  obtain ⟨d0, dv, dm, df⟩ := hD
  rw [ex, ey] at d0 dv
  refine Runs.append ⟨X25519Diff.diff256_acc s p o (by rw [sp]; exact hP) (by rw [hA']; exact hA)
    (fun j hj => by
      rw [sp, Nat.mod_eq_of_lt (show o < 256 by omega), ← ofNat_add_assoc]
      simpa only [slot, Nat.mul_comm] using hW j hj), rfl⟩ fun t ht => ?_
  subst ht
  refine cont _ ?_ ?_ d0 dv df
  · show State.regs _ 13 = P
    rw [df 13 (by decide) (by decide)]; exact sp
  · rw [dm, sp]; exact fr.storeWords _ (by simp; omega)

end

/-! ### Product values in the frame -/

/-- The 8 slots of an indirect (`direct = false`) product. -/
theorem w8F_lo {F : Nat → Word} {k : Nat} {t : State} {l0 l1 : Word} (f0 : F k = l0)
    (f1 : F (k + 1) = l1)
    (fc : ∀ j (hj : j < (cregs false t).length), F (k + coff false / 4 + j) = (cregs false t)[j]) :
    w8F F k = l0.toNat + 2 ^ 32 * l1.toNat + 2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) +
      2 ^ 192 * (t.regs 4).toNat + 2 ^ 224 * (t.regs 5).toNat := by
  have g : ∀ j (hj : j < 6), F (k + 2 + j) = (cregs false t)[j]'(by simp [cregs]; omega) :=
    fun j hj => fc j _
  unfold w8F
  rw [f0, f1, show k + 2 = k + 2 + 0 from rfl, g 0 (by omega), show k + 3 = k + 2 + 1 by omega,
    g 1 (by omega), show k + 4 = k + 2 + 2 by omega, g 2 (by omega), show k + 5 = k + 2 + 3 by omega,
    g 3 (by omega), show k + 6 = k + 2 + 4 by omega, g 4 (by omega),
    show k + 7 = k + 2 + 5 by omega, g 5 (by omega)]
  simp only [cregs, Bool.false_eq_true, ↓reduceIte, List.getElem_cons_zero, List.getElem_cons_succ, w4]
  omega

/-- Slots `k + 4 ..` of a direct (`direct = true`) product. -/
theorem w4F_hi {F : Nat → Word} {k : Nat} {t : State}
    (fc : ∀ j (hj : j < (cregs true t).length), F (k + coff true / 4 + j) = (cregs true t)[j]) :
    F (k + 4) = t.regs 2 ∧ F (k + 5) = t.regs 3 ∧ F (k + 6) = t.regs 4 ∧ F (k + 7) = t.regs 5 := by
  have g : ∀ j (hj : j < 4), F (k + 4 + j) = (cregs true t)[j]'(by simp [cregs]; omega) :=
    fun j hj => fc j _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := g 0 (by omega); simpa [cregs] using this
  · have := g 1 (by omega); simpa [cregs, Nat.add_assoc] using this
  · have := g 2 (by omega); simpa [cregs, Nat.add_assoc] using this
  · have := g 3 (by omega); simpa [cregs, Nat.add_assoc] using this

/-- `combine_reduce`'s 256-bit frame reads are the frame's slots. -/
theorem w8_eq {P : Word} {m0 : Mem} {F : Nat → Word} {m : Mem} (fr : FrameOk P 37 m0 F m) {k : Nat}
    (hk : k + 8 ≤ 37) : X25519CR.w8 m P k = w8F F k := by
  unfold X25519CR.w8 w8F X25519CR.fr
  rw [fr.slots k (by omega), fr.slots (k + 1) (by omega), fr.slots (k + 2) (by omega),
    fr.slots (k + 3) (by omega), fr.slots (k + 4) (by omega), fr.slots (k + 5) (by omega),
    fr.slots (k + 6) (by omega), fr.slots (k + 7) (by omega)]

/-- `add sp, #i`: only SP changes. -/
theorem regs_addSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addSp i).next s).regs r = if r = 13 then s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem regs_addImm8_16 (s : State) (d : LowReg) :
    ((Instr.addImm8 d 16).next s).regs d.toReg = s.regs d.toReg + BitVec.ofNat 32 16 := by
  rw [X25519Mem.regs_addImm8 _ _ _ _ (InstrNext.toReg_ne15 d), if_pos rfl, M0Crypto.Release.add_flags]; rfl

end M0Crypto.Release.X25519FeSteps
