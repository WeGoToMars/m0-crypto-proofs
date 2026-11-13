import M0Crypto.Release.X25519Mul128
import M0Crypto.Release.X25519Frame
import M0Crypto.Release.X25519MulcFacts

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
Pieces shared by the routine proofs of `m0c_fe_mul` and `m0c_fe_sqr` (plan `x25519-proofs.md`,
phase 8).

* Runs of the single memory instructions of the prologue and epilogue: `push {lr}`
  (`push_run`), `str rd, [sp, #4k]` (`strSp_run`), `ldr rd, [sp, #4k]` (`ldrSp_run`). The
  register-only instructions use `Runs.reg`.
* The frame as `FrameOk` (`X25519Frame`): `FrameOk.refresh` re-reads a block of slots after a
  store that stays inside it; `FrameOk.slotOut` turns the `SlotOut` post of `mul128` and
  `sqr128` into frame slots.
* `feVal` as two 128-bit halves (`feVal_halves`) and of an 8-word store (`feVal_store8`).
-/

namespace M0Crypto.Release.X25519FeCommon
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj InFrame read32_congr toNat_add_ofNat)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Slot (ld SlotOut)
open M0Crypto.Release.X25519Comb (coff cregs)
open M0Crypto.Release.X25519Macros (sl)
open M0Crypto.Release.X25519Mul128 (opv)
open M0Crypto.Release.X25519W4 (w4)
open M0Crypto.Release.X25519MulcChain (psum)
open M0Crypto.Release.X25519MulcFacts (feVal_psum)
open M0Crypto.Release.X25519Routines (feVal)

/-! ### Slots -/

theorem sl_slot (sp : Word) {k : Nat} (hk : k < 256) :
    sp + BitVec.ofNat 32 ((sl k).toNat * 4) = slot sp k := by
  simp only [sl, BitVec.toNat_ofNat, slot, Nat.mod_eq_of_lt hk, Nat.mul_comm]

theorem slot_add (p : Word) (k j : Nat) : slot p k + BitVec.ofNat 32 (4 * j) = slot p (k + j) := by
  simp only [slot, ofNat_add_assoc, Nat.mul_add]

/-! ### Single memory instructions -/

theorem push_run {Wr : Word → Prop} (s : State) (hsp : s.sp.toNat % 4 = 0)
    (hW : ∀ q < 4, Wr (s.sp - 4#32 + BitVec.ofNat 32 q)) :
    Runs (AccOk Wr) [.push 0 true] s fun t =>
      t.mem = write32 s.mem (s.sp - 4#32) (s.regs 14) ∧ t.regs 13 = s.sp - 4#32 ∧
        ∀ r : Reg, r ≠ 15 → r ≠ 13 → t.regs r = s.regs r := by
  have hb : bitCount (0 : BitVec 8) = 0 := by decide
  have hl : listRegs (0 : BitVec 8) = [] := by decide
  have h4 : s.sp - BitVec.ofNat 32 (4 * (bitCount (0 : BitVec 8) + true.toNat)) = s.sp - 4#32 := by
    rw [hb]; rfl
  refine ⟨accAll_cons (fun a ha => ?_) (accAll_nil _ _), ?_⟩
  · simp only [Instr.accesses, h4, hb] at ha
    have hal : (s.sp - 4#32).toNat % 4 = 0 := by
      have : (s.sp - 4#32).toNat = (s.sp.toNat + (2 ^ 32 - 4)) % 2 ^ 32 := by
        simp [BitVec.toNat_sub]; omega
      omega
    refine wordAccesses_ok hal (fun _ i hi q hq => ?_) a ha
    simp only [Bool.toNat_true] at hi
    rw [show i = 0 by omega]; simpa using hW q hq
  · simp only [execAll, Instr.next, Instr.exec, h4, hl, List.map_nil, List.nil_append, ite_true,
      storeWords, State.setReg]
    refine ⟨by simp, by simp, fun r h15 h13 => by simp [h15, h13]⟩

theorem strSp_run {Wr : Word → Prop} (s : State) (d : LowReg) {k : Nat} (hk : k < 256)
    (hsp : s.sp.toNat % 4 = 0) (hW : ∀ q < 4, Wr (slot s.sp k + BitVec.ofNat 32 q)) :
    Runs (AccOk Wr) [.strSp d (sl k)] s fun t =>
      t.mem = write32 s.mem (slot s.sp k) (s.reg d) ∧ ∀ r : Reg, r ≠ 15 → t.regs r = s.regs r := by
  refine ⟨accAll_cons (fun a ha => ?_) (accAll_nil _ _), ?_⟩
  · simp only [Instr.accesses, List.mem_singleton, sl_slot _ hk] at ha
    subst ha
    refine ⟨aligned_word (by simp only [slot]; exact word_add_aligned hsp (by omega)),
      fun _ q hq => hW q hq⟩
  · simp only [execAll, Instr.next, Instr.exec, sl_slot _ hk]
    exact ⟨by simp, fun r h15 => by simp [State.setReg, h15]⟩

theorem ldrSp_run {Wr : Word → Prop} (s : State) (d : LowReg) {k : Nat} (hk : k < 256)
    (hsp : s.sp.toNat % 4 = 0) :
    Runs (AccOk Wr) [.ldrSp d (sl k)] s fun t =>
      t.mem = s.mem ∧ t.regs d.toReg = read32 s.mem (slot s.sp k) ∧
        ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → t.regs r = s.regs r := by
  refine ⟨accAll_cons (fun a ha => ?_) (accAll_nil _ _), ?_⟩
  · simp only [Instr.accesses, List.mem_singleton, sl_slot _ hk] at ha
    subst ha
    exact ⟨aligned_word (by simp only [slot]; exact word_add_aligned hsp (by omega)),
      fun h => by cases h⟩
  · simp only [execAll]
    refine ⟨X25519Mem.mem_ldrSp _ _ _, ?_, fun r h15 hd => ?_⟩
    · rw [X25519Mem.regs_ldrSp _ _ _ _ (Blake2s.toReg_ne15 d), ite_eq_left_of_eq_true _ _ (eq_true rfl), sl_slot _ hk]
    · rw [X25519Mem.regs_ldrSp _ _ _ _ h15, if_neg hd]

/-! ### The frame -/

/-- After a store inside slots `[k, k + w)`, the frame reads those slots afresh. -/
theorem refresh {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m m' : Mem}
    (h : FrameOk fp n m0 F m) {k w : Nat} (hk : k + w ≤ n)
    (hm : ∀ y, (∀ i < 4 * w, y ≠ slot fp k + BitVec.ofNat 32 i) → m' y = m y) :
    FrameOk fp n m0 (fun i => if k ≤ i ∧ i < k + w then read32 m' (slot fp i) else F i) m' := by
  have hf := h.fits
  refine ⟨hf, fun i hi => ?_, fun y hy => ?_⟩
  · split
    · rfl
    · rename_i hn
      rw [← h.slots i hi]
      apply read32_congr
      intro q hq
      apply hm
      intro j hj e
      rw [slot_byte, slot_byte] at e
      have := congrArg BitVec.toNat e
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
      omega
  · rw [hm y fun i hi e => hy ⟨4 * k + i, by omega, by rw [e, slot_byte]⟩]
    exact h.out y hy

/-- The `SlotOut` post of `mul128` / `sqr128` at slot `k` of the frame. -/
theorem slotOut {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m m' : Mem}
    (h : FrameOk fp n m0 F m) {k : Nat} (hk : k + 8 ≤ n) (hk' : k < 256) {direct : Bool}
    {l0 l1 : Word} {t : State}
    (hs : SlotOut m m' (fp + BitVec.ofNat 32 ((sl k).toNat * 4)) direct l0 l1 t) :
    ∃ F' : Nat → Word, FrameOk fp n m0 F' m' ∧ (∀ i, (i < k ∨ k + 8 ≤ i) → F' i = F i) ∧
      F' k = l0 ∧ F' (k + 1) = l1 ∧
      ∀ j (hj : j < (cregs direct t).length), F' (k + coff direct / 4 + j) = (cregs direct t)[j] := by
  rw [sl_slot _ hk'] at hs
  obtain ⟨s0, s1, sc, so⟩ := hs
  refine ⟨_, refresh h hk fun y hy => so y hy, fun i hi => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega), ← s0]; unfold ld; rw [slot_add, Nat.add_zero]
  · rw [if_pos (by omega), ← s1]; unfold ld; rw [slot_add]
  · have hl := X25519Comb.cregs_length direct t
    have hc : coff direct = 4 * (coff direct / 4) ∧ coff direct / 4 + (cregs direct t).length = 8 := by
      cases direct <;> simp [coff, cregs]
    rw [if_pos (by omega), ← sc j hj]; unfold ld
    rw [hc.1, slot_add, slot_add, Nat.add_assoc]
    cases direct <;> simp [coff, Nat.add_assoc]

/-! ### Values -/

/-- `feVal` as the low and high 128-bit halves. -/
theorem feVal_halves (m : Mem) (a : Word) :
    feVal m a = opv m a + 2 ^ 128 * opv m (a + BitVec.ofNat 32 16) := by
  have e : ∀ j, a + BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * j) = slot a (4 + j) := fun j => by
    simp only [slot, ofNat_add_assoc, Nat.mul_add]
  have e0 : ∀ j, a + BitVec.ofNat 32 (4 * j) = slot a j := fun j => rfl
  rw [feVal_psum]
  unfold opv w4 ld
  rw [e 0, e 1, e 2, e 3, e0 0, e0 1, e0 2, e0 3]
  simp only [psum, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero]
  omega

/-- `feVal` of an 8-word store at `a`. -/
theorem feVal_store8 (m : Mem) (a : Word) (o0 o1 o2 o3 o4 o5 o6 o7 : Word) :
    feVal (storeWords m a [o0, o1, o2, o3, o4, o5, o6, o7]) a =
      w4 o0 o1 o2 o3 + 2 ^ 128 * w4 o4 o5 o6 o7 := by
  have r : ∀ i (hi : i < 8), read32 (storeWords m a [o0, o1, o2, o3, o4, o5, o6, o7]) (slot a i) =
      [o0, o1, o2, o3, o4, o5, o6, o7][i] := fun i hi =>
    Frame.read32_storeWords_same m a _ i (by simpa using hi) (by simp)
  rw [feVal_psum]
  simp only [psum, r 0 (by omega), r 1 (by omega), r 2 (by omega), r 3 (by omega), r 4 (by omega),
    r 5 (by omega), r 6 (by omega), r 7 (by omega), w4]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  omega

/-! ### Disjointness -/

/-- A window of `a` and a window of `b`, from disjoint `a` and `b`. -/
theorem disj_shift {a b : Word} {n m : Nat} (h : Disj a n b m) {o1 l1 o2 l2 : Nat}
    (h1 : o1 + l1 ≤ n) (h2 : o2 + l2 ≤ m) (hl1 : 0 < l1) (hl2 : 0 < l2) :
    Disj (a + BitVec.ofNat 32 o1) l1 (b + BitVec.ofNat 32 o2) l2 := by
  obtain ⟨d1, d2, d3⟩ := h
  unfold Disj
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

/-- Two disjoint windows of one non-wrapping region. -/
theorem disj_in {b : Word} {n : Nat} (hf : b.toNat + n ≤ 2 ^ 32) {o1 l1 o2 l2 : Nat}
    (h1 : o1 + l1 ≤ n) (h2 : o2 + l2 ≤ n) (hs : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) (hl1 : 0 < l1)
    (hl2 : 0 < l2) : Disj (b + BitVec.ofNat 32 o1) l1 (b + BitVec.ofNat 32 o2) l2 := by
  unfold Disj
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
  omega

theorem add_zero' (a : Word) : a + BitVec.ofNat 32 0 = a := by simp

/-! ### The routine frame of `m0c_fe_mul` and `m0c_fe_sqr` -/

section
open M0Crypto.Release.X25519Routines (Call mulFrame)
variable (c : Call)

abbrev fp : Word := c.fp mulFrame

theorem fp_toNat (hlo : mulFrame ≤ c.sp0.toNat) : (fp c).toNat = c.sp0.toNat - 148 := by
  simp only [mulFrame] at hlo
  simp only [fp, Call.fp, mulFrame, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem fp_fits (hlo : mulFrame ≤ c.sp0.toNat) : (fp c).toNat + 4 * 37 ≤ 2 ^ 32 := by
  have := c.sp0.isLt; rw [fp_toNat c hlo]; omega

theorem fp_al (h4 : c.sp0.toNat % 4 = 0) (hlo : mulFrame ≤ c.sp0.toNat) : (fp c).toNat % 4 = 0 := by
  rw [fp_toNat c hlo]; simp only [mulFrame] at hlo; omega

theorem slot36 : slot (fp c) 36 = c.sp0 - 4#32 := by
  simp only [slot, fp, Call.fp, mulFrame]; bv_omega

theorem fp_sub : c.sp0 - 4#32 - BitVec.ofNat 32 ((BitVec.ofNat 7 X25519Macros.SFRAME).toNat * 4) = fp c := by
  simp only [fp, Call.fp, mulFrame, X25519Macros.SFRAME, BitVec.toNat_ofNat]; bv_omega

theorem fp_add : fp c + BitVec.ofNat 32 ((BitVec.ofNat 7 X25519Macros.SFRAME).toNat * 4) = c.sp0 - 4#32 := by
  simp only [fp, Call.fp, mulFrame, X25519Macros.SFRAME, BitVec.toNat_ofNat]; bv_omega

theorem wr_fp {o : Nat} (ho : o < 148) : Region (fp c) mulFrame (fp c + BitVec.ofNat 32 o) := by
  show (fp c + BitVec.ofNat 32 o - fp c).toNat < 148
  rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact ho

theorem wr_slot {k q : Nat} (hk : k < 37) (hq : q < 4) :
    Region (fp c) mulFrame (slot (fp c) k + BitVec.ofNat 32 q) := by
  rw [slot_byte]; exact wr_fp c (by omega)

theorem wr_sl {k j : Nat} (h : k * 4 + j < 148) :
    Region (fp c) mulFrame (fp c + BitVec.ofNat 32 ((sl k).toNat * 4 + j)) := by
  have : (sl k).toNat ≤ k := by simp only [sl, BitVec.toNat_ofNat]; omega
  exact wr_fp c (by omega)

theorem frame_init (hlo : mulFrame ≤ c.sp0.toNat) :
    FrameOk (fp c) 37 c.m0 (fun i => read32 c.m0 (slot (fp c) i)) c.m0 :=
  ⟨fp_fits c hlo, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Bytes outside the routine's stack bytes are outside the frame. -/
theorem not_inFrame {y : Word} (h : ¬ Region (fp c) mulFrame y) : ¬ InFrame (fp c) 37 y := by
  rintro ⟨o, ho, rfl⟩; exact h (wr_fp c ho)

end

/-! ### Frame values -/

theorem upd_ne (F : Nat → Word) {k i : Nat} (v : Word) (h : i ≠ k) : upd F k [v] i = F i := by
  simp only [upd, List.length_singleton]; split <;> first | rfl | omega

theorem upd_eq (F : Nat → Word) (k : Nat) (v : Word) : upd F k [v] k = v := by simp [upd]

theorem upd_out (F : Nat → Word) {k i : Nat} (vs : List Word) (h : i < k ∨ k + vs.length ≤ i) :
    upd F k vs i = F i := by
  simp only [upd]; split <;> first | rfl | omega

theorem upd_in (F : Nat → Word) (k : Nat) (vs : List Word) (j : Nat) (hj : j < vs.length) :
    upd F k vs (k + j) = vs[j] := by
  simp only [upd, if_pos (show k ≤ k + j ∧ k + j < k + vs.length by omega), Nat.add_sub_cancel_left]
  simp [hj]

/-- Eight frame slots from `k` as one 256-bit value. -/
def w8F (F : Nat → Word) (k : Nat) : Nat :=
  w4 (F k) (F (k + 1)) (F (k + 2)) (F (k + 3)) + 2 ^ 128 * w4 (F (k + 4)) (F (k + 5)) (F (k + 6)) (F (k + 7))

theorem w8F_congr {F G : Nat → Word} {k : Nat} (h : ∀ i, k ≤ i → i < k + 8 → F i = G i) :
    w8F F k = w8F G k := by
  unfold w8F
  rw [h k (by omega) (by omega), h (k + 1) (by omega) (by omega), h (k + 2) (by omega) (by omega),
    h (k + 3) (by omega) (by omega), h (k + 4) (by omega) (by omega), h (k + 5) (by omega) (by omega),
    h (k + 6) (by omega) (by omega), h (k + 7) (by omega) (by omega)]

/-- `opv` of a 16-byte buffer disjoint from the frame reads the entry memory. -/
theorem opv_frame {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m : Mem}
    (h : FrameOk fp n m0 F m) {p : Word} (hd : Disj p 16 fp (4 * n)) : opv m p = opv m0 p := by
  unfold opv ld
  rw [h.read_disj hd (i := 0) (by omega), h.read_disj hd (i := 1) (by omega),
    h.read_disj hd (i := 2) (by omega), h.read_disj hd (i := 3) (by omega)]

/-- `opv` of four frame slots. -/
theorem opv_slot {fp : Word} {n : Nat} {m0 : Mem} {F : Nat → Word} {m : Mem}
    (h : FrameOk fp n m0 F m) {k : Nat} (hk : k + 4 ≤ n) :
    opv m (slot fp k) = w4 (F k) (F (k + 1)) (F (k + 2)) (F (k + 3)) := by
  unfold opv ld
  rw [slot_add, slot_add, slot_add, slot_add, Nat.add_zero, h.slots _ (by omega), h.slots _ (by omega),
    h.slots _ (by omega), h.slots _ (by omega)]

/-- The high half of a buffer, as word reads from its start. -/
theorem opv_hi (m : Mem) (a : Word) :
    opv m (a + BitVec.ofNat 32 16) = w4 (read32 m (a + BitVec.ofNat 32 (4 * 4)))
      (read32 m (a + BitVec.ofNat 32 (4 * 5))) (read32 m (a + BitVec.ofNat 32 (4 * 6)))
      (read32 m (a + BitVec.ofNat 32 (4 * 7))) := by
  unfold opv ld
  simp only [ofNat_add_assoc]

/-- `~(mA ^ mB)` for two sign masks is the mask of equal signs. -/
theorem not_xor_masks (x y : Bool) :
    ~~~(X25519W4.mask y ^^^ X25519W4.mask x) = X25519W4.mask (x == y) := by
  cases x <;> cases y <;> decide

/-- A word disjoint from a word store reads as before. -/
theorem read_store_disj (m : Mem) {a b : Word} {ws : List Word} (hd : Disj a 4 b (4 * ws.length)) :
    read32 (storeWords m b ws) a = read32 m a := by
  have := X25519Slot.read32_storeWords_disj m a b ws hd 0 (by omega)
  simpa using this

/-- A byte outside `[b, b + 32)` is not written by an 8-word store at `b`. -/
theorem store8_out (m : Mem) {b y : Word} {ws : List Word} (hl : ws.length = 8) (hb : b.toNat + 32 ≤ 2 ^ 32)
    (hy : ¬ Region b 32 y) : storeWords m b ws y = m y := by
  apply storeWords_other
  intro i q hi hq e
  apply hy
  subst e
  show (b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q - b).toNat < 32
  rw [ofNat_add_assoc, Frame.sub_ofNat_toNat _ _ (by omega)]
  omega

end M0Crypto.Release.X25519FeCommon
