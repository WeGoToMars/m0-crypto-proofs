import M0Crypto.Release.Reach

set_option linter.unusedSimpArgs false

/-!
Shared frame bookkeeping for the whole-function proofs: address arithmetic, the `Region`
reading, word reads and writes of stack slots, `bytesAt` lemmas, blocks that write only
SP-relative frame slots, and register-list helpers. Function-specific frames live with their
function (`Frame` for `m0c_chacha20_xor`).
-/

namespace M0Crypto.Release.Frame

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb

/-- A stack-relative word store advances the PC and writes its selected slot. -/
theorem strSp_next (t : State) (src : LowReg) (k : Nat) (hk : k < 256) :
    (Instr.strSp src (BitVec.ofNat 8 k)).next t =
      { t.setReg 15 (t.pc + 2#32) with mem := write32 t.mem (slot (t.regs 13) k) (t.regs src.toReg) } := by
  simp only [Instr.next, Instr.exec, M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, Instr.size]
  congr 3
  simp [slot, Nat.mod_eq_of_lt hk, Nat.mul_comm]

/-! ## Address arithmetic -/

theorem toNat_add_ofNat (a : Word) (i : Nat) (h : a.toNat + i < 2 ^ 32) :
    (a + BitVec.ofNat 32 i).toNat = a.toNat + i := by
  simp [BitVec.toNat_add]; omega

theorem sub_ofNat_toNat (a : Word) (i : Nat) (hi : i < 2 ^ 32) :
    (a + BitVec.ofNat 32 i - a).toNat = i := by
  have : a + BitVec.ofNat 32 i - a = BitVec.ofNat 32 i := by bv_omega
  rw [this]; simp [Nat.mod_eq_of_lt hi]

theorem eq_add_sub (a y : Word) : y = a + BitVec.ofNat 32 (y - a).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-! ## `Region`: the offset reading -/

/-- A byte at an offset below `n` is in the region. -/
theorem _root_.M0Crypto.Release.Region.mk {a y : Word} {n o : Nat} (h : o < n)
    (e : y = a + BitVec.ofNat 32 o) : Region a n y := by
  subst e
  have : a + BitVec.ofNat 32 o - a = BitVec.ofNat 32 o := by bv_omega
  show (a + BitVec.ofNat 32 o - a).toNat < n
  rw [this, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- A byte of the region is at an offset below `n`. -/
theorem _root_.M0Crypto.Release.Region.exists {a y : Word} {n : Nat} (h : Region a n y) :
    ∃ o < n, y = a + BitVec.ofNat 32 o := ⟨_, h, eq_add_sub a y⟩

/-- Outside the region: different from every byte of it. -/
theorem _root_.M0Crypto.Release.Region.ne {a y : Word} {n : Nat} (h : ¬ Region a n y) :
    ∀ o < n, y ≠ a + BitVec.ofNat 32 o := fun _ ho e => h (.mk ho e)

theorem _root_.M0Crypto.Release.Region.not {a y : Word} {n : Nat}
    (h : ∀ o < n, y ≠ a + BitVec.ofNat 32 o) : ¬ Region a n y := fun r =>
  let ⟨o, ho, e⟩ := Region.exists r; h o ho e

/-- Two addresses in non-overlapping, non-wrapping intervals differ. -/
theorem ne_of_disj {a b : Word} {n m i j : Nat} (ha : a.toNat + n ≤ 2 ^ 32)
    (hb : b.toNat + m ≤ 2 ^ 32) (hd : a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)
    (hi : i < n) (hj : j < m) : a + BitVec.ofNat 32 i ≠ b + BitVec.ofNat 32 j := by
  intro h
  have := congrArg BitVec.toNat h
  rw [toNat_add_ofNat a i (by omega), toNat_add_ofNat b j (by omega)] at this
  omega

/-- Bytes `4i + p` and `4j + q` of a slot array are distinct for distinct slots. -/
theorem slot_byte_ne' (sp : Word) (i j p q : Nat) (hi : i < 2 ^ 28) (hj : j < 2 ^ 28)
    (hp : p < 4) (hq : q < 4) (hij : i ≠ j) :
    slot sp i + BitVec.ofNat 32 p ≠ slot sp j + BitVec.ofNat 32 q := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem read32_congr {m m' : Mem} {a : Word} (h : ∀ k < 4, m' (a + BitVec.ofNat 32 k) = m (a + BitVec.ofNat 32 k)) :
    read32 m' a = read32 m a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read32]
  rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, h0, h1, h2, h3]

/-- Reading a word from a short list of consecutive word stores. -/
theorem read32_storeWords_same (m : Mem) : ∀ (a : Word) (vs : List Word) (i : Nat) (hi : i < vs.length),
    vs.length ≤ 2 ^ 28 → read32 (storeWords m a vs) (a + BitVec.ofNat 32 (4 * i)) = vs[i]
  | _, [], _, hi, _ => absurd hi (by simp)
  | a, v :: vs, 0, _, hl => by
    simp only [storeWords, Nat.mul_zero, BitVec.add_zero, List.getElem_cons_zero]
    rw [Frame.read32_congr (m := write32 m a v)]
    · exact M0Crypto.Armv6M.read32_write32_same m a v
    · intro k hk
      apply storeWords_other
      intro j q hj hq e
      have := congrArg BitVec.toNat e
      simp only [List.length_cons] at hl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
  | a, v :: vs, i + 1, hi, hl => by
    simp only [storeWords, List.getElem_cons_succ]
    have := read32_storeWords_same (write32 m a v) (a + 4#32) vs i
      (by simp only [List.length_cons] at hi; omega) (by simp only [List.length_cons] at hl; omega)
    rw [← this, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc, show 4 + 4 * i = 4 * (i + 1) by omega]

theorem read32_write32_slot' (m : Mem) (sp v : Word) (i j : Nat) (hi : i < 2 ^ 28) (hj : j < 2 ^ 28) :
    read32 (write32 m (slot sp i) v) (slot sp j) = if i = j then v else read32 m (slot sp j) := by
  split
  · subst_vars; exact M0Crypto.Armv6M.read32_write32_same m _ v
  · rename_i hij
    apply read32_congr
    intro k hk
    apply M0Crypto.Armv6M.write32_other
    intro q hq
    exact (slot_byte_ne' sp i j q k hi hj hq hk hij).symm

/-- Byte `p` of the word at `a`. -/
theorem byte_of_read32 (m : Mem) (a : Word) (p : Nat) (hp : p < 4) :
    m (a + BitVec.ofNat 32 p) = (read32 m a).extractLsb' (8 * p) 8 := by
  simp only [read32]
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl
  all_goals
    try simp only [BitVec.add_zero]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    try simp (config := { decide := true }) only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    repeat' split
    all_goals first
      | omega
      | rfl
      | (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega)

/-! ## Helper lemmas -/

theorem and_not3_toNat (a : Word) : (a &&& ~~~3#32).toNat = a.toNat - a.toNat % 4 := by
  have h1 : (a &&& ~~~3#32) &&& (a &&& 3#32) = 0 := by
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases a[i] <;> cases (3#32)[i] <;> simp
  have h2 : (a &&& ~~~3#32) + (a &&& 3#32) = a := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ h1]
    ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
    cases a[i] <;> cases (3#32)[i] <;> rfl
  have h3 : (a &&& 3#32).toNat = a.toNat % 4 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod a.toNat 2
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_add, h3] at this
  have : a.toNat < 2 ^ 32 := a.isLt
  have : (a &&& ~~~3#32).toNat < 2 ^ 32 := (a &&& ~~~3#32).isLt
  omega

/-- Literal-pool address of `ldr rt, [pc, #imm*4]` at offset `off`. -/
theorem lit_addr (base : Word) (hb : base.toNat % 4 = 0) (off imm : Nat)
    (h : base.toNat + off + 4 + imm * 4 < 2 ^ 32) :
    ((base + BitVec.ofNat 32 off + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm * 4) =
      base + BitVec.ofNat 32 ((off + 4) / 4 * 4 + imm * 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and_not3_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The little-endian word of the artifact at offset `off`. -/
def codeWord (off : Nat) : Word :=
  B.getD (off + 3) 0 ++ B.getD (off + 2) 0 ++ B.getD (off + 1) 0 ++ B.getD off 0

theorem read32_code {m : Mem} {base : Word} (hc : CodeAt m base B) (off : Nat) (h : off + 4 ≤ Artifacts.Release.size) :
    read32 m (base + BitVec.ofNat 32 off) = codeWord off := by
  have hl := B_len
  simp only [read32, codeWord]
  rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc,
    hc off (by omega), hc (off + 1) (by omega), hc (off + 2) (by omega), hc (off + 3) (by omega)]
  simp [List.getD_eq_getElem?_getD, show off < B.length by omega, show off + 1 < B.length by omega,
    show off + 2 < B.length by omega, show off + 3 < B.length by omega]

theorem bytesAt_succ (m : Mem) (a : Word) (n : Nat) :
    Ctx.bytesAt m a (n + 1) = m a :: Ctx.bytesAt m (a + 1#32) n := rfl

theorem bytesAt_get (m : Mem) : ∀ (a : Word) (n i : Nat), i < n →
    (Ctx.bytesAt m a n)[i]? = some (m (a + BitVec.ofNat 32 i))
  | a, n + 1, 0, _ => by simp [bytesAt_succ]
  | a, n + 1, i + 1, h => by
    rw [bytesAt_succ, List.getElem?_cons_succ, bytesAt_get m _ n i (by omega)]
    rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_assoc, Nat.add_comm 1 i]

theorem bytesAt_length (m : Mem) : ∀ (a : Word) (n : Nat), (Ctx.bytesAt m a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by rw [bytesAt_succ, List.length_cons, bytesAt_length m _ n]

/-! ## Blocks writing only to SP-relative frame slots -/

/-- Every instruction is a `str rt, [sp, #4k]` with `k < n`, or writes no memory and not SP. -/
def frameWB (n : Nat) (is : List Instr) : Bool := is.all fun i => match i with
  | .strSp _ k => decide (k.toNat < n)
  | i => !i.writesMem && !(i.dsts.contains 13)

def InFrame (sp : Word) (n : Nat) (y : Word) : Prop := ∃ o < 4 * n, y = sp + BitVec.ofNat 32 o

theorem frameWB_cons {n : Nat} {i : Instr} {is : List Instr} (h : frameWB n (i :: is) = true) :
    frameWB n is = true := by
  simp only [frameWB, List.all_cons, Bool.and_eq_true] at h ⊢; exact h.2

theorem frameWB_head {n : Nat} {i : Instr} {is : List Instr} (h : frameWB n (i :: is) = true) :
    13 ∉ i.dsts ∧ ∀ (s : State) y, Writes (i.accesses s) y → InFrame (s.regs 13) n y := by
  simp only [frameWB, List.all_cons, Bool.and_eq_true] at h
  have h1 := h.1
  cases i
  case strSp t k =>
    simp only [decide_eq_true_eq] at h1
    refine ⟨by simp [Instr.dsts], ?_⟩
    rintro s y ⟨a, ha, -, j, hj, rfl⟩
    simp only [Instr.accesses, List.mem_singleton] at ha; subst ha
    exact ⟨k.toNat * 4 + j, by simp at hj; omega, by simp [M0Crypto.Armv6M.State.sp, ofNat_add_assoc]⟩
  all_goals
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h1
    refine ⟨h1.2, ?_⟩
    rintro s y ⟨a, ha, hw, -⟩
    rw [accesses_read h1.1 s a ha] at hw; cases hw

theorem frameWB_sp {n : Nat} : ∀ (is : List Instr) (s : State), frameWB n is = true →
    (execAll is s).regs 13 = s.regs 13
  | [], _, _ => rfl
  | i :: is, s, h => by
    rw [execAll, frameWB_sp is _ (frameWB_cons h)]
    exact next_regs_other s 13 (by decide) (frameWB_head h).1

theorem frameWB_writes {n : Nat} : ∀ (is : List Instr) (s : State), frameWB n is = true →
    ∀ e ∈ traceAll is s, ∀ y, Writes e.accesses y → InFrame (s.regs 13) n y
  | [], _, _ => by intro e he; cases he
  | i :: is, s, h => by
    intro e he y hy
    rcases List.mem_cons.mp he with rfl | h'
    · exact (frameWB_head h).2 s y hy
    · have := frameWB_writes is (i.next s) (frameWB_cons h) e h' y hy
      rwa [next_regs_other s 13 (by decide) (frameWB_head h).1] at this

theorem frameWB_mem {n : Nat} : ∀ (is : List Instr) (s : State), frameWB n is = true →
    is.all Instr.falls = true → ∀ y, ¬ InFrame (s.regs 13) n y → (execAll is s).mem y = s.mem y
  | [], _, _, _, _, _ => rfl
  | i :: is, s, h, hf, y, hy => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    have h13 := next_regs_other s 13 (by decide) (frameWB_head h).1
    rw [execAll, frameWB_mem is _ (frameWB_cons h) hf.2 y (by rw [h13]; exact hy)]
    exact exec_mem_other i s _ (exec_ok_of_falls hf.1 s) y (fun hw => hy ((frameWB_head h).2 s y hw))

/-! ## Saved registers and register-list helpers -/

/-- Saved register words at slots 35..43: r8-r11, r4-r7, LR. -/
def saved (r : Reg → Word) (i : Nat) : Word :=
  match i with
  | 0 => r 8 | 1 => r 9 | 2 => r 10 | 3 => r 11
  | 4 => r 4 | 5 => r 5 | 6 => r 6 | 7 => r 7 | _ => r 14

theorem listRegs_f0 : listRegs 0xf0 = [4, 5, 6, 7] := by decide

theorem listRegs_240 : listRegs 240#8 = [4, 5, 6, 7] := by decide

theorem bitCount_f0 : bitCount 0xf0 = 4 := by decide

theorem four_eq : (4#32 : Word) = BitVec.ofNat 32 4 := rfl

theorem slot_eq (fp : Word) (i : Nat) : slot fp i = fp + BitVec.ofNat 32 (4 * i) := rfl

end M0Crypto.Release.Frame
