import M0Crypto.Release.Reach
import M0Crypto.Release.ChaChaSpec
import M0Crypto.Release.ChaChaLayout

set_option linter.unusedSimpArgs false

/-!
Memory bookkeeping for the whole-function proof of `m0c_chacha20_xor`.

`Ctx` fixes one call: code base, entry SP, the arguments and the entry memory and
registers. The frame after the prologue is `fp = sp0 - 176`: word slots 0..34 are
the function's frame (`X`, `J`, `LEN`, `OUTP`, `INP`), 35..43 the saved registers,
44..45 the stack arguments.
-/

namespace M0Crypto.Release.Frame

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (Byte initState)
open M0Crypto.Spec.AEAD (chacha20)
open M0Crypto.Release.ChaChaLayout (chStackBytes chFrameBytes chFrameWords slotJ slotLen slotOutp slotInp)

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

/-! ## The call -/

structure Ctx where
  base : Word
  sp0 : Word
  out : Word
  inp : Word
  len : Word
  key : Word
  nonce : Word
  ctr : Word
  m0 : Mem
  regs0 : Reg → Word

namespace Ctx

variable (c : Ctx)

/-- Frame pointer after the prologue. -/
def fp : Word := c.sp0 - BitVec.ofNat 32 chStackBytes

/-- `n` bytes of `m` from `a`. -/
def bytesAt (m : Mem) : Word → Nat → List Byte
  | _, 0 => []
  | a, n + 1 => m a :: bytesAt m (a + 1#32) n

def keyB : List Byte := bytesAt c.m0 c.key 32
def nonceB : List Byte := bytesAt c.m0 c.nonce 12
def msg : List Byte := bytesAt c.m0 c.inp c.len.toNat

/-- Expected output byte `i`. -/
def outB (i : Nat) : Byte := (chacha20 c.keyB c.ctr.toNat c.nonceB c.msg)[i]!

/-- Input state of block `k`, as a word function (0 beyond 16). -/
def J (k : Nat) (i : Nat) : Word :=
  if i < 16 then (initState c.keyB (c.ctr + BitVec.ofNat 32 k) c.nonceB)[i]! else 0

/-- Memory after the prologue: r4-r7, LR at `sp0 - 20`, r8-r11 at `sp0 - 36`. -/
def mP : Mem :=
  storeWords (storeWords c.m0 (c.sp0 - BitVec.ofNat 32 20)
    [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])
    (c.sp0 - BitVec.ofNat 32 20 - BitVec.ofNat 32 16) [c.regs0 8, c.regs0 9, c.regs0 10, c.regs0 11]

/-- Frame word `i`. -/
def fw (s : State) (i : Nat) : Word := read32 s.mem (slot c.fp i)

/-- `y` lies outside the 140-byte frame. -/
def OutF (y : Word) : Prop := ∀ o < chFrameBytes, y ≠ c.fp + BitVec.ofNat 32 o

/-- Output index of address `y`. -/
def oidx (y : Word) : Nat := (y - c.out).toNat

/-- Memory outside the frame: the first `P` output bytes are final, the rest is `mP`. -/
def MemOk (P : Nat) (m : Mem) : Prop :=
  ∀ y, c.OutF y → m y = if c.oidx y < P then c.outB (c.oidx y) else c.mP y

/-- Writes allowed to the function: its 176 stack bytes and the output buffer. -/
def Wr (y : Word) : Prop := (∃ o < chStackBytes, y = c.fp + BitVec.ofNat 32 o) ∨ c.oidx y < c.len.toNat

end Ctx

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

namespace Ctx
variable (c : Ctx)

theorem memOk_write_slot {P : Nat} {m : Mem} (h : c.MemOk P m) (k : Nat) (hk : k < chFrameWords) (v : Word) :
    c.MemOk P (write32 m (slot c.fp k) v) := by
  intro y hy
  have hb : chFrameBytes = 4 * chFrameWords := rfl
  rw [M0Crypto.Armv6M.write32_other]
  · exact h y hy
  · intro q hq e; exact hy (4 * k + q) (by omega) (by rw [e]; simp only [slot]; rw [ofNat_add_assoc])

theorem fw_write {s : State} {m : Mem} (hm : s.mem = write32 m (slot c.fp k) v) (j : Nat)
    (hk : k < 2 ^ 28) (hj : j < 2 ^ 28) :
    c.fw s j = if k = j then v else read32 m (slot c.fp j) := by
  simp only [fw, hm]; exact read32_write32_slot' m c.fp v k j hk hj

end Ctx

/-! ## The input state words -/

theorem bytesAt_succ (m : Mem) (a : Word) (n : Nat) :
    Ctx.bytesAt m a (n + 1) = m a :: Ctx.bytesAt m (a + 1#32) n := rfl

theorem bytesAt_get (m : Mem) : ∀ (a : Word) (n i : Nat), i < n →
    (Ctx.bytesAt m a n)[i]? = some (m (a + BitVec.ofNat 32 i))
  | a, n + 1, 0, _ => by simp [bytesAt_succ]
  | a, n + 1, i + 1, h => by
    rw [bytesAt_succ, List.getElem?_cons_succ, bytesAt_get m _ n i (by omega)]
    rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_assoc, Nat.add_comm 1 i]

/-- Little-endian word `i` of `n` words of memory from `a`. -/
theorem wordsOfBytes_bytesAt (m : Mem) : ∀ (n : Nat) (a : Word) (i : Nat), i < n →
    (M0Crypto.Spec.ChaCha20.wordsOfBytes (Ctx.bytesAt m a (4 * n)))[i]? =
      some (M0Crypto.Spec.ChaCha20.wordOfBytes (m (a + BitVec.ofNat 32 (4 * i)))
        (m (a + BitVec.ofNat 32 (4 * i + 1))) (m (a + BitVec.ofNat 32 (4 * i + 2)))
        (m (a + BitVec.ofNat 32 (4 * i + 3))))
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega]
    simp only [bytesAt_succ, M0Crypto.Spec.ChaCha20.wordsOfBytes]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.mul_zero, Nat.zero_add, BitVec.add_zero,
        BitVec.add_assoc, Option.some.injEq]
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ]
      rw [wordsOfBytes_bytesAt m n _ i (by omega)]
      have e4 : a + 1#32 + 1#32 + 1#32 + 1#32 = a + BitVec.ofNat 32 4 := by bv_omega
      rw [e4, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc,
        show 4 + 4 * i = 4 * (i + 1) by omega, show 4 + (4 * i + 1) = 4 * (i + 1) + 1 by omega,
        show 4 + (4 * i + 2) = 4 * (i + 1) + 2 by omega, show 4 + (4 * i + 3) = 4 * (i + 1) + 3 by omega]

theorem bytesAt_length (m : Mem) : ∀ (a : Word) (n : Nat), (Ctx.bytesAt m a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by rw [bytesAt_succ, List.length_cons, bytesAt_length m _ n]

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length initState constants) in
theorem J_list (c : Ctx) (k i : Nat) (hi : i < 16) :
    c.J k i = ((constants ++ wordsOfBytes c.keyB ++ [c.ctr + BitVec.ofNat 32 k] ++ wordsOfBytes c.nonceB)[i]?).getD 0 := by
  simp [Ctx.J, initState, hi]; rfl

/-- Key word `i` of the input state. -/
def keyW (c : Ctx) (i : Nat) : Word :=
  M0Crypto.Spec.ChaCha20.wordOfBytes (c.m0 (c.key + BitVec.ofNat 32 (4 * i)))
    (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 1))) (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 2)))
    (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 3)))

def nonceW (c : Ctx) (i : Nat) : Word :=
  M0Crypto.Spec.ChaCha20.wordOfBytes (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i)))
    (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 1))) (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 2)))
    (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 3)))

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_key (c : Ctx) (k i : Nat) (hi : i < 8) : c.J k (4 + i) = keyW c i := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  rw [J_list c k _ (by omega), Nat.add_comm, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp [constants]), List.getElem?_append_left (by simp [constants, hl]; omega)]
  simp only [constants, List.length_cons, List.length_nil, Nat.add_sub_cancel]
  have := wordsOfBytes_bytesAt c.m0 8 c.key i hi
  simp only [Nat.reduceMul] at this
  rw [Ctx.keyB, this]; rfl

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_nonce (c : Ctx) (k i : Nat) (hi : i < 3) : c.J k (13 + i) = nonceW c i := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  have hn : (wordsOfBytes c.nonceB).length = 3 := by simp [wordsOfBytes_length, Ctx.nonceB, bytesAt_length]
  rw [J_list c k _ (by omega), List.getElem?_append_right (by simp [constants, hl])]
  simp only [constants, List.length_append, List.length_cons, List.length_nil, hl]
  have := wordsOfBytes_bytesAt c.m0 3 c.nonce i hi
  simp only [Nat.reduceMul] at this
  rw [show 13 + i - (0 + 1 + 1 + 1 + 1 + 8 + (0 + 1)) = i by omega, Ctx.nonceB, this]; rfl

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_ctr (c : Ctx) (k : Nat) : c.J k 12 = c.ctr + BitVec.ofNat 32 k := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  rw [J_list c k _ (by omega), List.getElem?_append_left (by simp [constants, hl]),
    List.getElem?_append_right (by simp [constants, hl])]
  simp [constants, hl]

theorem J_const (c : Ctx) (k : Nat) :
    c.J k 0 = 0x61707865#32 ∧ c.J k 1 = 0x3320646e#32 ∧ c.J k 2 = 0x79622d32#32 ∧ c.J k 3 = 0x6b206574#32 := by
  simp [J_list, M0Crypto.Spec.ChaCha20.constants]

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

/-! ## Preconditions -/

/-- `[a, a + n)` and `[b, b + m)` do not wrap and do not overlap. -/
def Disj (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 32 ∧ b.toNat + m ≤ 2 ^ 32 ∧ (a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)

structure Valid (c : Ctx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp8 : c.sp0.toNat % 8 = 0
  spLo : 176 ≤ c.sp0.toNat
  /-- code vs. the 184 bytes of frame, saved registers and stack arguments -/
  codeF : Disj c.base Artifacts.Release.size c.fp 184
  /-- code vs. output -/
  codeO : Disj c.base Artifacts.Release.size c.out c.len.toNat
  /-- output vs. frame, saved registers and stack arguments -/
  outF : Disj c.out c.len.toNat c.fp 184
  /-- input vs. frame and saved registers -/
  inF : Disj c.inp c.len.toNat c.fp 176
  /-- exact in-place or disjoint -/
  inOut : c.inp = c.out ∨ Disj c.inp c.len.toNat c.out c.len.toNat
  keyF : Disj c.key 32 c.fp chStackBytes
  nonceF : Disj c.nonce 12 c.fp chStackBytes
  /-- the artifact is in memory at `base` -/
  code : CodeAt c.m0 c.base B

/-- State at `.Lblock` (offset `bpreOff`) before block `k`. -/
structure BlockInv (c : Ctx) (k : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 M0Crypto.Release.ChaChaLayout.bpreOff
  sp : t.regs 13 = c.fp
  j : ∀ i < 16, c.fw t (slotJ + i) = c.J k i
  len : c.fw t slotLen = c.len - BitVec.ofNat 32 (64 * k)
  outp : c.fw t slotOutp = c.out + BitVec.ofNat 32 (64 * k)
  inp : c.fw t slotInp = c.inp + BitVec.ofNat 32 (64 * k)
  mem : c.MemOk (64 * k) t.mem
  lt : 64 * k < c.len.toNat
  ok : M0Crypto.Spec.AEAD.counterOk c.ctr.toNat c.len.toNat = true

end M0Crypto.Release.Frame
