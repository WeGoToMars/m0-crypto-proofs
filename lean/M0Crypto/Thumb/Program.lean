import M0Crypto.Thumb.Exec

/-!
Program-level lemmas for the whole-function model.

* `CodeAt m base bytes`: the artifact bytes sit at `base` in memory `m`.
* `instrAt bytes off`: the instruction the artifact holds at byte offset `off`
  (a pure function of the bytes, evaluated by `decide` in proofs).
* `step_of_instrAt`: if `CodeAt` holds and PC = base + off, one step executes
  `instrAt bytes off`.
* `exec_mem_other`: an instruction changes memory only at the bytes of its own
  write accesses. With it, `CodeAt` is preserved by any step whose writes avoid
  the code, which is how the whole-function theorems discharge the
  "code is not overwritten" assumption of the single-memory model.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

/-! ## Code placement -/

def CodeAt (m : Mem) (base : Word) (bytes : List (BitVec 8)) : Prop :=
  ∀ i (h : i < bytes.length), m (base + BitVec.ofNat 32 i) = bytes[i]

/-- Little-endian halfword of the artifact at byte offset `off` (0 past the end). -/
def hwAt (bytes : List (BitVec 8)) (off : Nat) : BitVec 16 :=
  bytes.getD (off + 1) 0 ++ bytes.getD off 0

/-- The instruction the artifact holds at offset `off`. -/
def instrAt (bytes : List (BitVec 8)) (off : Nat) : Option Instr :=
  decode (hwAt bytes off) (hwAt bytes (off + 2))

theorem ofNat_add_assoc (base : Word) (a b : Nat) :
    base + BitVec.ofNat 32 a + BitVec.ofNat 32 b = base + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem fetch16_of_codeAt {m : Mem} {base : Word} {bytes : List (BitVec 8)}
    (h : CodeAt m base bytes) (off : Nat) (hoff : off + 2 ≤ bytes.length) :
    fetch16 m (base + BitVec.ofNat 32 off) = hwAt bytes off := by
  have h0 := h off (by omega)
  have h1 := h (off + 1) (by omega)
  simp only [fetch16, hwAt]
  rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_assoc, h1, h0]
  simp [List.getD_eq_getElem?_getD, show off < bytes.length by omega,
    show off + 1 < bytes.length by omega]

/-- If the first halfword is not a 32-bit prefix, `decode` ignores the second. -/
theorem decode_of_not_is32 (hw1 a b : BitVec 16) (h : is32 hw1 = false) :
    decode hw1 a = decode hw1 b := by
  simp [decode, h]

theorem decodeBL_size {hw1 hw2 : BitVec 16} {i : Instr} (h : decodeBL hw1 hw2 = some i) :
    i.size = 4 := by
  unfold decodeBL at h
  split at h
  · cases h; rfl
  · cases h

/-- Decoding the instruction at PC from memory agrees with `instrAt`. The second
halfword is only needed when the instruction is 32 bits wide. -/
theorem decode_at {m : Mem} {base : Word} {bytes : List (BitVec 8)} (h : CodeAt m base bytes)
    (off : Nat) (i : Instr) (hi : instrAt bytes off = some i)
    (hlen : off + i.size ≤ bytes.length) :
    decode (fetch16 m (base + BitVec.ofNat 32 off))
      (fetch16 m (base + BitVec.ofNat 32 off + 2#32)) = some i := by
  have hsz : 2 ≤ i.size := by cases i <;> simp [Instr.size]
  rw [fetch16_of_codeAt h off (by omega)]
  unfold instrAt at hi
  cases h32 : is32 (hwAt bytes off)
  · rw [decode_of_not_is32 _ _ (hwAt bytes (off + 2)) h32]; exact hi
  · have hbl : decodeBL (hwAt bytes off) (hwAt bytes (off + 2)) = some i := by
      simpa [decode, h32] using hi
    have h4 := decodeBL_size hbl
    rw [show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_assoc,
      fetch16_of_codeAt h (off + 2) (by omega)]
    exact hi

/-- One step at a known artifact offset. -/
theorem step_of_instrAt {s s' : State} {base : Word} {bytes : List (BitVec 8)}
    (h : CodeAt s.mem base bytes) (off : Nat) (i : Instr)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (heven : (base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some i) (hlen : off + i.size ≤ bytes.length)
    (hal : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s') :
    step s = .ok (s', ⟨s.pc, i, i.accesses s⟩) := by
  have hd := decode_at h off i hi hlen
  simp only [step, hpc, heven, hd, hal, hex]
  simp

/-! ## Memory frame -/

/-- Byte addresses written by an access list. -/
def Writes (acc : List Access) (y : Word) : Prop :=
  ∃ a ∈ acc, a.kind = .write ∧ ∃ k, k < a.width ∧ y = a.addr + BitVec.ofNat 32 k

theorem write8_other (m : Mem) (a v y : Word) (h : y ≠ a) : write8 m a v y = m y := by
  simp [write8, h]

theorem write16_other (m : Mem) (a v y : Word) (h0 : y ≠ a) (h1 : y ≠ a + 1#32) :
    write16 m a v y = m y := by
  simp [write16, h0, h1]

theorem write32_other' (m : Mem) (a v y : Word)
    (h : ∀ k, k < 4 → y ≠ a + BitVec.ofNat 32 k) : write32 m a v y = m y :=
  write32_other m a v y h

theorem storeWords_other (m : Mem) (a : Word) (vs : List Word) (y : Word)
    (h : ∀ i k, i < vs.length → k < 4 → y ≠ a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :
    storeWords m a vs y = m y := by
  induction vs generalizing m a with
  | nil => rfl
  | cons v vs ih =>
    simp only [storeWords]
    rw [ih]
    · apply write32_other
      intro k hk
      have := h 0 k (by simp) hk
      simpa using this
    · intro i k hi hk
      have := h (i + 1) k (by simp; omega) hk
      have e : a + 4#32 + BitVec.ofNat 32 (4 * i) = a + BitVec.ofNat 32 (4 * (i + 1)) := by
        rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
        congr 2; omega
      rwa [e]

theorem loadRegs_mem (s : State) (a : Word) (rs : List Reg) : (loadRegs s a rs).mem = s.mem := by
  induction rs generalizing s a with
  | nil => rfl
  | cons r rs ih => simp only [loadRegs]; rw [ih]; rfl

theorem wordAccesses_writes (a : Word) (n : Nat) (y : Word)
    (h : ∀ i k, i < n → k < 4 → y ≠ a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :
    ¬ Writes (wordAccesses .write a n) y := by
  rintro ⟨acc, hm, _, k, hk, rfl⟩
  simp only [wordAccesses, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  exact h i k hi hk rfl

theorem bitCount_listRegs (l : BitVec 8) : (listRegs l).length = bitCount l := rfl

@[simp] theorem setReg_mem (s : State) (r : Reg) (x : Word) : (s.setReg r x).mem = s.mem := rfl
@[simp] theorem setNZ_mem (s : State) (x : Word) : (s.setNZ x).mem = s.mem := rfl
@[simp] theorem setNZC_mem (s : State) (x : Word) (c : Bool) : (s.setNZC x c).mem = s.mem := rfl
@[simp] theorem setNZCV_mem (s : State) (x : Word) (c v : Bool) :
    (s.setNZCV x c v).mem = s.mem := rfl
@[simp] theorem addFlags_mem (s : State) (d : Reg) (a b : Word) (c w : Bool) :
    (addFlags s d a b c w).mem = s.mem := by
  simp only [addFlags]; split <;> rfl

/-- Not writing `y` through a word transfer means `y` is outside every word. -/
theorem not_writes_words {a y : Word} {n : Nat}
    (hy : ¬ Writes (wordAccesses .write a n) y) :
    ∀ i k, i < n → k < 4 → y ≠ a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k := by
  intro i k hi hk h
  apply hy
  refine ⟨⟨.write, a + BitVec.ofNat 32 (4 * i), 4⟩, ?_, rfl, k, hk, h⟩
  simp only [wordAccesses, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

theorem not_writes_one {kind : Kind} {a y : Word} {w : Nat} (hk : kind = .write)
    (hy : ¬ Writes [⟨kind, a, w⟩] y) : ∀ k, k < w → y ≠ a + BitVec.ofNat 32 k := by
  intro k hlt h
  exact hy ⟨_, List.mem_singleton_self _, hk, k, hlt, h⟩

theorem memOp_mem_other (next : State) (op : MemOp) (t : LowReg) (a y : Word)
    (h : op.isLoad = false → ∀ k, k < op.width → y ≠ a + BitVec.ofNat 32 k) :
    (Instr.exec.memOp next op t a).mem y = next.mem y := by
  cases op <;> simp only [Instr.exec.memOp, setReg_mem]
  · exact write32_other _ _ _ _ (h rfl)
  · have h0 := h rfl 0 (by decide); have h1 := h rfl 1 (by decide)
    simp only [BitVec.add_zero] at h0
    exact write16_other _ _ _ _ h0 h1
  · have h0 := h rfl 0 (by decide)
    simp only [BitVec.add_zero] at h0
    exact write8_other _ _ _ _ h0

/-- An instruction changes memory only at the bytes of its write accesses. -/
theorem exec_mem_other (i : Instr) (s s' : State) (hex : i.exec s = .ok s') (y : Word)
    (hy : ¬ Writes (i.accesses s) y) : s'.mem y = s.mem y := by
  cases i
  case dp op dn m => cases op <;> simp [Instr.exec] at hex <;> subst hex <;> simp
  case memReg op t n m =>
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    rw [memOp_mem_other]; · rfl
    intro hl k hk
    simp only [Instr.accesses, hl] at hy
    exact not_writes_one rfl hy k hk
  case memImm op t n imm5 =>
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    rw [memOp_mem_other]; · rfl
    intro hl k hk
    simp only [Instr.accesses, hl] at hy
    exact not_writes_one rfl hy k hk
  case strSp t imm8 =>
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    exact write32_other _ _ _ _ (not_writes_one rfl hy)
  case push l lr =>
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    simp only [setReg_mem]
    apply storeWords_other
    intro i k hi hk
    apply not_writes_words hy i k _ hk
    simp only [List.length_append, List.length_map, bitCount_listRegs] at hi
    cases lr <;> simp_all
  case stm n l =>
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    simp only [setReg_mem]
    apply storeWords_other
    intro i k hi hk
    apply not_writes_words hy i k _ hk
    simpa [bitCount_listRegs] using hi
  case pop l pc =>
    simp only [Instr.exec] at hex
    split at hex
    · split at hex
      · simp only [Except.ok.injEq] at hex; subst hex; simp [loadRegs_mem]
      · cases hex
    · simp only [Except.ok.injEq] at hex; subst hex; simp [loadRegs_mem]
  case ldm n l =>
    simp only [Instr.exec] at hex
    split at hex <;> (simp only [Except.ok.injEq] at hex; subst hex; simp [loadRegs_mem])
  case bcond cond imm8 =>
    simp only [Instr.exec] at hex
    split at hex <;> (simp only [Except.ok.injEq] at hex; subst hex; simp)
  all_goals (simp [Instr.exec] at hex; subst hex; simp)

end M0Crypto.Thumb
