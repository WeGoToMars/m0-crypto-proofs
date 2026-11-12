import M0Crypto.Thumb.Program

/-!
`Instr.accesses` agrees with `Instr.exec` on reads.

The trace records `Instr.accesses`; the state changes by `Instr.exec`. The two are written
separately, so a load whose recorded address or width differed from the bytes it uses would
make the read-bound and constant-time theorems speak about the wrong addresses.

* `exec_mem_other` (in `Program.lean`): an instruction changes memory only at the bytes of
  its write accesses.
* `exec_reads_only` (here): an instruction's result depends on memory only at the bytes of
  its read accesses.

Together: every byte an instruction reads or writes is in its recorded accesses.
-/

namespace M0Crypto.Thumb
open M0Crypto.Armv6M

private theorem reads_one {a y : Word} {w k : Nat} (hk : k < w)
    (hy : y = a + BitVec.ofNat 32 k) : Reads [⟨.read, a, w⟩] y :=
  ⟨_, List.mem_singleton_self _, rfl, k, hk, hy⟩

private theorem reads_words {a y : Word} {n i k : Nat} (hi : i < n) (hk : k < 4)
    (hy : y = a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :
    Reads (wordAccesses .read a n) y := by
  refine ⟨⟨.read, a + BitVec.ofNat 32 (4 * i), 4⟩, ?_, rfl, k, hk, hy⟩
  simp only [wordAccesses, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

private theorem read32_congr {m m' : Mem} {a : Word}
    (h : ∀ k, k < 4 → m' (a + BitVec.ofNat 32 k) = m (a + BitVec.ofNat 32 k)) :
    read32 m' a = read32 m a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read32, h0, h1, h2, h3]

private theorem read16_congr {m m' : Mem} {a : Word}
    (h : ∀ k, k < 2 → m' (a + BitVec.ofNat 32 k) = m (a + BitVec.ofNat 32 k)) :
    read16 m' a = read16 m a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read16, h0, h1]

private theorem read8_congr {m m' : Mem} {a : Word}
    (h : ∀ k, k < 1 → m' (a + BitVec.ofNat 32 k) = m (a + BitVec.ofNat 32 k)) :
    read8 m' a = read8 m a := by
  have h0 := h 0 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [read8, h0]

/-- A written byte has the same value whatever the memory was before. -/
private theorem write32_written (m m' : Mem) (a v : Word) {y : Word} {k : Nat} (hk : k < 4)
    (hy : y = a + BitVec.ofNat 32 k) : write32 m' a v y = write32 m a v y := by
  subst hy
  match k, hk with
  | 0, _ => simp [write32]
  | 1, _ => simp [write32]
  | 2, _ => simp [write32]
  | 3, _ => simp [write32]

private theorem write32_congr (m m' : Mem) (a v y : Word) (h : m' y = m y) :
    write32 m' a v y = write32 m a v y := by
  simp only [write32, h]

private theorem write16_written (m m' : Mem) (a v : Word) {y : Word} {k : Nat} (hk : k < 2)
    (hy : y = a + BitVec.ofNat 32 k) : write16 m' a v y = write16 m a v y := by
  subst hy
  match k, hk with
  | 0, _ => simp [write16]
  | 1, _ => simp [write16]

private theorem write8_written (m m' : Mem) (a v : Word) {y : Word} {k : Nat} (hk : k < 1)
    (hy : y = a + BitVec.ofNat 32 k) : write8 m' a v y = write8 m a v y := by
  subst hy
  match k, hk with
  | 0, _ => simp [write8]

private theorem storeWords_congr (m m' : Mem) (a : Word) (vs : List Word) (y : Word)
    (h : m' y = m y ∨ ∃ i k, i < vs.length ∧ k < 4 ∧
      y = a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) :
    storeWords m' a vs y = storeWords m a vs y := by
  induction vs generalizing m m' a with
  | nil =>
    rcases h with h | ⟨i, k, hi, _⟩
    · exact h
    · simp at hi
  | cons v vs ih =>
    simp only [storeWords]
    apply ih
    rcases h with h | ⟨i, k, hi, hk, hy⟩
    · exact .inl (write32_congr _ _ _ _ _ h)
    · cases i with
      | zero => exact .inl (write32_written _ _ _ _ hk (by simpa using hy))
      | succ i =>
        refine .inr ⟨i, k, by simpa using hi, hk, ?_⟩
        have e : a + 4#32 + BitVec.ofNat 32 (4 * i) = a + BitVec.ofNat 32 (4 * (i + 1)) := by
          rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]; congr 2; omega
        rw [e]; exact hy

private theorem loadRegs_congr (s : State) (m : Mem) (a : Word) (rs : List Reg)
    (h : ∀ i k, i < rs.length → k < 4 →
      m (a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k) =
        s.mem (a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k)) :
    loadRegs { s with mem := m } a rs = { loadRegs s a rs with mem := m } := by
  induction rs generalizing s a with
  | nil => rfl
  | cons r rs ih =>
    have h0 : read32 m a = read32 s.mem a :=
      read32_congr (fun k hk => by simpa using h 0 k (by simp) hk)
    simp only [loadRegs, h0]
    refine ih (s.setReg r (read32 s.mem a)) (a + 4#32) (fun i k hi hk => ?_)
    have := h (i + 1) k (by simpa using hi) hk
    have e : a + 4#32 + BitVec.ofNat 32 (4 * i) = a + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]; congr 2; omega
    rw [e]; exact this

/-- The conclusion of `exec_reads_only`, in a form convenient to prove per instruction. -/
private def ReadsOnly (i : Instr) (s : State) (m : Mem) : Prop :=
  (∀ t, i.exec s = .ok t → ∃ t', i.exec { s with mem := m } = .ok t' ∧
    t'.regs = t.regs ∧ t'.n = t.n ∧ t'.z = t.z ∧ t'.c = t.c ∧ t'.v = t.v ∧
    ∀ y, (m y = s.mem y ∨ Writes (i.accesses s) y) → t'.mem y = t.mem y) ∧
  (∀ e, i.exec s = .error e → i.exec { s with mem := m } = .error e)

/-- An instruction without write accesses whose result does not read the memory. -/
private theorem ReadsOnly.of_map {i : Instr} {s : State} {m : Mem}
    (hw : ∀ y, ¬ Writes (i.accesses s) y)
    (h : i.exec { s with mem := m } = (i.exec s).map fun t => { t with mem := m }) :
    ReadsOnly i s m := by
  refine ⟨fun t hex => ⟨{ t with mem := m }, by rw [h, hex]; rfl, rfl, rfl, rfl, rfl, rfl,
    fun y hy => ?_⟩, fun e hex => by rw [h, hex]; rfl⟩
  rcases hy with hy | hy
  · exact hy.trans (exec_mem_other i s t hex y (hw y)).symm
  · exact absurd hy (hw y)

/-! Replacing the memory commutes with everything that does not read it. -/

@[simp] private theorem setReg_withMem (s : State) (m : Mem) (r : Reg) (x : Word) :
    ({ s with mem := m } : State).setReg r x = { s.setReg r x with mem := m } := rfl
@[simp] private theorem pc_withMem (s : State) (m : Mem) :
    ({ s with mem := m } : State).pc = s.pc := rfl
@[simp] private theorem sp_withMem (s : State) (m : Mem) :
    ({ s with mem := m } : State).sp = s.sp := rfl
@[simp] private theorem reg_withMem (s : State) (m : Mem) (r : LowReg) :
    ({ s with mem := m } : State).reg r = s.reg r := rfl

private theorem no_writes_of_read {a : Word} {n : Nat} (y : Word) :
    ¬ Writes (wordAccesses .read a n) y := by
  rintro ⟨acc, hm, hk, _⟩
  simp only [wordAccesses, List.mem_map] at hm
  obtain ⟨_, _, rfl⟩ := hm
  cases hk

/-- One load or store: the result depends on `next.mem` only at the bytes a load reads. -/
private theorem memOp_reads_only (next : State) (m : Mem) (op : MemOp) (t : LowReg) (a : Word)
    (h : op.isLoad = true → ∀ k, k < op.width →
      m (a + BitVec.ofNat 32 k) = next.mem (a + BitVec.ofNat 32 k)) :
    ∃ m', Instr.exec.memOp { next with mem := m } op t a =
        { Instr.exec.memOp next op t a with mem := m' } ∧
      ∀ y, (m y = next.mem y ∨ (op.isLoad = false ∧ ∃ k, k < op.width ∧
        y = a + BitVec.ofNat 32 k)) → m' y = (Instr.exec.memOp next op t a).mem y := by
  cases op
  case str =>
    refine ⟨write32 m a (next.reg t), rfl, fun y hy => ?_⟩
    rcases hy with hy | ⟨_, k, hk, hy⟩
    · exact write32_congr _ _ _ _ _ hy
    · exact write32_written _ _ _ _ hk hy
  case strh =>
    refine ⟨write16 m a (next.reg t), rfl, fun y hy => ?_⟩
    rcases hy with hy | ⟨_, k, hk, hy⟩
    · show write16 m a _ y = write16 next.mem a _ y
      simp only [write16, hy]
    · exact write16_written _ _ _ _ hk hy
  case strb =>
    refine ⟨write8 m a (next.reg t), rfl, fun y hy => ?_⟩
    rcases hy with hy | ⟨_, k, hk, hy⟩
    · show write8 m a _ y = write8 next.mem a _ y
      simp only [write8, hy]
    · exact write8_written _ _ _ _ hk hy
  case ldr =>
    refine ⟨m, ?_, fun y hy => ?_⟩
    · show State.setReg _ _ (read32 m a) = _
      rw [read32_congr (h rfl)]; rfl
    · rcases hy with hy | ⟨hl, _⟩
      · exact hy
      · cases hl
  case ldrh =>
    refine ⟨m, ?_, fun y hy => ?_⟩
    · show State.setReg _ _ (read16 m a) = _
      rw [read16_congr (h rfl)]; rfl
    · rcases hy with hy | ⟨hl, _⟩
      · exact hy
      · cases hl
  case ldrb =>
    refine ⟨m, ?_, fun y hy => ?_⟩
    · show State.setReg _ _ (read8 m a) = _
      rw [read8_congr (h rfl)]; rfl
    · rcases hy with hy | ⟨hl, _⟩
      · exact hy
      · cases hl

/-- Single load or store through `memOp` (the register-offset and immediate-offset forms). -/
private theorem readsOnly_memOp (i : Instr) (op : MemOp) (t : LowReg)
    (addr : State → Word) (haddr : ∀ s m, addr { s with mem := m } = addr s)
    (hexec : ∀ s, i.exec s = .ok (Instr.exec.memOp
      (s.setReg 15 (s.pc + BitVec.ofNat 32 i.size)) op t (addr s)))
    (hacc : ∀ s, i.accesses s = [⟨if op.isLoad then .read else .write, addr s, op.width⟩])
    (s : State) (m : Mem) (h : ∀ y, Reads (i.accesses s) y → m y = s.mem y) :
    ReadsOnly i s m := by
  obtain ⟨m', hm', hmem⟩ := memOp_reads_only (s.setReg 15 (s.pc + BitVec.ofNat 32 i.size)) m op t
    (addr s) (fun hl k hk => h _ (by rw [hacc, hl]; exact reads_one hk rfl))
  refine ⟨fun t' hex => ?_, fun e hex => by rw [hexec] at hex; cases hex⟩
  rw [hexec, Except.ok.injEq] at hex; subst hex
  refine ⟨{ Instr.exec.memOp (s.setReg 15 (s.pc + BitVec.ofNat 32 i.size)) op t (addr s) with
      mem := m' }, by rw [hexec, haddr]; exact congrArg Except.ok hm',
    rfl, rfl, rfl, rfl, rfl, fun y hy => hmem y ?_⟩
  rcases hy with hy | ⟨acc, hacc', hkind, k, hk, hy⟩
  · exact .inl hy
  · rw [hacc, List.mem_singleton] at hacc'; subst hacc'
    refine .inr ⟨?_, k, hk, hy⟩
    cases hl : op.isLoad
    · rfl
    · simp [hl] at hkind

private theorem readsOnly (i : Instr) (s : State) (m : Mem)
    (h : ∀ y, Reads (i.accesses s) y → m y = s.mem y) : ReadsOnly i s m := by
  cases i
  case dp op dn mm =>
    cases op <;> exact .of_map (fun y hy => by simp [Instr.accesses, Writes] at hy) rfl
  case bcond cond imm8 =>
    refine .of_map (fun y hy => by simp [Instr.accesses, Writes] at hy) ?_
    simp only [Instr.exec, pc_withMem]
    show (if condPassed cond s = true then _ else _) = _
    split <;> rfl
  case ldrLit t imm8 =>
    refine .of_map (fun y hy => by simp [Instr.accesses, Writes] at hy) ?_
    have e := read32_congr (m := s.mem) (m' := m)
      (a := ((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm8.toNat * 4))
      fun k hk => h _ (reads_one hk rfl)
    simp only [Instr.exec, pc_withMem, setReg_withMem, e]; rfl
  case ldrSp t imm8 =>
    refine .of_map (fun y hy => by simp [Instr.accesses, Writes] at hy) ?_
    have e := read32_congr (m := s.mem) (m' := m) (a := s.sp + BitVec.ofNat 32 (imm8.toNat * 4))
      fun k hk => h _ (reads_one hk rfl)
    simp only [Instr.exec, pc_withMem, sp_withMem, setReg_withMem, e]; rfl
  case strSp t imm8 =>
    refine ⟨fun t' hex => ?_, fun e hex => by simp [Instr.exec] at hex⟩
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    show write32 m _ _ y = write32 s.mem _ _ y
    rcases hy with hy | ⟨acc, hacc, _, k, hk, hy⟩
    · exact write32_congr _ _ _ _ _ hy
    · simp only [Instr.accesses, List.mem_singleton] at hacc; subst hacc
      exact write32_written _ _ _ _ hk hy
  case memReg op t n mm =>
    exact readsOnly_memOp _ op t (fun s => s.reg n + s.reg mm) (fun _ _ => rfl) (fun _ => rfl)
      (fun _ => rfl) s m h
  case memImm op t n imm5 =>
    exact readsOnly_memOp _ op t (fun s => s.reg n + BitVec.ofNat 32 (imm5.toNat * op.width))
      (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) s m h
  case push l lr =>
    refine ⟨fun t' hex => ?_, fun e hex => by simp [Instr.exec] at hex⟩
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    show storeWords m _ _ y = storeWords s.mem _ _ y
    apply storeWords_congr
    rcases hy with hy | ⟨acc, hacc, _, k, hk, hy⟩
    · exact .inl hy
    · simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at hacc
      obtain ⟨i, hi, rfl⟩ := hacc
      refine .inr ⟨i, k, ?_, hk, hy⟩
      cases lr <;> simp_all [bitCount_listRegs]
  case stm n l =>
    refine ⟨fun t' hex => ?_, fun e hex => by simp [Instr.exec] at hex⟩
    simp only [Instr.exec, Except.ok.injEq] at hex; subst hex
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩
    show storeWords m _ _ y = storeWords s.mem _ _ y
    apply storeWords_congr
    rcases hy with hy | ⟨acc, hacc, _, k, hk, hy⟩
    · exact .inl hy
    · simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at hacc
      obtain ⟨i, hi, rfl⟩ := hacc
      exact .inr ⟨i, k, by simpa [bitCount_listRegs] using hi, hk, hy⟩
  case pop l pcBit =>
    refine .of_map (fun y => no_writes_of_read y) ?_
    have e1 := loadRegs_congr (s.setReg 15 (s.pc + BitVec.ofNat 32 (Instr.pop l pcBit).size)) m
      s.sp ((listRegs l).map LowReg.toReg)
      (fun i k hi hk => h _ (reads_words
        (by simp only [List.length_map, bitCount_listRegs] at hi; omega) hk rfl))
    cases pcBit
    · simp only [Instr.exec, pc_withMem, sp_withMem, setReg_withMem, Bool.false_eq_true,
        ↓reduceIte, e1]; rfl
    · have e2 := read32_congr (m := s.mem) (m' := m)
        (a := s.sp + BitVec.ofNat 32 (4 * bitCount l))
        fun k hk => h _ (reads_words (i := bitCount l) (by simp) hk rfl)
      simp only [Instr.exec, pc_withMem, sp_withMem, setReg_withMem, ↓reduceIte, e1, e2]
      split <;> rfl
  case ldm n l =>
    refine .of_map (fun y => no_writes_of_read y) ?_
    have e1 := loadRegs_congr (s.setReg 15 (s.pc + BitVec.ofNat 32 (Instr.ldm n l).size)) m
      (s.reg n) ((listRegs l).map LowReg.toReg)
      (fun i k hi hk => h _ (reads_words (by simpa [bitCount_listRegs] using hi) hk rfl))
    simp only [Instr.exec, pc_withMem, reg_withMem, setReg_withMem, e1]
    split <;> rfl
  all_goals exact .of_map (fun y hy => by simp [Instr.accesses, Writes] at hy) rfl

/-- An instruction's effect depends on memory only at the bytes of its read accesses.
Take any memory `m` that agrees with the memory of `s` on those bytes and execute the
instruction in `m` instead: it faults in the same way, or it succeeds with the same
registers and flags, and the two final memories agree wherever the initial ones did and on
every byte the instruction writes. -/
theorem exec_reads_only (i : Instr) (s : State) (m : Mem)
    (h : ∀ y, Reads (i.accesses s) y → m y = s.mem y) :
    match i.exec s, i.exec { s with mem := m } with
    | .ok t, .ok t' => t'.regs = t.regs ∧ t'.n = t.n ∧ t'.z = t.z ∧ t'.c = t.c ∧ t'.v = t.v ∧
        ∀ y, (m y = s.mem y ∨ Writes (i.accesses s) y) → t'.mem y = t.mem y
    | .error e, .error e' => e' = e
    | _, _ => False := by
  obtain ⟨hok, herr⟩ := readsOnly i s m h
  cases hex : i.exec s with
  | error e => rw [herr e hex]
  | ok t => obtain ⟨t', ht', hrest⟩ := hok t hex; rw [ht']; exact hrest

end M0Crypto.Thumb
