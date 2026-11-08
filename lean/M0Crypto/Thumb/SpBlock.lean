import M0Crypto.Thumb.Seq

/-!
Blocks whose only data accesses are SP-relative word loads and stores.

`Instr.spRel` gives such an instruction's accesses as (kind, offset from SP)
pairs, statically. For a list of such instructions that never writes SP:

* `alignedAll_sp`: every access is aligned if SP is and every offset is a
  multiple of 4;
* `execAll_mem_sp`: memory changes only inside the written words;
* `traceAll_sp_congr`: the trace depends only on the starting PC and SP, so
  it is independent of all register and memory contents (the constant-time
  property of such blocks).
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

/-- SP-relative accesses of an instruction: `some` list of (kind, byte offset from SP),
all of width 4; `none` if it accesses memory any other way. -/
def Instr.spRel : Instr → Option (List (Kind × Nat))
  | .ldrSp _ k => some [(.read, k.toNat * 4)]
  | .strSp _ k => some [(.write, k.toNat * 4)]
  | .memReg _ _ _ _ | .memImm _ _ _ _ | .ldrLit _ _ | .push _ _ | .pop _ _ | .stm _ _
  | .ldm _ _ => none
  | _ => some []

def spAccess (sp : Word) (p : Kind × Nat) : Access := ⟨p.1, sp + BitVec.ofNat 32 p.2, 4⟩

theorem accesses_spRel {i : Instr} {l : List (Kind × Nat)} (h : i.spRel = some l) (s : State) :
    i.accesses s = l.map (spAccess (s.regs 13)) := by
  cases i <;> simp only [Instr.spRel, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [Instr.accesses, spAccess, State.sp]

/-- The block is SP-relative, never writes SP, and `ok` holds of every access. -/
def SpBlock (is : List Instr) (ok : Kind × Nat → Prop) : Prop :=
  ∀ i ∈ is, 13 ∉ i.dsts ∧ ∃ l, i.spRel = some l ∧ ∀ p ∈ l, ok p

theorem SpBlock.tail {i : Instr} {is : List Instr} {ok} (h : SpBlock (i :: is) ok) : SpBlock is ok :=
  fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem SpBlock.mono {is : List Instr} {ok ok' : Kind × Nat → Prop} (h : SpBlock is ok)
    (hm : ∀ p, ok p → ok' p) : SpBlock is ok' := by
  intro i hi
  obtain ⟨h13, l, hl, hp⟩ := h i hi
  exact ⟨h13, l, hl, fun p hp' => hm p (hp p hp')⟩

theorem next_sp {i : Instr} (h : 13 ∉ i.dsts) (s : State) : (i.next s).regs 13 = s.regs 13 :=
  next_regs_other s 13 (by decide) h

theorem alignedAll_sp : ∀ (is : List Instr) (s : State),
    SpBlock is (fun p => p.2 % 4 = 0) → (s.regs 13).toNat % 4 = 0 → alignedAll is s = true
  | [], _, _, _ => rfl
  | i :: is, s, h, hsp => by
    obtain ⟨h13, l, hl, hp⟩ := h i List.mem_cons_self
    simp only [alignedAll, Bool.and_eq_true]
    refine ⟨?_, alignedAll_sp is _ h.tail (by rw [next_sp h13]; exact hsp)⟩
    rw [accesses_spRel hl, List.all_eq_true]
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨p, hpm, rfl⟩ := ha
    have := hp p hpm
    simp only [spAccess, Access.aligned, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Memory is unchanged at `y` if no store of the block covers it. -/
theorem execAll_mem_sp : ∀ (is : List Instr) (s : State) (y : Word),
    SpBlock is (fun p => p.1 = .read ∨ ∀ j < 4, y ≠ s.regs 13 + BitVec.ofNat 32 p.2 + BitVec.ofNat 32 j) →
    (execAll is s).mem y = s.mem y
  | [], _, _, _ => rfl
  | i :: is, s, y, h => by
    obtain ⟨h13, l, hl, hp⟩ := h i List.mem_cons_self
    have hsp := next_sp h13 s
    rw [execAll, execAll_mem_sp is _ y (by rw [hsp]; exact h.tail)]
    unfold Instr.next
    split
    · rename_i s' hex
      apply exec_mem_other i s s' hex y
      rintro ⟨a, ha, hw, k, hk, rfl⟩
      rw [accesses_spRel hl] at ha
      simp only [List.mem_map] at ha
      obtain ⟨p, hpm, rfl⟩ := ha
      have := hp p hpm
      rcases this with hr | hn
      · simp [spAccess, hr] at hw
      · exact hn k hk rfl
    · rfl

/-- The trace of an SP-relative block depends only on the starting PC and SP. -/
theorem traceAll_sp_congr : ∀ (is : List Instr) (s t : State), SpBlock is (fun _ => True) →
    is.all Instr.falls = true → s.pc = t.pc → s.regs 13 = t.regs 13 →
    traceAll is s = traceAll is t
  | [], _, _, _, _, _, _ => rfl
  | i :: is, s, t, h, hf, hpc, hsp => by
    obtain ⟨h13, l, hl, -⟩ := h i List.mem_cons_self
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [traceAll, accesses_spRel hl, hpc, hsp]
    congr 1
    apply traceAll_sp_congr is _ _ h.tail hf.2
    · rw [exec_pc hf.1 (exec_ok_of_falls hf.1 s), exec_pc hf.1 (exec_ok_of_falls hf.1 t), hpc]
    · rw [next_sp h13, next_sp h13, hsp]

/-- Decidable form of `SpBlock`. -/
def spBlockB (is : List Instr) (ok : Kind × Nat → Bool) : Bool :=
  is.all fun i => !(i.dsts.contains 13) && match i.spRel with
    | some l => l.all ok
    | none => false

theorem spBlock_of_B {is : List Instr} {ok : Kind × Nat → Bool} (h : spBlockB is ok = true) :
    SpBlock is (fun p => ok p = true) := by
  intro i hi
  simp only [spBlockB, List.all_eq_true] at h
  have := h i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  refine ⟨this.1, ?_⟩
  revert this
  cases hs : i.spRel with
  | none => simp
  | some l =>
    intro ⟨_, hl⟩
    simp only [List.all_eq_true] at hl
    exact ⟨l, rfl, hl⟩

/-- Stores of an SP block inside `[SP, SP + n)` leave memory outside it unchanged. -/
theorem execAll_mem_sp_window (is : List Instr) (s : State) (n : Nat)
    (h : SpBlock is (fun p => p.1 = .read ∨ p.2 + 4 ≤ n)) (y : Word)
    (hy : ∀ o < n, y ≠ s.regs 13 + BitVec.ofNat 32 o) : (execAll is s).mem y = s.mem y := by
  apply execAll_mem_sp is s y (h.mono _)
  intro p hp
  rcases hp with hr | hw
  · exact .inl hr
  · right; intro j hj e
    apply hy (p.2 + j) (by omega)
    rw [e, ofNat_add_assoc]

/-- Writes of a trace lie in `[lo, lo + n)`. -/
def WritesIn (tr : List Event) (lo : Word) (n : Nat) : Prop :=
  ∀ e ∈ tr, ∀ y, Writes e.accesses y → ∃ o < n, y = lo + BitVec.ofNat 32 o

theorem WritesIn.append {t1 t2 : List Event} {lo : Word} {n : Nat} (h1 : WritesIn t1 lo n)
    (h2 : WritesIn t2 lo n) : WritesIn (t1 ++ t2) lo n := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem WritesIn.nil (lo : Word) (n : Nat) : WritesIn [] lo n := by intro e he; cases he

theorem WritesIn.cons_noacc {e : Event} {t : List Event} {lo : Word} {n : Nat} (he : e.accesses = [])
    (h : WritesIn t lo n) : WritesIn (e :: t) lo n := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | h'
  · intro y ⟨a, ha, _⟩; rw [he] at ha; cases ha
  · exact h e' h'

theorem traceAll_writes_sp : ∀ (is : List Instr) (s : State) (n : Nat),
    SpBlock is (fun p => p.1 = .read ∨ p.2 + 4 ≤ n) → WritesIn (traceAll is s) (s.regs 13) n
  | [], _, _, _ => WritesIn.nil _ _
  | i :: is, s, n, h => by
    obtain ⟨h13, l, hl, hp⟩ := h i List.mem_cons_self
    have ih := traceAll_writes_sp is (i.next s) n h.tail
    rw [next_sp h13] at ih
    intro e he
    rcases List.mem_cons.mp he with rfl | h'
    · rintro y ⟨a, ha, hw, k, hk, rfl⟩
      simp only [accesses_spRel hl, List.mem_map] at ha
      obtain ⟨p, hpm, rfl⟩ := ha
      rcases hp p hpm with hr | hn
      · simp [spAccess, hr] at hw
      · exact ⟨p.2 + k, by simp [spAccess] at hk; omega, by simp [spAccess, ofNat_add_assoc]⟩
    · exact ih e h'

/-- Every byte accessed by a trace lies in the given region. -/
def AccessesIn (tr : List Event) (lo : Word) (n : Nat) : Prop :=
  ∀ e ∈ tr, ∀ a ∈ e.accesses, ∀ k < a.width,
    ∃ o < n, a.addr + BitVec.ofNat 32 k = lo + BitVec.ofNat 32 o

theorem AccessesIn.append {t1 t2 : List Event} {lo : Word} {n : Nat}
    (h1 : AccessesIn t1 lo n) (h2 : AccessesIn t2 lo n) : AccessesIn (t1 ++ t2) lo n := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact h1 e he
  · exact h2 e he

theorem AccessesIn.nil (lo : Word) (n : Nat) : AccessesIn [] lo n := by
  intro e he; cases he

theorem AccessesIn.cons_noacc {e : Event} {t : List Event} {lo : Word} {n : Nat}
    (he : e.accesses = []) (h : AccessesIn t lo n) : AccessesIn (e :: t) lo n := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | he'
  · intro a ha; rw [he] at ha; cases ha
  · exact h e' he'

/-- Every byte accessed by a bounded SP-relative instruction sequence is in
its starting stack region. -/
theorem traceAll_accesses_sp : ∀ (is : List Instr) (s : State) (n : Nat),
    SpBlock is (fun p => p.2 + 4 ≤ n) → AccessesIn (traceAll is s) (s.regs 13) n
  | [], _, _, _ => AccessesIn.nil _ _
  | i :: is, s, n, h => by
    obtain ⟨h13, l, hl, hp⟩ := h i List.mem_cons_self
    have ih := traceAll_accesses_sp is (i.next s) n h.tail
    rw [next_sp h13] at ih
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · intro a ha k hk
      simp only [accesses_spRel hl, List.mem_map] at ha
      obtain ⟨p, hpm, rfl⟩ := ha
      have hn := hp p hpm
      exact ⟨p.2 + k, by simp [spAccess] at hk; omega, by simp [spAccess, ofNat_add_assoc]⟩
    · exact ih e he

end M0Crypto.Thumb
