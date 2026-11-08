import M0Crypto.Thumb.Harvard

/-!
Straight-line blocks.

`runSeq is s` executes the instruction list `is` in order, with the same alignment
check and the same events as `step`, but without fetching: it is a pure function
of the instructions and the state, so blocks can be specified and proved once,
independently of where they sit in the artifact.

`runH_seq` connects it to the Harvard runner: if the artifact holds `is` at
consecutive offsets from `off` (`seqAt`, decided on the bytes), and no instruction
in `is` branches (`Instr.falls`), then `runH` for `is.length` steps from
PC = base + off is `runSeq is`.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

/-- Instructions whose only effect on PC is to advance it by their size. -/
def Instr.falls : Instr → Bool
  | .bcond _ _ | .b _ | .bl _ => false
  | .pop _ pc => !pc
  | .movHi d _ => d.val != 15
  | _ => true

/-- Execute a list of instructions in order (no fetch). -/
def runSeq : List Instr → State → Except Fault (State × List Event)
  | [], s => .ok (s, [])
  | i :: is, s =>
    let acc := i.accesses s
    if acc.all Access.aligned then
      match i.exec s with
      | .ok s1 =>
        match runSeq is s1 with
        | .ok (s2, es) => .ok (s2, ⟨s.pc, i, acc⟩ :: es)
        | .error e => .error e
      | .error e => .error e
    else .error (.unaligned s.pc)

/-- The artifact holds `is` at consecutive offsets from `off`. -/
def seqAt (bytes : List (BitVec 8)) : Nat → List Instr → Bool
  | _, [] => true
  | off, i :: is =>
    instrAt bytes off == some i && decide (off + i.size ≤ bytes.length) && seqAt bytes (off + i.size) is

/-- Total size in bytes. -/
def seqSize (is : List Instr) : Nat := (is.map Instr.size).sum

/-! ## PC after a falling-through instruction -/

theorem setReg_regs_ne (s : State) (r r' : Reg) (x : Word) (h : r' ≠ r) :
    (s.setReg r x).regs r' = s.regs r' := by
  simp [State.setReg, h]

theorem toReg_ne_15 (d : LowReg) : d.toReg ≠ 15 := by
  intro h; have := congrArg Fin.val h; simp [LowReg.toReg] at this; omega

@[simp] theorem setNZ_regs (s : State) (x : Word) : (s.setNZ x).regs = s.regs := rfl
@[simp] theorem setNZC_regs (s : State) (x : Word) (c : Bool) : (s.setNZC x c).regs = s.regs := rfl
@[simp] theorem setNZCV_regs (s : State) (x : Word) (c v : Bool) :
    (s.setNZCV x c v).regs = s.regs := rfl

theorem addFlags_regs_ne (s : State) (d r : Reg) (a b : Word) (c w : Bool) (h : r ≠ d) :
    (addFlags s d a b c w).regs r = s.regs r := by
  simp only [addFlags]; split <;> cases w <;> simp [State.setReg, h]

theorem loadRegs_regs_ne (s : State) (a : Word) (rs : List Reg) (r : Reg) (h : r ∉ rs) :
    (loadRegs s a rs).regs r = s.regs r := by
  induction rs generalizing s a with
  | nil => rfl
  | cons r0 rs ih =>
    simp only [loadRegs]
    rw [ih _ _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact setReg_regs_ne _ _ _ _ (fun he => h (he ▸ List.mem_cons_self))

theorem not_mem_lowRegs (l : List LowReg) : (15 : Reg) ∉ l.map LowReg.toReg := by
  simp only [List.mem_map, not_exists, not_and]
  intro x _ h; exact toReg_ne_15 x h

theorem exec_pc {i : Instr} {s s1 : State} (hf : i.falls = true) (h : i.exec s = .ok s1) :
    s1.pc = s.pc + BitVec.ofNat 32 i.size := by
  have h15 := toReg_ne_15
  have h15' : ∀ d : LowReg, (15 : Reg) ≠ d.toReg := fun d e => toReg_ne_15 d e.symm
  have h0 : (15 : Reg) ≠ 0 := by decide
  have h13 : (15 : Reg) ≠ 13 := by decide
  have hn : ∀ (t : State) (x : Word), (t.setReg 15 x).regs 15 = x := by
    intro t x; simp [State.setReg]
  cases i <;> simp only [Instr.falls, Bool.false_eq_true] at hf <;> simp only [Instr.exec] at h
  case dp op dn m =>
    cases op <;> simp only [Except.ok.injEq] at h <;> subst h <;>
      simp [State.pc, addFlags_regs_ne, setReg_regs_ne, h15', h0, hn]
  case pop l pc =>
    cases pc
    · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h; subst h
      simp only [State.pc]
      rw [setReg_regs_ne _ _ _ _ (by decide), loadRegs_regs_ne _ _ _ _ (not_mem_lowRegs _), hn]
    · simp at hf
  case ldm n l =>
    split at h <;> simp only [Except.ok.injEq] at h <;> subst h <;> simp only [State.pc]
    · rw [loadRegs_regs_ne _ _ _ _ (not_mem_lowRegs _), hn]
    · rw [setReg_regs_ne _ _ _ _ (h15 n).symm, loadRegs_regs_ne _ _ _ _ (not_mem_lowRegs _), hn]
  case memReg op t n m =>
    simp only [Except.ok.injEq] at h; subst h
    cases op <;> simp [Instr.exec.memOp, State.pc, setReg_regs_ne, h15', hn]
  case memImm op t n imm5 =>
    simp only [Except.ok.injEq] at h; subst h
    cases op <;> simp [Instr.exec.memOp, State.pc, setReg_regs_ne, h15', hn]
  case movHi d m =>
    simp only [Except.ok.injEq] at h; subst h
    have : d ≠ 15 := by intro e; subst e; revert hf; decide
    simp only [State.pc]; rw [setReg_regs_ne _ _ _ _ (Ne.symm this), hn]
  all_goals
    simp only [Except.ok.injEq] at h; subst h
    simp [State.pc, addFlags_regs_ne, setReg_regs_ne, h15', h0, h13, hn, State.sp]

/-! ## The bridge -/

theorem instr_size_even (i : Instr) : i.size % 2 = 0 := by cases i <;> simp [Instr.size]

theorem pc_even (base : Word) (off : Nat) (hb : base.toNat % 2 = 0) (ho : off % 2 = 0) :
    (base + BitVec.ofNat 32 off).getLsbD 0 = false := by
  simp only [BitVec.getLsbD, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.testBit_zero]
  simp only [decide_eq_false_iff_not]
  omega

theorem sub_base (base : Word) (off : Nat) (h : off < 2 ^ 32) :
    (base + BitVec.ofNat 32 off - base).toNat = off := by
  have : (base + BitVec.ofNat 32 off - base) = BitVec.ofNat 32 off := by bv_omega
  rw [this]; simp [Nat.mod_eq_of_lt h]

theorem runH_seq {bytes : List (BitVec 8)} {base : Word} (hb : base.toNat % 2 = 0)
    (hlen : bytes.length < 2 ^ 32) :
    ∀ (is : List Instr) (off : Nat) (s : State), s.pc = base + BitVec.ofNat 32 off →
      off % 2 = 0 → seqAt bytes off is = true → is.all Instr.falls = true →
      runH bytes base is.length s = runSeq is s
  | [], _, _, _, _, _, _ => rfl
  | i :: is, off, s, hpc, ho, hseq, hf => by
    simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hseq
    obtain ⟨⟨hi, hsz⟩, hrest⟩ := hseq
    simp only [List.all_cons, Bool.and_eq_true] at hf
    have hoff : (s.pc - base).toNat = off := by rw [hpc]; exact sub_base base off (by omega)
    have hev := pc_even base off hb ho
    rw [← hpc] at hev
    simp only [List.length_cons, runH, runSeq, stepH, hev, hoff, hi, hsz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hal : (i.accesses s).all Access.aligned
    · simp
    · cases hex : i.exec s with
      | error e => simp
      | ok s1 =>
        have hpc1 : s1.pc = base + BitVec.ofNat 32 (off + i.size) := by
          rw [exec_pc hf.1 hex, hpc, ofNat_add_assoc]
        simp only [↓reduceIte]
        rw [runH_seq hb hlen is (off + i.size) s1 hpc1 (by have := instr_size_even i; omega) hrest hf.2]
        cases runSeq is s1 <;> rfl

/-! ## Total form for non-branching code

Only `POP {..., PC}` can make `Instr.exec` fail, and it is not `falls`. So for
non-branching code `runSeq` is "check alignment, then a total state function".
Block proofs work with `execAll` / `alignedAll` / `traceAll`, which carry no
`Except` structure. -/

/-- The successor state (the state itself if `exec` fails, which `falls` rules out). -/
def Instr.next (i : Instr) (s : State) : State :=
  match i.exec s with
  | .ok s' => s'
  | .error _ => s

theorem exec_ne_error {i : Instr} (hf : i.falls = true) (s : State) (e : Fault) :
    i.exec s ≠ .error e := by
  cases i <;> simp only [Instr.falls, Bool.false_eq_true] at hf
  case dp op _ _ => cases op <;> simp [Instr.exec]
  case pop l pc => cases pc <;> simp_all [Instr.exec]
  case ldm n l => simp only [Instr.exec]; split <;> simp
  all_goals simp [Instr.exec]

theorem exec_ok_of_falls {i : Instr} (hf : i.falls = true) (s : State) :
    i.exec s = .ok (i.next s) := by
  unfold Instr.next
  cases h : i.exec s with
  | ok s' => rfl
  | error e => exact absurd h (exec_ne_error hf s e)

def execAll : List Instr → State → State
  | [], s => s
  | i :: is, s => execAll is (i.next s)

def alignedAll : List Instr → State → Bool
  | [], _ => true
  | i :: is, s => (i.accesses s).all Access.aligned && alignedAll is (i.next s)

def traceAll : List Instr → State → List Event
  | [], _ => []
  | i :: is, s => ⟨s.pc, i, i.accesses s⟩ :: traceAll is (i.next s)

theorem runSeq_eq : ∀ (is : List Instr) (s : State), is.all Instr.falls = true →
    alignedAll is s = true → runSeq is s = .ok (execAll is s, traceAll is s)
  | [], _, _, _ => rfl
  | i :: is, s, hf, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [alignedAll, Bool.and_eq_true] at ha
    simp only [runSeq, ha.1, ↓reduceIte, exec_ok_of_falls hf.1, runSeq_eq is _ hf.2 ha.2,
      execAll, traceAll]

theorem execAll_append (l₁ l₂ : List Instr) (s : State) :
    execAll (l₁ ++ l₂) s = execAll l₂ (execAll l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

theorem alignedAll_append (l₁ l₂ : List Instr) (s : State) :
    alignedAll (l₁ ++ l₂) s = (alignedAll l₁ s && alignedAll l₂ (execAll l₁ s)) := by
  induction l₁ generalizing s with
  | nil => simp [alignedAll, execAll]
  | cons i is ih => simp [alignedAll, execAll, ih, Bool.and_assoc]

theorem traceAll_append (l₁ l₂ : List Instr) (s : State) :
    traceAll (l₁ ++ l₂) s = traceAll l₁ s ++ traceAll l₂ (execAll l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => simp [traceAll, execAll, ih]

/-! ## Static frame: memory and registers an instruction may write -/

/-- The instruction may write memory. -/
def Instr.writesMem : Instr → Bool
  | .memReg op _ _ _ | .memImm op _ _ _ => !op.isLoad
  | .strSp _ _ | .push _ _ | .stm _ _ => true
  | _ => false

/-- Registers other than PC the instruction may write. -/
def Instr.dsts : Instr → List Nat
  | .lslImm d _ _ | .lsrImm d _ _ | .addReg d _ _ | .subReg d _ _ | .addImm3 d _ _
  | .subImm3 d _ _ | .movImm d _ | .addImm8 d _ | .subImm8 d _ | .addRdSp d _ | .uxth d _ => [d.val]
  | .cmpImm _ _ | .strSp _ _ | .bcond _ _ | .b _ => []
  | .dp op dn _ => if op = .tst ∨ op = .cmp then [] else [dn.val]
  | .movHi d _ => [d.val]
  | .ldrLit t _ | .ldrSp t _ => [t.val]
  | .memReg op t _ _ | .memImm op t _ _ => if op.isLoad then [t.val] else []
  | .addSp _ | .subSp _ | .push _ _ => [13]
  | .pop l _ => (listRegs l).map (·.val) ++ [13]
  | .stm n _ => [n.val]
  | .ldm n l => (listRegs l).map (·.val) ++ [n.val]
  | .bl _ => [14]

theorem accesses_read {i : Instr} (h : i.writesMem = false) (s : State) :
    ∀ a ∈ i.accesses s, a.kind = .read := by
  intro a ha
  cases i <;> simp only [Instr.writesMem, Bool.true_eq_false,
    Bool.not_eq_false'] at h <;> simp only [Instr.accesses, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  all_goals first
    | (subst ha; simp [h])
    | (simp only [wordAccesses, List.mem_map, List.mem_range] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl)
    | exact absurd ha (by simp)

theorem next_mem {i : Instr} (h : i.writesMem = false) (s : State) : (i.next s).mem = s.mem := by
  unfold Instr.next
  split
  · rename_i s' hex
    funext y
    apply exec_mem_other i s s' hex y
    rintro ⟨a, ha, hw, _⟩
    rw [accesses_read h s a ha] at hw; cases hw
  · rfl

theorem execAll_mem : ∀ (is : List Instr) (s : State), is.all (!·.writesMem) = true →
    (execAll is s).mem = s.mem
  | [], _, _ => rfl
  | i :: is, s, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [execAll, execAll_mem is _ h.2, next_mem h.1]

theorem loadRegs_regs_other (s : State) (a : Word) (rs : List LowReg) (r : Reg)
    (h : r.val ∉ rs.map (·.val)) : (loadRegs s a (rs.map LowReg.toReg)).regs r = s.regs r := by
  apply loadRegs_regs_ne
  simp only [List.mem_map, not_exists, not_and] at h ⊢
  intro x hx e; exact h x hx (by rw [← e]; rfl)

theorem next_regs_other {i : Instr} (s : State) (r : Reg) (h15 : r.val ≠ 15)
    (hd : r.val ∉ i.dsts) : (i.next s).regs r = s.regs r := by
  have h15' : (r = 15) = False := by
    apply propext; constructor
    · intro e; exact h15 (by rw [e]; rfl)
    · intro f; exact f.elim
  unfold Instr.next
  split
  · rename_i s' hex
    cases i <;> simp only [Instr.dsts, List.mem_cons, List.not_mem_nil, or_false] at hd
    case pop l pc =>
      simp only [List.mem_append, List.mem_singleton, not_or] at hd
      simp only [Instr.exec] at hex
      split at hex
      · split at hex
        · cases hex
          simp only [M0Crypto.Armv6M.State.setReg, h15', ite_false]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hd.2 (by rw [e]; rfl))), loadRegs_regs_other _ _ _ _ hd.1]
          simp [M0Crypto.Armv6M.State.setReg, h15']
        · cases hex
      · cases hex
        simp only [M0Crypto.Armv6M.State.setReg]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hd.2 (by rw [e]; rfl))), loadRegs_regs_other _ _ _ _ hd.1]
        simp [h15']
    case ldm n l =>
      simp only [List.mem_append, List.mem_singleton, not_or] at hd
      simp only [Instr.exec] at hex
      split at hex <;> cases hex
      · rw [loadRegs_regs_other _ _ _ _ hd.1]; simp [M0Crypto.Armv6M.State.setReg, h15']
      · simp only [M0Crypto.Armv6M.State.setReg]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hd.2 (by rw [e]; rfl))), loadRegs_regs_other _ _ _ _ hd.1]
        simp [h15']
    case bcond =>
      simp only [Instr.exec] at hex
      split at hex <;> cases hex <;> simp [M0Crypto.Armv6M.State.setReg, h15']
    case dp op dn m =>
      cases op <;> simp only [Instr.exec] at hex <;> cases hex <;>
        simp_all [addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
          M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV, LowReg.toReg, Fin.ext_iff]
    case memReg op t n m =>
      simp only [Instr.exec] at hex; cases hex
      cases op <;> simp_all [Instr.exec.memOp, MemOp.isLoad, M0Crypto.Armv6M.State.setReg,
        LowReg.toReg, Fin.ext_iff]
    case memImm op t n imm =>
      simp only [Instr.exec] at hex; cases hex
      cases op <;> simp_all [Instr.exec.memOp, MemOp.isLoad, M0Crypto.Armv6M.State.setReg,
        LowReg.toReg, Fin.ext_iff]
    all_goals
      simp only [Instr.exec] at hex; cases hex
      simp_all [addFlags, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
        M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV, LowReg.toReg, Fin.ext_iff]
      try (intro e; exact absurd e ‹¬ (r.val = 13)›)
      try (intro e; exact absurd e ‹¬ (r.val = 14)›)
  · rfl

theorem execAll_regs_other : ∀ (is : List Instr) (s : State) (r : Reg), r.val ≠ 15 →
    is.all (fun i => !(i.dsts.contains r.val)) = true → (execAll is s).regs r = s.regs r
  | [], _, _, _, _ => rfl
  | i :: is, s, r, h15, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    rw [execAll, execAll_regs_other is _ r h15 (by simpa using h.2), next_regs_other s r h15 h.1]

/-! ## Blocks and single steps inside a Harvard run -/

theorem execAll_pc : ∀ (is : List Instr) (s : State), is.all Instr.falls = true →
    (execAll is s).pc = s.pc + BitVec.ofNat 32 (seqSize is)
  | [], s, _ => by simp [execAll, seqSize]
  | i :: is, s, hf => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    rw [execAll, execAll_pc is _ hf.2, exec_pc hf.1 (exec_ok_of_falls hf.1 s)]
    simp only [seqSize, List.map_cons, List.sum_cons]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem seqAt_size : ∀ (bytes : List (BitVec 8)) (off : Nat) (is : List Instr),
    seqAt bytes off is = true → off + seqSize is ≤ bytes.length ∨ is = []
  | _, _, [], _ => .inr rfl
  | bytes, off, i :: is, h => by
    simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    left
    rcases seqAt_size bytes (off + i.size) is h.2 with h' | h'
    · simp only [seqSize, List.map_cons, List.sum_cons] at h' ⊢; omega
    · subst h'; simp [seqSize]; omega

/-- A decoded, aligned, non-branching block, then `n` more steps. -/
theorem runH_block {bytes : List (BitVec 8)} {base : Word} (hb : base.toNat % 2 = 0)
    (hlen : bytes.length < 2 ^ 32) (is : List Instr) (off : Nat) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hseq : seqAt bytes off is = true)
    (hf : is.all Instr.falls = true) (ha : alignedAll is s = true) (n : Nat) :
    runH bytes base (is.length + n) s =
      match runH bytes base n (execAll is s) with
      | .error e => .error e
      | .ok (s2, t2) => .ok (s2, traceAll is s ++ t2) := by
  rw [runH_add, runH_seq hb hlen is off s hpc ho hseq hf, runSeq_eq is s hf ha]
  rfl

/-- One Harvard step of the instruction at offset `off`. -/
theorem stepH_of_instr {bytes : List (BitVec 8)} {base : Word} (hb : base.toNat % 2 = 0)
    (hlen : bytes.length < 2 ^ 32) {s s' : State} {off : Nat} {i : Instr}
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt bytes off = some i) (hsz : off + i.size ≤ bytes.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s') :
    stepH bytes base s = .ok (s', ⟨s.pc, i, i.accesses s⟩) := by
  have hev := pc_even base off hb ho
  rw [← hpc] at hev
  have hoff : (s.pc - base).toNat = off := by rw [hpc]; exact sub_base base off (by omega)
  simp only [stepH, hev, hoff, hi, hsz, ha, hex, Bool.false_eq_true, ↓reduceIte]

theorem runH_one_step {bytes : List (BitVec 8)} {base : Word} {s s' : State} {e : Event} (n : Nat)
    (h : stepH bytes base s = .ok (s', e)) :
    runH bytes base (n + 1) s =
      match runH bytes base n s' with
      | .error e' => .error e'
      | .ok (s2, t2) => .ok (s2, e :: t2) := by
  simp only [runH, h]
  rfl

theorem seqAt_append (bytes : List (BitVec 8)) : ∀ (off : Nat) (l₁ l₂ : List Instr),
    seqAt bytes off (l₁ ++ l₂) = (seqAt bytes off l₁ && seqAt bytes (off + seqSize l₁) l₂)
  | off, [], l₂ => by simp [seqAt, seqSize]
  | off, i :: is, l₂ => by
    simp only [List.cons_append, seqAt, seqAt_append bytes (off + i.size) is l₂, Bool.and_assoc]
    simp only [seqSize, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem seqSize_append (l₁ l₂ : List Instr) : seqSize (l₁ ++ l₂) = seqSize l₁ + seqSize l₂ := by
  simp [seqSize]

end M0Crypto.Thumb
