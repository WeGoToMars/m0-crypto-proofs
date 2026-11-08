import M0Crypto.Armv6M.Step

/-!
Reusable lemmas for straight-line code. If the code region decodes to a list of
instructions starting at the current PC, every data access along the way is
aligned, and PC doesn't wrap, then running `length` steps executes exactly those
instructions. The resulting trace depends only on the starting PC and SP.
-/

namespace M0Crypto.Armv6M

/-- Execute a list of decoded instructions in order. -/
def execAll : List Instr → State → State
  | [], s => s
  | i :: is, s => execAll is (exec i s)

/-- Trace of straight-line execution of `is` from `s`. -/
def execTrace : List Instr → State → List Event
  | [], _ => []
  | i :: is, s => ⟨s.pc.toNat, i, i.accesses s⟩ :: execTrace is (exec i s)

/-- Every data access along straight-line execution of `is` from `s` is aligned. -/
def alignedAll : List Instr → State → Bool
  | [], _ => true
  | i :: is, s => i.aligned s && alignedAll is (exec i s)

/-- The code region decodes to `is` starting at address `a` (decidable check). -/
def decodesAt (c : Code) : Nat → List Instr → Bool
  | _, [] => true
  | a, i :: is =>
    (match c.fetch a with
     | some hw => decode hw == .ok i
     | none => false) && decodesAt c (a + 2) is

theorem execAll_append (l₁ l₂ : List Instr) (s : State) :
    execAll (l₁ ++ l₂) s = execAll l₂ (execAll l₁ s) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (exec i s)

theorem exec_pc (i : Instr) (s : State) : (exec i s).pc = s.pc + 2#32 := by
  cases i <;> simp [exec, State.setReg, State.pc]

/-- General-purpose register written by an instruction, or 16 if none (stores). -/
def Instr.dst : Instr → Nat
  | .movsImm d _ => d.val
  | .addsReg d _ _ => d.val
  | .eorsReg dn _ => dn.val
  | .rorsReg dn _ => dn.val
  | .ldrSp t _ => t.val
  | .strSp _ _ => 16

def Instr.isStore : Instr → Bool
  | .strSp _ _ => true
  | _ => false

theorem exec_mem (i : Instr) (s : State) (h : i.isStore = false) : (exec i s).mem = s.mem := by
  cases i <;> simp_all [exec, State.setReg, State.setNZ, Instr.isStore]

theorem execAll_mem : ∀ (is : List Instr) (s : State),
    (∀ i ∈ is, i.isStore = false) → (execAll is s).mem = s.mem
  | [], _, _ => rfl
  | i :: is, s, h => by
    rw [execAll, execAll_mem is _ (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      exec_mem i s (h i List.mem_cons_self)]

theorem execAll_pc : ∀ (is : List Instr) (s : State),
    (execAll is s).pc = s.pc + BitVec.ofNat 32 (2 * is.length)
  | [], s => by simp [execAll]
  | i :: is, s => by
    rw [execAll, execAll_pc is, exec_pc, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_cons]
    omega

theorem exec_regs_other (i : Instr) (s : State) (r : Reg)
    (h15 : r.val ≠ 15) (hd : r.val ≠ i.dst) : (exec i s).regs r = s.regs r := by
  cases i <;> simp only [Instr.dst] at hd <;>
    simp [exec, State.setReg, State.setNZ, LowReg.toReg, Fin.ext_iff, hd]
  -- Residual goals `↑r = ↑(15 : Fin 16) → _`; `↑(15 : Fin 16)` is `15` by definition.
  all_goals exact fun h => absurd h h15

theorem execAll_regs_other : ∀ (is : List Instr) (s : State) (r : Reg),
    r.val ≠ 15 → (∀ i ∈ is, r.val ≠ i.dst) → (execAll is s).regs r = s.regs r
  | [], _, _, _, _ => rfl
  | i :: is, s, r, h15, hd => by
    rw [execAll, execAll_regs_other is _ r h15 (fun j hj => hd j (List.mem_cons_of_mem _ hj)),
      exec_regs_other i s r h15 (hd i List.mem_cons_self)]

/-- No instruction in the subset writes SP. -/
theorem exec_sp (i : Instr) (s : State) : (exec i s).regs 13 = s.regs 13 :=
  exec_regs_other i s 13 (by decide) (by cases i <;> simp [Instr.dst] <;> omega)

theorem accesses_congr (i : Instr) (s₁ s₂ : State) (h : s₁.regs 13 = s₂.regs 13) :
    i.accesses s₁ = i.accesses s₂ := by
  cases i <;> simp [Instr.accesses, spAddr, h]

/-- Constant-time core: the straight-line trace is determined by the starting PC and SP. -/
theorem execTrace_congr : ∀ (is : List Instr) (s₁ s₂ : State),
    s₁.pc = s₂.pc → s₁.regs 13 = s₂.regs 13 → execTrace is s₁ = execTrace is s₂
  | [], _, _, _, _ => rfl
  | i :: is, s₁, s₂, hpc, hsp => by
    simp only [execTrace, hpc, accesses_congr i s₁ s₂ hsp]
    rw [execTrace_congr is (exec i s₁) (exec i s₂) (by rw [exec_pc, exec_pc, hpc])
      (by rw [exec_sp, exec_sp, hsp])]

/-- Instructions with data-memory accesses. -/
def Instr.isMem : Instr → Bool
  | .ldrSp _ _ => true
  | .strSp _ _ => true
  | _ => false

theorem accesses_nil (i : Instr) (s : State) (h : i.isMem = false) : i.accesses s = [] := by
  cases i <;> simp_all [Instr.isMem, Instr.accesses]

/-- Without memory instructions, the trace is determined by the starting PC alone. -/
theorem execTrace_congr_noMem : ∀ (is : List Instr) (s₁ s₂ : State),
    (∀ i ∈ is, i.isMem = false) → s₁.pc = s₂.pc → execTrace is s₁ = execTrace is s₂
  | [], _, _, _, _ => rfl
  | i :: is, s₁, s₂, hm, hpc => by
    have hi := hm i List.mem_cons_self
    simp only [execTrace, hpc, accesses_nil i s₁ hi, accesses_nil i s₂ hi]
    rw [execTrace_congr_noMem is (exec i s₁) (exec i s₂)
      (fun j hj => hm j (List.mem_cons_of_mem _ hj)) (by rw [exec_pc, exec_pc, hpc])]

theorem alignedAll_noMem : ∀ (is : List Instr) (s : State),
    (∀ i ∈ is, i.isMem = false) → alignedAll is s = true
  | [], _, _ => rfl
  | i :: is, s, hm => by
    simp only [alignedAll, Instr.aligned, accesses_nil i s (hm i List.mem_cons_self),
      List.all_nil, Bool.true_and]
    exact alignedAll_noMem is _ (fun j hj => hm j (List.mem_cons_of_mem _ hj))

theorem alignedAll_congr : ∀ (is : List Instr) (s₁ s₂ : State),
    s₁.regs 13 = s₂.regs 13 → alignedAll is s₁ = alignedAll is s₂
  | [], _, _, _ => rfl
  | i :: is, s₁, s₂, hsp => by
    simp only [alignedAll, Instr.aligned, accesses_congr i s₁ s₂ hsp]
    rw [alignedAll_congr is (exec i s₁) (exec i s₂) (by rw [exec_sp, exec_sp, hsp])]

/-- With SP word-aligned, every access in the subset is aligned (all are SP + 4·imm8). -/
theorem aligned_of_sp (i : Instr) (s : State) (h : (s.regs 13).toNat % 4 = 0) :
    i.aligned s = true := by
  cases i <;> simp [Instr.aligned, Instr.accesses, spAddr, BitVec.toNat_add] <;> omega

theorem alignedAll_of_sp : ∀ (is : List Instr) (s : State),
    (s.regs 13).toNat % 4 = 0 → alignedAll is s = true
  | [], _, _ => rfl
  | i :: is, s, h => by
    simp only [alignedAll, aligned_of_sp i s h, Bool.true_and]
    exact alignedAll_of_sp is _ (by rw [exec_sp]; exact h)

theorem step_of_decodes (c : Code) (s : State) (i : Instr)
    (h : (match c.fetch s.pc.toNat with
          | some hw => decode hw == .ok i
          | none => false) = true)
    (ha : i.aligned s = true) :
    step c s = .ok (exec i s, ⟨s.pc.toNat, i, i.accesses s⟩) := by
  unfold step
  cases hf : c.fetch s.pc.toNat with
  | none => simp [hf] at h
  | some hw =>
    simp only [hf, beq_iff_eq] at h
    simp [hf, h, ha]

theorem run_straight (c : Code) :
    ∀ (is : List Instr) (s : State),
      decodesAt c s.pc.toNat is = true →
      alignedAll is s = true →
      s.pc.toNat + 2 * is.length < 2 ^ 32 →
      run c is.length s = .ok (execAll is s, execTrace is s)
  | [], _, _, _, _ => rfl
  | i :: is, s, hd, ha, hb => by
    simp only [decodesAt, Bool.and_eq_true] at hd
    simp only [alignedAll, Bool.and_eq_true] at ha
    obtain ⟨h1, h2⟩ := hd
    have hstep := step_of_decodes c s i h1 ha.1
    have hpc : (exec i s).pc.toNat = s.pc.toNat + 2 := by
      rw [exec_pc, BitVec.toNat_add]
      simp only [List.length_cons] at hb
      simp only [BitVec.toNat_ofNat]
      omega
    have ih := run_straight c is (exec i s) (by rw [hpc]; exact h2) ha.2
      (by rw [hpc]; simp only [List.length_cons] at hb; omega)
    simp only [List.length_cons, run, hstep, ih, execAll, execTrace]

end M0Crypto.Armv6M
