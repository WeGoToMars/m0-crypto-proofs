import M0Crypto.Release.RoutinePieces

set_option linter.unusedSimpArgs false

/-!
# Branches and literal loads as pieces

Rules for routines whose code branches, in the style of `RoutinePieces`: each takes the check of
its pieces followed by any `rest` and hands the check of `rest` on.

- `branch`: a glue block and a conditional branch `g; b<cond> tgt`. One continuation receives the
  state after the branch and the pc it has on each outcome of the condition, so a caller that
  knows the outcome takes one side and a caller that does not splits on it.
- `jump`: an unconditional branch `b tgt`.
- `lit`: a literal-pool load `ldr rt, [pc, #imm]` into any low register (`ReachF.lit` keeps the
  caller's high registers and so loads only `r0`-`r3`).
- The condition flags of the compares and shifts that precede the branches, as comparisons of
  `toNat` values.
-/

namespace M0Crypto.Release.RoutineBranch

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.TraceSpec (InStackWindow)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

variable {base : Word} {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
  {t : State} {Q : State → Prop} {o d : Nat} {rest : List Piece}

/-- The judgment of a routine body with the caller facts `Caller base sp0 N Wc`. -/
abbrev Body (base : Word) (cs : List (Nat × Nat)) (Rc Wc : List Rgn) (sp0 : Word) (N : Nat)
    (t : State) (Q : State → Prop) : Prop :=
  ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q

theorem setReg15_regs (u : State) (v : Word) (r : Reg) (h : r.val ≠ 15) :
    (u.setReg 15 v).regs r = u.regs r := by
  simp [State.setReg, show r ≠ 15 from fun e => h (by rw [e]; rfl)]

theorem setReg15_pc (u : State) (v : Word) : (u.setReg 15 v).pc = v := by
  simp [State.setReg, State.pc]

theorem condPassed_setReg (u : State) (r : Reg) (v : Word) (c : BitVec 4) :
    condPassed c (u.setReg r v) = condPassed c u := rfl

/-! ## Conditional branches -/

/-- The decided checks of `g; b<cond> tgt` at `o`: the glue's, and the branch in the caller's code
and the artifact, reaching `tgt`. -/
def branchOk [CodeBytes B BS] (cs : List (Nat × Nat)) (g : List Instr) (o tgt d N : Nat) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) : Bool :=
  glueOk cs g o d N al wg rg && (o + seqSize g) % 2 == 0 &&
  rangesSub [(o + seqSize g, o + seqSize g + 2)] cs &&
  decide (o + seqSize g + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 (o + seqSize g) + 4#32 + (brImm8 (o + seqSize g) tgt ++ 0#1).signExtend 32 =
    BitVec.ofNat 32 tgt)

/-- **A glue block and a conditional branch** `g; b<cond> tgt`. The continuation receives the
state `u` after the branch: the registers other than the pc, the memory and the flags of the
state after `g`, the frame of `g`, and the pc on each outcome (the fall-through with the check of
`rest`). -/
theorem branch (F : Caller base sp0 N Wc) (g : List Instr) (c : BitVec 4) {tgt : Nat}
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat))
    (hp : piecesAt B o (.seq g :: .bcond c tgt :: rest) = true)
    (hok : branchOk cs g o tgt d N al wg rg = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B) (hs : GlueSides t Rc Wc al wg rg)
    (k : ∀ u, (∀ r : Reg, r.val ≠ 15 → u.regs r = (execAll g t).regs r) →
      u.mem = (execAll g t).mem → (∀ c', condPassed c' u = condPassed c' (execAll g t)) →
      MemEq (regions t wg) t.mem u.mem → CodeAt u.mem base B →
      (condPassed c (execAll g t) = true → u.pc = base + BitVec.ofNat 32 tgt) →
      (condPassed c (execAll g t) = false → u.pc = base + BitVec.ofNat 32 (o + seqSize g + 2) ∧
        piecesAt B (o + seqSize g + 2) rest = true) →
      Body base cs Rc Wc sp0 N u Q) :
    Body base cs Rc Wc sp0 N t Q := by
  obtain ⟨h1, h2⟩ := piecesAt_cons hp
  obtain ⟨h2, h3⟩ := piecesAt_cons h2
  simp only [Piece.instrs, Piece.size] at h1 h2 h3
  rw [show brSize = 2 from rfl] at h3
  simp only [branchOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hg, ho2⟩, hcs⟩, hsz⟩, ht⟩ := hok
  have hd : d ≤ N := by
    simp only [glueOk, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.2
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  refine ReachF.glue F g al wg rg h1 hpc h13 hcode hs (fun p1 s1 c1 m1 => ?_) hg
  refine ReachF.bcond hb2 tgt c _ p1 ho2 (instrAt_of_seqAt h2) hsz ht
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega))) ⟨d, hd, s1⟩
    (fun hT => ?_) (fun hF => ?_)
  · exact k _ (fun r hr => setReg15_regs _ _ r hr) rfl (fun _ => rfl) m1 c1
      (fun _ => setReg15_pc _ _) (fun h => absurd h (by simp [hT]))
  · exact k _ (fun r hr => setReg15_regs _ _ r hr) rfl (fun _ => rfl) m1 c1
      (fun h => absurd h (by simp [hF])) (fun _ => ⟨setReg15_pc _ _, h3⟩)

/-! ## Unconditional branches -/

/-- The decided checks of `b tgt` at `o`. -/
def jumpOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o tgt d N : Nat) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (o + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 o + 4#32 + (brImm11 o tgt ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt) &&
  decide (d ≤ N)

/-- **`b tgt`**. -/
theorem jump {tgt : Nat} (F : Caller base sp0 N Wc) (hp : piecesAt B o (.b tgt :: rest) = true)
    (hok : jumpOk cs o tgt d N = true) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (k : Body base cs Rc Wc sp0 N (t.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    Body base cs Rc Wc sp0 N t Q := by
  obtain ⟨h1, -⟩ := piecesAt_cons hp
  simp only [Piece.instrs] at h1
  simp only [jumpOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨ho, hcs⟩, hsz⟩, ht⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  exact ReachS.b hb2 o tgt _ hpc ho (instrAt_of_seqAt h1) hsz ht
    ⟨by rw [hpc]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega)),
      fun y hy => absurd hy (writes_nil y), fun y hy => absurd hy (reads_nil y), ⟨d, hd, h13⟩⟩ k

/-! ## Literal loads -/

/-- The decided checks of `ldr rt, [pc, #imm * 4]` at `o`. -/
def litOk' [CodeBytes B BS] (cs : List (Nat × Nat)) (o d N : Nat) (imm : BitVec 8) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs &&
  decide (litOff o imm + 4 ≤ BS) && decide (d ≤ N)

/-- **A literal-pool load into any low register**: the state after it is `litState`, which loads
the code word at `litOff o imm`. -/
theorem lit (F : Caller base sp0 N Wc) (rt : LowReg) (imm : BitVec 8)
    (hp : piecesAt B o (.seq [.ldrLit rt imm] :: rest) = true) (hok : litOk' cs o d N imm = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B) (hrd : Sub [codeR base] Rc)
    (k : piecesAt B (o + 2) rest = true →
      Body base cs Rc Wc sp0 N (litState base t o rt (Frame.codeWord (litOff o imm))) Q) :
    Body base cs Rc Wc sp0 N t Q := by
  obtain ⟨h1, h2⟩ := piecesAt_cons hp
  simp only [Piece.instrs, Piece.size] at h1 h2
  have hi := instrAt_of_seqAt h1
  simp only [litOk', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨ho, hcs⟩, hsz⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have := F.code32
  have hl : litOff o imm % 4 = 0 := by simp only [litOff]; omega
  have : BS < 2 ^ 32 := CodeBytes.lt
  have ha : ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4) =
      base + BitVec.ofNat 32 (litOff o imm) := by
    rw [hpc, Frame.lit_addr base F.b4 o imm.toNat (by simp only [litOff] at hsz; omega)]; rfl
  have hal : (base + BitVec.ofNat 32 (litOff o imm)).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := F.b4; omega
  refine ReachF.step hb2 (.ldrLit rt imm) hpc ho hi (by rw [B_len]; simp [Instr.size]; simp only [litOff] at hsz; omega)
    (by simp only [Instr.accesses]; rw [ha]; simp [Access.aligned, hal]; have := F.b4; omega) ?_
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by simp [Instr.size]))) ?_ ?_
    ⟨d, hd, h13⟩ (k (by simpa [seqSize, Instr.size] using h2))
  · rw [show (Instr.ldrLit rt imm).exec t = .ok ((t.setReg 15 (t.pc + BitVec.ofNat 32 2)).setReg
      rt.toReg (read32 t.mem (((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4))))
      from rfl, ha, Frame.read32_code hcode _ hsz, hpc, ofNat_add_assoc]
    rfl
  · intro y hy; simp [Instr.accesses, Writes] at hy
  · rintro y ⟨a, ha', -, j, hj, rfl⟩
    simp only [Instr.accesses, List.mem_singleton] at ha'
    subst ha'
    refine hrd.has ⟨_, List.mem_singleton_self _, litOff o imm + j,
      by simp only [codeR] at *; omega, by rw [ha, ofNat_add_assoc]; rfl⟩

theorem litState_regs (t : State) (o : Nat) (rt : LowReg) (v : Word) (r : Reg) (h15 : r.val ≠ 15) :
    (litState base t o rt v).regs r = if r = rt.toReg then v else t.regs r := by
  by_cases h : r = rt.toReg
  · subst h; simp [litState, State.setReg]
  · simp [litState, State.setReg, h, show r ≠ 15 from fun e => h15 (by rw [e]; rfl)]

theorem litState_pc (t : State) (o : Nat) (rt : LowReg) (v : Word) :
    (litState base t o rt v).pc = base + BitVec.ofNat 32 (o + 2) := by
  have h : (15 : Reg) ≠ rt.toReg := fun he => by
    have : (rt.toReg).val < 8 := rt.isLt
    rw [← he] at this; exact absurd this (by decide)
  simp [litState, State.setReg, State.pc, h]

/-! ## Flags -/

theorem cmpImm_flags (n : LowReg) (k : BitVec 8) (s : State) :
    ((Instr.cmpImm n k).next s).c = decide (k.toNat ≤ (s.regs n.toReg).toNat) ∧
    ((Instr.cmpImm n k).next s).z = decide ((s.regs n.toReg).toNat = k.toNat) := by
  have hk := k.isLt; have hr := (s.regs n.toReg).isLt
  simp [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setNZ, State.reg,
    M0Crypto.Armv6M.addWithCarry]
  refine ⟨by omega, Bool.eq_iff_iff.mpr ?_⟩
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp; omega

theorem cmpReg_flags (a b : LowReg) (s : State) :
    ((Instr.dp .cmp a b).next s).c = decide ((s.regs b.toReg).toNat ≤ (s.regs a.toReg).toNat) ∧
    ((Instr.dp .cmp a b).next s).z = decide ((s.regs a.toReg).toNat = (s.regs b.toReg).toNat) := by
  have ha := (s.regs a.toReg).isLt; have hb := (s.regs b.toReg).isLt
  simp [Instr.next, Instr.exec, addFlags, State.setNZCV, State.setNZ, State.reg,
    M0Crypto.Armv6M.addWithCarry]
  refine ⟨by omega, Bool.eq_iff_iff.mpr ?_⟩
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq; simp; omega

theorem shl31_eq_zero (x : Word) : (x <<< 31 == 0#32) = decide (x.toNat % 2 = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

theorem lsl31_z (d m : LowReg) (s : State) :
    ((Instr.lslImm d m 31).next s).z = decide ((s.regs m.toReg).toNat % 2 = 0) := by
  have e : (Instr.lslImm d m 31).next s =
      ((s.setReg 15 (s.pc + 2#32)).setReg d.toReg (s.regs m.toReg <<< 31)).setNZC
        (s.regs m.toReg <<< 31) ((s.regs m.toReg).getLsbD 1) := rfl
  rw [e]
  exact shl31_eq_zero _

/-- `b<cond>` after a compare: equal (0), not equal (1), unsigned lower (3), unsigned higher (8). -/
theorem cond_eq (u : State) : condPassed 0 u = u.z := rfl
theorem cond_ne (u : State) : condPassed 1 u = !u.z := rfl
theorem cond_lo (u : State) : condPassed 3 u = !u.c := rfl
theorem cond_hi (u : State) : condPassed 8 u = (u.c && !u.z) := rfl

end M0Crypto.Release.RoutineBranch
