import M0Crypto.Release.X25519MulcWord

set_option linter.unusedSimpArgs false

/-!
Macro step of the `m0c_fe_mulc_add` chain (`X25519Macros.mulcStep`; plan `x25519-proofs.md`,
phase 8): one `word` with carry-in register `k` (low word in `r4`, high word in `a`), then
`mov r5, r12; str r4, [r5, #4i]`.

`mulcStep_run_w` is generic in the word index `i` and the registers `k`, `a`: the store goes
to word `i` from the pointer in `r12`, and the high word is left in `a` as the next carry-in.
-/

namespace M0Crypto.Release.X25519MulcStep
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem (regs_strImm mem_strImm)
open M0Crypto.Release.Blake2s (regs_movHi)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519MulcWord
open M0Crypto.Release.X25519Macros (mulcWord mulcStep)

/-- The store of a step: `mov r5, r12; str r4, [r5, #4i]`. -/
def store (i : Nat) : List Instr := [.movHi 5 12, .memImm .str 4 5 (BitVec.ofNat 5 i)]

/-- The address of word `i` from `r12`. -/
def sAddr (s : State) (i : Nat) : Word := s.regs 12 + BitVec.ofNat 32 ((BitVec.ofNat 5 i).toNat * 4)

theorem mulcStep_split (i : Nat) (k a : LowReg) : mulcStep i k a = mulcWord i (some k) a 4 5 ++ store i :=
  rfl

theorem store_exec (s : State) (i : Nat) :
    let s' := execAll (store i) s
    s'.mem = write32 s.mem (sAddr s i) (s.reg 4) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 5 → s'.regs r = s.regs r := by
  intro s'
  refine ⟨?_, fun r h15 h5 => ?_⟩
  · simp only [s', store, execAll, mem_strImm, next_mem (i := .movHi 5 12) rfl, State.reg, sAddr]
    simp (config := {decide := true}) only [regs_movHi, ne_eq, ite_true, ite_false,
      toReg_ne_15, not_false_eq_true]
  · simp only [s', store, execAll, regs_strImm _ _ _ _ _ h15, regs_movHi _ _ _ _ h15, h5, ite_false]

theorem store_acc {Wr : Word → Prop} (s : State) (i : Nat) (h12 : (s.regs 12).toNat % 4 = 0)
    (hW : ∀ q < 4, Wr (sAddr s i + BitVec.ofNat 32 q)) : AccAll (AccOk Wr) (store i) s := by
  refine accAll_cons (fun x hx => by simp [Instr.accesses] at hx) (accAll_cons (fun x hx => ?_) (accAll_nil _ _))
  have e : ((Instr.movHi 5 12).next s).reg 5 = s.regs 12 := by
    simp (config := {decide := true}) only [State.reg, regs_movHi _ _ _ _ (toReg_ne_15 5), ite_true]
  simp only [Instr.accesses, MemOp.isLoad, MemOp.width, e, List.mem_singleton] at hx
  subst hx
  refine ⟨aligned_word (word_add_aligned h12 (by omega)), fun _ q hq => hW q hq⟩

/-- The registers of a step: `k`, `a`, `r4`, `r5` and the fixed `r1, r2, r6, r7` are
distinct. -/
def SDist (k a : LowReg) : Prop := [k, a, 4, 5, 1, 2, 6, 7].Nodup

theorem sdist_word {k a : LowReg} (h : SDist k a) : Dist a 4 5 ∧ KOk a 4 5 (some k) := by
  simp only [SDist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨k1, k2, k3, -, -, -, -⟩, ⟨a1, a2, a3, a4, a5, a6⟩, -⟩ := h
  refine ⟨?_, k1, k2, k3⟩
  simp only [Dist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨a1, a2, a3, a4, a5, a6⟩, by decide, by decide, by decide, by decide, by decide⟩

theorem mulcStep_falls (i : Nat) (k a : LowReg) : (mulcStep i k a).all Instr.falls = true := by
  simp [mulcStep, mulcWord, Instr.falls]; decide

/-- One chain step in a `ReachW` proof: `L` (the low word) is stored at word `i` from `r12`,
the high word is left in `a`, and `L + 2^32 * a = 121666 * a[i] + b[i] + k`. -/
theorem mulcStep_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off i : Nat} {k a : LowReg} (hd : SDist k a)
    (hseq : seqAt B off (mulcStep i k a) = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (mulcStep i k a)))
    (h1 : (x.reg 1).toNat % 4 = 0) (h2 : (x.reg 2).toNat % 4 = 0)
    (h12 : (x.regs 12).toNat % 4 = 0)
    (h6 : x.reg 6 = 0#32) (h7 : x.reg 7 = 60833#32)
    (hW : ∀ q < 4, Wr (sAddr x i + BitVec.ofNat 32 q)) {Q : State → Prop}
    (cont : ∀ (y : State) (L : Word), y.pc = base + BitVec.ofNat 32 (off + seqSize (mulcStep i k a)) →
      L.toNat + 2 ^ 32 * (y.reg a).toNat =
        121666 * (read32 x.mem (wAddr x 1 i)).toNat + (read32 x.mem (wAddr x 2 i)).toNat +
          (x.reg k).toNat →
      y.mem = write32 x.mem (sAddr x i) L →
      (∀ r : Reg, r ≠ 15 → r ≠ a.toReg → r ≠ 4 → r ≠ 5 → y.regs r = x.regs r) →
      ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  obtain ⟨hd', hk⟩ := sdist_word hd
  have hf := mulcStep_falls i k a
  rw [mulcStep_split] at hseq hr hf cont
  have hfw := mulcWord_falls i (some k) a 4 5
  obtain ⟨v, m, o⟩ := mulcWord_exec x i (some k) a 4 5 hd' hk h6 h7
  generalize hx1 : execAll (mulcWord i (some k) a 4 5) x = x1 at v m o
  have lo : ∀ y : LowReg, (12 : Reg) ≠ y.toReg := fun y e => by
    have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have e12 : x1.regs 12 = x.regs 12 := o 12 (by decide) (lo a) (lo 4) (lo 5)
  have hs1 : sAddr x1 i = sAddr x i := by simp only [sAddr, e12]
  refine ReachW.blockAcc hb _ off hpc ho hseq (by rw [List.all_append, hfw]; rfl)
    (accAll_append (mulcWord_acc x i (some k) a 4 5 hd' h1 h2)
      (by rw [hx1]; exact store_acc x1 i (by rw [e12]; exact h12) (by rw [hs1]; exact hW))) hr ?_
  rw [execAll_append, hx1]
  obtain ⟨sm, so⟩ := store_exec x1 i
  have ha5 : a.toReg ≠ 5 := by
    have h := hd'
    simp only [Dist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    exact fun e => h.1.2.1 (by rw [← X25519Mul.toReg_inj]; exact e)
  refine cont _ (x1.reg 4) ?_ ?_ ?_ ?_
  · rw [execAll_pc _ _ (by rfl), ← hx1, execAll_pc _ _ hfw, hpc, ofNat_add_assoc, ofNat_add_assoc,
      seqSize_append]
  · have ea : (execAll (store i) x1).reg a = x1.reg a := so a.toReg (toReg_ne_15 a) ha5
    rw [ea]; exact v
  · rw [sm, m, hs1]
  · intro r h15 ha h4 h5
    rw [so r h15 h5, o r h15 ha h4 h5]

end M0Crypto.Release.X25519MulcStep
