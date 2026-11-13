import M0Crypto.Release.X25519Block

set_option linter.unusedSimpArgs false

/-!
Macro `word` of `m0c_fe_mulc_add` (`X25519Macros.mulcWord`; plan `x25519-proofs.md`, phase 8):
load `a[i]` through `r1` and `b[i]` through `r2`, and leave `121666 * a[i] + b[i] (+ k)` in
`t` (low word) and `a` (high word), with `r7 = 60833` and `r6 = 0`.

The lemma is generic in the word index and the registers: the hypotheses say only that the
registers are distinct and differ from the fixed `r1, r2, r6, r7`. The macro is the core
(`mulcWord i none`) and, with a carry-in register `k`, a two-instruction tail. The value
comes from `X25519Word.mulcWord_nat`. `mulcWord_acc` gives the two (aligned, read-only)
accesses.
-/

namespace M0Crypto.Release.X25519MulcWord
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem (regs_ldrImm mem_ldrImm c_ldrImm)
open M0Crypto.Release.X25519Mul (regs_lsr regs_lsl regs_muls regs_uxth regs_adcs regs_adds c_adcs
  c_adds lo16 hi16 shl17 hi15 mul_small toReg_inj)
open M0Crypto.Release.X25519Mem (c_muls c_uxth)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.X25519Macros (mulcWord)

/-- The address of word `i` from the pointer in `n`, as `ldr`/`str` with offset `i` give it. -/
def wAddr (s : State) (n : LowReg) (i : Nat) : Word :=
  s.reg n + BitVec.ofNat 32 ((BitVec.ofNat 5 i).toNat * 4)

/-- The registers of one `word`: `a, t, u` and the fixed `r1, r2, r6, r7` are distinct. -/
def Dist (a t u : LowReg) : Prop := [a, t, u, 1, 2, 6, 7].Nodup

/-- The carry-in register, if any, is not one of `a, t, u`. -/
def KOk (a t u : LowReg) : Option LowReg → Prop
  | none => True
  | some k => k ≠ a ∧ k ≠ t ∧ k ≠ u

/-- The carry-in value: `0` without a carry-in register. -/
def kVal (s : State) : Option LowReg → Nat
  | none => 0
  | some k => (s.reg k).toNat

theorem mem_dp (s : State) (op : DpOp) (d m : LowReg) : ((Instr.dp op d m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_lsl (s : State) (d m : LowReg) (k : BitVec 5) : ((Instr.lslImm d m k).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_lsr (s : State) (d m : LowReg) (k : BitVec 5) : ((Instr.lsrImm d m k).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_adds (s : State) (d n m : LowReg) : ((Instr.addReg d n m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_uxth (s : State) (d m : LowReg) : ((Instr.uxth d m).next s).mem = s.mem :=
  next_mem rfl s

theorem mulcWord_some (i : Nat) (k a t u : LowReg) :
    mulcWord i (some k) a t u = mulcWord i none a t u ++ [.addReg t t k, .dp .adcs a 6] := rfl

/-- The pieces of one `word` as natural numbers (`X25519Word.mulcWord_nat`, with `k = 0`). -/
theorem core_nat (A B : Word) (C1 D1 C2 D2 C3 D3 : Word × Bool × Bool)
    (e1 : C1 = addWithCarry (60833#32 * (A.setWidth 16).setWidth 32)
      (60833#32 * (A.setWidth 16).setWidth 32) false)
    (f1 : D1 = addWithCarry ((60833#32 * (A >>> 16)) >>> 15) 0#32 C1.2.1)
    (e2 : C2 = addWithCarry C1.1 ((60833#32 * (A >>> 16)) <<< 17) false)
    (f2 : D2 = addWithCarry D1.1 0#32 C2.2.1)
    (e3 : C3 = addWithCarry C2.1 B false)
    (f3 : D3 = addWithCarry D2.1 0#32 C3.2.1) :
    C3.1.toNat + 2 ^ 32 * D3.1.toNat = 121666 * A.toNat + B.toNat := by
  have haL : ((A.setWidth 16).setWidth 32).toNat = A.toNat % 2 ^ 16 := lo16 A
  have haH : (A >>> 16).toNat = A.toNat / 2 ^ 16 := hi16 A
  have := A.isLt
  have l1 : A.toNat % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have l2 : A.toNat / 2 ^ 16 < 2 ^ 16 := by omega
  have k7 : (60833#32 : Word).toNat = 60833 := rfl
  have hX : (60833#32 * (A.setWidth 16).setWidth 32).toNat = A.toNat % 2 ^ 16 * 60833 := by
    rw [mul_small _ _ (by rw [k7]; omega) (by rw [haL]; exact l1), k7, haL, Nat.mul_comm]
  have hY : (60833#32 * (A >>> 16)).toNat = A.toNat / 2 ^ 16 * 60833 := by
    rw [mul_small _ _ (by rw [k7]; omega) (by rw [haH]; exact l2), k7, haH, Nat.mul_comm]
  have z : (0#32 : Word).toNat = 0 := rfl
  have a1 := adc_nat (60833#32 * (A.setWidth 16).setWidth 32)
    (60833#32 * (A.setWidth 16).setWidth 32) false
  have b1 := adc_nat ((60833#32 * (A >>> 16)) >>> 15) 0#32 C1.2.1
  have a2 := adc_nat C1.1 ((60833#32 * (A >>> 16)) <<< 17) false
  have b2 := adc_nat D1.1 0#32 C2.2.1
  have a3 := adc_nat C2.1 B false
  have b3 := adc_nat D2.1 0#32 C3.2.1
  rw [← e1, hX] at a1
  rw [← f1, hi15, hY, z] at b1
  rw [← e2, shl17, hY] at a2
  rw [← f2, z] at b2
  rw [← e3] at a3
  rw [← f3, z] at b3
  simp only [Bool.toNat_false, Nat.add_zero] at a1 a2 a3 b1 b2 b3
  have key := X25519Word.mulcWord_nat (A.toNat % 2 ^ 16) (A.toNat / 2 ^ 16) B.toNat 0
    C1.1.toNat C1.2.1.toNat D1.1.toNat D1.2.1.toNat C2.1.toNat C2.2.1.toNat D2.1.toNat
    D2.2.1.toNat C3.1.toNat C3.2.1.toNat D3.1.toNat D3.2.1.toNat C3.1.toNat 0 D3.1.toNat 0
    l1 l2 B.isLt (by decide) a1 b1 a2 b2 a3 b3 (by omega) (by omega) C3.1.isLt D3.1.isLt
    C3.1.isLt D3.1.isLt
  rw [show A.toNat % 2 ^ 16 + 2 ^ 16 * (A.toNat / 2 ^ 16) = A.toNat by omega] at key
  omega

theorem core_exec (s : State) (i : Nat) (a t u : LowReg) (hd : Dist a t u)
    (h6 : s.reg 6 = 0#32) (h7 : s.reg 7 = 60833#32) :
    let s' := execAll (mulcWord i none a t u) s
    (s'.reg t).toNat + 2 ^ 32 * (s'.reg a).toNat =
        121666 * (read32 s.mem (wAddr s 1 i)).toNat + (read32 s.mem (wAddr s 2 i)).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ a.toReg → r ≠ t.toReg → r ≠ u.toReg → s'.regs r = s.regs r := by
  simp only [Dist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨dat, dau, da1, da2, da6, da7⟩, ⟨dtu, dt1, dt2, dt6, dt7⟩,
    ⟨du1, du2, du6, du7⟩, -, -, -⟩ := hd
  intro s'
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [mulcWord, Instr.writesMem, MemOp.isLoad])
  refine ⟨?_, hm, ?_⟩
  · simp only [s', mulcWord, List.append_nil, execAll, State.reg]
    simp (config := {decide := true}) only [regs_ldrImm, regs_lsr _ _ _ 16 (by decide), regs_lsr _ _ _ 15 (by decide),
      regs_lsl _ _ _ 17 (by decide), regs_muls, regs_uxth, regs_adcs, regs_adds, c_adcs, c_adds,
      c_muls, c_uxth, c_ldrImm, mem_ldrImm, mem_dp, mem_lsl, mem_lsr, mem_adds, mem_uxth, toReg_ne_15, ne_eq, not_false_eq_true, State.reg, toReg_inj,
      dat, dau, da1, da2, da6, da7, dtu, dt1, dt2, dt6, dt7, du1, du2, du6, du7,
      Ne.symm dat, Ne.symm dau, Ne.symm da1, Ne.symm da2, Ne.symm da6, Ne.symm da7, Ne.symm dtu,
      Ne.symm dt1, Ne.symm dt2, Ne.symm dt6, Ne.symm dt7, Ne.symm du1, Ne.symm du2, Ne.symm du6,
      Ne.symm du7, ite_true, ite_false]
    have h6' : s.regs (LowReg.toReg 6) = 0#32 := h6
    have h7' : s.regs (LowReg.toReg 7) = 60833#32 := h7
    simp only [wAddr, State.reg, h6', h7']
    generalize read32 s.mem (s.regs (LowReg.toReg 1) + BitVec.ofNat 32 ((BitVec.ofNat 5 i).toNat * 4)) = A
    generalize read32 s.mem (s.regs (LowReg.toReg 2) + BitVec.ofNat 32 ((BitVec.ofNat 5 i).toNat * 4)) = B
    exact core_nat A B _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · intro r h15 ha ht hu
    have v : ∀ x : LowReg, r ≠ x.toReg → r.val ≠ x.val := fun x h e => h (Fin.ext e)
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      simp [mulcWord, Instr.dsts, MemOp.isLoad, v a ha, v t ht, v u hu])

/-- The tail `adds t, t, k; adcs a, r6` adds `K` to the 64-bit `hi:lo`. -/
theorem tail_nat (lo hi K lo' c hi' d : Nat) (hV : lo + 2 ^ 32 * hi + K < 2 ^ 64)
    (e : lo' + 2 ^ 32 * c = lo + K) (f : hi' + 2 ^ 32 * d = hi + c)
    (hl : lo' < 2 ^ 32) (hh : hi' < 2 ^ 32) :
    lo' + 2 ^ 32 * hi' = lo + 2 ^ 32 * hi + K := by
  omega

theorem tail_exec (s : State) (a t k : LowReg) (h6 : s.reg 6 = 0#32) (hta : t ≠ a) (ht6 : t ≠ 6)
    (hV : (s.reg t).toNat + 2 ^ 32 * (s.reg a).toNat + (s.reg k).toNat < 2 ^ 64) :
    let s' := execAll [.addReg t t k, .dp .adcs a 6] s
    (s'.reg t).toNat + 2 ^ 32 * (s'.reg a).toNat =
        (s.reg t).toNat + 2 ^ 32 * (s.reg a).toNat + (s.reg k).toNat ∧
      s'.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → r ≠ a.toReg → r ≠ t.toReg → s'.regs r = s.regs r := by
  intro s'
  refine ⟨?_, rfl, ?_⟩
  · have h6' : s.regs (LowReg.toReg 6) = 0#32 := h6
    simp only [s', execAll, State.reg]
    simp only [regs_adcs, regs_adds, c_adds, toReg_ne_15, ne_eq, not_false_eq_true, State.reg,
      toReg_inj, hta, Ne.symm hta, ht6, Ne.symm ht6,
      ite_true, ite_false, h6']
    simp only [State.reg] at hV
    have e := adc_nat (s.regs t.toReg) (s.regs k.toReg) false
    have f := adc_nat (s.regs a.toReg) 0#32 (addWithCarry (s.regs t.toReg) (s.regs k.toReg) false).2.1
    simp only [Bool.toNat_false, Nat.add_zero, show (0#32 : Word).toNat = 0 from rfl] at e f
    exact tail_nat _ _ _ _ _ _ _ hV e f (BitVec.isLt _) (BitVec.isLt _)
  · intro r h15 ha ht
    have v : ∀ x : LowReg, r ≠ x.toReg → r.val ≠ x.val := fun x h e => h (Fin.ext e)
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      simp [Instr.dsts, v a ha, v t ht])

/-- Macro `word`: `t` (low) and `a` (high) hold `121666 * a[i] + b[i] + k`, read through
`r1` and `r2`; memory and every register outside `a, t, u` are unchanged. -/
theorem mulcWord_exec (s : State) (i : Nat) (k : Option LowReg) (a t u : LowReg) (hd : Dist a t u)
    (hk : KOk a t u k) (h6 : s.reg 6 = 0#32) (h7 : s.reg 7 = 60833#32) :
    let s' := execAll (mulcWord i k a t u) s
    (s'.reg t).toNat + 2 ^ 32 * (s'.reg a).toNat =
        121666 * (read32 s.mem (wAddr s 1 i)).toNat + (read32 s.mem (wAddr s 2 i)).toNat +
          kVal s k ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ a.toReg → r ≠ t.toReg → r ≠ u.toReg → s'.regs r = s.regs r := by
  obtain ⟨v, m, o⟩ := core_exec s i a t u hd h6 h7
  cases k with
  | none => exact ⟨v, m, o⟩
  | some k =>
    obtain ⟨hka, hkt, hku⟩ := hk
    have hd' := hd
    simp only [Dist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd'
    obtain ⟨⟨dat, -, -, -, da6, -⟩, ⟨-, -, -, dt6, -⟩, ⟨-, -, du6, -⟩, -⟩ := hd'
    intro s'
    simp only [s', mulcWord_some, execAll_append]
    generalize hs1 : execAll (mulcWord i none a t u) s = s1 at v m o
    have hr : ∀ x : LowReg, x ≠ a → x ≠ t → x ≠ u → s1.reg x = s.reg x := fun x h1 h2 h3 =>
      o x.toReg (toReg_ne_15 x) (by rw [ne_eq, toReg_inj]; exact h1)
        (by rw [ne_eq, toReg_inj]; exact h2) (by rw [ne_eq, toReg_inj]; exact h3)
    have hk1 : s1.reg k = s.reg k := hr k hka hkt hku
    have h61 : s1.reg 6 = 0#32 := by
      rw [hr 6 (Ne.symm da6) (Ne.symm dt6) (Ne.symm du6), h6]
    have hA := (read32 s.mem (wAddr s 1 i)).isLt
    have hB := (read32 s.mem (wAddr s 2 i)).isLt
    have hK := (s.reg k).isLt
    obtain ⟨v2, m2, o2⟩ := tail_exec s1 a t k h61 (Ne.symm dat) dt6
      (by rw [v, hk1]; omega)
    refine ⟨by rw [v2, v, hk1]; rfl, by rw [m2, m], fun r h15 ha ht hu => ?_⟩
    rw [o2 r h15 ha ht, o r h15 ha ht hu]

/-! ## Accesses and the `ReachW` block lemma -/

/-- The register-only instructions between the two loads. -/
def mid (a t u : LowReg) : List Instr :=
  [.uxth t a, .lsrImm a a 16, .dp .muls t 7, .dp .muls a 7, .lslImm u a 17, .lsrImm a a 15,
   .addReg t t t, .dp .adcs a 6, .addReg t t u, .dp .adcs a 6]

/-- The register-only instructions after the second load. -/
def rest (k : Option LowReg) (a t u : LowReg) : List Instr :=
  [.addReg t t u, .dp .adcs a 6] ++ (match k with | some k => [.addReg t t k, .dp .adcs a 6] | none => [])

theorem mulcWord_split (i : Nat) (k : Option LowReg) (a t u : LowReg) :
    mulcWord i k a t u = [.memImm .ldr a 1 (BitVec.ofNat 5 i)] ++ mid a t u ++
      [.memImm .ldr u 2 (BitVec.ofNat 5 i)] ++ rest k a t u := by
  cases k <;> rfl

open M0Crypto.Release.X25519Mul (regOnly accesses_regOnly) in
theorem accAll_regOnly {P : Access → Prop} (is : List Instr) (s : State)
    (h : is.all regOnly = true) : AccAll P is s :=
  accAll_none is s fun i hi t => accesses_regOnly i t (List.all_eq_true.mp h i hi)

/-- A word load through `n` whose pointer is aligned. -/
theorem ldr_acc {Wr : Word → Prop} (s : State) (d n : LowReg) (i : BitVec 5)
    (h : (s.reg n).toNat % 4 = 0) : AccAll (AccOk Wr) [.memImm .ldr d n i] s := by
  refine accAll_cons (fun x hx => ?_) (accAll_nil _ _)
  simp only [Instr.accesses, MemOp.isLoad, MemOp.width, ite_true, List.mem_singleton] at hx
  subst hx
  exact ⟨aligned_word (word_add_aligned h (by omega)), fun e => by cases e⟩

theorem mulcWord_acc {Wr : Word → Prop} (s : State) (i : Nat) (k : Option LowReg) (a t u : LowReg)
    (hd : Dist a t u) (h1 : (s.reg 1).toNat % 4 = 0) (h2 : (s.reg 2).toNat % 4 = 0) :
    AccAll (AccOk Wr) (mulcWord i k a t u) s := by
  simp only [Dist, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨-, -, -, da2, -, -⟩, ⟨-, -, dt2, -, -⟩, ⟨-, du2, -, -⟩, -⟩ := hd
  rw [mulcWord_split]
  refine accAll_append (accAll_append (accAll_append (ldr_acc s a 1 _ h1)
    (accAll_regOnly _ _ (by simp [mid, X25519Mul.regOnly]))) (ldr_acc _ u 2 _ ?_))
    (accAll_regOnly _ _ (by cases k <;> simp [rest, X25519Mul.regOnly]))
  have v : ∀ x : LowReg, x ≠ 2 → (2 : Nat) ≠ x.val := fun x h e => h (Fin.ext e.symm)
  have e : (execAll ([.memImm .ldr a 1 (BitVec.ofNat 5 i)] ++ mid a t u) s).reg 2 = s.reg 2 :=
    execAll_regs_other _ _ _ (by decide) (by
      simp [mid, Instr.dsts, MemOp.isLoad, LowReg.toReg, v a da2, v t dt2, v u du2])
  rw [e]; exact h2

theorem mulcWord_falls (i : Nat) (k : Option LowReg) (a t u : LowReg) :
    (mulcWord i k a t u).all Instr.falls = true := by
  cases k <;> simp [mulcWord, Instr.falls]

/-- One `word` in a `ReachW` proof. -/
theorem mulcWord_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {x : State}
    {off i : Nat} {k : Option LowReg} {a t u : LowReg} (hd : Dist a t u) (hk : KOk a t u k)
    (hseq : seqAt B off (mulcWord i k a t u) = true) (ho : off % 2 = 0)
    (hpc : x.pc = base + BitVec.ofNat 32 off)
    (hr : InRegion Pc base off (seqSize (mulcWord i k a t u)))
    (h1 : (x.reg 1).toNat % 4 = 0) (h2 : (x.reg 2).toNat % 4 = 0)
    (h6 : x.reg 6 = 0#32) (h7 : x.reg 7 = 60833#32) {Q : State → Prop}
    (cont : ∀ y : State, y.pc = base + BitVec.ofNat 32 (off + seqSize (mulcWord i k a t u)) →
      (y.reg t).toNat + 2 ^ 32 * (y.reg a).toNat =
        121666 * (read32 x.mem (wAddr x 1 i)).toNat + (read32 x.mem (wAddr x 2 i)).toNat +
          kVal x k →
      y.mem = x.mem →
      (∀ r : Reg, r ≠ 15 → r ≠ a.toReg → r ≠ t.toReg → r ≠ u.toReg → y.regs r = x.regs r) →
      ReachW base Pc Wr y Q) :
    ReachW base Pc Wr x Q := by
  have hf := mulcWord_falls i k a t u
  refine ReachW.blockAcc hb _ off hpc ho hseq hf (mulcWord_acc x i k a t u hd h1 h2) hr ?_
  obtain ⟨v, m, o⟩ := mulcWord_exec x i k a t u hd hk h6 h7
  exact cont _ (by rw [execAll_pc _ _ hf, hpc, ofNat_add_assoc]) v m o

end M0Crypto.Release.X25519MulcWord
