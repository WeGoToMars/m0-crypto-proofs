import M0Crypto.Release.X25519Block
import M0Crypto.Release.X25519W4

set_option linter.unusedSimpArgs false

/-!
Macro `diff256` of `m0c_fe_mul` and `m0c_fe_sqr` (plan `x25519-proofs.md`, phase 8): load the
pointer in a frame slot, load the 8 words `X` it points to, and store `|X0 - X1|` (4 words) at
another frame slot; the mask of `X0 < X1` is left in `r0`. `X0` is words 0-3, `X1` words 4-7.

The macro is a load (`dload`), the register-only core (`dcore`: subtract, mask, complement,
correct) and a store (`dstore`). The core's value is `X25519Kara.absdiff` on 128 bits through
the four-word chains of `X25519W4`. `diff256_exec` composes the three; `diff256_acc` checks
the accesses (aligned, writes in the target slots); `diff256_run_w` is the `ReachW` block
lemma.
-/

namespace M0Crypto.Release.X25519Diff
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Macros (diff256 sl)
open M0Crypto.Release.X25519Mul (regs_sbcs regs_subs c_sbcs c_subs)
open M0Crypto.Release.Blake2s (toReg_ne15 regs_eors)

/-- Load the pointer in slot `p` and the 8 words: `X0` in `r4`-`r7`, `X1` in `r0`-`r3`. -/
def dload (p : Nat) : List Instr := [.ldrSp 0 (sl p), .ldm 0 0xf0, .ldm 0 0x0f]

/-- Store `r4`-`r7` at slot `o`. -/
def dstore (o : Nat) : List Instr := [.addRdSp 1 (sl o), .stm 1 0xf0]

/-- The register-only core: subtract, mask, complement and correct. -/
def dcore : List Instr :=
  [.subReg 4 4 0, .dp .sbcs 5 1, .dp .sbcs 6 2, .dp .sbcs 7 3, .dp .sbcs 0 0,
   .dp .eors 4 0, .dp .eors 5 0, .dp .eors 6 0, .dp .eors 7 0,
   .subReg 4 4 0, .dp .sbcs 5 0, .dp .sbcs 6 0, .dp .sbcs 7 0]

theorem dcore_exec (s : State) :
    let t := execAll dcore s
    let x := w4 (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7)
    let y := w4 (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3)
    t.regs 0 = mask (decide (x < y)) ∧
      (x : Int) - y = (if x < y then -(w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7) : Int)
        else w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7)) ∧
      t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 0 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → t.regs r = s.regs r := by
  intro t x y
  have hm : t.mem = s.mem := execAll_mem _ _ (by decide)
  have ho : ∀ r : Reg, r ≠ 15 → r ≠ 0 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → t.regs r = s.regs r := by
    intro r h15 h0 h4 h5 h6 h7
    simp only [ne_eq, Fin.ext_iff] at h15 h0 h4 h5 h6 h7
    exact execAll_regs_other _ _ _ h15 (by simp [dcore, Instr.dsts, LowReg.toReg]; omega)
  suffices H : t.regs 0 = mask (decide (x < y)) ∧
      (x : Int) - y = (if x < y then -(w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7) : Int)
        else w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7)) from ⟨H.1, H.2, hm, ho⟩
  simp only [t, dcore, execAll]
  simp (config := {decide := true}) only [regs_sbcs, regs_subs, regs_eors, c_sbcs, c_subs, c_eors,
    State.reg, ne_eq, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true,
    ite_false, sbcs_self]
  generalize h0 : addWithCarry (s.regs 4) (~~~s.regs 0) true = A0
  generalize h1 : addWithCarry (s.regs 5) (~~~s.regs 1) A0.2.1 = A1
  generalize h2 : addWithCarry (s.regs 6) (~~~s.regs 2) A1.2.1 = A2
  generalize h3 : addWithCarry (s.regs 7) (~~~s.regs 3) A2.2.1 = A3
  have hs := sub4 h0 h1 h2 h3
  generalize hn : (!A3.2.1) = neg
  have hx := xor4 A0.1 A1.1 A2.1 A3.1 neg
  generalize g0 : addWithCarry (A0.1 ^^^ mask neg) (~~~mask neg) true = R0
  generalize g1 : addWithCarry (A1.1 ^^^ mask neg) (~~~mask neg) R0.2.1 = R1
  generalize g2 : addWithCarry (A2.1 ^^^ mask neg) (~~~mask neg) R1.2.1 = R2
  generalize g3 : addWithCarry (A3.1 ^^^ mask neg) (~~~mask neg) R2.2.1 = R3
  have hr := sub4 g0 g1 g2 g3
  have hb : 1 - A3.2.1.toNat = if neg then 1 else 0 := by rw [← hn]; cases A3.2.1 <;> rfl
  simp only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] at hs hr
  rw [hb] at hs
  rw [w4_mask] at hr
  have hlt : neg = decide (x < y) := by
    have := w4_lt A0.1 A1.1 A2.1 A3.1
    simp only [x, y]
    cases neg <;> simp at hs ⊢ <;> omega
  refine ⟨by rw [hlt], ?_⟩
  have key := M0Crypto.Release.X25519Kara.absdiff (2 ^ 128) x y (w4 A0.1 A1.1 A2.1 A3.1)
    (if neg then 1 else 0)
    (w4 (A0.1 ^^^ mask neg) (A1.1 ^^^ mask neg) (A2.1 ^^^ mask neg) (A3.1 ^^^ mask neg)) (w4 R0.1 R1.1 R2.1 R3.1) (1 - R3.2.1.toNat) (w4_lt _ _ _ _)
    (w4_lt _ _ _ _) (w4_lt _ _ _ _) (by split <;> omega) (by omega) hs
    (by rw [hx]; cases neg <;> rfl) (by cases neg <;> simp at hr ⊢ <;> omega)
  rw [key, hlt]
  by_cases h : x < y <;> simp [h]

theorem diff256_split (p o : Nat) : diff256 p o = dload p ++ dcore ++ dstore o := rfl

theorem listRegs_f0 : listRegs 0xf0 = [4, 5, 6, 7] := by decide
theorem listRegs_0f : listRegs 0x0f = [0, 1, 2, 3] := by decide
theorem bitCount_f0 : bitCount 0xf0 = 4 := by decide

theorem dload_exec (s : State) (p : Nat) :
    let t := execAll (dload p) s
    let A := read32 s.mem (s.sp + BitVec.ofNat 32 (p % 256 * 4))
    let X := fun i : Nat => read32 s.mem (A + BitVec.ofNat 32 (4 * i))
    t.regs 4 = X 0 ∧ t.regs 5 = X 1 ∧ t.regs 6 = X 2 ∧ t.regs 7 = X 3 ∧
      t.regs 0 = X 4 ∧ t.regs 1 = X 5 ∧ t.regs 2 = X 6 ∧ t.regs 3 = X 7 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t A X
  have hm : t.mem = s.mem := execAll_mem _ _ (by simp [dload, Instr.writesMem])
  have hsl : (sl p).toNat = p % 256 := by simp [sl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm, ?_⟩
  rotate_left 8
  · intro r h15 h8
    have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
    simp (config := {decide := true}) only [t, dload, execAll, regs_ldm, regs_ldrSp, listRegs_f0,
      listRegs_0f, bitCount_f0, State.reg, List.map, toReg0, toReg1, toReg2, toReg3, toReg4,
      toReg5, toReg6, toReg7, ne_eq, List.mem_cons, List.not_mem_nil, n 0 (by decide),
      n 1 (by decide), n 2 (by decide), n 3 (by decide), n 4 (by decide), n 5 (by decide),
      n 6 (by decide), n 7 (by decide), h15, or_self, ite_false, not_false_eq_true]
  all_goals
    simp (config := {decide := true}) only [t, dload, execAll, regs_ldm, regs_ldrSp, listRegs_f0,
      listRegs_0f, bitCount_f0, State.reg, mem_ldm, mem_ldrSp, List.map, toReg0, toReg1, toReg2,
      toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false, ne_eq, List.mem_cons,
      List.idxOf, hsl]
    try rw [ofNat_add_assoc]
    rfl

theorem dstore_exec (s : State) (o : Nat) :
    let t := execAll (dstore o) s
    t.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 (o % 256 * 4))
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7] ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → t.regs r = s.regs r := by
  intro t
  have hsl : (sl o).toNat = o % 256 := by simp [sl]
  constructor
  · simp (config := {decide := true}) only [t, dstore, execAll, mem_stm, mem_addRdSp, regs_addRdSp,
      listRegs_f0, List.map, State.reg, toReg1, toReg4, toReg5, toReg6, toReg7, ite_true,
      ite_false, hsl, State.sp]
  · intro r h15 h1
    simp only [t, dstore, execAll, regs_stm _ _ _ _ h15, regs_addRdSp _ _ _ _ h15, toReg1, h1, ite_false]

theorem diff256_exec (s : State) (p o : Nat) (ho : o < 256) :
    let A := read32 s.mem (s.sp + BitVec.ofNat 32 (p % 256 * 4))
    let X := fun i : Nat => read32 s.mem (A + BitVec.ofNat 32 (4 * i))
    let x := w4 (X 0) (X 1) (X 2) (X 3)
    let y := w4 (X 4) (X 5) (X 6) (X 7)
    let t := execAll (diff256 p o) s
    t.regs 0 = mask (decide (x < y)) ∧
      (x : Int) - y = (if x < y then -(w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7) : Int)
        else w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7)) ∧
      t.mem = storeWords s.mem (slot s.sp o) [t.regs 4, t.regs 5, t.regs 6, t.regs 7] ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro A X x y t
  have L := dload_exec s p
  have C := dcore_exec (execAll (dload p) s)
  have D := dstore_exec (execAll dcore (execAll (dload p) s)) o
  simp only [t, diff256_split, execAll_append]
  generalize execAll (dload p) s = s1 at L C D
  generalize execAll dcore s1 = s2 at C D
  generalize execAll (dstore o) s2 = s3 at D
  obtain ⟨l4, l5, l6, l7, l0, l1, l2, l3, lm, lo⟩ := L
  obtain ⟨c0, cv, cm, co⟩ := C
  obtain ⟨dm, dr⟩ := D
  have n : ∀ k : Reg, k.val < 8 → ∀ r : Reg, 8 ≤ r.val → r ≠ k := fun k hk r h e => by
    subst e; omega
  have d4 : s3.regs 4 = s2.regs 4 := dr 4 (by decide) (by decide)
  have d5 : s3.regs 5 = s2.regs 5 := dr 5 (by decide) (by decide)
  have d6 : s3.regs 6 = s2.regs 6 := dr 6 (by decide) (by decide)
  have d7 : s3.regs 7 = s2.regs 7 := dr 7 (by decide) (by decide)
  have d0 : s3.regs 0 = s2.regs 0 := dr 0 (by decide) (by decide)
  have hsp : s2.sp = s.sp := by
    simp only [State.sp]
    rw [co 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      lo 13 (by decide) (by decide)]
  rw [l4, l5, l6, l7, l0, l1, l2, l3] at c0 cv
  refine ⟨by rw [d0, c0], by rw [d4, d5, d6, d7]; exact cv, ?_, ?_⟩
  · rw [dm, cm, lm, hsp, d4, d5, d6, d7, Nat.mod_eq_of_lt ho]
    simp only [slot, Nat.mul_comm 4 o]
  · intro r h15 h8
    rw [dr r h15 (n 1 (by decide) r h8),
      co r h15 (n 0 (by decide) r h8) (n 4 (by decide) r h8) (n 5 (by decide) r h8)
        (n 6 (by decide) r h8) (n 7 (by decide) r h8), lo r h15 h8]

theorem diff256_falls (p o : Nat) : (diff256 p o).all Instr.falls = true := by
  simp [diff256, Instr.falls]

theorem diff256_size (p o : Nat) : seqSize (diff256 p o) = 36 := by
  simp [diff256, seqSize, Instr.size]

/-- The accesses: the pointer slot, the 8 words, and the 4 target words. -/
theorem diff256_acc {Wr : Word → Prop} (s : State) (p o : Nat) (hsp : s.sp.toNat % 4 = 0)
    (hA : (read32 s.mem (s.sp + BitVec.ofNat 32 (p % 256 * 4))).toNat % 4 = 0)
    (hW : ∀ j < 16, Wr (s.sp + BitVec.ofNat 32 (o % 256 * 4 + j))) :
    AccAll (AccOk Wr) (diff256 p o) s := by
  have hsl : ∀ k, (sl k).toNat = k % 256 := fun k => by simp [sl]
  rw [diff256_split]
  refine accAll_append (accAll_append ?_ ?_) ?_
  · refine accAll_cons ?_ (accAll_cons ?_ (accAll_cons ?_ (accAll_nil _ _)))
    · intro a ha
      simp only [Instr.accesses, hsl, List.mem_singleton] at ha
      subst ha
      exact ⟨aligned_word (word_add_aligned hsp (by omega)), fun h => by cases h⟩
    · intro a ha
      simp only [Instr.accesses] at ha
      refine wordAccesses_ok ?_ (fun h => by cases h) a ha
      simp only [State.reg, toReg0, regs_ldrSp _ _ _ _ (by decide : (0 : Reg) ≠ 15), ite_true, hsl]
      exact hA
    · intro a ha
      simp only [Instr.accesses] at ha
      refine wordAccesses_ok ?_ (fun h => by cases h) a ha
      simp (config := {decide := true}) only [State.reg, toReg0, regs_ldm, regs_ldrSp, listRegs_f0,
        bitCount_f0, List.map, toReg4, toReg5, toReg6, toReg7, List.mem_cons, ite_true, ite_false,
        hsl]
      exact word_add_aligned hA (by omega)
  · exact accAll_none _ _ (fun i hi t => by
      simp only [dcore, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl)
  · refine accAll_cons (fun a ha => by simp [Instr.accesses] at ha) (accAll_cons ?_ (accAll_nil _ _))
    intro a ha
    simp only [Instr.accesses] at ha
    have hsp' : (execAll (dload p ++ dcore) s).regs 13 = s.regs 13 := by
      obtain ⟨-, -, -, -, -, -, -, -, -, lo⟩ := dload_exec s p
      obtain ⟨-, -, -, co⟩ := dcore_exec (execAll (dload p) s)
      rw [execAll_append, co 13 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), lo 13 (by decide) (by decide)]
    have e : ((Instr.addRdSp 1 (sl o)).next (execAll (dload p ++ dcore) s)).reg 1 =
        s.sp + BitVec.ofNat 32 (o % 256 * 4) := by
      simp only [State.reg, toReg1, regs_addRdSp _ _ _ _ (by decide : (1 : Reg) ≠ 15), ite_true,
        hsl, State.sp, hsp']
    rw [e, bitCount_f0] at ha
    refine wordAccesses_ok (word_add_aligned hsp (by omega)) (fun _ i hi q hq => ?_) a ha
    rw [ofNat_add_assoc, ofNat_add_assoc]
    exact hW _ (by omega)

/-- The effect of `diff256 p o` from `s` to `t`: the words `X` at the pointer in slot `p`,
`r0` the mask of `X0 < X1`, `|X0 - X1|` stored at slot `o` (and left in `r4`-`r7`), registers
from `r8` up unchanged. -/
def DiffPost (s : State) (p o : Nat) (t : State) : Prop :=
  let A := read32 s.mem (s.sp + BitVec.ofNat 32 (p % 256 * 4))
  let X := fun i : Nat => read32 s.mem (A + BitVec.ofNat 32 (4 * i))
  let x := w4 (X 0) (X 1) (X 2) (X 3)
  let y := w4 (X 4) (X 5) (X 6) (X 7)
  t.regs 0 = mask (decide (x < y)) ∧
    (x : Int) - y = (if x < y then -(w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7) : Int)
      else w4 (t.regs 4) (t.regs 5) (t.regs 6) (t.regs 7)) ∧
    t.mem = storeWords s.mem (slot s.sp o) [t.regs 4, t.regs 5, t.regs 6, t.regs 7] ∧
    ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r

/-- One `diff256` block in a `ReachW` proof. -/
theorem diff256_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {t : State}
    {off p o : Nat} (ho : o < 256) (hseq : seqAt B off (diff256 p o) = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off 36)
    (hsp : t.sp.toNat % 4 = 0)
    (hA : (read32 t.mem (t.sp + BitVec.ofNat 32 (p % 256 * 4))).toNat % 4 = 0)
    (hW : ∀ j < 16, Wr (t.sp + BitVec.ofNat 32 (o * 4 + j))) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + 36) → DiffPost t p o t' →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  have hf := diff256_falls p o
  refine ReachW.blockAcc hb _ off hpc hoff hseq hf
    (diff256_acc t p o hsp hA (by rw [Nat.mod_eq_of_lt ho]; exact hW))
    (by rw [diff256_size]; exact hr) (k _ ?_ (diff256_exec t p o ho))
  rw [execAll_pc _ _ hf, diff256_size, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Diff
