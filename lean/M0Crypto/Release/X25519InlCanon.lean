import M0Crypto.Release.X25519InlChain
import M0Crypto.Release.X25519Reduce

set_option linter.unusedSimpArgs false

/-!
`canon_body` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: reduce the value at
`r0` to `0 ≤ r < p` in place.

* `canonHead`: `r2 = 0`, `r3 = 19`, `r4 = 19 * bit 255`, bit 255 cleared in memory.
* `canonAdd c st`: add `r_c` to the eight words at `r0` (`adds`, then seven `adcs` with
  `r2 = 0`), storing each word if `st`. Built from one macro, `canonWord st i`; the generic
  lemma `canonWord_step` carries the chain invariant `CInv` from word `j` to `j + 1`.
* Passes: add `19 * bit` (stored); add `19` (not stored, only the top bit is used,
  `canonMid`); add `19 * that bit` (stored); `canonTail` clears bit 255.

The arithmetic is `X25519Reduce.canon_nat`. Accesses: `cSafe` is a syntactic check of every
instruction (no write to `r0`; memory only through `r0` at word offsets below 8),
`cSafe_ok` its meaning.
-/

namespace M0Crypto.Release.X25519Inl
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (B Region ReachW InRegion)
open M0Crypto.Release.X25519Frame (FrameOk upd)
open M0Crypto.Release.X25519MulcChain (psum psum_congr)
open M0Crypto.Release.X25519Block (AccAll AccOk accAll_cons accAll_nil accAll_append)
open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg2 toReg3 toReg4)
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Release.X25519Congr

/-! ## Instruction lists -/

/-- Word `i ≥ 1` of a pass: `ldr r1, [r0, #4i]; adcs r1, r2` and, if `st`, the store. -/
def canonWord (st : Bool) (i : Nat) : List Instr :=
  [.memImm .ldr 1 0 (BitVec.ofNat 5 i), .dp .adcs 1 2] ++
    (if st then [.memImm .str 1 0 (BitVec.ofNat 5 i)] else [])

/-- Word 0 of a pass: `ldr r1, [r0]; adds r1, r1, r_c` and, if `st`, the store. -/
def canonFirst (c : LowReg) (st : Bool) : List Instr :=
  [.memImm .ldr 1 0 0, .addReg 1 1 c] ++ (if st then [.memImm .str 1 0 0] else [])

/-- Words `1..n` of a pass. -/
def canonWords (st : Bool) : Nat → List Instr
  | 0 => []
  | n + 1 => canonWords st n ++ canonWord st (n + 1)

def canonAdd (c : LowReg) (st : Bool) : List Instr := canonFirst c st ++ canonWords st 7

def canonHead : List Instr :=
  [.movImm 2 0, .movImm 3 19, .memImm .ldr 1 0 7, .lsrImm 4 1 31, .lslImm 1 1 1, .lsrImm 1 1 1,
    .memImm .str 1 0 7, .dp .muls 4 3]

def canonMid : List Instr := [.lsrImm 4 1 31, .dp .muls 4 3]

def canonTail : List Instr := [.lslImm 1 1 1, .lsrImm 1 1 1, .memImm .str 1 0 7]

def canonBody : List Instr :=
  canonHead ++ canonAdd 4 true ++ canonAdd 3 false ++ canonMid ++ canonAdd 4 true ++ canonTail

theorem canonBody_at : SiteOk canonBody := by
  constructor
  · decide +kernel
  · rw [seqAt_eq_scan]; decide +kernel

theorem canonBody_falls : canonBody.all Instr.falls = true := by decide +kernel

/-! ## Single words -/

theorem addr_slot (p : Word) {j : Nat} (hj : j < 32) :
    p + BitVec.ofNat 32 ((BitVec.ofNat 5 j).toNat * 4) = slot p j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), slot, Nat.mul_comm]

theorem c_strImm (s : State) (t n : LowReg) (i : BitVec 5) :
    ((Instr.memImm .str t n i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem regs1_ne (r : Reg) (h : r ≠ 1) : r ≠ LowReg.toReg 1 := by rw [toReg1]; exact h

/-- One word: load word `j`, add `r2` with carry, store it back if `st`. -/
theorem canonWord_exec (s : State) (st : Bool) {j : Nat} (hj : j < 32) :
    let t := execAll (canonWord st j) s
    let v := (addWithCarry (read32 s.mem (slot (s.regs 0) j)) (s.regs 2) s.c)
    t.regs 1 = v.1 ∧ t.c = v.2.1 ∧
      t.mem = (if st then write32 s.mem (slot (s.regs 0) j) v.1 else s.mem) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → t.regs r = s.regs r := by
  intro t v
  have h1 := regs1_ne
  cases st
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp (config := {decide := true}) only [t, v, canonWord, Bool.false_eq_true,
      ite_true, ite_false, List.append_nil, List.cons_append, List.nil_append, execAll,
      X25519Mem.regs_ldrImm, X25519Mem.mem_ldrImm, X25519Mem.c_ldrImm, X25519Mem.regs_strImm,
      X25519Mem.mem_strImm, c_strImm, X25519Mul.regs_adcs, X25519Mul.c_adcs, X25519MulcWord.mem_dp,
      State.reg, toReg0, toReg1, toReg2, addr_slot _ hj]
  all_goals
    try (intro r h15 hr
         simp (config := {decide := true}) only [X25519Mem.regs_strImm _ _ _ _ _ h15,
           X25519Mul.regs_adcs _ _ _ _ h15, X25519Mem.regs_ldrImm _ _ _ _ _ h15, toReg1,
           hr, ite_false])

/-- Word 0 of a pass. -/
theorem canonFirst_exec (s : State) (c : LowReg) (hc : c ≠ 1) (st : Bool) :
    let t := execAll (canonFirst c st) s
    let v := addWithCarry (read32 s.mem (slot (s.regs 0) 0)) (s.reg c) false
    t.regs 1 = v.1 ∧ t.c = v.2.1 ∧
      t.mem = (if st then write32 s.mem (slot (s.regs 0) 0) v.1 else s.mem) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → t.regs r = s.regs r := by
  intro t v
  have hc' : c.toReg ≠ LowReg.toReg 1 := by rw [ne_eq, X25519Mul.toReg_inj]; exact hc
  have hc1 : c.toReg ≠ (1 : Reg) := by rw [← toReg1]; exact hc'
  have a0 : s.regs 0 + BitVec.ofNat 32 ((0 : BitVec 5).toNat * 4) = slot (s.regs 0) 0 := by
    simp [slot]
  cases st
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp (config := {decide := true}) only [t, v, canonFirst, Bool.false_eq_true,
      ite_true, ite_false, List.append_nil, List.cons_append, List.nil_append, execAll,
      X25519Mem.regs_ldrImm, X25519Mem.mem_ldrImm, X25519Mem.c_ldrImm, X25519Mem.regs_strImm,
      X25519Mem.mem_strImm, c_strImm, X25519Mul.regs_adds, X25519Mul.c_adds,
      X25519MulcWord.mem_adds, State.reg, toReg0, toReg1, Ne.symm hc', hc', hc1, a0,
      Blake2s.toReg_ne15, ne_eq, not_false_eq_true]
  all_goals
    try (intro r h15 hr
         simp (config := {decide := true}) only [X25519Mem.regs_strImm _ _ _ _ _ h15,
           X25519Mul.regs_adds _ _ _ _ _ h15, X25519Mem.regs_ldrImm _ _ _ _ _ h15, toReg1,
           hr, ite_false])

/-! ## The chain of a pass -/

/-- After words `0..j-1` of a pass started in `s0` with carry-in `cin`: the stored words are
`W` (if `st`), `r1` holds the last one, and `W` plus the carry is the input plus `cin`. -/
structure CInv (s0 : State) (st : Bool) (cin : Nat) (j : Nat) (t : State) : Prop where
  keep : ∀ r : Reg, r ≠ 15 → r ≠ 1 → t.regs r = s0.regs r
  val : ∃ W F : Nat → Word, FrameOk (s0.regs 0) 8 s0.mem F t.mem ∧
    (∀ i < 8, F i = if st ∧ i < j then W i else read32 s0.mem (slot (s0.regs 0) i)) ∧
    t.regs 1 = W (j - 1) ∧
    psum (fun i => (W i).toNat) j + 2 ^ (32 * j) * t.c.toNat =
      psum (fun i => (read32 s0.mem (slot (s0.regs 0) i)).toNat) j + cin

theorem chain_nat (S P c Sx x cin r c' : Nat) (h : S + P * c = Sx + cin)
    (e : r + 2 ^ 32 * c' = x + 0 + c) : S + P * r + P * 2 ^ 32 * c' = Sx + P * x + cin := by
  have e' := congrArg (P * ·) e
  simp only [Nat.mul_add, Nat.add_zero] at e'
  rw [Nat.mul_assoc]; omega

theorem canonFirst_inv (s0 : State) (c : LowReg) (hc : c ≠ 1) (st : Bool)
    (hf : (s0.regs 0).toNat + 32 ≤ 2 ^ 32) :
    CInv s0 st (s0.reg c).toNat 1 (execAll (canonFirst c st) s0) := by
  obtain ⟨t1, tc, tm, to⟩ := canonFirst_exec s0 c hc st
  generalize hv : addWithCarry (read32 s0.mem (slot (s0.regs 0) 0)) (s0.reg c) false = v at t1 tc tm
  refine ⟨to, fun _ => v.1,
    if st then upd (fun i => read32 s0.mem (slot (s0.regs 0) i)) 0 [v.1]
      else fun i => read32 s0.mem (slot (s0.regs 0) i), ?_, ?_, t1, ?_⟩
  · cases st
    · simp only [Bool.false_eq_true, ite_false] at tm ⊢
      rw [tm]; exact frame_init s0.mem hf
    · simp only [ite_true] at tm ⊢
      rw [tm]; exact (frame_init s0.mem hf).write (k := 0) (by omega) _
  · intro i hi
    cases st
    · simp
    · simp only [upd, List.length_singleton, ite_true, true_and]
      by_cases h : i < 1
      · simp [h, show i = 0 by omega]
      · simp [h]
  · rw [tc]
    have e := adc_nat (read32 s0.mem (slot (s0.regs 0) 0)) (s0.reg c) false
    rw [hv] at e
    simp only [psum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_one,
      Bool.toNat_false, Nat.add_zero] at e ⊢
    omega

/-- The generic step: word `j` keeps the chain invariant. -/
theorem canonWord_step {s0 : State} {st : Bool} {cin j : Nat} (hj : 1 ≤ j) (hj8 : j < 8)
    (h2 : s0.regs 2 = 0#32) {t : State} (h : CInv s0 st cin j t) :
    CInv s0 st cin (j + 1) (execAll (canonWord st j) t) := by
  obtain ⟨keep, W, F, hF, hFW, h1, hv⟩ := h
  obtain ⟨u1, uc, um, uo⟩ := canonWord_exec t st (j := j) (by omega)
  have e0 : t.regs 0 = s0.regs 0 := keep 0 (by decide) (by decide)
  have e2 : t.regs 2 = 0#32 := by rw [keep 2 (by decide) (by decide), h2]
  have rx : read32 t.mem (slot (t.regs 0) j) = read32 s0.mem (slot (s0.regs 0) j) := by
    rw [e0, hF.slots j hj8, hFW j hj8]; simp only [Nat.lt_irrefl, and_false, ↓reduceIte]
  rw [rx, e2] at u1 uc um
  generalize hv' : addWithCarry (read32 s0.mem (slot (s0.regs 0) j)) 0#32 t.c = v at u1 uc um
  let W' := fun i => if i = j then v.1 else W i
  refine ⟨fun r h15 h1 => by rw [uo r h15 h1, keep r h15 h1], W', ?_, ?_, ?_, ?_, ?_⟩
  · exact if st then (upd F j [v.1]) else F
  · cases st
    · simpa [um] using hF
    · simpa [um, e0] using hF.write (k := j) hj8 v.1
  · intro i hi
    cases st
    · simpa using hFW i hi
    · simp only [upd, List.length_singleton, ite_true, true_and, W']
      by_cases hij : i = j
      · subst hij; simp
      · simp only [show ¬(j ≤ i ∧ i < j + 1) by omega, ↓reduceIte]
        rw [hFW i hi]
        by_cases hlt : i < j
        · simp [hlt, show i < j + 1 by omega, hij]
        · simp [hlt, show ¬ i < j + 1 by omega]
  · rw [u1]; simp [W']
  · have ps : psum (fun i => (W' i).toNat) j = psum (fun i => (W i).toNat) j :=
      psum_congr fun i hi => by simp [W', show i ≠ j by omega]
    have e := adc_nat (read32 s0.mem (slot (s0.regs 0) j)) 0#32 t.c
    rw [hv'] at e
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at e
    simp only [psum, ps, uc, show W' j = v.1 by simp [W'], Nat.mul_add, Nat.mul_one, Nat.pow_add]
    exact chain_nat _ _ _ _ _ _ _ _ hv e

theorem canonWords_inv {s0 : State} {st : Bool} {cin : Nat} (h2 : s0.regs 2 = 0#32) :
    ∀ n, n ≤ 7 → ∀ {t : State}, CInv s0 st cin 1 t → CInv s0 st cin (n + 1) (execAll (canonWords st n) t)
  | 0, _, _, h => h
  | n + 1, hn, t, h => by
    rw [canonWords, execAll_append]
    exact canonWord_step (by omega) (by omega) h2 (canonWords_inv h2 n (by omega) h)

/-- A whole pass: the eight words plus `r_c`, stored if `st`. -/
theorem canonAdd_exec (s0 : State) (c : LowReg) (hc : c ≠ 1) (st : Bool)
    (hf : (s0.regs 0).toNat + 32 ≤ 2 ^ 32) (h2 : s0.regs 2 = 0#32) :
    CInv s0 st (s0.reg c).toNat 8 (execAll (canonAdd c st) s0) := by
  rw [canonAdd, execAll_append]
  exact canonWords_inv h2 7 (by omega) (canonFirst_inv s0 c hc st hf)

/-! ## Head, middle and tail -/

theorem canonHead_exec (s : State) :
    let t := execAll canonHead s
    let x := read32 s.mem (slot (s.regs 0) 7)
    t.regs 2 = 0#32 ∧ t.regs 3 = 19#32 ∧ (t.regs 4).toNat = 19 * (x.toNat / 2 ^ 31) ∧
      t.mem = write32 s.mem (slot (s.regs 0) 7) ((x <<< 1) >>> 1) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4] : List Reg) → t.regs r = s.regs r := by
  intro t x
  have k1 : (1 : BitVec 5).toNat = 1 := rfl
  have k31 : (31 : BitVec 5).toNat = 31 := rfl
  have k19 : (19 : BitVec 8).setWidth 32 = 19#32 := rfl
  have k0 : (0 : BitVec 8).setWidth 32 = 0#32 := rfl
  have a7 : s.regs 0 + BitVec.ofNat 32 ((7 : BitVec 5).toNat * 4) = slot (s.regs 0) 7 := by
    simp [slot]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [t, canonHead, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, Blake2s.regs_movImm, X25519Mul.regs_muls, X25519Mem.regs_ldrImm,
      X25519Mem.regs_strImm, toReg0, toReg1, toReg2, toReg3, toReg4, ite_true, ite_false, k0]
  · simp (config := {decide := true}) only [t, canonHead, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, Blake2s.regs_movImm, X25519Mul.regs_muls, X25519Mem.regs_ldrImm,
      X25519Mem.regs_strImm, toReg0, toReg1, toReg2, toReg3, toReg4, ite_true, ite_false, k19]
  · simp (config := {decide := true}) only [t, canonHead, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, Blake2s.regs_movImm, X25519Mul.regs_muls, X25519Mem.regs_ldrImm,
      X25519Mem.regs_strImm, X25519Mem.mem_ldrImm, X25519Mem.mem_strImm, mem_movImm,
      toReg0, toReg1, toReg2, toReg3, toReg4, ite_true, ite_false, k19, k31, a7]
    have := x.isLt
    simp only [x, BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.reduceMod] at this ⊢
    omega
  · simp (config := {decide := true}) only [t, canonHead, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, Blake2s.regs_movImm, X25519Mul.regs_muls, X25519Mem.regs_ldrImm,
      X25519Mem.regs_strImm, X25519Mem.mem_ldrImm, X25519Mem.mem_strImm, mem_movImm,
      X25519MulcWord.mem_lsl, X25519MulcWord.mem_lsr, X25519MulcWord.mem_dp,
      toReg0, toReg1, toReg2, toReg3, toReg4, ite_true, ite_false, k1, k31, a7, x]
  · intro r h15 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    have v : ∀ n : Reg, r ≠ n → r.val ≠ n.val := fun n h e => h (Fin.ext e)
    have v1 : r.val ≠ 1 := v 1 h1
    have v2 : r.val ≠ 2 := v 2 h2
    have v3 : r.val ≠ 3 := v 3 h3
    have v4 : r.val ≠ 4 := v 4 h4
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have l1 : ((1 : LowReg) : Nat) = 1 := rfl
      have l2 : ((2 : LowReg) : Nat) = 2 := rfl
      have l3 : ((3 : LowReg) : Nat) = 3 := rfl
      have l4 : ((4 : LowReg) : Nat) = 4 := rfl
      simp [canonHead, Instr.dsts, MemOp.isLoad, l1, l2, l3, l4, v1, v2, v3, v4])


theorem canonMid_exec (s : State) (h3 : s.regs 3 = 19#32) :
    let t := execAll canonMid s
    (t.regs 4).toNat = 19 * ((s.regs 1).toNat / 2 ^ 31) ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 4 → t.regs r = s.regs r := by
  intro t
  have k31 : (31 : BitVec 5).toNat = 31 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [t, canonMid, execAll, State.reg, X25519Mul.regs_lsr,
      X25519Mul.regs_muls, X25519MulcWord.mem_lsr, toReg1, toReg3, toReg4, ite_true, ite_false,
      k31, h3]
    have := (s.regs 1).isLt
    simp only [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.reduceMod] at this ⊢
    omega
  · simp only [t, canonMid, execAll, X25519MulcWord.mem_lsr, X25519MulcWord.mem_dp]
  · intro r h15 h4
    have v4 : r.val ≠ 4 := fun e => h4 (Fin.ext e)
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have l4 : ((4 : LowReg) : Nat) = 4 := rfl
      simp [canonMid, Instr.dsts, l4, v4])

theorem canonTail_exec (s : State) :
    let t := execAll canonTail s
    t.mem = write32 s.mem (slot (s.regs 0) 7) ((s.regs 1 <<< 1) >>> 1) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 1 → t.regs r = s.regs r := by
  intro t
  have k1 : (1 : BitVec 5).toNat = 1 := rfl
  have a7 : s.regs 0 + BitVec.ofNat 32 ((7 : BitVec 5).toNat * 4) = slot (s.regs 0) 7 := by
    simp [slot]
  refine ⟨?_, ?_⟩
  · simp (config := {decide := true}) only [t, canonTail, execAll, State.reg, X25519Mul.regs_lsl,
      X25519Mul.regs_lsr, X25519Mem.mem_strImm, X25519MulcWord.mem_lsl, X25519MulcWord.mem_lsr,
      toReg0, toReg1, ite_true, ite_false, k1, a7]
  · intro r h15 h1
    have v1 : r.val ≠ 1 := fun e => h1 (Fin.ext e)
    exact execAll_regs_other _ _ _ (fun e => h15 (Fin.ext e)) (by
      have l1 : ((1 : LowReg) : Nat) = 1 := rfl
      simp [canonTail, Instr.dsts, MemOp.isLoad, l1, v1])

/-! ## Arithmetic -/

/-- The three passes in numbers. The input is `L + 2^224 X7` (`L` the low seven words); pass
`k` produces `Pk` with carry `ck`; `T2`, `T3` are the top words of passes 2 and 3 and `L3` the
low words of pass 3. The result is `a mod p`. -/
theorem canon_arith (L X7 P1 c1 P2 c2 L2 T2 P3 c3 L3 T3 : Nat)
    (hL : L < 2 ^ 224) (hX : X7 < 2 ^ 32)
    (h1 : P1 + 2 ^ 256 * c1 = L + 2 ^ 224 * (X7 % 2 ^ 31) + 19 * (X7 / 2 ^ 31))
    (hP1 : P1 < 2 ^ 256)
    (h2 : P2 + 2 ^ 256 * c2 = P1 + 19) (hP2 : P2 = L2 + 2 ^ 224 * T2) (hL2 : L2 < 2 ^ 224)
    (hT2 : T2 < 2 ^ 32)
    (h3 : P3 + 2 ^ 256 * c3 = P1 + 19 * (T2 / 2 ^ 31)) (hP3 : P3 = L3 + 2 ^ 224 * T3)
    (hL3 : L3 < 2 ^ 224) (hT3 : T3 < 2 ^ 32) :
    L3 + 2 ^ 224 * (T3 % 2 ^ 31) = (L + 2 ^ 224 * X7) % X25519Reduce.pN ∧
      L3 + 2 ^ 224 * (T3 % 2 ^ 31) < X25519Reduce.pN := by
  have c1z : c1 = 0 := by omega
  have hq1 : (L + 2 ^ 224 * X7) / 2 ^ 255 = X7 / 2 ^ 31 := by omega
  have hr1 : (L + 2 ^ 224 * X7) % 2 ^ 255 = L + 2 ^ 224 * (X7 % 2 ^ 31) := by omega
  have c2z : c2 = 0 := by omega
  have hq2 : P2 / 2 ^ 255 = T2 / 2 ^ 31 := by omega
  have c3z : c3 = 0 := by omega
  have hr3 : P3 % 2 ^ 255 = L3 + 2 ^ 224 * (T3 % 2 ^ 31) := by omega
  subst c1z c2z c3z
  exact X25519Reduce.canon_nat (L + 2 ^ 224 * X7) P1 (T2 / 2 ^ 31) P3 _ (by omega)
    (by rw [hr1, hq1]; omega) (by rw [← hq2]; omega) (by omega) hr3.symm

theorem toNat_clear (x : Word) : ((x <<< 1) >>> 1).toNat = x.toNat % 2 ^ 31 := by
  have := x.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

theorem psum8 (f : Nat → Nat) : psum f 8 = psum f 7 + 2 ^ 224 * f 7 := rfl

theorem psum7_lt (f : Nat → Word) : psum (fun i => (f i).toNat) 7 < 2 ^ 224 :=
  X25519MulcChain.psum_lt (fun i => (f i).isLt) 7

theorem psum8_lt (f : Nat → Word) : psum (fun i => (f i).toNat) 8 < 2 ^ 256 :=
  X25519MulcChain.psum_lt (fun i => (f i).isLt) 8

theorem psum_upd7 (f : Nat → Word) (v : Word) :
    psum (fun i => (upd f 7 [v] i).toNat) 8 =
      psum (fun i => (f i).toNat) 7 + 2 ^ 224 * v.toNat := by
  rw [psum8]
  have e : psum (fun i => (upd f 7 [v] i).toNat) 7 = psum (fun i => (f i).toNat) 7 :=
    psum_congr fun i hi => by simp [upd, show ¬ 7 ≤ i by omega]
  rw [e]; simp [upd]

/-- Read the eight slots through a frame. -/
theorem frame_psum {p : Word} {m0 m : Mem} {F : Nat → Word} (h : FrameOk p 8 m0 F m)
    {G : Nat → Word} (hG : ∀ i < 8, F i = G i) :
    psum (fun i => (read32 m (slot p i)).toNat) 8 = psum (fun i => (G i).toNat) 8 :=
  psum_congr fun i hi => by rw [h.slots i hi, hG i hi]

theorem w8 : (2 : Nat) ^ (32 * 8) = 2 ^ 256 := rfl

/-! ## The body -/

/-- The whole body: the value at `r0` becomes its reduction modulo `p`; bytes outside the 32
at `r0` and the registers other than `r1`..`r4` are unchanged. -/
theorem canon_exec (s : State) (hf : (s.regs 0).toNat + 32 ≤ 2 ^ 32) :
    let t := execAll canonBody s
    X25519Routines.feVal t.mem (s.regs 0) =
        X25519Routines.feVal s.mem (s.regs 0) % X25519Reduce.pN ∧
      X25519Routines.feVal t.mem (s.regs 0) < X25519Reduce.pN ∧
      (∀ y, ¬ Region (s.regs 0) 32 y → t.mem y = s.mem y) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4] : List Reg) → t.regs r = s.regs r := by
  intro t
  obtain ⟨h2, h3, h4, hm, ho⟩ := canonHead_exec s
  simp only [t, canonBody, execAll_append]
  generalize hp : s.regs 0 = p at hf h4 hm ho ⊢
  generalize hx : read32 s.mem (slot p 7) = x7 at h4 hm
  generalize execAll canonHead s = s1 at h2 h3 h4 hm ho ⊢
  have q0 : s1.regs 0 = p := by rw [ho 0 (by decide) (by decide), hp]
  have F1 := (frame_init s.mem hf).write (k := 7) (by omega) ((x7 <<< 1) >>> 1)
  rw [← hm] at F1
  -- pass 1: add `19 * bit 255`, stored
  obtain ⟨k1, W1, G1, F2, hG1, -, v1⟩ := canonAdd_exec s1 4 (by decide) true
    (by rw [q0]; exact hf) h2
  generalize execAll (canonAdd 4 true) s1 = s2 at k1 F2 v1 ⊢
  rw [q0] at F2 hG1 v1
  -- pass 2: add `19`, not stored
  have h22 : s2.regs 2 = 0#32 := by rw [k1 2 (by decide) (by decide), h2]
  have q2 : s2.regs 0 = p := by rw [k1 0 (by decide) (by decide), q0]
  obtain ⟨k2, W2, G2, F3, hG2, r2, v2⟩ := canonAdd_exec s2 3 (by decide) false
    (by rw [q2]; exact hf) h22
  generalize execAll (canonAdd 3 false) s2 = s3 at k2 F3 r2 v2 ⊢
  rw [q2] at F3 hG2 v2
  -- middle: `r4 = 19 * bit 255` of pass 2
  have h33 : s3.regs 3 = 19#32 := by
    rw [k2 3 (by decide) (by decide), k1 3 (by decide) (by decide), h3]
  obtain ⟨m4, mm, mo⟩ := canonMid_exec s3 h33
  generalize execAll canonMid s3 = s4 at m4 mm mo ⊢
  -- pass 3: add `19 * that bit`, stored
  have h24 : s4.regs 2 = 0#32 := by
    rw [mo 2 (by decide) (by decide), k2 2 (by decide) (by decide), h22]
  have q4 : s4.regs 0 = p := by
    rw [mo 0 (by decide) (by decide), k2 0 (by decide) (by decide), q2]
  obtain ⟨k3, W3, G3, F5, hG3, r3, v3⟩ := canonAdd_exec s4 4 (by decide) true
    (by rw [q4]; exact hf) h24
  generalize execAll (canonAdd 4 true) s4 = s5 at k3 F5 r3 v3 ⊢
  rw [q4] at F5 hG3 v3
  -- tail: clear bit 255
  have q5 : s5.regs 0 = p := by rw [k3 0 (by decide) (by decide), q4]
  obtain ⟨tm, to⟩ := canonTail_exec s5
  generalize execAll canonTail s5 = s6 at tm to ⊢
  rw [q5] at tm
  have F6 := (frame_init s5.mem hf).write (k := 7) (by omega) ((s5.regs 1 <<< 1) >>> 1)
  rw [← tm] at F6
  -- the numbers
  have e1 : psum (fun i => (read32 s1.mem (slot p i)).toNat) 8 =
      psum (fun i => (read32 s.mem (slot p i)).toNat) 7 + 2 ^ 224 * (x7.toNat % 2 ^ 31) := by
    rw [frame_psum F1 (fun _ _ => rfl), psum_upd7, toNat_clear]
  have e2 : psum (fun i => (read32 s2.mem (slot p i)).toNat) 8 =
      psum (fun i => (W1 i).toNat) 8 :=
    frame_psum F2 fun i hi => by rw [hG1 i hi]; simp [hi]
  have e3 : ∀ i < 8, read32 s3.mem (slot p i) = W1 i := fun i hi => by
    rw [F3.slots i hi, hG2 i hi]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    rw [F2.slots i hi, hG1 i hi]; simp [hi]
  have e4 : psum (fun i => (read32 s4.mem (slot p i)).toNat) 8 =
      psum (fun i => (W1 i).toNat) 8 :=
    psum_congr fun i hi => by rw [mm, e3 i hi]
  have e5 : ∀ i < 8, read32 s5.mem (slot p i) = W3 i := fun i hi => by
    rw [F5.slots i hi, hG3 i hi]; simp [hi]
  have e6 : X25519Routines.feVal s6.mem p =
      psum (fun i => (W3 i).toNat) 7 + 2 ^ 224 * ((W3 7).toNat % 2 ^ 31) := by
    rw [feVal_frame F6, psum_upd7, toNat_clear, r3]
    rw [psum_congr fun i (hi : i < 7) => by rw [e5 i (by omega)]]
  have ea : X25519Routines.feVal s.mem p =
      psum (fun i => (read32 s.mem (slot p i)).toNat) 7 + 2 ^ 224 * x7.toNat := by
    rw [X25519MulcFacts.feVal_psum, psum8, hx]
  have r4 : (s1.reg 4).toNat = 19 * (x7.toNat / 2 ^ 31) := by rw [State.reg, toReg4, h4]
  have r33 : (s2.reg 3).toNat = 19 := by
    rw [State.reg, toReg3, k1 3 (by decide) (by decide), h3]; rfl
  have r44 : (s4.reg 4).toNat = 19 * ((W2 7).toNat / 2 ^ 31) := by
    rw [State.reg, toReg4, m4, r2]
  rw [e1, r4, w8] at v1
  rw [e2, r33, w8] at v2
  rw [e4, r44, w8] at v3
  rw [psum8] at v2 v3
  obtain ⟨hR, hlt⟩ := canon_arith _ _ _ _ _ _ _ _ _ _ _ _ (psum7_lt _) x7.isLt v1 (psum8_lt W1)
    v2 rfl (psum7_lt W2) (W2 7).isLt v3 rfl (psum7_lt W3) (W3 7).isLt
  refine ⟨by rw [e6, ea]; exact hR, by rw [e6]; exact hlt, fun y hy => ?_, fun r h15 hr => ?_⟩
  · rw [frame_out F6 y hy, frame_out F5 y hy, mm, frame_out F3 y hy, frame_out F2 y hy,
      frame_out F1 y hy]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4⟩ := hr
    rw [to r h15 n1, k3 r h15 n1, mo r h15 n4, k2 r h15 n1, k1 r h15 n1,
      ho r h15 (by simp [n1, n2, n3, n4])]

/-! ## Accesses -/

/-- The memory instructions of the body: word loads into a register other than `r0`, or word
stores, through `r0` at word offsets below 8. -/
def cMem : Instr → Bool
  | .memImm op t n k => n == 0 && decide (k.toNat < 8) && (op == .str || (op == .ldr && t != 0))
  | _ => false

/-- Every instruction of the body keeps `r0` and accesses memory only as `cMem` says. -/
def cSafe (i : Instr) : Bool := (X25519Mul.regOnly i && decide (0 ∉ i.dsts)) || cMem i

theorem cSafe_body : canonBody.all cSafe = true := by decide +kernel

theorem next_regs_other' (i : Instr) (s : State) (r : Reg) (h15 : r.val ≠ 15)
    (h : r.val ∉ i.dsts) : (i.next s).regs r = s.regs r :=
  execAll_regs_other [i] s r h15 (by simp [h])

theorem cSafe_ok {Wr : Word → Prop} {d : Word} (hd : d.toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (d + BitVec.ofNat 32 j)) (i : Instr) (h : cSafe i = true) (t : State)
    (h0 : t.regs 0 = d) : (i.next t).regs 0 = d ∧ ∀ a ∈ i.accesses t, AccOk Wr a := by
  simp only [cSafe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hr, hn⟩ | h
  · refine ⟨by rw [next_regs_other' i t 0 (by decide) hn, h0], ?_⟩
    rw [X25519Mul.accesses_regOnly i t hr]; intro a ha; cases ha
  · cases i with
    | memImm op r n k =>
      simp only [cMem, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        bne_iff_ne, ne_eq] at h
      obtain ⟨⟨rfl, hk⟩, hop⟩ := h
      have hd' : (t.reg 0).toNat % 4 = 0 := by rw [State.reg, toReg0, h0]; exact hd
      rcases hop with rfl | ⟨rfl, hr0⟩
      · refine ⟨by rw [next_regs_other' _ t 0 (by decide) (by simp [Instr.dsts, MemOp.isLoad]),
          h0], ?_⟩
        intro a ha
        simp only [Instr.accesses, MemOp.isLoad, MemOp.width, List.mem_singleton] at ha
        subst ha
        refine ⟨X25519Block.aligned_word (X25519Block.word_add_aligned hd' (by omega)), fun _ q (hq : q < 4) => ?_⟩
        rw [State.reg, toReg0, h0, ofNat_add_assoc]; exact hW _ (by omega)
      · have hr0' : (0 : Nat) ∉ (Instr.memImm .ldr r 0 k).dsts := by
          simp only [Instr.dsts, MemOp.isLoad, ite_true, List.mem_singleton]
          intro e; exact hr0 (Fin.ext e.symm)
        refine ⟨by rw [next_regs_other' _ t 0 (by decide) hr0', h0], ?_⟩
        intro a ha
        simp only [Instr.accesses, MemOp.isLoad, MemOp.width, ite_true, List.mem_singleton] at ha
        subst ha
        exact ⟨X25519Block.aligned_word (X25519Block.word_add_aligned hd' (by omega)), fun e => by cases e⟩
    | _ => simp [cMem] at h

theorem accAll_keep {P : Access → Prop} (I : State → Prop) :
    ∀ (is : List Instr) (s : State), I s →
      (∀ i ∈ is, ∀ t, I t → I (i.next t) ∧ ∀ a ∈ i.accesses t, P a) → AccAll P is s
  | [], s, _, _ => accAll_nil P s
  | i :: is, s, hs, h => by
    obtain ⟨h1, h2⟩ := h i List.mem_cons_self s hs
    exact accAll_cons h2 (accAll_keep I is _ h1 fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem canon_acc {Wr : Word → Prop} (s : State) (h0 : (s.regs 0).toNat % 4 = 0)
    (hW : ∀ j < 32, Wr (s.regs 0 + BitVec.ofNat 32 j)) : AccAll (AccOk Wr) canonBody s :=
  accAll_keep (fun t => t.regs 0 = s.regs 0) canonBody s rfl fun i hi =>
    cSafe_ok h0 hW i (List.all_eq_true.mp cSafe_body i hi)

/-! ## The block in a `ReachW` proof -/

/-- One `canon_body` block in a `ReachW` proof: the value at `p` (in `r0`) is reduced in
place to its canonical representative below `2^255 - 19`. -/
theorem canon_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off : Nat} {p : Word}
    (hseq : seqAt B off canonBody = true) (hoff : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hr : InRegion Pc base off (seqSize canonBody))
    (h0 : t.regs 0 = p) (hd : p.toNat % 4 = 0) (hf : p.toNat + 32 ≤ 2 ^ 32)
    (hW : ∀ j < 32, Wr (p + BitVec.ofNat 32 j)) {Q : State → Prop}
    (k : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize canonBody) →
      (X25519Routines.feVal t'.mem p : Int) ≡p X25519Routines.feVal t.mem p →
      X25519Routines.feVal t'.mem p < 2 ^ 255 - 19 →
      (∀ y, ¬ Region p 32 y → t'.mem y = t.mem y) →
      (∀ r : Reg, r ≠ 15 → r ∉ ([1, 2, 3, 4] : List Reg) → t'.regs r = t.regs r) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst h0
  obtain ⟨ev, el, em, eo⟩ := canon_exec t hf
  have ec : (X25519Routines.feVal (execAll canonBody t).mem (t.regs 0) : Int) ≡p
      X25519Routines.feVal t.mem (t.regs 0) := by
    rw [ev]
    exact ModP.symm (X25519Reduce.congr_of_eq (Nat.mod_add_div _ _).symm)
  have el' : X25519Routines.feVal (execAll canonBody t).mem (t.regs 0) < 2 ^ 255 - 19 := by
    unfold X25519Reduce.pN at el; exact el
  refine X25519Block.ReachW.blockAcc hb _ off hpc hoff hseq canonBody_falls (canon_acc t hd hW) hr
    (k _ ?_ ec el' em eo)
  rw [execAll_pc _ _ canonBody_falls, hpc, ofNat_add_assoc]

end M0Crypto.Release.X25519Inl
