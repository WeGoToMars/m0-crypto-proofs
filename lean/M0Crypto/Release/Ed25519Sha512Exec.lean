import M0Crypto.Release.Ed25519Sha512Code
import M0Crypto.Release.Ed25519Sha512Pairs
import M0Crypto.Release.Field25519Carry

set_option linter.unusedSimpArgs false

/-!
# Straight-line effects for the SHA-512 block (reusable)

* `nx_*`: the effect of one instruction on a register (away from the pc), in query form: a
  register of `i.next s` is an `if` over the destination and the registers of `s`. A block's
  register is computed by `simp` with these rules from the outside in, so no intermediate
  state is ever built (`blk_simp`).
* `wval`, `adcChain`, `adcChain_val`: an `adds`/`adcs` chain over `n` words is addition of
  `n`-word numbers with a carry out. `pair_add`: its two-word case on 64-bit pairs `hi ++ lo`.
  Generic in the words, for any multi-word addition (lanes B: `mp_mul`, `sc_reduce`, `sc_muladd`).
* `sigma_regs`, `sigma_mem`: macro `sigma` for any rotation list and shift (one lemma for its
  four uses); `sigLo`, `sigHi` are its two result words as the XOR of its terms in emission order.
-/

namespace M0Crypto.Release.Ed25519Sha512Exec

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519Sha512Code

/-! ## One instruction -/

section
variable (s : State) (r : Reg) (hr : r ≠ 15)
include hr

theorem nx_lsr (d m : LowReg) (k : BitVec 5) : ((Instr.lsrImm d m k).next s).regs r =
    if r = d.toReg then s.regs m.toReg >>> (if k.toNat = 0 then 32 else k.toNat) else s.regs r := by
  simp [Instr.next, Instr.exec, lsrC, State.setReg, State.setNZC, State.setNZ, State.reg, hr]

theorem nx_lsl (d m : LowReg) (k : BitVec 5) : ((Instr.lslImm d m k).next s).regs r =
    if r = d.toReg then (if k.toNat = 0 then s.regs m.toReg else s.regs m.toReg <<< k.toNat)
    else s.regs r := by
  by_cases h : k.toNat = 0 <;>
    simp [Instr.next, Instr.exec, lslC, State.setReg, State.setNZC, State.setNZ, State.reg, hr, h]

theorem nx_eors (d m : LowReg) : ((Instr.dp .eors d m).next s).regs r =
    if r = d.toReg then s.regs d.toReg ^^^ s.regs m.toReg else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, hr]

theorem nx_ands (d m : LowReg) : ((Instr.dp .ands d m).next s).regs r =
    if r = d.toReg then s.regs d.toReg &&& s.regs m.toReg else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, State.reg, hr]

theorem nx_adds (d n m : LowReg) : ((Instr.addReg d n m).next s).regs r =
    if r = d.toReg then (addWithCarry (s.regs n.toReg) (s.regs m.toReg) false).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg, hr]

theorem nx_adcs (d m : LowReg) : ((Instr.dp .adcs d m).next s).regs r =
    if r = d.toReg then (addWithCarry (s.regs d.toReg) (s.regs m.toReg) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg, hr]

theorem nx_addImm8 (d : LowReg) (k : BitVec 8) : ((Instr.addImm8 d k).next s).regs r =
    if r = d.toReg then s.regs d.toReg + BitVec.ofNat 32 k.toNat else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg, hr,
    M0Crypto.Proofs.addWithCarry_fst]

theorem nx_movImm (d : LowReg) (k : BitVec 8) : ((Instr.movImm d k).next s).regs r =
    if r = d.toReg then BitVec.ofNat 32 k.toNat else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem nx_movHi (d m : Reg) : ((Instr.movHi d m).next s).regs r =
    if r = d then s.regs m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem nx_ldrSp (t : LowReg) (k : BitVec 8) : ((Instr.ldrSp t k).next s).regs r =
    if r = t.toReg then read32 s.mem (s.regs 13 + BitVec.ofNat 32 (k.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem nx_ldrImm (t n : LowReg) (k : BitVec 5) : ((Instr.memImm .ldr t n k).next s).regs r =
    if r = t.toReg then read32 s.mem (s.regs n.toReg + BitVec.ofNat 32 (k.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, MemOp.width, hr]

theorem nx_ldrReg (t n m : LowReg) : ((Instr.memReg .ldr t n m).next s).regs r =
    if r = t.toReg then read32 s.mem (s.regs n.toReg + s.regs m.toReg) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, hr]

theorem nx_rev (d m : LowReg) : ((Instr.rev d m).next s).regs r =
    if r = d.toReg then revBytes (s.regs m.toReg) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg, hr]

theorem nx_addRdSp (d : LowReg) (k : BitVec 8) : ((Instr.addRdSp d k).next s).regs r =
    if r = d.toReg then s.regs 13 + BitVec.ofNat 32 (k.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

/-- A register no instruction form below writes. -/
theorem nx_strSp (t : LowReg) (k : BitVec 8) : ((Instr.strSp t k).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.sp, State.reg, State.setReg, hr]

theorem nx_strReg (t n m : LowReg) : ((Instr.memReg .str t n m).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, toReg_ne_15, hr]

theorem nx_cmpImm (d : LowReg) (k : BitVec 8) : ((Instr.cmpImm d k).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZCV, addFlags, hr]

theorem nx_keep (i : Instr) (h : r.val ∉ i.dsts) : (i.next s).regs r = s.regs r :=
  next_regs_other s r (fun e => hr (Fin.ext e)) h

end

theorem regs_subImm8 (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.subImm8 d i).next s).regs r = if r = d.toReg then s.regs d.toReg - i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.reg, hr,
    M0Crypto.Release.sub_flags]

theorem z_subImm8 (s : State) (d : LowReg) (i : BitVec 8) :
    ((Instr.subImm8 d i).next s).z = (s.regs d.toReg - i.setWidth 32 == 0) := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg,
    M0Crypto.Release.sub_flags]

theorem mem_subImm8 (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.subImm8 d i).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV]

theorem nx_adds_c (s : State) (d n m : LowReg) :
    ((Instr.addReg d n m).next s).c = (addWithCarry (s.regs n.toReg) (s.regs m.toReg) false).2.1 := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, State.setNZ, State.reg]

theorem nx_strSp_mem (s : State) (t : LowReg) (k : BitVec 8) : ((Instr.strSp t k).next s).mem =
    write32 s.mem (s.regs 13 + BitVec.ofNat 32 (k.toNat * 4)) (s.regs t.toReg) := by
  simp [Instr.next, Instr.exec, State.sp, State.reg]

theorem nx_strReg_mem (s : State) (t n m : LowReg) : ((Instr.memReg .str t n m).next s).mem =
    write32 s.mem (s.regs n.toReg + s.regs m.toReg) (s.regs t.toReg) := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, State.reg, toReg_ne_15]

/-- `ldm n!, {a, b}` with `n ∉ {a, b}`. -/
theorem nx_ldm2 (s : State) (n : LowReg) (l : BitVec 8) (a b : LowReg) (hl : listRegs l = [a, b])
    (hn : l.getLsbD n.val = false) (r : Reg) (hr : r ≠ 15) : ((Instr.ldm n l).next s).regs r =
    if r = n.toReg then s.regs n.toReg + 8#32 else if r = b.toReg then read32 s.mem (s.regs n.toReg + 4#32)
    else if r = a.toReg then read32 s.mem (s.regs n.toReg) else s.regs r := by
  simp only [Instr.next, Instr.exec, hn, hl, bitCount, List.map, loadRegs, Bool.false_eq_true,
    ite_false, State.setReg, State.reg, List.length]
  by_cases h1 : r = n.toReg <;> by_cases h2 : r = b.toReg <;> by_cases h3 : r = a.toReg <;>
    simp [h1, h2, h3, hr]

theorem nx_mem (i : Instr) (h : i.writesMem = false) (s : State) : (i.next s).mem = s.mem :=
  next_mem h s

/-- `nx_mem` per instruction form, without a side condition, for `simp`. -/
theorem mem_lsl (d m : LowReg) (k : BitVec 5) (s : State) : ((Instr.lslImm d m k).next s).mem = s.mem := next_mem rfl s
theorem mem_lsr (d m : LowReg) (k : BitVec 5) (s : State) : ((Instr.lsrImm d m k).next s).mem = s.mem := next_mem rfl s
theorem mem_dp (o : DpOp) (d m : LowReg) (s : State) : ((Instr.dp o d m).next s).mem = s.mem := next_mem rfl s
theorem mem_addReg (d n m : LowReg) (s : State) : ((Instr.addReg d n m).next s).mem = s.mem := next_mem rfl s
theorem mem_movHi (d m : Reg) (s : State) : ((Instr.movHi d m).next s).mem = s.mem := next_mem rfl s
theorem mem_movImm (d : LowReg) (k : BitVec 8) (s : State) : ((Instr.movImm d k).next s).mem = s.mem := next_mem rfl s
theorem mem_addImm8 (d : LowReg) (k : BitVec 8) (s : State) : ((Instr.addImm8 d k).next s).mem = s.mem := next_mem rfl s
theorem mem_ldrSp (t : LowReg) (k : BitVec 8) (s : State) : ((Instr.ldrSp t k).next s).mem = s.mem := next_mem rfl s
theorem mem_ldrImm (t n : LowReg) (k : BitVec 5) (s : State) : ((Instr.memImm .ldr t n k).next s).mem = s.mem := next_mem rfl s
theorem mem_ldrReg (t n m : LowReg) (s : State) : ((Instr.memReg .ldr t n m).next s).mem = s.mem := next_mem rfl s
theorem mem_ldm (n : LowReg) (l : BitVec 8) (s : State) : ((Instr.ldm n l).next s).mem = s.mem := next_mem rfl s
theorem mem_rev (d m : LowReg) (s : State) : ((Instr.rev d m).next s).mem = s.mem := next_mem rfl s
theorem mem_addRdSp (d : LowReg) (k : BitVec 8) (s : State) : ((Instr.addRdSp d k).next s).mem = s.mem := next_mem rfl s
theorem mem_cmpImm (d : LowReg) (k : BitVec 8) (s : State) : ((Instr.cmpImm d k).next s).mem = s.mem := next_mem rfl s
theorem mem_strReg (t n m : LowReg) (s : State) : ((Instr.memReg .str t n m).next s).mem =
    write32 s.mem (s.regs n.toReg + s.regs m.toReg) (s.regs t.toReg) := nx_strReg_mem s t n m

/-! ## Words in the frame -/

/-- `ldr`/`str` at `sp` with the `imm8` of word `k`. -/
theorem sp_imm (sp : Word) (k : Nat) (hk : k < 256) :
    sp + BitVec.ofNat 32 ((BitVec.ofNat 8 k).toNat * 4) = slot sp k := by
  simp only [slot, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hk, Nat.mul_comm]

/-- The 64-bit word at `a`, low word first. -/
def pairAt (m : Mem) (a : Word) : BitVec 64 := read32 m (a + 4#32) ++ read32 m a

/-- `read32_write32_slot` for frames of up to `2^20` words. -/
theorem read32_write32_slotN (m : Mem) (sp v : Word) (i j : Nat) (hi : i < 2 ^ 20) (hj : j < 2 ^ 20) :
    read32 (write32 m (slot sp i) v) (slot sp j) = if i = j then v else read32 m (slot sp j) := by
  split
  · subst_vars; exact M0Crypto.Armv6M.read32_write32_same m _ v
  · rename_i hij
    have hb : ∀ q, q < 4 → write32 m (slot sp i) v (slot sp j + BitVec.ofNat 32 q) =
        m (slot sp j + BitVec.ofNat 32 q) := by
      intro q hq
      apply M0Crypto.Armv6M.write32_other
      intro k hk h
      have := congrArg BitVec.toNat h
      simp only [slot, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    have h0 := hb 0 (by omega); have h1 := hb 1 (by omega)
    have h2 := hb 2 (by omega); have h3 := hb 3 (by omega)
    simp only [BitVec.add_zero] at h0
    simp only [read32]
    rw [h0, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, h1,
      show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, h2,
      show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, h3]

/-- Pair `i` of the variables `V` in the frame at `sp`. -/
def vp (m : Mem) (sp : Word) (i : Nat) : BitVec 64 :=
  read32 m (slot sp (vw i true)) ++ read32 m (slot sp (vw i false))

theorem vw_lt {i : Nat} (hi : i < 8) (b : Bool) : vw i b < (VOFF + VB) / 4 := by
  cases b <;> simp [vw, VOFF, VB] <;> omega

theorem vw_small {i : Nat} (hi : i < 8) (b : Bool) : vw i b < 2 ^ 20 :=
  Nat.lt_trans (vw_lt hi b) (by decide)

/-- A pair store: `vp` of the stored pair is the value, the other pairs are kept. -/
theorem vp_write (m : Mem) (sp : Word) {i j : Nat} (hi : i < 8) (hj : j < 8) (lo hv : Word) :
    vp (write32 (write32 m (slot sp (vw j false)) lo) (slot sp (vw j true)) hv) sp i =
      if i = j then hv ++ lo else vp m sp i := by
  have e : ∀ a b : Bool, (vw j a = vw i b) ↔ (j = i ∧ a = b) := by
    intro a b; cases a <;> cases b <;> simp [vw, VOFF] <;> omega
  simp only [vp, read32_write32_slotN _ _ _ _ _ (vw_small hj _) (vw_small hi _), e]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## Multi-word addition -/

/-- The value of little-endian words. -/
def wval : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 32 * wval ws

/-- `adds` on the first words and `adcs` on the rest, from carry `c`: the words and the carry out. -/
def adcChain : List Word → List Word → Bool → List Word × Bool
  | x :: xs, y :: ys, c =>
    let r := addWithCarry x y c
    let t := adcChain xs ys r.2.1
    (r.1 :: t.1, t.2)
  | _, _, c => ([], c)

/-- **The add chain** is addition of `n`-word numbers with a carry out. -/
theorem adcChain_val : ∀ (xs ys : List Word) (c : Bool), xs.length = ys.length →
    wval (adcChain xs ys c).1 + 2 ^ (32 * xs.length) * (adcChain xs ys c).2.toNat =
      wval xs + wval ys + c.toNat
  | [], [], c, _ => by simp [adcChain, wval]
  | x :: xs, y :: ys, c, h => by
    have ih := adcChain_val xs ys (addWithCarry x y c).2.1 (by simpa using h)
    have e := Field25519Carry.adc_nat x y c
    simp only [adcChain, wval, List.length_cons]
    rw [show 32 * (xs.length + 1) = 32 * xs.length + 32 by omega, Nat.pow_add]
    generalize 2 ^ (32 * xs.length) = P at ih ⊢
    generalize adcChain xs ys (addWithCarry x y c).2.1 = t at ih ⊢
    generalize (addWithCarry x y c).2.1.toNat = k at ih e
    generalize (addWithCarry x y c).1.toNat = r at e ⊢
    have h2 : 2 ^ 32 * (wval t.1 + P * t.2.toNat) = 2 ^ 32 * (wval xs + wval ys + k) := by rw [ih]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ 32) P] at h2
    omega

/-- `adds lo; adcs hi` on 64-bit pairs `hi ++ lo`. -/
theorem pair_add (xh xl yh yl : Word) :
    (xh ++ xl) + (yh ++ yl) =
      (addWithCarry xh yh (addWithCarry xl yl false).2.1).1 ++ (addWithCarry xl yl false).1 := by
  have h := adcChain_val [xl, xh] [yl, yh] false rfl
  simp only [adcChain, wval, List.length, Bool.toNat_false] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Ed25519Sha512Pairs.toNat_app, Ed25519Sha512Pairs.toNat_app,
    Ed25519Sha512Pairs.toNat_app]
  have := (addWithCarry xh yh (addWithCarry xl yl false).2.1).2.1.toNat_le
  have := (addWithCarry xl yl false).1.isLt
  have := (addWithCarry xh yh (addWithCarry xl yl false).2.1).1.isLt
  omega

/-! ## Macro `sigma` -/

/-- The value of a shift term on the input words. -/
def tv (t : STerm) (xl xh : Word) : Word :=
  if t.left then (if t.sHi then xh else xl) <<< t.amt else (if t.sHi then xh else xl) >>> t.amt

/-- The XOR of the terms into result word `hi`, after `a` when started. -/
def accX (xl xh : Word) (hi : Bool) : Option Word → List STerm → Option Word
  | a, [] => a
  | a, t :: ts => accX xl xh hi
      (if t.dHi = hi then some ((a.map (· ^^^ tv t xl xh)).getD (tv t xl xh)) else a) ts

def sigLo (rots : List Nat) (shr : Option Nat) (xl xh : Word) : Word :=
  (accX xl xh false none (sTerms rots shr)).getD 0
def sigHi (rots : List Nat) (shr : Option Nat) (xl xh : Word) : Word :=
  (accX xl xh true none (sTerms rots shr)).getD 0

theorem accX_getD (xl xh : Word) (hi : Bool) : ∀ (ts : List STerm) (a : Option Word) (d d' : Word),
    (a.isSome || ts.any (·.dHi == hi)) = true →
      (accX xl xh hi a ts).getD d = (accX xl xh hi a ts).getD d'
  | [], a, d, d', h => by cases a <;> simp_all [accX]
  | t :: ts, a, d, d', h => by
    simp only [accX]
    apply accX_getD
    by_cases e : t.dHi = hi <;> simp_all

/-- The shifts are by `1 … 31`, and each result word has a term. -/
def sOk (rots : List Nat) (shr : Option Nat) : Bool :=
  (sTerms rots shr).all (fun t => 0 < t.amt && t.amt < 32) &&
    (sTerms rots shr).any (·.dHi == false) && (sTerms rots shr).any (·.dHi == true)

theorem ofNat5 {a : Nat} (h0 : 0 < a) (h : a < 32) :
    (if (BitVec.ofNat 5 a).toNat = 0 then 32 else (BitVec.ofNat 5 a).toNat) = a ∧
    (BitVec.ofNat 5 a).toNat = a := by
  simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; simp; omega

/-- The instructions of one term: into its result word, or through `r4` once it is started. -/
def termI (t : STerm) (st : Bool) : List Instr :=
  if st then [shI t.left 4 (if t.sHi then 1 else 0) t.amt, .dp .eors (if t.dHi then 3 else 2) 4]
  else [shI t.left (if t.dHi then 3 else 2) (if t.sHi then 1 else 0) t.amt]

theorem emitS_cons (t : STerm) (ts : List STerm) (sl sh : Bool) :
    emitS (t :: ts) sl sh = termI t (if t.dHi then sh else sl) ++ emitS ts (sl || !t.dHi) (sh || t.dHi) := by
  cases h : t.dHi <;> cases sl <;> cases sh <;> simp [emitS, termI, h]

theorem termI_run (t : STerm) (st : Bool) (u : State) (h0 : 0 < t.amt) (h32 : t.amt < 32) :
    let u' := execAll (termI t st) u
    let v := tv t (u.regs 0) (u.regs 1)
    u'.mem = u.mem ∧ u'.regs 0 = u.regs 0 ∧ u'.regs 1 = u.regs 1 ∧
    u'.regs 2 = (if t.dHi then u.regs 2 else if st then u.regs 2 ^^^ v else v) ∧
    u'.regs 3 = (if t.dHi then (if st then u.regs 3 ^^^ v else v) else u.regs 3) ∧
    ∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 15 → u'.regs r = u.regs r := by
  obtain ⟨e1, e2⟩ := ofNat5 h0 h32
  obtain ⟨dHi, left, sHi, a⟩ := t
  simp only at e1 e2 h0
  have ha : (a = 0) = False := by simp; omega
  refine ⟨execAll_mem _ _ (by cases st <;> cases left <;> rfl), ?_⟩
  cases st <;> cases dHi <;> cases left <;> cases sHi <;>
    simp (config := {decide := true, contextual := true}) [termI, shI, tv, execAll, nx_lsr, nx_lsl,
      nx_eors, e2, ha, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4]

theorem emitS_run : ∀ (ts : List STerm) (sl sh : Bool) (s : State),
    ts.all (fun t => 0 < t.amt && t.amt < 32) = true →
    let s' := execAll (emitS ts sl sh) s
    s'.mem = s.mem ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 1 = s.regs 1 ∧
    s'.regs 2 = (accX (s.regs 0) (s.regs 1) false (if sl then some (s.regs 2) else none) ts).getD (s.regs 2) ∧
    s'.regs 3 = (accX (s.regs 0) (s.regs 1) true (if sh then some (s.regs 3) else none) ts).getD (s.regs 3) ∧
    ∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 15 → s'.regs r = s.regs r
  | [], sl, sh, s, _ => by cases sl <;> cases sh <;> simp [emitS, execAll, accX]
  | t :: ts, sl, sh, s, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, h32⟩, h⟩ := h
    intro s'
    simp only [s', emitS_cons, execAll_append]
    obtain ⟨m1, a0, a1, a2, a3, ar⟩ := termI_run t (if t.dHi then sh else sl) s h0 h32
    generalize execAll (termI t _) s = u at m1 a0 a1 a2 a3 ar
    obtain ⟨m2, b0, b1, b2, b3, br⟩ := emitS_run ts (sl || !t.dHi) (sh || t.dHi) u h
    refine ⟨m2.trans m1, b0.trans a0, b1.trans a1, ?_, ?_, fun r q2 q3 q4 q15 =>
      (br r q2 q3 q4 q15).trans (ar r q2 q3 q4 q15)⟩
    · rw [b2, a0, a1, a2]
      cases e : t.dHi <;> cases sl <;> simp only [e, accX, ite_true, ite_false, Bool.or_true,
        Bool.or_false, Bool.not_false, Bool.not_true, Option.map, Option.getD, reduceCtorEq] <;>
        first | rfl | exact accX_getD _ _ _ _ _ _ _ (by simp)
    · rw [b3, a0, a1, a3]
      cases e : t.dHi <;> cases sh <;> simp only [e, accX, ite_true, ite_false, Bool.or_true,
        Bool.or_false, Bool.not_false, Bool.not_true, Option.map, Option.getD, reduceCtorEq] <;>
        first | rfl | exact accX_getD _ _ _ _ _ _ _ (by simp)

/-- **Macro `sigma`**: `r2:r3` are `sigLo`, `sigHi` of `r0:r1`; the memory and the registers
other than `r2`, `r3`, `r4` are kept. -/
theorem sigma_run (rots : List Nat) (shr : Option Nat) (h : sOk rots shr = true) (s : State) :
    let s' := execAll (sigmaI rots shr) s
    s'.mem = s.mem ∧ s'.regs 2 = sigLo rots shr (s.regs 0) (s.regs 1) ∧
    s'.regs 3 = sigHi rots shr (s.regs 0) (s.regs 1) ∧
    ∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 15 → s'.regs r = s.regs r := by
  simp only [sOk, Bool.and_eq_true] at h
  obtain ⟨⟨ha, hl⟩, hh⟩ := h
  simp only [sigmaI]
  obtain ⟨m, -, -, r2, r3, rr⟩ := emitS_run (sTerms rots shr) false false s ha
  refine ⟨m, ?_, ?_, rr⟩
  · rw [r2]; exact accX_getD _ _ _ _ _ _ _ (by simpa using hl)
  · rw [r3]; exact accX_getD _ _ _ _ _ _ _ (by simpa using hh)

/-- `sigma_run` in query form, for `blk_simp`. -/
theorem sigma_regs (rots : List Nat) (shr : Option Nat) (h : sOk rots shr = true) (s : State) (r : Reg)
    (h4 : r ≠ 4) (h15 : r ≠ 15) : (execAll (sigmaI rots shr) s).regs r =
      if r = 2 then sigLo rots shr (s.regs 0) (s.regs 1) else if r = 3 then sigHi rots shr (s.regs 0) (s.regs 1)
      else s.regs r := by
  obtain ⟨-, r2, r3, rr⟩ := sigma_run rots shr h s
  by_cases e2 : r = 2
  · subst e2; simpa using r2
  by_cases e3 : r = 3
  · subst e3; simpa using r3
  simp only [e2, e3, ite_false]; exact rr r e2 e3 h4 h15

theorem sigma_mem (rots : List Nat) (shr : Option Nat) (h : sOk rots shr = true) (s : State) :
    (execAll (sigmaI rots shr) s).mem = s.mem := (sigma_run rots shr h s).1

/-- The four uses, against `Spec.Sha512` (`Ed25519Sha512Pairs`). -/
theorem Sigma1_sig (h l : Word) :
    Spec.Sha512.Sigma1 (h ++ l) = sigHi [14, 18, 41] none l h ++ sigLo [14, 18, 41] none l h := by
  rw [Ed25519Sha512Pairs.Sigma1_pair]; rfl

theorem Sigma0_sig (h l : Word) :
    Spec.Sha512.Sigma0 (h ++ l) = sigHi [28, 34, 39] none l h ++ sigLo [28, 34, 39] none l h := by
  rw [Ed25519Sha512Pairs.Sigma0_pair]; rfl

theorem sigma0_sig (h l : Word) :
    Spec.Sha512.sigma0 (h ++ l) = sigHi [1, 8] (some 7) l h ++ sigLo [1, 8] (some 7) l h := by
  rw [Ed25519Sha512Pairs.sigma0_pair]; rfl

theorem sigma1_sig (h l : Word) :
    Spec.Sha512.sigma1 (h ++ l) = sigHi [19, 61] (some 6) l h ++ sigLo [19, 61] (some 6) l h := by
  rw [Ed25519Sha512Pairs.sigma1_pair]; rfl

end M0Crypto.Release.Ed25519Sha512Exec
