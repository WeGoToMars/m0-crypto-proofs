import M0Crypto.Sym.Norm
import M0Crypto.Release.Field25519Mul

/-!
# The effect of a straight-line block, decided

`Eff` states what a block does: the registers it sets, as syntax over its entry state (`regs`),
the registers it leaves unspecified (`clob`), optionally the `Z` and `C` flags, and its memory as
stores over the entry memory (`mem`). Every other register is kept. `effOk is E` compares the
normalised symbolic run of `is` (`Sym.symExec`, `Sym.norm`) with `E`, register by register, so
a decided `effOk` gives the whole effect at once (`eff_run`): no per-instruction rules and no
proof that a register is kept.

`mulS` names the two words of macro `mul32` in any registers from its inputs, as the executor
forms them, and `mulS_nat` is their product, so blocks around `mul32` state their effect through
it. `acc2_nat` is the 64-bit accumulation `adds lo, d; adcs hi, #0; adds lo, c; adcs hi, #0`.
`subS`, `cnt` and `cmp_ne` are the `subs`/`cmp` of a loop counter and its `bne`.
-/

namespace M0Crypto.Release.BlockEffect

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Sym

-- `norm` leaves the carry of an `awc` and the memory of a load as written, so they are normalised
-- first (`dN`, `dB`, `dM`): a carry or a load built from `ld32 (r + 0)` then equals one from `ld32 r`.
mutual
def dN : SExpr → SExpr
  | .awc a b c => .awc (dN a) (dN b) (dB c)
  | .add a b => .add (dN a) (dN b)
  | .sub a b => .sub (dN a) (dN b)
  | .and a b => .and (dN a) (dN b)
  | .or a b => .or (dN a) (dN b)
  | .xor a b => .xor (dN a) (dN b)
  | .not a => .not (dN a)
  | .lsl a n => .lsl (dN a) n
  | .lsr a n => .lsr (dN a) n
  | .ld32 m a => .ld32 (dM m) (dN a)
  | e => e

/-- `norm` inside a flag. -/
def dB : SBool → SBool
  | .msb a => .msb (norm (dN a))
  | .isZero a => .isZero (norm (dN a))
  | .awcC a b c => .awcC (norm (dN a)) (norm (dN b)) (dB c)
  | .awcV a b c => .awcV (norm (dN a)) (norm (dN b)) (dB c)
  | b => b

/-- `norm` in the addresses and values of stores. -/
def dM : SMem → SMem
  | .mem0 => .mem0
  | .w32 m a v => .w32 (dM m) (norm (dN a)) (norm (dN v))
  | .w16 m a v => .w16 (dM m) (norm (dN a)) (norm (dN v))
  | .w8 m a v => .w8 (dM m) (norm (dN a)) (norm (dN v))
end

mutual
theorem dN_sound (s : State) : ∀ e : SExpr, (dN e).denote s = e.denote s
  | .awc a b c => by simp only [dN, SExpr.denote, dN_sound s a, dN_sound s b, dB_sound s c]
  | .add a b | .sub a b | .and a b | .or a b | .xor a b => by
    simp only [dN, SExpr.denote, dN_sound s a, dN_sound s b]
  | .not a | .lsl a _ | .lsr a _ => by simp only [dN, SExpr.denote, dN_sound s a]
  | .ld32 m a => by simp only [dN, SExpr.denote, dN_sound s a, dM_sound s m]
  | .reg0 _ | .const _ | .mul .. | .uxth _ | .ror .. | .lslR .. | .lsrR .. | .asr .. | .rev _
  | .ld16 .. | .ld8 .. | .rotl .. => rfl

theorem dB_sound (s : State) : ∀ b : SBool, (dB b).denote s = b.denote s
  | .msb a | .isZero a => by simp only [dB, SBool.denote, norm_sound, dN_sound s a]
  | .awcC a b c | .awcV a b c => by
    simp only [dB, SBool.denote, norm_sound, dN_sound s a, dN_sound s b, dB_sound s c]
  | .n0 | .z0 | .c0 | .v0 | .const _ | .lslC .. | .lsrC .. | .rorC .. | .lslRC .. | .lsrRC ..
  | .asrC .. => rfl

theorem dM_sound (s : State) : ∀ m : SMem, (dM m).denote s = m.denote s
  | .mem0 => rfl
  | .w32 m a v | .w16 m a v | .w8 m a v => by
    simp only [dM, SMem.denote, dM_sound s m, norm_sound, dN_sound]
end

/-- The normal form the check compares. -/
def nf (e : SExpr) : SExpr := norm (dN e)

theorem nf_sound (s : State) (e : SExpr) : (nf e).denote s = e.denote s := by
  rw [nf, norm_sound, dN_sound]

/-- **The effect of a block**: the registers set (`regs`, first match), those left unspecified
(`clob`), the flags if stated, the memory. -/
structure Eff where
  regs : List (Reg × SExpr) := []
  clob : List Reg := []
  z : Option SBool := none
  c : Option SBool := none
  /-- The memory as stores over the entry memory, if stated (by default: unchanged). -/
  mem : Option SMem := some .mem0
  /-- Words read back after the block: at the address `a` (entry state), the value `v`. -/
  reads : List (SExpr × SExpr) := []

/-- Register `r` after the block: its entry in `regs`, else kept. -/
def Eff.reg (E : Eff) (r : Reg) : SExpr := ((E.regs.find? (·.1 = r)).map (·.2)).getD (.reg0 r)

/-- The decided check: `is` falls through and its normalised symbolic run is `E`. -/
def effOk (is : List Instr) (E : Eff) : Bool :=
  let S := symExec is SState.init
  is.all Instr.falls &&
  (List.finRange 16).all (fun r => r.val == 15 || E.clob.contains r || decide (nf (S.regs r) = nf (E.reg r))) &&
  E.z.all (fun z => decide (dB S.z = dB z)) && E.c.all (fun c => decide (dB S.c = dB c)) &&
  E.mem.all (fun m => decide (dM S.mem = dM m)) &&
  E.reads.all (fun p => decide (nf (.ld32 S.mem p.1) = nf p.2))

/-- What a decided `effOk is E` gives at the state `s`. -/
structure Holds (is : List Instr) (E : Eff) (s : State) : Prop where
  reg : ∀ r : Reg, r.val ≠ 15 → r ∉ E.clob → (execAll is s).regs r = (E.reg r).denote s
  z : ∀ z, E.z = some z → (execAll is s).z = z.denote s
  c : ∀ c, E.c = some c → (execAll is s).c = c.denote s
  mem : ∀ m, E.mem = some m → (execAll is s).mem = m.denote s
  rd : ∀ a v, (a, v) ∈ E.reads → read32 (execAll is s).mem (a.denote s) = v.denote s

theorem eff_run {is : List Instr} {E : Eff} (h : effOk is E = true) (s : State) : Holds is E s := by
  simp only [effOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.contains_iff_mem, Option.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hf, hr⟩, hz⟩, hc⟩, hm⟩, hrd⟩ := h
  have e := symExec_sound is (sound_all (List.all_eq_true.mpr hf)) s SState.init
  rw [SState.init_denote] at e
  refine ⟨fun r h15 hcl => ?_, fun z hz' => ?_, fun c hc' => ?_, fun m hm' => ?_, fun a v hav => ?_⟩ <;> rw [← e]
  · rcases hr r (List.mem_finRange r) with (h | h) | h
    · exact absurd h h15
    · exact absurd h hcl
    · rw [denote_regs, ← nf_sound, h, nf_sound]
  · show SBool.denote s _ = _; rw [← dB_sound, hz z hz', dB_sound]
  · show SBool.denote s _ = _; rw [← dB_sound, hc c hc', dB_sound]
  · show SMem.denote s _ = _; rw [← dM_sound, hm m hm', dM_sound]
  · rw [← nf_sound s v, ← hrd _ hav, nf_sound]; rfl

/-- What fails in `effOk is E` (not used by proofs): the registers, flags, memory or reads whose
normal forms differ. -/
def effFailure (is : List Instr) (E : Eff) : List String :=
  let S := symExec is SState.init
  (if is.all Instr.falls then [] else ["a block instruction does not fall through"]) ++
  ((List.finRange 16).filter (fun r => !(r.val == 15 || E.clob.contains r) &&
    !decide (nf (S.regs r) = nf (E.reg r)))).map (fun r => s!"r{r.val}") ++
  (if E.z.all (fun z => decide (dB S.z = dB z)) then [] else ["Z"]) ++
  (if E.c.all (fun c => decide (dB S.c = dB c)) then [] else ["C"]) ++
  (if E.mem.all (fun m => decide (dM S.mem = dM m)) then [] else ["memory"]) ++
  ((List.range E.reads.length).filter (fun k => (E.reads[k]?).all fun p =>
    !decide (nf (.ld32 S.mem p.1) = nf p.2))).map (fun k => s!"read {k}")

/-! ## `mul32` -/

open M0Crypto.Release.Field25519Mul (mul32 mul32_exec Dist5)

/-- The low and high words of `mul32 rl rh rb rt ru` with `x` in `rl` and `y` in `rb`. -/
def mulS (rl rh rb rt ru : LowReg) (x y : SExpr) : SExpr × SExpr :=
  let S := symExec (mul32 rl rh rb rt ru) ((SState.init.setReg rl.toReg x).setReg rb.toReg y)
  (S.regs rl.toReg, S.regs rh.toReg)

theorem mulS_nat {rl rh rb rt ru : LowReg} (h : Dist5 rl rh rb rt ru) (x y : SExpr) (s : State) :
    ((mulS rl rh rb rt ru x y).1.denote s).toNat + 2 ^ 32 * ((mulS rl rh rb rt ru x y).2.denote s).toNat =
      (x.denote s).toNat * (y.denote s).toNat := by
  have e := symExec_sound (mul32 rl rh rb rt ru) (sound_all (by simp [mul32, Instr.falls]))
    s ((SState.init.setReg rl.toReg x).setReg rb.toReg y)
  simp only [SState.denote_setReg, SState.init_denote] at e
  have hm := (mul32_exec ((s.setReg rl.toReg (x.denote s)).setReg rb.toReg (y.denote s)) rl rh rb rt ru h).1
  simp only [← e, State.reg, SState.denote] at hm
  have hne : rl.toReg ≠ rb.toReg := fun he => h.ac (by
    have := congrArg Fin.val he; simpa [LowReg.toReg] using this)
  simp only [mulS, hm, State.setReg, hne, ite_false, ite_true]

/-! ## A 64-bit accumulation -/

/-- `adds lo, d; adcs hi, #0; adds lo, c; adcs hi, #0` on `hi:lo = P ≤ (2^32 − 1)^2`: no carry is
lost. -/
theorem acc2_nat {lo hi d c : Word} {P : Nat} (hm : lo.toNat + 2 ^ 32 * hi.toNat = P)
    (hP : P ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1)) :
    (addWithCarry (addWithCarry lo d false).1 c false).1.toNat + 2 ^ 32 *
      (addWithCarry (addWithCarry hi 0#32 (addWithCarry lo d false).2.1).1 0#32
        (addWithCarry (addWithCarry lo d false).1 c false).2.1).1.toNat = P + d.toNat + c.toNat := by
  have a1 := Field25519Carry.adc_nat lo d false
  generalize addWithCarry lo d false = p1 at a1 ⊢
  have a2 := Field25519Carry.adc_nat p1.1 c false
  have a3 := Field25519Carry.adc_nat hi 0#32 p1.2.1
  generalize addWithCarry p1.1 c false = p2 at a2 ⊢
  generalize addWithCarry hi 0#32 p1.2.1 = p3 at a3 ⊢
  have a4 := Field25519Carry.adc_nat p3.1 0#32 p2.2.1
  generalize addWithCarry p3.1 0#32 p2.2.1 = p4 at a4 ⊢
  have := p1.2.1.toNat_le; have := p2.2.1.toNat_le; have := p3.2.1.toNat_le; have := p4.2.1.toNat_le
  have := p2.1.isLt; have := p3.1.isLt; have := p4.1.isLt; have := d.isLt; have := c.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Bool.toNat_false] at a1 a2 a3 a4
  omega

/-! ## Counters and shifts -/

/-- `x − k` as `subs` forms it. -/
def subS (x : SExpr) (k : Nat) : SExpr := .awc x (.const (~~~(BitVec.ofNat 32 k))) (.const true)

@[simp] theorem subS_denote (x : SExpr) (k : Nat) (u : State) :
    (subS x k).denote u = x.denote u - BitVec.ofNat 32 k := awc_not_true _ _

/-- `i · 4` and `x · 2` as shifts. -/
theorem lsl2 (i : Nat) : BitVec.ofNat 32 i <<< 2 = BitVec.ofNat 32 (4 * i) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
theorem lsl1 (x : Word) : x <<< 1 = BitVec.ofNat 32 (2 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- A count `m − j` down by one, and its `bne` taken exactly while passes remain. -/
theorem cnt {m j : Nat} (hj : j < m) (hm : m < 2 ^ 32) :
    BitVec.ofNat 32 (m - j) - 1#32 = BitVec.ofNat 32 (m - (j + 1)) ∧
    (!(BitVec.ofNat 32 (m - (j + 1)) == 0#32)) = decide (j + 1 < m) := by
  constructor
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · by_cases h : j + 1 < m
    · have : BitVec.ofNat 32 (m - (j + 1)) ≠ 0#32 := by
        intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
      simp [h, this]
    · have : BitVec.ofNat 32 (m - (j + 1)) = 0#32 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      simp [h, this]

/-- `cmp i + 1, y; bne`: taken exactly while `i + 1 < y`. -/
theorem cmp_ne {i : Nat} {y : Word} (h : i < y.toNat) :
    (!(BitVec.ofNat 32 (i + 1) - y == 0#32)) = decide (i + 1 < y.toNat) := by
  by_cases e : i + 1 < y.toNat
  · have : BitVec.ofNat 32 (i + 1) - y ≠ 0#32 := by
      intro h0; have := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    simp [e, this]
  · have : BitVec.ofNat 32 (i + 1) - y = 0#32 := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp [e, this]

/-- `condPassed` at `u.setReg 15 v`, in the form `simp [State.setReg]` leaves. -/
theorem cond_pc {u : State} {v : Word} {c : BitVec 4} :
    condPassed c { u with regs := fun i => if i = 15 then v else u.regs i } = condPassed c u := rfl

end M0Crypto.Release.BlockEffect
