import M0Crypto.Release.Ed25519DsmProg
import M0Crypto.Release.Ed25519DecompressBlocks

/-!
# The public blocks of `m0c_ge_dsm`

Each block's effect is decided symbolically (`Eff`, `effOk`) and read as values:

* `scanG` (the top-digit scan, `dsm_scan`): `Z` exactly when both digit bytes at index `r0` are
  `0` (`scan_z`); `subs r0, #1` sets `N` exactly when `r0 = 0` (`dec_n`).
* `loopG` (`dsm_loop`): `ldr r0, [sp, #I]; cmp r0, #0`; `bge` continues exactly when `0 ≤ I`
  (`loop_ge`).
* `digG` (`dsm_load_digits`): `DA`, `DB` are the digit bytes at `I` sign-extended (`dig_run`).
* `orG` (`dsm_test_digits`): `Z` exactly when `DA = DB = 0` (`or_z`); `cmp r0, #0` after `ldr DA` or `DB`
  (`dsm_test_a`, `dsm_a_test_next`, `dsm_a_done`) by `cmp0_z`.
* `headA` (`dsm_a_index`): `r0 = sp + AI + 128 (|δ| / 2)` for the digit `δ` in `DA` (`headA_run`);
  `headB1` (`dsm_b_index`): `r0 = 96 (|δ| / 2)` for `δ` in `DB` (`headB1_run`), before the load of
  `m0c_ed_odd_b` and `adds r0, r1`.
* `tailG` (`dsm_a_table`, `dsm_b_entry` after its head): the pointers `EP`, `EA`, `EB` (the entry, its
  `y + x` and `y − x`, swapped for a negative digit) and `TZ`, `TT` (the destinations of `D + C`
  and `D − C`, swapped likewise) (`tail_run`).
* `decG` (`dsm_dec_index`): `I − 1` (`dec_run`).

`*_at` decide the instructions at their offsets in both builds. Over the digits `hd`, `sd` of
`dsmStep` (`digOf`, the signed bytes of the arrays at `H` and `S`): `scan_spec`, `dig_spec`,
`or_spec`, `one_spec`.
-/

namespace M0Crypto.Release.Ed25519DsmBlocks

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Sym (SExpr SBool SMem)
open M0Crypto.Release.BlockEffect (Eff effOk eff_run)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (dsm_a_done dsm_a_index dsm_a_table dsm_a_test_next dsm_b_entry dsm_b_index dsm_dec_index
  dsm_load_digits dsm_loop dsm_scan dsm_scan_dec dsm_test_a dsm_test_digits)

/-! ## The blocks -/

def scanG : List Instr := [.ldrSp 1 6, .memReg .ldrb 1 1 0, .ldrSp 2 5, .memReg .ldrb 2 2 0, .dp .orrs 1 2]
def loopG : List Instr := [.ldrSp 0 1, .cmpImm 0 0]
def digG : List Instr := [.ldrSp 1 6, .memReg .ldrb 1 1 0, .lslImm 1 1 24, .asrImm 1 1 24, .strSp 1 2,
  .ldrSp 1 5, .memReg .ldrb 1 1 0, .lslImm 1 1 24, .asrImm 1 1 24, .strSp 1 3]
def orG : List Instr := [.ldrSp 0 2, .ldrSp 1 3, .dp .orrs 0 1]
def headA : List Instr := [.ldrSp 0 2, .lsrImm 1 0 31, .dp .rsbs 1 1, .dp .eors 0 1, .subReg 0 0 1, .lsrImm 0 0 1,
  .lslImm 0 0 7, .addRdSp 1 108, .addReg 0 0 1]
def headB1 : List Instr := [.ldrSp 0 3, .lsrImm 1 0 31, .dp .rsbs 1 1, .dp .eors 0 1, .subReg 0 0 1, .lsrImm 0 0 1,
  .movImm 1 96, .dp .muls 0 1]
/-- The pointers from `r0 = EP` and the sign of the digit word at `sp + 4 ds`. -/
def tailG (ds : Nat) : List Instr :=
  [.strSp 0 4, .ldrSp 0 (BitVec.ofNat 8 ds), .lsrImm 0 0 31, .lslImm 0 0 5, .ldrSp 1 4, .addReg 2 1 0, .strSp 2 8,
   .addImm8 1 32, .subReg 1 1 0, .strSp 1 9, .addRdSp 1 60, .addReg 2 1 0, .strSp 2 10, .addImm8 1 32,
   .subReg 1 1 0, .strSp 1 11]
def decG : List Instr := [.ldrSp 0 1, .subImm8 0 1, .strSp 0 1]

theorem scan_at (b : Build) : seqAt b.bytes dsm_scan scanG = true ∧ seqAt b.bytes dsm_scan_dec [.subImm8 0 1] = true := by
  cases b <;> (rw [seqAt_eq_scan, seqAt_eq_scan]; decide +kernel)
theorem loop_at (b : Build) : seqAt b.bytes dsm_loop loopG = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem dig_at (b : Build) : seqAt b.bytes dsm_load_digits digG = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem or_at (b : Build) : seqAt b.bytes dsm_test_digits orG = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem da_at (b : Build) : seqAt b.bytes dsm_test_a [.ldrSp 0 2, .cmpImm 0 0] = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem ptrA_at (b : Build) : seqAt b.bytes dsm_a_index (headA ++ tailG 2) = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem db_at (b : Build) :
    seqAt b.bytes dsm_a_test_next [.ldrSp 0 3, .cmpImm 0 0] = true ∧ seqAt b.bytes dsm_a_done [.ldrSp 0 3, .cmpImm 0 0] = true := by
  cases b <;> (rw [seqAt_eq_scan, seqAt_eq_scan]; decide +kernel)
theorem ptrB_at (b : Build) : seqAt b.bytes dsm_b_index (headB1 ++ [.ldrLit 1 48, .addPc 1, .addReg 0 0 1] ++ tailG 3) = true := by
  cases b <;> (rw [seqAt_eq_scan]; decide +kernel)
theorem dec_at (b : Build) : seqAt b.bytes dsm_dec_index decG = true := by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)

/-! ## The decided effects -/

def spW (o : Nat) : SExpr := .add (.reg0 13) (.const (BitVec.ofNat 32 o))
def dW (o : Nat) : SExpr := .ld32 .mem0 (spW o)
def byteAt (o : Nat) : SExpr := .ld8 .mem0 (.add (dW o) (.reg0 0))
def sh (d : SExpr) : SExpr := .lsl (.lsr d 31) 5
def mk (d : SExpr) : SExpr := .add (.not (.lsr d 31)) (.const 1#32)
def absE (d : SExpr) : SExpr := .sub (.xor d (mk d)) (mk d)
def sext (b : SExpr) : SExpr := .asr (.lsl b 24) 24

def eScan : Eff := { regs := [], clob := [1, 2], z := some (.isZero (.or (byteAt oHp) (byteAt oSp))) }
/-- The second byte is read after the store of `DA`. -/
def vDb : SExpr := sext (.ld8 (.w32 .mem0 (spW oDa) (sext (byteAt oHp))) (.add (dW oSp) (.reg0 0)))
def eDig : Eff :=
  { clob := [1], mem := some (.w32 (.w32 .mem0 (spW oDa) (sext (byteAt oHp))) (spW oDb) vDb),
    reads := [(spW oDa, sext (byteAt oHp)), (spW oDb, vDb)] }
def eOr : Eff := { clob := [0, 1], z := some (.isZero (.or (dW oDa) (dW oDb))) }
def eHeadA : Eff := { regs := [(0, .add (.lsl (.lsr (absE (dW oDa)) 1) 7) (spW oAI))], clob := [1] }
def eHeadB1 : Eff := { regs := [(0, .mul (.const 96#32) (.lsr (absE (dW oDb)) 1))], clob := [1] }
def eTail (ds : Nat) : Eff :=
  let ws := [(spW oEp, .reg0 0), (spW oEa, .add (.reg0 0) (sh (dW (4 * ds)))),
      (spW oEb, .sub (.add (.reg0 0) (.const 32#32)) (sh (dW (4 * ds)))),
      (spW oTz, .add (spW (oT + 64)) (sh (dW (4 * ds)))), (spW oTt, .sub (spW (oT + 96)) (sh (dW (4 * ds))))]
  { clob := [0, 1, 2], mem := some (ws.foldl (fun m (a, v) => .w32 m a v) .mem0), reads := ws }
def eDec : Eff :=
  { clob := [0], mem := some (.w32 .mem0 (spW oI) (.add (dW oI) (.const 0xffffffff#32))),
    reads := [(spW oI, .add (dW oI) (.const 0xffffffff#32))] }
def eLoop : Eff := { regs := [(0, dW oI)] }

theorem effs_ok : effOk scanG eScan = true ∧ effOk digG eDig = true ∧ effOk orG eOr = true ∧
    effOk headA eHeadA = true ∧ effOk headB1 eHeadB1 = true ∧ effOk (tailG 2) (eTail 2) = true ∧
    effOk (tailG 3) (eTail 3) = true ∧ effOk decG eDec = true ∧ effOk [.ldrSp 0 1] eLoop = true := by
  decide +kernel

/-! ## Words -/

theorem toInt_cond (w : Word) : w.toInt = if w.toNat < 2 ^ 31 then (w.toNat : Int) else (w.toNat : Int) - 2 ^ 32 := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : w.toNat < 2 ^ 31
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]; rfl

theorem shr31 (w : Word) : w >>> 31 = if w.toNat < 2 ^ 31 then 0#32 else 1#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  split <;> simp <;> omega

/-- `(w ⊕ m) − m` with `m = −(w >>> 31)`: the absolute value of the signed word. -/
theorem abs_toNat (w : Word) :
    ((w ^^^ (~~~(w >>> 31) + 1#32)) - (~~~(w >>> 31) + 1#32)).toNat = w.toInt.natAbs := by
  rw [shr31, toInt_cond]
  have := w.isLt
  by_cases hw : w.toNat < 2 ^ 31
  · simp only [hw, ↓reduceIte]
    rw [show ~~~(0#32) + 1#32 = 0#32 from by decide, BitVec.xor_zero, BitVec.sub_zero, Int.natAbs_natCast]
  · simp only [hw, ↓reduceIte]
    rw [show ~~~(1#32) + 1#32 = BitVec.allOnes 32 from by decide, BitVec.xor_allOnes,
      show (w.toNat : Int) - 2 ^ 32 = -((2 ^ 32 - w.toNat : Nat) : Int) by omega, Int.natAbs_neg, Int.natAbs_natCast,
      BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes]
    omega

/-- The sign bit of a word, times 32. -/
theorem sh_toNat (w : Word) : ((w >>> 31) <<< 5).toNat = if w.toInt < 0 then 32 else 0 := by
  rw [shr31, toInt_cond]
  have := w.isLt
  by_cases hw : w.toNat < 2 ^ 31
  · rw [ite_eq_left hw, ite_eq_left hw, ite_eq_right (by omega)]; rfl
  · rw [ite_eq_right hw, ite_eq_right hw, ite_eq_left (by omega)]; rfl

/-- `lsls #24; asrs #24` of a byte: the byte read as signed. -/
theorem sext_toInt (b : BitVec 8) : ((b.setWidth 32 <<< 24).sshiftRight 24).toInt = b.toInt := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, toInt_cond, BitVec.toInt_eq_toNat_cond]
  have hb := b.isLt
  have hn : (b.setWidth 32 <<< 24).toNat = b.toNat * 2 ^ 24 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hn]
  by_cases h : b.toNat < 128
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]; omega
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega

/-! ## The blocks' values -/

open M0Crypto.Release.Ed25519DecompressProg (cmp0_z awc_not)

theorem dW_den (t : State) (o : Nat) : (dW o).denote t = read32 t.mem (t.regs 13 + BitVec.ofNat 32 o) := rfl

/-- The entry offset `128 (|δ| / 2)` or `96 (|δ| / 2)` of a small digit. -/
theorem idx_eq (x : Word) (c k : Nat) (hk : k = 2 ^ c) :
    (x >>> 1) <<< c = BitVec.ofNat 32 (k * (x.toNat / 2)) := by
  subst hk
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, Nat.pow_one, Nat.mul_comm]

/-- **`DA`'s entry in `AI`**: `r0 = sp + AI + 128 (|δ| / 2)`; memory unchanged. -/
theorem headA_run (t : State) :
    (execAll headA t).regs 0 = t.regs 13 + BitVec.ofNat 32
      (oAI + 128 * ((read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDa)).toInt.natAbs / 2)) ∧
    (execAll headA t).mem = t.mem := by
  have H := eff_run effs_ok.2.2.2.1 t
  refine ⟨?_, H.mem _ rfl⟩
  rw [H.reg 0 (by decide) (by decide)]
  show SExpr.denote t (.add (.lsl (.lsr (absE (dW oDa)) 1) 7) (spW oAI)) = _
  simp only [absE, mk, SExpr.denote, SMem.denote, dW, spW]
  generalize read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDa) = w
  rw [idx_eq _ 7 128 rfl, abs_toNat, BitVec.add_comm, ofNat_add_assoc]

/-- **`DB`'s entry offset in `m0c_ed_odd_b`**: `r0 = 96 (|δ| / 2)`; memory unchanged. -/
theorem headB1_run (t : State) :
    (execAll headB1 t).regs 0 = BitVec.ofNat 32 (96 * ((read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDb)).toInt.natAbs / 2)) ∧
    (execAll headB1 t).mem = t.mem := by
  have H := eff_run effs_ok.2.2.2.2.1 t
  refine ⟨?_, H.mem _ rfl⟩
  rw [H.reg 0 (by decide) (by decide)]
  show SExpr.denote t (.mul (.const 96#32) (.lsr (absE (dW oDb)) 1)) = _
  simp only [absE, mk, SExpr.denote, SMem.denote, dW, spW]
  generalize read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDb) = w
  have hw := abs_toNat w
  generalize (w ^^^ (~~~(w >>> 31) + 1#32)) - (~~~(w >>> 31) + 1#32) = x at hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hw]

/-- The pointers' sign: `32` for a negative digit word. -/
def sg (w : Word) : Nat := if w.toInt < 0 then 32 else 0

theorem sh_den (t : State) (o : Nat) :
    (sh (dW o)).denote t = BitVec.ofNat 32 (sg (read32 t.mem (t.regs 13 + BitVec.ofNat 32 o))) := by
  apply BitVec.eq_of_toNat_eq
  show (((dW o).denote t >>> 31) <<< 5).toNat = _
  rw [sh_toNat, dW_den, sg, BitVec.toNat_ofNat]
  split <;> rfl

/-- **The pointers**: from `r0 = EP` and the digit word `w` at `sp + 4 ds`, `EP`, `EA = EP + sg`,
`EB = EP + 32 − sg`, `TZ = sp + T + 64 + sg`, `TT = sp + T + 96 − sg`. -/
theorem tail_run (u : State) (ds : Nat) (hds : ds = 2 ∨ ds = 3) :
    let w := read32 u.mem (u.regs 13 + BitVec.ofNat 32 (4 * ds))
    let m := (execAll (tailG ds) u).mem
    read32 m (u.regs 13 + BitVec.ofNat 32 oEp) = u.regs 0 ∧
    read32 m (u.regs 13 + BitVec.ofNat 32 oEa) = u.regs 0 + BitVec.ofNat 32 (sg w) ∧
    read32 m (u.regs 13 + BitVec.ofNat 32 oEb) = u.regs 0 + 32#32 - BitVec.ofNat 32 (sg w) ∧
    read32 m (u.regs 13 + BitVec.ofNat 32 oTz) = u.regs 13 + BitVec.ofNat 32 (oT + 64) + BitVec.ofNat 32 (sg w) ∧
    read32 m (u.regs 13 + BitVec.ofNat 32 oTt) = u.regs 13 + BitVec.ofNat 32 (oT + 96) - BitVec.ofNat 32 (sg w) := by
  intro w m
  have H : BlockEffect.Holds (tailG ds) (eTail ds) u := by
    rcases hds with rfl | rfl
    · exact eff_run effs_ok.2.2.2.2.2.1 u
    · exact eff_run effs_ok.2.2.2.2.2.2.1 u
  have r0 := H.rd (spW oEp) (.reg0 0) (List.mem_cons_self ..)
  have r1 := H.rd (spW oEa) (.add (.reg0 0) (sh (dW (4 * ds)))) (by simp [eTail])
  have r2 := H.rd (spW oEb) (.sub (.add (.reg0 0) (.const 32#32)) (sh (dW (4 * ds)))) (by simp [eTail])
  have r3 := H.rd (spW oTz) (.add (spW (oT + 64)) (sh (dW (4 * ds)))) (by simp [eTail])
  have r4 := H.rd (spW oTt) (.sub (spW (oT + 96)) (sh (dW (4 * ds)))) (by simp [eTail])
  simp only [SExpr.denote, sh_den] at r0 r1 r2 r3 r4
  exact ⟨r0, r1, r2, r3, r4⟩

/-! ## The tests -/

theorem byte_zero (b : BitVec 8) : b.setWidth 32 = 0#32 ↔ b = 0#8 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
    exact BitVec.eq_of_toNat_eq this
  · rintro rfl; rfl

/-- **The top-digit scan**: `Z` exactly when both digit bytes at index `r0` are `0`. -/
theorem scan_z (t : State) :
    (execAll scanG t).z = true ↔
      t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oHp) + t.regs 0) = 0#8 ∧
      t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0) = 0#8 := by
  rw [(eff_run effs_ok.1 t).z _ rfl]
  show ((read8 _ _ ||| read8 _ _) == 0#32) = true ↔ _
  rw [beq_iff_eq, BitVec.or_eq_zero_iff, read8, read8, byte_zero, byte_zero]; rfl

/-- `subs r0, #1` (`dsm_scan_dec`): `N` exactly when `r0 = 0`, for `r0 ≤ 2^31`; `r0` becomes `r0 − 1`. -/
theorem dec_n (t : State) (h : (t.regs 0).toNat ≤ 2 ^ 31) :
    (((Instr.subImm8 0 1).next t).n = true ↔ t.regs 0 = 0#32) ∧
    ((Instr.subImm8 0 1).next t).regs 0 = t.regs 0 - 1#32 := by
  have e := awc_not (t.regs 0) 1#32
  have e0 : LowReg.toReg 0 = 0 := rfl
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, State.reg, State.setNZ, e0] at e ⊢
  rw [e]
  refine ⟨?_, rfl⟩
  constructor
  · intro h2
    rw [BitVec.msb_eq_decide, decide_eq_true_iff, BitVec.toNat_sub] at h2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat] at h2 ⊢; omega
  · intro h2; rw [h2]; decide

/-- `cmp r, #0`: `N = V` exactly when `0 ≤ r` as a signed word. -/
theorem cmp0_ge (s : State) (n : LowReg) :
    (((Instr.cmpImm n 0).next s).n == ((Instr.cmpImm n 0).next s).v) = decide (0 ≤ (s.regs n.toReg).toInt) := by
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, State.reg,
    M0Crypto.Armv6M.addWithCarry, State.setNZ]
  generalize s.regs n.toReg = x
  have hx : BitVec.ofNat 32 (x.toNat + 4294967295 + 1) = x := by
    apply BitVec.eq_of_toNat_eq; have := x.isLt; simp only [BitVec.toNat_ofNat]; omega
  rw [hx, show x.toInt + -1 + 1 = x.toInt by omega, BitVec.msb_eq_decide, BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [decide_eq_true (by omega : 2 ^ (32 - 1) ≤ x.toNat), ite_eq_right (by omega)]
    have : ¬(0 ≤ (x.toNat : Int) - ((2 ^ 32 : Nat) : Int)) := by
      rw [show ((2 ^ 32 : Nat) : Int) = 4294967296 from rfl]; omega
    rw [decide_eq_false this]; simp
  · rw [decide_eq_false (by omega : ¬2 ^ (32 - 1) ≤ x.toNat), ite_eq_left (by omega)]
    rw [decide_eq_true (by omega)]; rfl

/-- **The loop test** (`dsm_loop`, then `bge`): continues exactly when `0 ≤ I`. -/
theorem loop_ge (t : State) :
    ((execAll loopG t).n == (execAll loopG t).v) = true ↔ 0 ≤ (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oI)).toInt := by
  have e : execAll loopG t = (Instr.cmpImm 0 0).next (execAll [.ldrSp 0 1] t) := rfl
  rw [e, cmp0_ge, decide_eq_true_iff]
  rw [show LowReg.toReg 0 = 0 from rfl, (eff_run effs_ok.2.2.2.2.2.2.2.2 t).reg 0 (by decide) (by decide)]
  rfl

/-- **Both digits zero** (`dsm_test_digits`): `Z` exactly when `DA = DB = 0`. -/
theorem or_z (t : State) :
    (execAll orG t).z = true ↔
      read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDa) = 0#32 ∧ read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDb) = 0#32 := by
  rw [(eff_run effs_ok.2.2.1 t).z _ rfl]
  show ((read32 _ _ ||| read32 _ _) == 0#32) = true ↔ _
  rw [beq_iff_eq, BitVec.or_eq_zero_iff]; rfl

/-- **The digits** (`dsm_load_digits`): `DA` and `DB` are the digit bytes at index `r0` read as signed,
when `S`'s byte is not in `DA`'s word. -/
theorem dig_run (t : State)
    (hs : ∀ k < 4, read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0 ≠
      t.regs 13 + BitVec.ofNat 32 oDa + BitVec.ofNat 32 k) :
    (read32 (execAll digG t).mem (t.regs 13 + BitVec.ofNat 32 oDa)).toInt =
      (t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oHp) + t.regs 0)).toInt ∧
    (read32 (execAll digG t).mem (t.regs 13 + BitVec.ofNat 32 oDb)).toInt =
      (t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0)).toInt ∧
    (execAll digG t).mem = (SMem.w32 (.w32 .mem0 (spW oDa) (sext (byteAt oHp))) (spW oDb) vDb).denote t := by
  have H := eff_run effs_ok.2.1 t
  have ra := H.rd _ _ (List.mem_cons_self ..)
  have rb := H.rd (spW oDb) vDb (by simp [eDig])
  refine ⟨?_, ?_, H.mem _ rfl⟩
  · change read32 _ (t.regs 13 + BitVec.ofNat 32 oDa) = _ at ra
    rw [ra]; exact sext_toInt _
  · change read32 _ (t.regs 13 + BitVec.ofNat 32 oDb) = _ at rb
    rw [rb]
    have hw : M0Crypto.Armv6M.write32 t.mem ((spW oDa).denote t) ((sext (byteAt oHp)).denote t)
        (((dW oSp).add (.reg0 0)).denote t) = t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0) :=
      M0Crypto.Armv6M.write32_other _ _ _ _ hs
    show ((read8 (M0Crypto.Armv6M.write32 t.mem _ _) _ <<< 24).sshiftRight 24).toInt = _
    rw [read8, hw]
    exact sext_toInt _

/-- **The index step** (`dsm_dec_index`): `I` becomes `I − 1`; nothing else in memory changes. -/
theorem dec_run (t : State) :
    (execAll decG t).mem = M0Crypto.Armv6M.write32 t.mem (t.regs 13 + BitVec.ofNat 32 oI)
      (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oI) - 1#32) := by
  rw [(eff_run effs_ok.2.2.2.2.2.2.2.1 t).mem _ rfl]
  show M0Crypto.Armv6M.write32 _ _ (_ + 0xffffffff#32) = _
  rw [show ∀ x : Word, x + 0xffffffff#32 = x - 1#32 from fun x => by bv_omega]; rfl

/-! ## Over the digits

`dsmStep sd hd` tests `hd i = 0` and `sd i = 0`; the digits are the signed bytes of the
arrays at `H` and `S`. -/

/-- The signed byte `i` of the array at `p`. -/
def digOf (m : Mem) (p : Word) (i : Nat) : Int := (m (p + BitVec.ofNat 32 i)).toInt

theorem toInt_zero {n : Nat} (b : BitVec n) : b.toInt = 0 ↔ b = 0#n := by
  constructor
  · intro h; exact BitVec.eq_of_toInt_eq (by rw [h]; simp)
  · rintro rfl; simp

/-- **The scan over the digits**: at index `i`, `Z` exactly when `hd i = sd i = 0`. -/
theorem scan_spec (t : State) (i : Nat) (hi : t.regs 0 = BitVec.ofNat 32 i) :
    (execAll scanG t).z = true ↔
      digOf t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oHp)) i = 0 ∧
      digOf t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp)) i = 0 := by
  rw [scan_z, hi, digOf, digOf, toInt_zero, toInt_zero]

/-- **The digits at `i`**: `DA = hd i`, `DB = sd i`. -/
theorem dig_spec (t : State) (i : Nat) (hi : t.regs 0 = BitVec.ofNat 32 i)
    (hs : ∀ k < 4, read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp) + t.regs 0 ≠
      t.regs 13 + BitVec.ofNat 32 oDa + BitVec.ofNat 32 k) :
    (read32 (execAll digG t).mem (t.regs 13 + BitVec.ofNat 32 oDa)).toInt =
      digOf t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oHp)) i ∧
    (read32 (execAll digG t).mem (t.regs 13 + BitVec.ofNat 32 oDb)).toInt =
      digOf t.mem (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oSp)) i := by
  have h := dig_run t hs
  rw [hi] at h
  exact ⟨h.1, h.2.1⟩

/-- **Both digits zero, over the digits**: from `DA = hd i`, `DB = sd i`. -/
theorem or_spec (t : State) (hd sd : Int)
    (ha : (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDa)).toInt = hd)
    (hb : (read32 t.mem (t.regs 13 + BitVec.ofNat 32 oDb)).toInt = sd) :
    (execAll orG t).z = true ↔ hd = 0 ∧ sd = 0 := by
  rw [or_z, ← toInt_zero, ← toInt_zero, ha, hb]

/-- **One digit zero** (`ldr DA` or `DB`, `cmp r0, #0`): `Z` exactly when the digit is `0`. -/
theorem one_spec (u : State) (d : Int) (hd : (u.regs 0).toInt = d) :
    ((Instr.cmpImm 0 0).next u).z = true ↔ d = 0 := by
  rw [cmp0_z, show LowReg.toReg 0 = 0 from rfl, beq_iff_eq, ← toInt_zero, hd]

end M0Crypto.Release.Ed25519DsmBlocks
