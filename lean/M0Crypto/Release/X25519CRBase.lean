import M0Crypto.Release.X25519Diff

set_option linter.unusedSimpArgs false

/-!
Helpers for the machine proof of `X25519Macros.combineReduce` (the fused Karatsuba combine
and reduction of `m0c_fe_mul` and `m0c_fe_sqr`): frame words by slot, address
normalisation, reads through slot and buffer writes, and the register-list facts of the
`ldm`/`stm` masks the macro uses.

`fr m sp k` is the word in frame slot `k`. A load of the macro produces an address
`sp + ofNat a + ofNat b + …`; `addr_slot` turns it into `slot sp k` once the offsets add up to
`4 * k` (checked by `omega`, never written as a literal in a statement).
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

/-- Frame slot `k` of memory `m` with frame pointer `sp`. -/
def fr (m : Mem) (sp : Word) (k : Nat) : Word := read32 m (slot sp k)

theorem listRegs_60 : listRegs 0x60 = [5, 6] := by decide
theorem listRegs_30 : listRegs 0x30 = [4, 5] := by decide
theorem listRegs_03 : listRegs 0x03 = [0, 1] := by decide
theorem listRegs_0f : listRegs 0x0f = [0, 1, 2, 3] := by decide
theorem bitCount_60 : bitCount 0x60 = 2 := by decide
theorem bitCount_30 : bitCount 0x30 = 2 := by decide
theorem bitCount_03 : bitCount 0x03 = 2 := by decide
theorem bitCount_0f : bitCount 0x0f = 4 := by decide

theorem sl_toNat (k : Nat) : (X25519Macros.sl k).toNat = k % 256 := by
  simp [X25519Macros.sl]

/-- An address `sp + ofNat a` is slot `k` when `a = 4 * k`. -/
theorem addr_slot (sp : Word) {a k : Nat} (h : a = 4 * k) : sp + BitVec.ofNat 32 a = slot sp k := by
  rw [h]; rfl

theorem addr2 (sp : Word) (a b : Nat) :
    sp + BitVec.ofNat 32 a + BitVec.ofNat 32 b = sp + BitVec.ofNat 32 (a + b) :=
  ofNat_add_assoc sp a b

/-- `subs rd, #i` on an address `a + (x + c)` with `i ≤ c`. -/
theorem sub_imm (a : Word) (x c : Nat) (i : BitVec 8) (h : i.toNat ≤ c) :
    (addWithCarry (a + BitVec.ofNat 32 (x + c)) (~~~(i.setWidth 32)) true).1 =
      a + BitVec.ofNat 32 (x + (c - i.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have := i.isLt; have := a.isLt
  simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_not,
    BitVec.toNat_setWidth, Bool.toNat_true]
  omega

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := by
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this; omega

/-- Two distinct frame slots do not share a byte. -/
theorem slot_bytes_ne (sp : Word) {i j p q : Nat} (hi : i < 2 ^ 28) (hj : j < 2 ^ 28)
    (hij : i ≠ j) (hp : p < 4) (hq : q < 4) :
    slot sp j + BitVec.ofNat 32 p ≠ slot sp i + BitVec.ofNat 32 q := by
  simp only [slot, ofNat_add_assoc]
  intro e
  have e' := (BitVec.add_right_inj sp).mp e
  exact ofNat_ne (by omega) (by omega) (by omega) e'

/-- A word store to slot `i` leaves slot `j ≠ i`. -/
theorem fr_write_ne (m : Mem) (sp v : Word) {i j : Nat} (hi : i < 2 ^ 28) (hj : j < 2 ^ 28)
    (hij : i ≠ j) : fr (write32 m (slot sp i) v) sp j = fr m sp j := by
  unfold fr
  exact read32_congr fun p hp =>
    M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq => slot_bytes_ne sp hi hj hij hp hq

theorem fr_write_same (m : Mem) (sp v : Word) (i : Nat) : fr (write32 m (slot sp i) v) sp i = v :=
  M0Crypto.Armv6M.read32_write32_same _ _ _

/-- `storeWords` at slot `k` of the words `vs`, read at a slot `j` outside them. -/
theorem fr_store_out (sp : Word) {j : Nat} (hj : j < 2 ^ 27) :
    ∀ (vs : List Word) (m : Mem) (k : Nat), k + vs.length < 2 ^ 27 → (j < k ∨ k + vs.length ≤ j) →
      fr (storeWords m (slot sp k) vs) sp j = fr m sp j
  | [], _, _, _, _ => rfl
  | v :: vs, m, k, hk, hjk => by
    simp only [List.length_cons] at hk hjk
    simp only [storeWords]
    rw [show slot sp k + 4#32 = slot sp (k + 1) by
      rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl]; simp only [slot, ofNat_add_assoc]
      congr 2]
    rw [fr_store_out sp hj vs _ (k + 1) (by omega) (by omega)]
    exact fr_write_ne m sp v (by omega) (by omega) (by omega)

/-- `storeWords` at slot `k` of four words, read at slot `k + i`. -/
theorem fr_store4 (m : Mem) (sp : Word) (k : Nat) (hk : k < 2 ^ 26) (a b c d : Word) :
    fr (storeWords m (slot sp k) [a, b, c, d]) sp k = a ∧
    fr (storeWords m (slot sp k) [a, b, c, d]) sp (k + 1) = b ∧
    fr (storeWords m (slot sp k) [a, b, c, d]) sp (k + 2) = c ∧
    fr (storeWords m (slot sp k) [a, b, c, d]) sp (k + 3) = d := by
  have e : ∀ i, slot sp (k + i) + 4#32 = slot sp (k + i + 1) := fun i => by
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl]; simp only [slot, ofNat_add_assoc]
    congr 2
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  simp only [Nat.add_zero] at e0
  simp only [storeWords, e0, e1, e2, show k + 1 + 1 = k + 2 by omega, show k + 2 + 1 = k + 3 by omega]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fr_write_ne _ _ _ (by omega) (by omega) (by omega),
      fr_write_ne _ _ _ (by omega) (by omega) (by omega),
      fr_write_ne _ _ _ (by omega) (by omega) (by omega), fr_write_same]
  · rw [fr_write_ne _ _ _ (by omega) (by omega) (by omega),
      fr_write_ne _ _ _ (by omega) (by omega) (by omega), fr_write_same]
  · rw [fr_write_ne _ _ _ (by omega) (by omega) (by omega), fr_write_same]
  · rw [fr_write_same]

/-- A word store into a buffer `[a, a + 32)` disjoint from the first `n` frame words leaves
those frame words. -/
theorem fr_write_disj (m : Mem) (sp a v : Word) {n j o : Nat} (hd : Disj a 32 sp (4 * n))
    (hj : j < n) (ho : o + 4 ≤ 32) :
    fr (write32 m (a + BitVec.ofNat 32 o) v) sp j = fr m sp j := by
  obtain ⟨h1, h2, h3⟩ := hd
  unfold fr
  refine read32_congr fun p hp => M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq e => ?_
  simp only [slot, ofNat_add_assoc] at e
  have := congrArg BitVec.toNat e
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega

end M0Crypto.Release.X25519CR

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (State LowReg Reg)
open M0Crypto.Thumb

/-! Memory is unchanged by the register-only instruction forms. -/
theorem mem_dp (s : State) (op : DpOp) (d m : LowReg) : ((Instr.dp op d m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_addReg (s : State) (d n m : LowReg) : ((Instr.addReg d n m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_subReg (s : State) (d n m : LowReg) : ((Instr.subReg d n m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_movHi (s : State) (d m : Reg) : ((Instr.movHi d m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_lsl (s : State) (d m : LowReg) (i : BitVec 5) : ((Instr.lslImm d m i).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_lsr (s : State) (d m : LowReg) (i : BitVec 5) : ((Instr.lsrImm d m i).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_uxth (s : State) (d m : LowReg) : ((Instr.uxth d m).next s).mem = s.mem :=
  next_mem rfl s
theorem mem_subImm8 (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.subImm8 d i).next s).mem = s.mem :=
  next_mem rfl s

end M0Crypto.Release.X25519CR

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Mem read32 slot)

/-- A load at `sp + a` with `a` a multiple of 4 is the frame word `a / 4`. Used by `simp`
with an `omega` discharger, so offsets are never written out. -/
theorem rd_norm (m : Mem) (sp : Word) (a : Nat) (h : a % 4 = 0) :
    read32 m (sp + BitVec.ofNat 32 a) = fr m sp (a / 4) := by
  unfold fr slot; rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)]

theorem div4 (k j : Nat) : (k * 4 + j) / 4 = k + j / 4 := by omega
theorem div4' (k : Nat) : k * 4 / 4 = k := by omega

end M0Crypto.Release.X25519CR
