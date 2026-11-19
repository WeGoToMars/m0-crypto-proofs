import M0Crypto.Release.Ed25519Words
import M0Crypto.Spec.Ed25519

/-!
Byte strings as numbers, clamping, and signed digit bytes.

* `decodeInt_lt`, `decodeInt_byte`, `decodeInt_bit`: the spec's little-endian `decodeInt`, its
  bytes and its bits. `decodeInt_bit` is what `m0c_sbit` and the bit reads of
  `m0c_sc_recode_comb` compute: bit `i` of the scalar is bit `i % 8` of byte `i / 8`.
* `secretScalar_eq`: the spec's pruning (RFC 8032 section 5.1.5, step 2) is `clampNat` of the
  first 32 digest bytes. `clamp_words` and `clamp_lo`, `clamp_hi`: the generator's `clamp` on
  words 0 and 7 of the digest computes `clampNat`.
* `sext_byte`, `digit_byte`: the signed digit bytes of `m0c_sc_wnaf`, stored with `strb` and
  read back with `ldrb; lsls #24; asrs #24`.
-/

namespace M0Crypto.Release.Ed25519Bytes

open M0Crypto.Release.Ed25519Words
open M0Crypto.Spec.Ed25519 (decodeInt secretScalar)

abbrev Byte := BitVec 8

/-! ## `decodeInt` -/

theorem decodeInt_cons (b : Byte) (bs : List Byte) :
    decodeInt (b :: bs) = 2 ^ 8 * decodeInt bs + b.toNat := by
  rw [decodeInt]; omega

theorem decodeInt_lt (bs : List Byte) : decodeInt bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [decodeInt]
  | cons b bs ih =>
    rw [decodeInt_cons, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have := b.isLt
    have := Nat.mul_le_mul_right (2 ^ 8) (Nat.succ_le_of_lt ih)
    rw [Nat.succ_mul] at this
    omega

/-- Byte `i` of `decodeInt bs`. -/
theorem decodeInt_byte (bs : List Byte) (i : Nat) :
    decodeInt bs / 2 ^ (8 * i) % 2 ^ 8 = (bs.getD i 0).toNat := by
  induction bs generalizing i with
  | nil => simp [decodeInt]
  | cons b bs ih =>
    have hb := b.isLt
    cases i with
    | zero => simp only [decodeInt_cons]; simp; omega
    | succ i =>
      rw [decodeInt_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * i)),
        ← Nat.div_div_eq_div_mul, Nat.mul_add_div (Nat.two_pow_pos 8),
        Nat.div_eq_of_lt hb, Nat.add_zero, ih]
      rfl

/-- Bit `i` of `decodeInt bs` is bit `i % 8` of byte `i / 8`. -/
theorem decodeInt_bit (bs : List Byte) (i : Nat) :
    decodeInt bs / 2 ^ i % 2 = (bs.getD (i / 8) 0).toNat / 2 ^ (i % 8) % 2 := by
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit]
  congr 1
  induction bs generalizing i with
  | nil => simp [decodeInt]
  | cons b bs ih =>
    rw [decodeInt_cons, Nat.testBit_two_pow_mul_add _ b.isLt]
    by_cases h : i < 8
    · rw [ite_eq_left h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; rfl
    · rw [ite_eq_right h, ih]
      have e1 : i / 8 = (i - 8) / 8 + 1 := by omega
      have e2 : i % 8 = (i - 8) % 8 := by omega
      rw [e1, e2]; rfl

/-! ## Clamping -/

/-- RFC 8032 section 5.1.5 step 2 on a 256-bit number: clear bits 0 to 2 and bit 255, set
bit 254. -/
def clampNat (s : Nat) : Nat := s % 2 ^ 254 - s % 8 + 2 ^ 254

theorem decodeInt_set (bs : List Byte) {i : Nat} (y : Byte) (hi : i < bs.length) :
    decodeInt (bs.set i y) + 2 ^ (8 * i) * (bs.getD i 0).toNat =
      decodeInt bs + 2 ^ (8 * i) * y.toNat := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero, decodeInt_cons]; simp; omega
    | succ i =>
      simp only [List.set_cons_succ, decodeInt_cons, List.getD_cons_succ]
      have := ih (i := i) (by simp at hi; omega)
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * i)), Nat.mul_assoc, Nat.mul_assoc]
      omega

theorem and_f8 (b : Byte) : (b &&& 0xf8#8).toNat = b.toNat - b.toNat % 8 := by
  have h : ∀ n : Fin (2 ^ 8), (BitVec.ofFin n &&& 0xf8#8).toNat =
      (BitVec.ofFin n).toNat - (BitVec.ofFin n).toNat % 8 := by decide +kernel
  exact h b.toFin

theorem and_7f_or_40 (b : Byte) :
    ((b &&& 0x7f#8) ||| 0x40#8).toNat = b.toNat % 64 + 64 := by
  have h : ∀ n : Fin (2 ^ 8), ((BitVec.ofFin n &&& 0x7f#8) ||| 0x40#8).toNat =
      (BitVec.ofFin n).toNat % 64 + 64 := by decide +kernel
  exact h b.toFin

/-- The spec's secret scalar is `clampNat` of the first 32 digest bytes. -/
theorem secretScalar_eq (h : List Byte) (hlen : 32 ≤ h.length) :
    secretScalar h = clampNat (decodeInt (h.take 32)) := by
  unfold secretScalar clampNat
  dsimp only
  generalize hb : h.take 32 = buf
  have hl : buf.length = 32 := by rw [← hb, List.length_take]; omega
  have hs := decodeInt_lt buf
  rw [hl] at hs
  have h0 := decodeInt_byte buf 0
  have h31 := decodeInt_byte buf 31
  have e1 := decodeInt_set buf (i := 0) (buf.getD 0 0 &&& 0xf8#8) (by omega)
  have hl1 : (buf.set 0 (buf.getD 0 0 &&& 0xf8#8)).length = 32 := by simp [hl]
  have e2 := decodeInt_set (buf.set 0 (buf.getD 0 0 &&& 0xf8#8)) (i := 31)
    (((buf.set 0 (buf.getD 0 0 &&& 0xf8#8)).getD 31 0 &&& 0x7f#8) ||| 0x40#8) (by omega)
  have g31 : (buf.set 0 (buf.getD 0 0 &&& 0xf8#8)).getD 31 0 = buf.getD 31 0 := by
    simp [List.getD_eq_getElem?_getD]
  rw [g31] at e2 ⊢
  rw [and_f8] at e1
  rw [and_7f_or_40] at e2
  generalize decodeInt buf = s at *
  generalize (buf.getD 0 0).toNat = b0 at *
  generalize (buf.getD 31 0).toNat = b31 at *
  generalize decodeInt (buf.set 0 (buf.getD 0 0 &&& 0xf8#8)) = s1 at *
  generalize decodeInt ((buf.set 0 (buf.getD 0 0 &&& 0xf8#8)).set 31
    ((buf.getD 31 0 &&& 0x7f#8) ||| 0x40#8)) = s2 at *
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.one_mul] at h0 e1 e2 h31
  rw [show 8 * 31 = 248 from rfl, show 8 * 32 = 256 from rfl] at *
  have d1 := Nat.div_add_mod s (2 ^ 248)
  have d2 := Nat.mod_lt s (Nat.two_pow_pos 248)
  generalize s / 2 ^ 248 = q at *
  omega

/-- The generator's `clamp` on the digest words: word 0 loses its low 3 bits and word 7 its top
2 bits, then gains bit 30. -/
theorem clamp_words {W W' : Nat → Nat} (hW : ∀ j, j < 8 → W j < 2 ^ 32)
    (h0 : W' 0 = W 0 - W 0 % 8) (h7 : W' 7 = W 7 % 2 ^ 30 + 2 ^ 30)
    (hmid : ∀ j, 0 < j → j < 7 → W' j = W j) :
    wsum W' 8 = clampNat (wsum W 8) := by
  have hm : wsum W' 7 + W 0 % 8 = wsum W 7 := by
    have e : wsum W' 7 = wsum (fun j => if j = 0 then W 0 - W 0 % 8 else W j) 7 :=
      wsum_congr (fun j hj => by
        by_cases hj0 : j = 0
        · subst hj0; simp [h0]
        · rw [ite_eq_right hj0, hmid j (by omega) hj])
    rw [e]
    simp only [wsum_succ, wsum_zero]
    simp
    omega
  have hlt7 := wsum_lt (n := 7) (fun j hj => hW j (by omega))
  have h70 := hW 7 (by omega)
  have hW0 : wsum W 7 % 8 = W 0 % 8 := by
    simp only [wsum_succ, wsum_zero]; omega
  unfold clampNat
  rw [wsum_succ W' 7, wsum_succ W 7, h7]
  rw [show 32 * 7 = 224 from rfl] at hlt7 ⊢
  omega

/-- `ldr; lsrs #3; lsls #3` on word 0. -/
theorem clamp_lo (w : BitVec 32) : ((w >>> 3) <<< 3).toNat = w.toNat - w.toNat % 8 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- `lsls #2; lsrs #2; orrs` with `1 << 30` on word 7. -/
theorem clamp_hi (w : BitVec 32) :
    (((w <<< 2) >>> 2) ||| (1#32 <<< 30)).toNat = w.toNat % 2 ^ 30 + 2 ^ 30 := by
  have hlo : ((w <<< 2) >>> 2).toNat = w.toNat % 2 ^ 30 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  have h30 : (1#32 <<< 30).toNat = 2 ^ 30 := by decide
  rw [BitVec.toNat_or, hlo, h30, Nat.or_comm, ← Nat.mul_one (2 ^ 30),
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 30))]
  omega

/-! ## Signed digit bytes -/

/-- `ldrb; lsls #24; asrs #24`: the byte read back as a signed number. `ASRS` is taken as
`BitVec.sshiftRight`, the value of the model's `asrC` (proofs `882401b`). -/
theorem sext_byte (b : Byte) : ((b.setWidth 32 <<< 24).sshiftRight 24).toInt = b.toInt := by
  have h : ∀ n : Fin (2 ^ 8),
      (((BitVec.ofFin n).setWidth 32 <<< 24).sshiftRight 24).toInt = (BitVec.ofFin n).toInt := by
    decide +kernel
  exact h b.toFin

/-- `strb` of a register holding the 32-bit two's complement of `d`, `|d| < 128`, stores the
byte whose signed value is `d`. -/
theorem digit_byte (d : Int) (h1 : -128 ≤ d) (h2 : d < 128) :
    ((BitVec.ofInt 32 d).extractLsb' 0 8).toInt = d := by
  have h : ∀ k : Fin 256,
      ((BitVec.ofInt 32 ((k : Int) - 128)).extractLsb' 0 8).toInt = (k : Int) - 128 := by
    decide +kernel
  have := h ⟨(d + 128).toNat, by omega⟩
  simp only at this
  rwa [Int.toNat_of_nonneg (by omega), Int.add_sub_cancel] at this

/-- The digit register of `m0c_sc_wnaf`, `word - (carry << w)` (`lsls r1, r2; subs r0, r1`), has
the low byte of the two's complement of `word - carry 2^w`. -/
theorem reg_byte (word c w : Nat) (hw : w ≤ 8) (hc : c ≤ 1) (hword : word < 2 ^ 32) :
    (BitVec.ofNat 32 word - (BitVec.ofNat 32 c <<< w)).extractLsb' 0 8 =
      (BitVec.ofInt 32 ((word : Int) - ((c * 2 ^ w : Nat) : Int))).extractLsb' 0 8 := by
  have hP : 2 ^ w ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_sub,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_zero, Nat.shiftRight_zero, BitVec.toNat_ofInt]
  generalize 2 ^ w = P at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    simp only [Nat.zero_mul, Nat.one_mul] <;> omega

/-- `strb` of the digit register of `m0c_sc_wnaf` stores the byte whose signed value is the
digit `word - carry 2^w` (`Ed25519WnafDigits.step`), when that digit fits a signed byte. -/
theorem digit_reg (word c w : Nat) (hw : w ≤ 8) (hc : c ≤ 1) (hword : word < 2 ^ 32)
    (h1 : -128 ≤ (word : Int) - c * 2 ^ w) (h2 : (word : Int) - c * 2 ^ w < 128) :
    ((BitVec.ofNat 32 word - (BitVec.ofNat 32 c <<< w)).extractLsb' 0 8).toInt =
      (word : Int) - c * 2 ^ w := by
  have e : ((c * 2 ^ w : Nat) : Int) = (c : Int) * 2 ^ w := by push_cast; rfl
  rw [reg_byte word c w hw hc hword, e]
  exact digit_byte _ h1 h2

end M0Crypto.Release.Ed25519Bytes
