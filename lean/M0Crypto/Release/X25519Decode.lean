import M0Crypto.Armv6M.Step
import M0Crypto.Release.X25519Val
import M0Crypto.Spec.X25519

/-!
Bytes, words and scalar bits of the X25519 entry.

* `leWord bs i`: the little-endian word that `load_le32` builds from bytes `4i` to `4i + 3`.
  `decodeScalar_val` and `decodeU_val` give the RFC decodings as `val` of the eight words,
  clamped or masked as the code does it; `clamped_bounds` gives the scalar's shape.
* `scalar_bit`: bit `t` of `val ws` is bit `t mod 32` of word `t / 32`; `word_index` is the
  code's byte offset `(t >>> 3) &&& 28`; `ror_bit` reads the bit with `rors` and `ands #1`.
* `out_byte`: byte `4i + j` of a value is byte `j` of its word `i`.

The generic list lemmas (`dle_set`, `dle_drop4`, `dle_val`) do the work; nothing enumerates
the 32 bytes.
-/

namespace M0Crypto.Release.X25519Decode

open M0Crypto.Release.X25519Val
open M0Crypto.Spec.X25519 (decodeLittleEndian)

abbrev Byte := M0Crypto.Spec.X25519.Byte

/-- `rd |= rt << k` with `rd < 2^k` is an addition. -/
theorem or_shift (x y k : Nat) (hx : x < 2 ^ k) : x ||| y <<< k = x + 2 ^ k * y := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.mul_comm]; omega
def leWord (bs : List Byte) (i : Nat) : Nat :=
  (bs.getD (4 * i) 0).toNat + 2 ^ 8 * (bs.getD (4 * i + 1) 0).toNat +
    2 ^ 16 * (bs.getD (4 * i + 2) 0).toNat + 2 ^ 24 * (bs.getD (4 * i + 3) 0).toNat

theorem dle_set (bs : List Byte) (i : Nat) (v : Byte) (hi : i < bs.length) :
    decodeLittleEndian (bs.set i v) + 256 ^ i * (bs.getD i 0).toNat =
      decodeLittleEndian bs + 256 ^ i * v.toNat := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [decodeLittleEndian]; omega
    | succ i =>
      have := ih i (by simp at hi; omega)
      simp only [List.set_cons_succ, decodeLittleEndian, List.getD_cons_succ, Nat.pow_succ]
      rw [Nat.mul_comm (256 ^ i) 256, Nat.mul_assoc, Nat.mul_assoc]
      omega

theorem dle_drop4 (bs : List Byte) (i : Nat) (h : 4 * i + 4 ≤ bs.length) :
    decodeLittleEndian (bs.drop (4 * i)) =
      leWord bs i + 2 ^ 32 * decodeLittleEndian (bs.drop (4 * i + 4)) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  simp only [decodeLittleEndian, leWord, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 4 * i < bs.length by omega),
    List.getElem?_eq_getElem (show 4 * i + 1 < bs.length by omega),
    List.getElem?_eq_getElem (show 4 * i + 2 < bs.length by omega),
    List.getElem?_eq_getElem (show 4 * i + 3 < bs.length by omega), Option.getD_some,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * i + 4 by omega]
  omega

theorem dle_val_aux (bs : List Byte) (n i : Nat) (h : 4 * (i + n) = bs.length) :
    decodeLittleEndian (bs.drop (4 * i)) = val ((List.range' i n).map (leWord bs)) := by
  induction n generalizing i with
  | zero => simp only [Nat.add_zero] at h; rw [h, List.drop_length]; rfl
  | succ n ih =>
    rw [dle_drop4 bs i (by omega), show 4 * i + 4 = 4 * (i + 1) by omega, ih (i + 1) (by omega)]
    simp [List.range'_succ, val]

theorem dle_val (bs : List Byte) (h : bs.length = 32) :
    decodeLittleEndian bs = val ((List.range 8).map (leWord bs)) := by
  have := dle_val_aux bs 8 0 (by omega)
  simpa [List.range_eq_range'] using this

theorem div_mod_low (x a b c : Nat) (h : a + b ≤ c) :
    x / 2 ^ a % 2 ^ b = x % 2 ^ c / 2 ^ a % 2 ^ b := by
  conv => lhs; rw [← Nat.mod_add_div x (2 ^ c)]
  rw [show 2 ^ c = 2 ^ a * 2 ^ (c - a) by rw [← Nat.pow_add]; congr 1; omega]
  rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos a)]
  obtain ⟨d, hd⟩ : 2 ^ b ∣ 2 ^ (c - a) := Nat.pow_dvd_pow 2 (by omega)
  rw [hd, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem and248 : ∀ b : BitVec 8, (b &&& 248#8).toNat = b.toNat / 8 * 8 := by decide
theorem and127 : ∀ b : BitVec 8, (b &&& 127#8).toNat = b.toNat % 128 := by decide
theorem clampTop : ∀ b : BitVec 8, ((b &&& 127#8) ||| 64#8).toNat = b.toNat % 64 + 64 := by
  decide

def words (bs : List Byte) (f0 f7 : Nat → Nat) : List Nat :=
  [f0 (leWord bs 0), leWord bs 1, leWord bs 2, leWord bs 3, leWord bs 4, leWord bs 5,
    leWord bs 6, f7 (leWord bs 7)]

theorem dle_words (bs : List Byte) (h : bs.length = 32) :
    decodeLittleEndian bs = val (words bs id id) := by
  rw [dle_val bs h]; rfl

theorem decodeScalar_val (kb : List Byte) (hk : kb.length = 32) :
    M0Crypto.Spec.X25519.decodeScalar25519 kb =
      val (words kb (fun w => w / 8 * 8) (fun w => w % 2 ^ 30 + 2 ^ 30)) := by
  unfold M0Crypto.Spec.X25519.decodeScalar25519
  have h1 := dle_set kb 0 (kb.getD 0 0 &&& 248#8) (by omega)
  have h2 := dle_set (kb.set 0 (kb.getD 0 0 &&& 248#8)) 31
    ((kb.getD 31 0 &&& 127#8) ||| 64#8) (by simp; omega)
  have hg : (kb.set 0 (kb.getD 0 0 &&& 248#8)).getD 31 0 = kb.getD 31 0 := by
    simp [List.getD_eq_getElem?_getD]
  rw [hg] at h2
  have h3 := dle_words kb hk
  simp only [words, val_eight, leWord, id, Nat.reduceMul, Nat.reduceAdd, and248, clampTop, Nat.pow_zero, Nat.one_mul] at h1 h2 h3 ⊢
  have := (kb.getD 0 0).isLt; have := (kb.getD 28 0).isLt; have := (kb.getD 29 0).isLt
  have := (kb.getD 30 0).isLt; have := (kb.getD 31 0).isLt
  omega

theorem decodeU_val (ub : List Byte) (hu : ub.length = 32) :
    M0Crypto.Spec.X25519.decodeUCoordinate ub = val (words ub id (fun w => w % 2 ^ 31)) := by
  unfold M0Crypto.Spec.X25519.decodeUCoordinate
  have h2 := dle_set ub 31 (ub.getD 31 0 &&& 127#8) (by omega)
  have h3 := dle_words ub hu
  simp only [words, val_eight, leWord, id, Nat.reduceMul, Nat.reduceAdd, and127] at h2 h3 ⊢
  have := (ub.getD 28 0).isLt; have := (ub.getD 29 0).isLt
  have := (ub.getD 30 0).isLt; have := (ub.getD 31 0).isLt
  omega

theorem leWord_lt (bs : List Byte) (i : Nat) : leWord bs i < 2 ^ 32 := by
  unfold leWord
  have := (bs.getD (4 * i) 0).isLt; have := (bs.getD (4 * i + 1) 0).isLt
  have := (bs.getD (4 * i + 2) 0).isLt; have := (bs.getD (4 * i + 3) 0).isLt
  omega

/-- The clamped scalar: a multiple of 8, bit 254 set, below `2^255`. -/
theorem clamped_bounds (kb : List Byte) :
    let k := val (words kb (fun w => w / 8 * 8) (fun w => w % 2 ^ 30 + 2 ^ 30))
    k % 8 = 0 ∧ 2 ^ 254 ≤ k ∧ k < 2 ^ 255 := by
  simp only [words, val_eight]
  have := leWord_lt kb 0; have := leWord_lt kb 1; have := leWord_lt kb 2
  have := leWord_lt kb 3; have := leWord_lt kb 4; have := leWord_lt kb 5
  have := leWord_lt kb 6; have := leWord_lt kb 7
  omega

/-- Bit `t` of a word list's value is bit `t % 32` of word `t / 32`. -/
theorem scalar_bit (ws : List Nat) (h : Words ws) (t : Nat) (ht : t < 32 * ws.length) :
    (val ws >>> t) &&& 1 = (ws[t / 32]'(by omega) >>> (t % 32)) &&& 1 := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rw [← val_word ws h (t / 32) (by omega)]
  have e : t = 32 * (t / 32) + t % 32 := (Nat.div_add_mod t 32).symm
  conv => lhs; rw [e]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize val ws / 2 ^ (32 * (t / 32)) = x
  have hm : t % 32 < 32 := Nat.mod_lt _ (by omega)
  generalize t % 32 = m at hm ⊢
  have := div_mod_low x m 1 32 (by omega)
  simpa only [Nat.pow_one] using this

theorem idx5 : ∀ n : Fin 32, (n.val &&& 28) = n.val / 4 * 4 := by decide

/-- The byte offset of the word holding bit `t`: `(t >>> 3) &&& 28 = 4 * (t / 32)`. -/
theorem word_index (t : Nat) (ht : t < 256) : (t >>> 3) &&& 28 = 4 * (t / 32) := by
  rw [Nat.shiftRight_eq_div_pow]
  have := idx5 ⟨t / 2 ^ 3, by omega⟩
  simp only at this; rw [this]; omega

theorem bit0_toNat (r : BitVec 32) : (r &&& 1#32).toNat = r.toNat % 2 := by
  rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]

/-- `rors` by `n`, then `ands #1`: bit `n mod 32` of the word. -/
theorem ror_bit (w : BitVec 32) (n : Nat) (c : Bool) :
    ((M0Crypto.Armv6M.rorC w n c).1 &&& 1#32).toNat = w.toNat / 2 ^ (n % 32) % 2 := by
  rw [bit0_toNat]
  unfold M0Crypto.Armv6M.rorC
  split
  · subst_vars; simp
  · simp only
    have hm : n % 32 < 32 := Nat.mod_lt _ (by omega)
    generalize n % 32 = m at hm ⊢
    rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
    rw [Nat.shiftRight_eq_div_pow]
    have he : w.toNat <<< (32 - m) % 2 ^ 32 % 2 = 0 := by
      rw [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 32)]
      obtain ⟨j, hj⟩ : ∃ j, 32 - m = j + 1 := ⟨31 - m, by omega⟩
      rw [hj, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
    have := Nat.or_mod_two_pow (a := w.toNat / 2 ^ m) (b := w.toNat <<< (32 - m) % 2 ^ 32) (n := 1)
    simp only [Nat.pow_one] at this
    rw [this, he, Nat.or_zero]

/-- Byte `4i + j` of a value is byte `j` of word `i`. -/
theorem out_byte (ws : List Nat) (h : Words ws) (i j : Nat) (hi : i < ws.length) (hj : j < 4) :
    BitVec.ofNat 8 (val ws / 2 ^ (8 * (4 * i + j))) = BitVec.ofNat 8 (ws[i] / 2 ^ (8 * j)) := by
  rw [← val_word ws h i hi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 8 * (4 * i + j) = 32 * i + 8 * j by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  exact div_mod_low _ (8 * j) 8 32 (by omega)

end M0Crypto.Release.X25519Decode
