import M0Crypto.Release.PolyArith
import M0Crypto.Release.Frame

set_option linter.unusedSimpArgs false

/-!
Bridge from the RFC 8439 §2.5 Poly1305 specification (`Spec.AEAD.poly1305`) to the
word-level, block-at-a-time view of `m0c_poly1305_*`.

* `polyBlocks r pad acc msg`: absorb the 16-byte chunks of `msg`, each with
  `pad * 2^128` added, starting from `acc`. With `pad = 1` and `16 ∣ msg.length`
  this is the RFC accumulator (`polyAcc_eq`); it splits at any 16-byte boundary
  (`polyBlocks_append`).
* `leNat` of 16 memory bytes is the 4-limb value of the little-endian words there
  (`leNat_bytesAt16`).
* `clamp` of 16 key bytes is the limb-wise clamp of the key words (`clamp_words`).
* the tag: `leBytes 16` depends only on the value mod 2^128, byte `4j + k` is byte
  `k` of word `j` (`leBytes_get`), and the final reduction `h mod p` for `h < 2p`
  agrees mod 2^128 with `h + 5 [h ≥ p]` (`tag_reduce`).
-/

namespace M0Crypto.Release.PolySpec

open M0Crypto.Armv6M (Word Mem read32)
open M0Crypto.Spec.ChaCha20 (Byte)
open M0Crypto.Spec.AEAD (p leNat leBytes clamp chunks16 polyAcc)
open M0Crypto.Release.Frame (Ctx)
open M0Crypto.Release.PolyArith (val4 val5)

/-! ## Absorbing 16-byte blocks -/

/-- One Poly1305 block step with explicit high bit `pad`. -/
def step (r pad acc : Nat) (blk : List Byte) : Nat := (acc + leNat blk + pad * 2 ^ 128) * r % p

def polyBlocks (r pad acc : Nat) (msg : List Byte) : Nat := (chunks16 msg).foldl (step r pad) acc

theorem leNat_append : ∀ (a b : List Byte), leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b
  | [], b => by simp [leNat]
  | x :: a, b => by
    simp only [List.cons_append, leNat, leNat_append a b, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ a.length)]; omega

theorem chunks16_cons (b : Byte) (rest : List Byte) :
    chunks16 (b :: rest) = (b :: rest).take 16 :: chunks16 ((b :: rest).drop 16) := by
  rw [chunks16]

theorem chunks16_nil : chunks16 [] = [] := by rw [chunks16]

/-- A full first block is the first chunk. -/
theorem chunks16_block (blk rest : List Byte) (h : blk.length = 16) :
    chunks16 (blk ++ rest) = blk :: chunks16 rest := by
  match blk, h with
  | b :: bs, h =>
    rw [List.cons_append, chunks16_cons, ← List.cons_append, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]

theorem split16 (a : List Byte) (n : Nat) (h : a.length = 16 * (n + 1)) :
    ∃ x y, a = x ++ y ∧ x.length = 16 ∧ y.length = 16 * n :=
  ⟨a.take 16, a.drop 16, (List.take_append_drop _ _).symm, by simp; omega, by simp; omega⟩

theorem chunks16_append : ∀ (n : Nat) (a b : List Byte), a.length = 16 * n →
    chunks16 (a ++ b) = chunks16 a ++ chunks16 b
  | 0, a, b, h => by
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [List.nil_append, chunks16_nil, List.nil_append]
  | n + 1, a, b, h => by
    obtain ⟨x, y, rfl, hx, hy⟩ := split16 a n h
    rw [List.append_assoc, chunks16_block _ _ hx, chunks16_block _ _ hx, chunks16_append n y b hy]
    rfl

theorem polyBlocks_append (r pad acc : Nat) (n : Nat) (a b : List Byte) (h : a.length = 16 * n) :
    polyBlocks r pad acc (a ++ b) = polyBlocks r pad (polyBlocks r pad acc a) b := by
  simp only [polyBlocks, chunks16_append n a b h, List.foldl_append]

theorem chunks16_one (blk : List Byte) (h : blk.length = 16) : chunks16 blk = [blk] := by
  have := chunks16_block blk [] h
  rwa [List.append_nil, chunks16_nil] at this

theorem polyBlocks_block (r pad acc : Nat) (blk : List Byte) (h : blk.length = 16) :
    polyBlocks r pad acc blk = step r pad acc blk := by
  unfold polyBlocks; rw [chunks16_one blk h, List.foldl_cons, List.foldl_nil]

theorem polyBlocks_nil (r pad acc : Nat) : polyBlocks r pad acc [] = acc := by
  unfold polyBlocks; rw [chunks16_nil, List.foldl_nil]

/-- Every chunk of a message of length `16 n` is 16 bytes long. -/
theorem chunks16_len : ∀ (n : Nat) (a : List Byte), a.length = 16 * n → ∀ c ∈ chunks16 a, c.length = 16
  | 0, a, h => by
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [chunks16_nil]; intro c hc; cases hc
  | n + 1, a, h => by
    obtain ⟨x, y, rfl, hx, hy⟩ := split16 a n h
    rw [chunks16_block _ _ hx]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hx
    · exact chunks16_len n y hy c hc

theorem foldl_congr {α β : Type} (f g : α → β → α) : ∀ (l : List β) (a : α),
    (∀ x ∈ l, ∀ a, f a x = g a x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self a]
    exact foldl_congr f g l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **RFC accumulator.** For a message of whole 16-byte blocks, RFC 8439's `polyAcc` (each
chunk with its 0x01 byte appended) is `polyBlocks` with `pad = 1` from 0. -/
theorem polyAcc_eq (r : Nat) (msg : List Byte) (h : msg.length % 16 = 0) :
    polyAcc r msg = polyBlocks r 1 0 msg := by
  simp only [polyAcc, polyBlocks]
  apply foldl_congr
  intro c hc a
  have hl := chunks16_len (msg.length / 16) msg (by omega) c hc
  simp only [step, leNat_append, hl, leNat, BitVec.toNat_ofNat]
  rw [show (256 : Nat) ^ 16 * (1 % 2 ^ 8 + 256 * 0) = 1 * 2 ^ 128 from rfl, Nat.add_assoc]

/-- Each step depends on the accumulator only modulo `p`. -/
theorem p_eq' : p = 2 ^ 130 - 5 := rfl

theorem step_mod (r pad acc : Nat) (blk : List Byte) : step r pad (acc % p) blk = step r pad acc blk := by
  simp only [step]
  have hd := Nat.mod_add_div acc p
  have e : (acc + leNat blk + pad * 2 ^ 128) * r =
      (acc % p + leNat blk + pad * 2 ^ 128) * r + p * (acc / p * r) := by
    conv => lhs; rw [← hd]
    grind
  rw [e, Nat.add_mul_mod_self_left]

/-! ## Memory bytes as words -/

theorem bytesAt_add (m : Mem) : ∀ (a : Word) (x y : Nat),
    Ctx.bytesAt m a (x + y) = Ctx.bytesAt m a x ++ Ctx.bytesAt m (a + BitVec.ofNat 32 x) y
  | a, 0, y => by simp [Ctx.bytesAt]
  | a, x + 1, y => by
    rw [show x + 1 + y = (x + y) + 1 by omega, Frame.bytesAt_succ, Frame.bytesAt_succ, bytesAt_add m _ x y,
      List.cons_append, show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, Thumb.ofNat_add_assoc,
      Nat.add_comm 1 x]

theorem shl8_or (x : Nat) (y : Byte) : x <<< 8 ||| y.toNat = 256 * x + y.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]; omega

theorem read32_toNat (m : Mem) (a : Word) :
    (read32 m a).toNat = (m a).toNat + 256 * ((m (a + 1#32)).toNat + 256 * ((m (a + 2#32)).toNat +
      256 * (m (a + 3#32)).toNat)) := by
  simp only [read32, BitVec.toNat_append, shl8_or]
  omega

theorem leNat_bytesAt4 (m : Mem) (a : Word) : leNat (Ctx.bytesAt m a 4) = (read32 m a).toNat := by
  rw [read32_toNat]
  simp only [Ctx.bytesAt, leNat]
  rw [show a + 1#32 + 1#32 = a + 2#32 by bv_omega, show a + 2#32 + 1#32 = a + 3#32 by bv_omega]
  omega

/-- 16 bytes from `a` are the 4-limb value of the words at `a, a + 4, a + 8, a + 12`. -/
theorem leNat_bytesAt16 (m : Mem) (a : Word) :
    leNat (Ctx.bytesAt m a 16) = val4 (read32 m a).toNat (read32 m (a + 4#32)).toNat
      (read32 m (a + 8#32)).toNat (read32 m (a + 12#32)).toNat := by
  rw [show 16 = 4 + (4 + (4 + 4)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add, leNat_append,
    leNat_append, leNat_append]
  simp only [Frame.bytesAt_length, leNat_bytesAt4, val4]
  rw [show a + 4#32 + 4#32 = a + 8#32 by bv_omega, show a + 8#32 + 4#32 = a + 12#32 by bv_omega]
  omega

/-! ## Clamp -/

theorem land_limb (a b c d : Nat) (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  have h := Nat.mod_add_div ((a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d)) (2 ^ 32)
  rw [Nat.and_mod_two_pow, Nat.and_div_two_pow] at h
  have e1 : (a + 2 ^ 32 * b) % 2 ^ 32 = a := by omega
  have e2 : (c + 2 ^ 32 * d) % 2 ^ 32 = c := by omega
  have e3 : (a + 2 ^ 32 * b) / 2 ^ 32 = b := by omega
  have e4 : (c + 2 ^ 32 * d) / 2 ^ 32 = d := by omega
  rw [e1, e2, e3, e4] at h
  exact h.symm

/-- **Clamp, limb-wise.** RFC 8439 `clamp` of a 128-bit value given by four 32-bit limbs. -/
theorem clamp_words (k0 k1 k2 k3 : Nat) (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    clamp (val4 k0 k1 k2 k3) =
      val4 (k0 &&& 0x0fffffff) (k1 &&& 0x0ffffffc) (k2 &&& 0x0ffffffc) (k3 &&& 0x0ffffffc) := by
  have hv : ∀ a0 a1 a2 a3 : Nat, val4 a0 a1 a2 a3 = a0 + 2 ^ 32 * (a1 + 2 ^ 32 * (a2 + 2 ^ 32 * a3)) := by
    intro a0 a1 a2 a3; simp only [val4]; omega
  rw [clamp, hv, hv, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) from rfl,
    land_limb _ _ _ _ h0 (by decide), land_limb _ _ _ _ h1 (by decide), land_limb _ _ _ _ h2 (by decide)]

/-! ## The tag -/

theorem leBytes_get (n x i : Nat) (hi : i < n) :
    (leBytes n x)[i]? = some (BitVec.ofNat 8 (x / 256 ^ i)) := by
  simp [leBytes, hi]

theorem leBytes_length (n x : Nat) : (leBytes n x).length = n := by simp [leBytes]

/-- Byte `4 j + k` of the 16-byte little-endian encoding of `val4 w0 w1 w2 w3 + 2^128 t` is
byte `k` of `w_j`. -/
theorem tag_byte (w0 w1 w2 w3 t j k : Nat) (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (hj : j < 4) (hk : k < 4) :
    BitVec.ofNat 8 ((val4 w0 w1 w2 w3 + 2 ^ 128 * t) / 256 ^ (4 * j + k)) =
      BitVec.ofNat 8 ((if j = 0 then w0 else if j = 1 then w1 else if j = 2 then w2 else w3) / 256 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, val4]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp only [ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
    show (3 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide] <;>
  omega

/-- **Final reduction.** For `h < 2p`, `(h mod p + s) mod 2^128` is `(h + 5 b + s) mod 2^128`
where `b = (h + 5) / 2^130` is 1 iff `h ≥ p`. -/
theorem tag_reduce (h s : Nat) (hh : h < 2 * p) :
    (h % p + s) % 2 ^ 128 = (h + 5 * ((h + 5) / 2 ^ 130) + s) % 2 ^ 128 := by
  rw [p_eq'] at hh ⊢
  by_cases hp : h < 2 ^ 130 - 5
  · rw [Nat.mod_eq_of_lt hp]; omega
  · have : h % (2 ^ 130 - 5) = h - (2 ^ 130 - 5) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [this]; omega

/-- **Tag value.** RFC 8439 `poly1305` is the 16-byte encoding of `polyAcc + s`. -/
theorem poly1305_eq (key msg : List Byte) :
    M0Crypto.Spec.AEAD.poly1305 key msg =
      leBytes 16 (polyAcc (clamp (leNat (key.take 16))) msg + leNat ((key.drop 16).take 16)) := rfl

end M0Crypto.Release.PolySpec
