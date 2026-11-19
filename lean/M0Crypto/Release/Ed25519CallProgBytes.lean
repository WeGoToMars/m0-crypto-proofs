import M0Crypto.Release.Footprint
import M0Crypto.Release.Ed25519Bytes
import M0Crypto.Spec.Ed25519Sha512

/-!
# Call programs: byte views as numbers

A byte view holds a list of bytes; the scalar and digest routines compute on little-endian
numbers. `decodeInt_words`: the `4n` bytes at `a` are the number of the `n` words there.
`encodeInt_decodeInt`, `decodeInt_encodeInt`: the spec's 32-byte encoding and decoding are inverse
on 32-byte lists and on numbers below `2^256`.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Mem read32)
open M0Crypto.Release.Footprint (bytesAt bytesAt_length)
open M0Crypto.Spec.Ed25519 (Byte decodeInt encodeInt encodePoint)
open M0Crypto.Release.Ed25519Words (wsum wsum_succ)

theorem bytesAt_split (m : Mem) (a : Word) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 32 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by simp only [Function.comp, Thumb.ofNat_add_assoc]

theorem decodeInt_append : ∀ (l r : List Byte),
    decodeInt (l ++ r) = decodeInt l + 2 ^ (8 * l.length) * decodeInt r
  | [], r => by simp [decodeInt]
  | b :: l, r => by
    simp only [List.cons_append, decodeInt, decodeInt_append l r, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 + 8 * l.length by omega, Nat.pow_add, Nat.mul_assoc]
    generalize 2 ^ (8 * l.length) * decodeInt r = q
    omega

/-- The 4 bytes at `a` are the word there. -/
theorem decodeInt_word (m : Mem) (a : Word) : decodeInt (bytesAt m a 4) = (read32 m a).toNat := by
  have h8 : ∀ (x : Nat) (y : Byte), x <<< 8 ||| y.toNat = 256 * x + y.toNat := fun x y => by
    rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]; omega
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, decodeInt, read32, BitVec.toNat_append, h8]
  simp only [BitVec.add_zero]
  omega

/-- **The `4n` bytes at `a` are the number of the `n` words there.** -/
theorem decodeInt_words (m : Mem) (a : Word) : ∀ n,
    decodeInt (bytesAt m a (4 * n)) = wsum (fun j => (read32 m (a + BitVec.ofNat 32 (4 * j))).toNat) n
  | 0 => by simp [bytesAt, decodeInt, wsum]
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, bytesAt_split, decodeInt_append, decodeInt_words m a n,
      bytesAt_length, decodeInt_word, wsum_succ, show 8 * (4 * n) = 32 * n by omega]

theorem encodeInt_length (n : Nat) : (encodeInt n).length = 32 := by simp [encodeInt]

theorem encodeInt_decodeInt {l : List Byte} (h : l.length = 32) : encodeInt (decodeInt l) = l := by
  apply List.ext_getElem (by rw [encodeInt_length, h])
  intro i h1 h2
  simp only [encodeInt, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Ed25519Bytes.decodeInt_byte]; simp [List.getD_eq_getElem?_getD, h2]

theorem decodeInt_encodeK (n : Nat) : ∀ k,
    decodeInt ((List.range k).map fun i => BitVec.ofNat 8 (n / 2 ^ (8 * i))) = n % 2 ^ (8 * k)
  | 0 => by simp [decodeInt, Nat.mod_one]
  | k + 1 => by
    rw [List.range_succ, List.map_append, decodeInt_append, decodeInt_encodeK n k, List.length_map,
      List.length_range, List.map_cons, List.map_nil, decodeInt, decodeInt, BitVec.toNat_ofNat,
      show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
    simp

/-- **Decoding inverts encoding** below `2^256`. -/
theorem decodeInt_encodeInt (n : Nat) : decodeInt (encodeInt n) = n % 2 ^ 256 :=
  decodeInt_encodeK n 32

theorem encodePoint_length (P : Spec.Ed25519.Point) : (encodePoint P).length = 32 := by
  unfold encodePoint; split; exact encodeInt_length _

/-! ## The digest length -/

theorem hash_size : ∀ (H : Array (BitVec 64)) (M : List Byte), H.size = 8 → (Spec.Sha512.hash H M).size = 8
  | H, [], h => by rw [Spec.Sha512.hash]; exact h
  | H, b :: M, _ => by
    rw [Spec.Sha512.hash]; exact hash_size _ _ (by simp [Spec.Sha512.compress])
termination_by _ M => M.length
decreasing_by simp; omega

/-- **A SHA-512 digest has 64 bytes.** -/
theorem sha512_length (M : List Byte) : (Spec.Sha512.sha512 M).length = 64 := by
  have hs := hash_size Spec.Sha512.H0 (Spec.Sha512.pad M) rfl
  simp only [Spec.Sha512.sha512, List.length_flatMap, Spec.Sha512.bytesBE, List.length_map,
    List.length_reverse, List.length_range]
  rw [← Array.length_toList] at hs
  generalize (Spec.Sha512.hash Spec.Sha512.H0 (Spec.Sha512.pad M)).toList = l at hs ⊢
  have : ∀ l : List (BitVec 64), (l.map fun _ => 8).sum = 8 * l.length := fun l => by
    induction l with
    | nil => rfl
    | cons _ _ ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  rw [this, hs]

end M0Crypto.Release.Ed25519CallProg
