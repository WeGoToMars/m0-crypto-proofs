import M0Crypto.Spec.AEAD
import M0Crypto.Proofs.ChaCha20DRound

set_option linter.unusedSimpArgs false

/-!
Byte-level reading of the RFC 8439 ChaCha20 specification (`Spec.AEAD.chacha20`),
for the whole-function proof: output byte `i` is input byte `i` XOR byte `i % 64` of
block `counter + i / 64`, and block byte `j` is byte `j % 4` of word `j / 4` of
`initState + innerBlocks 10 initState`.
-/

namespace M0Crypto.Release.ChaChaSpec

open M0Crypto.Spec.ChaCha20
open M0Crypto.Spec.AEAD (keystream chacha20)

/-- Indexing a concatenation of equal-length chunks. -/
theorem getElem?_flatMap_range {α : Type} (k : Nat) (hk : 0 < k) (f : Nat → List α)
    (hf : ∀ j, (f j).length = k) : ∀ (m i : Nat), i < k * m →
    ((List.range m).flatMap f)[i]? = (f (i / k))[i % k]?
  | 0, i, h => by omega
  | m + 1, i, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl : ((List.range m).flatMap f).length = k * m := by
      clear h; induction m with
      | zero => rfl
      | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih,
          List.flatMap_singleton, hf]; rw [Nat.mul_succ]
    by_cases hi : i < k * m
    · rw [List.getElem?_append_left (by rw [hl]; exact hi)]
      exact getElem?_flatMap_range k hk f hf m i hi
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl]
      have h1 : i / k = m := by
        apply Nat.div_eq_of_lt_le <;> rw [Nat.mul_comm] <;> omega
      have h2 : i % k = i - k * m := by
        have := Nat.div_add_mod i k; rw [h1] at this; omega
      rw [h1, h2]

theorem block_length' (key nonce : List Byte) (c : Word) : (block key c nonce).length = 64 :=
  block_length key nonce c

theorem keystream_length (key nonce : List Byte) (c n : Nat) :
    (keystream key c nonce n).length = n := by
  have : ((List.range ((n + 63) / 64)).flatMap fun i =>
      block key (BitVec.ofNat 32 (c + i)) nonce).length = 64 * ((n + 63) / 64) := by
    generalize (n + 63) / 64 = m
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih,
        List.flatMap_singleton, block_length']; rw [Nat.mul_succ]
  simp only [keystream, List.length_take, this]
  omega

theorem keystream_get (key nonce : List Byte) (c n i : Nat) (hi : i < n) :
    (keystream key c nonce n)[i]? =
      (block key (BitVec.ofNat 32 (c + i / 64)) nonce)[i % 64]? := by
  simp only [keystream, List.getElem?_take, hi, ite_true]
  exact getElem?_flatMap_range 64 (by decide) _ (fun j => block_length' _ _ _) _ i (by omega)

/-- Output byte `i` of ChaCha20 encryption. -/
theorem chacha20_get (key nonce msg : List Byte) (c i : Nat) (hi : i < msg.length) :
    (chacha20 key c nonce msg)[i]? =
      some (msg[i] ^^^ (block key (BitVec.ofNat 32 (c + i / 64)) nonce)[i % 64]'
        (by rw [block_length']; omega)) := by
  have hk := keystream_get key nonce c msg.length i hi
  have hl := keystream_length key nonce c msg.length
  simp only [chacha20, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp [hl, hi]), List.getElem_zip]
  rw [List.getElem?_eq_getElem (by rw [hl]; exact hi)] at hk
  rw [List.getElem?_eq_getElem (by rw [block_length']; omega)] at hk
  simp only [Option.some.injEq] at hk
  simp [hk]

theorem chacha20_length (key nonce msg : List Byte) (c : Nat) :
    (chacha20 key c nonce msg).length = msg.length := by
  simp [chacha20, keystream_length]

/-- Block byte `j` is byte `j % 4` of word `j / 4` of `s + innerBlocks 10 s`. -/
theorem block_get (key nonce : List Byte) (c : Word) (j : Nat) (hj : j < 64) :
    (block key c nonce)[j]? =
      (bytesOfWord ((initState key c nonce)[j / 4]! +
        (innerBlocks 10 (initState key c nonce))[j / 4]!))[j % 4]? := by
  simp only [block]
  have hl : (blockWords key c nonce).toList = (List.range 16).map fun i =>
      (initState key c nonce)[i]! + (innerBlocks 10 (initState key c nonce))[i]! := by
    simp [blockWords]
  rw [hl, List.flatMap_map]
  rw [getElem?_flatMap_range 4 (by decide) _ (fun _ => rfl) 16 j (by omega)]

end M0Crypto.Release.ChaChaSpec
