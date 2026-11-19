import M0Crypto.Spec.Ed25519Sha512

/-!
SHA-512 words on pairs of 32-bit registers, as `bench/ed25519/gen_sha512.py` computes them.

A 64-bit word is the pair `h ++ l` (high word `h`, low word `l`); the context, the frame and
the schedule store `l` at the lower address. Every lemma equates the specification's 64-bit
operation (`Spec.Sha512`) with the 32-bit expression of the code, in the code's order:

* `rotr_lt`, `rotr_ge`, `shr_lt`: `ROTR n` for `n < 32` and `n = 32 + m`, `SHR n`, as the two
  shift pairs that macro `sigma` combines with `eors` (the two halves have disjoint bits).
* `Sigma0_pair`, `Sigma1_pair`, `sigma0_pair`, `sigma1_pair`: macro `sigma` with the rotation
  lists of `round_body` and `schedule`, XORed in the order of the generator.
* `Ch_pair`, `Maj_pair`: the `eors`/`ands` sequences of `round_body`.
* `add_pair`: `adds` on the low words and `adcs` on the high words.
* `T1_order`, `a_order`, `sched_order`: the code's order of the 64-bit additions.
* `toWord_pair`: the big-endian load of `emit_block` (`ldm` of two words, `rev` each, swap).
* `bytesBE_pair`: the big-endian store of `emit_final` (`rev` each word, low address first).
* `length_bytes`: the 128-bit length field of `emit_final` from the 32-bit byte count `N`
  (`N >> 29` and `N << 3`, each reversed). `pad_zeros`: the number of zero bytes of the padding.

`rev32` is ARMv6-M `REV` (DDI 0419E A6.7.51): byte 0 of the result is byte 3 of the operand.
-/

namespace M0Crypto.Release.Ed25519Sha512Pairs

open M0Crypto.Spec.Sha512

/-! ## Rotations and shifts -/

/-- Closes a bitwise goal on pairs after the case split on the bit index. -/
local macro "pair_bits" : tactic => `(tactic|
  (simp (disch := omega) only [decide_eq_true, decide_eq_false, ite_eq_left, ite_eq_right,
    BitVec.getLsbD_of_ge, Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and,
    Bool.not_true, Bool.not_false, Bool.xor_false, Bool.false_xor] <;> (try (congr 1; omega))))

theorem rotr_lt (n : Nat) (h l : BitVec 32) (h0 : 0 < n) (h32 : n < 32) :
    ROTR n (h ++ l) = ((h >>> n) ^^^ (l <<< (32 - n))) ++ ((l >>> n) ^^^ (h <<< (32 - n))) := by
  unfold ROTR
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_append,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (show (i < 32 ∧ n + i < 32) ∨ (i < 32 ∧ 32 ≤ n + i) ∨ (32 ≤ i ∧ n + i < 64) ∨
    (32 ≤ i ∧ 64 ≤ n + i) by omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> pair_bits

theorem rotr_ge (m : Nat) (h l : BitVec 32) (h0 : 0 < m) (h32 : m < 32) :
    ROTR (32 + m) (h ++ l) =
      ((l >>> m) ^^^ (h <<< (32 - m))) ++ ((h >>> m) ^^^ (l <<< (32 - m))) := by
  unfold ROTR
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_append,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  rcases (show (i < 32 ∧ m + i < 32) ∨ (i < 32 ∧ 32 ≤ m + i) ∨ (32 ≤ i ∧ m + i < 64) ∨
    (32 ≤ i ∧ 64 ≤ m + i) by omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> pair_bits

theorem shr_lt (n : Nat) (h l : BitVec 32) (h0 : 0 < n) (h32 : n < 32) :
    SHR n (h ++ l) = (h >>> n) ++ ((l >>> n) ^^^ (h <<< (32 - n))) := by
  unfold SHR
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  rcases (show (i < 32 ∧ n + i < 32) ∨ (i < 32 ∧ 32 ≤ n + i) ∨ (32 ≤ i ∧ n + i < 64) ∨
    (32 ≤ i ∧ 64 ≤ n + i) by omega) with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> pair_bits

/-! ## The four sigma functions (macro `sigma`) -/

/-- `Σ1` (rotations 14, 18, 41) on `e = h ++ l`. -/
theorem Sigma1_pair (h l : BitVec 32) :
    Sigma1 (h ++ l) =
      (((((h >>> 14 ^^^ l <<< 18) ^^^ h >>> 18) ^^^ l <<< 14) ^^^ l >>> 9) ^^^ h <<< 23) ++
      (((((l >>> 14 ^^^ h <<< 18) ^^^ l >>> 18) ^^^ h <<< 14) ^^^ h >>> 9) ^^^ l <<< 23) := by
  unfold Sigma1
  rw [rotr_lt 14 h l (by omega) (by omega), rotr_lt 18 h l (by omega) (by omega),
    show (41 : Nat) = 32 + 9 from rfl, rotr_ge 9 h l (by omega) (by omega)]
  simp only [BitVec.xor_append, Nat.reduceSub, BitVec.xor_assoc]

/-- `Σ0` (rotations 28, 34, 39) on `a = h ++ l`. -/
theorem Sigma0_pair (h l : BitVec 32) :
    Sigma0 (h ++ l) =
      (((((h >>> 28 ^^^ l <<< 4) ^^^ l >>> 2) ^^^ h <<< 30) ^^^ l >>> 7) ^^^ h <<< 25) ++
      (((((l >>> 28 ^^^ h <<< 4) ^^^ h >>> 2) ^^^ l <<< 30) ^^^ h >>> 7) ^^^ l <<< 25) := by
  unfold Sigma0
  rw [rotr_lt 28 h l (by omega) (by omega), show (34 : Nat) = 32 + 2 from rfl,
    rotr_ge 2 h l (by omega) (by omega), show (39 : Nat) = 32 + 7 from rfl,
    rotr_ge 7 h l (by omega) (by omega)]
  simp only [BitVec.xor_append, Nat.reduceSub, BitVec.xor_assoc]

/-- `σ0` (rotations 1, 8, shift 7) on `W[j+1] = h ++ l`. -/
theorem sigma0_pair (h l : BitVec 32) :
    sigma0 (h ++ l) =
      ((((h >>> 1 ^^^ l <<< 31) ^^^ h >>> 8) ^^^ l <<< 24) ^^^ h >>> 7) ++
      (((((l >>> 1 ^^^ h <<< 31) ^^^ l >>> 8) ^^^ h <<< 24) ^^^ l >>> 7) ^^^ h <<< 25) := by
  unfold sigma0
  rw [rotr_lt 1 h l (by omega) (by omega), rotr_lt 8 h l (by omega) (by omega),
    shr_lt 7 h l (by omega) (by omega)]
  simp only [BitVec.xor_append, Nat.reduceSub, BitVec.xor_assoc]

/-- `σ1` (rotations 19, 61, shift 6) on `W[j+14] = h ++ l`. -/
theorem sigma1_pair (h l : BitVec 32) :
    sigma1 (h ++ l) =
      ((((h >>> 19 ^^^ l <<< 13) ^^^ l >>> 29) ^^^ h <<< 3) ^^^ h >>> 6) ++
      (((((l >>> 19 ^^^ h <<< 13) ^^^ h >>> 29) ^^^ l <<< 3) ^^^ l >>> 6) ^^^ h <<< 26) := by
  unfold sigma1
  rw [rotr_lt 19 h l (by omega) (by omega), show (61 : Nat) = 32 + 29 from rfl,
    rotr_ge 29 h l (by omega) (by omega), shr_lt 6 h l (by omega) (by omega)]
  simp only [BitVec.xor_append, Nat.reduceSub, BitVec.xor_assoc]

/-! ## `Ch` and `Maj` -/

theorem ch_bits {w : Nat} (e f g : BitVec w) :
    (e &&& f) ^^^ (~~~e &&& g) = ((f ^^^ g) &&& e) ^^^ g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> simp_all

theorem maj_bits {w : Nat} (a b c : BitVec w) :
    (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) = ((a ^^^ b) &&& (c ^^^ b)) ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> simp_all

/-- `Ch(e, f, g)`: `eors f, g; ands e; eors g` on each half. -/
theorem Ch_pair (eh el fh fl gh gl : BitVec 32) :
    Ch (eh ++ el) (fh ++ fl) (gh ++ gl) =
      (((fh ^^^ gh) &&& eh) ^^^ gh) ++ (((fl ^^^ gl) &&& el) ^^^ gl) := by
  unfold Ch
  rw [ch_bits, BitVec.xor_append, BitVec.and_append, BitVec.xor_append]

/-- `Maj(a, b, c)`: `eors c, b; eors a, b; ands; eors b` on each half. -/
theorem Maj_pair (ah al bh bl ch cl : BitVec 32) :
    Maj (ah ++ al) (bh ++ bl) (ch ++ cl) =
      (((ah ^^^ bh) &&& (ch ^^^ bh)) ^^^ bh) ++ (((al ^^^ bl) &&& (cl ^^^ bl)) ^^^ bl) := by
  unfold Maj
  rw [maj_bits, BitVec.xor_append, BitVec.xor_append, BitVec.and_append, BitVec.xor_append]

/-! ## 64-bit addition -/

theorem toNat_app {n m : Nat} (x : BitVec n) (y : BitVec m) :
    (x ++ y).toNat = x.toNat * 2 ^ m + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- `adds rl, xl, yl; adcs rh, xh, yh`, with the carry `c` of the low words. -/
theorem add_pair {xh xl yh yl rh rl : BitVec 32} {c : Nat}
    (hlo : rl.toNat + 2 ^ 32 * c = xl.toNat + yl.toNat)
    (hhi : rh.toNat = (xh.toNat + yh.toNat + c) % 2 ^ 32) :
    (xh ++ xl) + (yh ++ yl) = rh ++ rl := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_app, toNat_app, toNat_app, hhi]
  have := rl.isLt; have := xl.isLt; have := yl.isLt; have := xh.isLt; have := yh.isLt
  omega

/-- `T1` as `round_body` sums it: `Σ1(e) + Ch + h + K_t + W_t`. -/
theorem T1_order (h s1 ch k w : Word) : s1 + ch + h + k + w = h + s1 + ch + k + w := by
  rw [BitVec.add_comm (s1 + ch) h, BitVec.add_assoc h s1 ch]

/-- `a' = T2 + T1` in `round_body`, `T1 + T2` in the specification. -/
theorem a_order (t1 t2 : Word) : t2 + t1 = t1 + t2 := BitVec.add_comm t2 t1

/-- The schedule step: `W[j] + σ0(W[j+1]) + W[j+9] + σ1(W[j+14])` (indices mod 16) is
`σ1(W_{t-2}) + W_{t-7} + σ0(W_{t-15}) + W_{t-16}`. -/
theorem sched_order (w16 s0 w7 s1 : Word) : w16 + s0 + w7 + s1 = s1 + w7 + s0 + w16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add]
  omega

/-! ## Big-endian loads and stores -/

/-- ARMv6-M `REV`; the same definition as the model's `revBytes` (proofs `882401b`). -/
def rev32 (x : BitVec 32) : BitVec 32 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8

/-- The four bytes that `str`/`stm` write for `x`, lowest address first. -/
def leBytes (x : BitVec 32) : List Byte :=
  [x.extractLsb' 0 8, x.extractLsb' 8 8, x.extractLsb' 16 8, x.extractLsb' 24 8]

/-- The word that `ldr`/`ldm` read from the bytes `b0, b1, b2, b3` (`read32`). -/
def leWord (b0 b1 b2 b3 : Byte) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

theorem rev_leWord (b0 b1 b2 b3 : Byte) : rev32 (leWord b0 b1 b2 b3) = b0 ++ b1 ++ b2 ++ b3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [rev32, leWord, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i by omega) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h <;> pair_bits

/-- `ldm r1!, {r4, r5}; rev r6, r4; rev r4, r5; stm r2!, {r4, r6}`: the stored pair (high
word `rev` of the first word) is the specification's big-endian word of the 8 bytes. -/
theorem toWord_pair (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) :
    toWord [b0, b1, b2, b3, b4, b5, b6, b7] =
      rev32 (leWord b0 b1 b2 b3) ++ rev32 (leWord b4 b5 b6 b7) := by
  rw [rev_leWord, rev_leWord]
  apply BitVec.eq_of_toNat_eq
  simp only [toWord, List.foldl, BitVec.toNat_ofNat, toNat_app, Nat.reducePow]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  omega

/-- `rev` then `str`: the bytes of `x`, most significant first. -/
theorem leBytes_rev (x : BitVec 32) :
    leBytes (rev32 x) =
      [x.extractLsb' 24 8, x.extractLsb' 16 8, x.extractLsb' 8 8, x.extractLsb' 0 8] := by
  simp only [leBytes, rev32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;> pair_bits

/-- `ldm r0!, {r2, r3}; rev r3, r3; rev r2, r2; stm r1!, {r3}; stm r1!, {r2}`: the 8 bytes
of `emit_final` for the pair `h ++ l` are the specification's big-endian bytes. -/
theorem bytesBE_pair (h l : BitVec 32) :
    bytesBE 8 (h ++ l).toNat = leBytes (rev32 h) ++ leBytes (rev32 l) := by
  rw [leBytes_rev, leBytes_rev, toNat_app]
  simp only [bytesBE, List.range, List.range.loop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  have := h.isLt; have := l.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one] <;> omega

theorem bytesBE16 (x : Nat) (hx : x < 2 ^ 64) :
    bytesBE 16 x = List.replicate 8 0#8 ++ bytesBE 8 x := by
  simp only [bytesBE, List.range, List.range.loop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, List.replicate, List.cons.injEq, and_true, Nat.reducePow,
    Nat.reduceMul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Nat.div_eq_of_lt (by omega)] <;> rfl

/-- The length field of `emit_final`: with `N < 2^32` bytes hashed, the 16 bytes at `BUF + 112`
(two zero words, then `rev (N >> 29)` and `rev (N << 3)`) are the specification's 128-bit
big-endian bit length `8 N`. -/
theorem length_bytes (N : BitVec 32) :
    bytesBE 16 (8 * N.toNat) =
      leBytes 0#32 ++ leBytes 0#32 ++ leBytes (rev32 (N >>> 29)) ++ leBytes (rev32 (N <<< 3)) := by
  have hN := N.isLt
  have e : 8 * N.toNat = ((N >>> 29) ++ (N <<< 3)).toNat := by
    rw [toNat_app, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq]
    omega
  have hz : leBytes 0#32 ++ leBytes 0#32 = List.replicate 8 0#8 := by decide
  rw [bytesBE16 _ (by omega), e, bytesBE_pair, ← hz]
  simp only [List.append_assoc]

/-- Section 5.1.2 on whole bytes: the zero bytes after `0x80` number `111 - N mod 128` when the
length field fits the current block (`N mod 128 ≤ 111`), else `239 - N mod 128`. -/
theorem pad_zeros (N : Nat) :
    ((896 + 1023 - 8 * N % 1024) % 1024 - 7) / 8 =
      if N % 128 ≤ 111 then 111 - N % 128 else 239 - N % 128 := by
  split <;> omega

end M0Crypto.Release.Ed25519Sha512Pairs
