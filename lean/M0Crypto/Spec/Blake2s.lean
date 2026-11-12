/-
BLAKE2s-256 reference specification following RFC 7693 (unkeyed, 32-byte digest).

This file is the independent specification, written from the RFC text and not from
any assembly schedule. It must not import the machine model. Executable checks against
published vectors are in `M0Crypto.Spec.Blake2sVectors`.

Two descriptions of the same function appear here:

* `blake2s`, the RFC 7693 algorithm: split the message into 64-byte blocks, compress each
  with the byte counter `t`, and compress the last (zero-padded, possibly partial) block
  with the final flag.
* an abstract streaming state `(h, count, pending)` with `absorb` and `finish`, whose
  `pending` keeps a full block back until more input arrives (the last block is only
  known to be last at `finish`). `finish_absorb` proves it equals `blake2s`, and so any
  partition of the message gives the same digest (`stream_partition`).
-/

namespace M0Crypto.Spec.Blake2s

abbrev Word := BitVec 32
abbrev Byte := BitVec 8

/-- RFC 7693 §2.1 `>>>`: right rotation. -/
def rotr (x : Word) (n : Nat) : Word :=
  (x >>> n) ||| (x <<< (32 - n))

/-- RFC 7693 §2.6 initialization vector. -/
def IV : Array Word :=
  #[0x6A09E667#32, 0xBB67AE85#32, 0x3C6EF372#32, 0xA54FF53A#32,
    0x510E527F#32, 0x9B05688C#32, 0x1F83D9AB#32, 0x5BE0CD19#32]

/-- RFC 7693 §2.7 message word schedule, ten rows (rounds 10 and 11 would reuse rows 0, 1). -/
def SIGMA : Array (Array Nat) :=
  #[#[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
    #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
    #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
    #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
    #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
    #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
    #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
    #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
    #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
    #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- RFC 7693 §3.1 mixing function `G` on four words and two message words,
returned as `(a, b, c, d)`. -/
def G (a b c d x y : Word) : Word × Word × Word × Word :=
  let a := a + b + x
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 12
  let a := a + b + y
  let d := rotr (d ^^^ a) 8
  let c := c + d
  let b := rotr (b ^^^ c) 7
  (a, b, c, d)

/-- The 16-word working vector. -/
abbrev Vec := Array Word

/-- `G` applied to working-vector indices `ia ib ic id` with message words `x y`. -/
def mix (v : Vec) (ia ib ic id : Nat) (x y : Word) : Vec :=
  let (a, b, c, d) := G v[ia]! v[ib]! v[ic]! v[id]! x y
  (((v.set! ia a).set! ib b).set! ic c).set! id d

/-- RFC 7693 §3.2 round `r`: four column `G`s then four diagonal `G`s, with message
words chosen by `SIGMA[r % 10]`. -/
def round (v : Vec) (m : Array Word) (r : Nat) : Vec :=
  let s := SIGMA[r % 10]!
  let v := mix v 0 4  8 12 m[s[ 0]!]! m[s[ 1]!]!
  let v := mix v 1 5  9 13 m[s[ 2]!]! m[s[ 3]!]!
  let v := mix v 2 6 10 14 m[s[ 4]!]! m[s[ 5]!]!
  let v := mix v 3 7 11 15 m[s[ 6]!]! m[s[ 7]!]!
  let v := mix v 0 5 10 15 m[s[ 8]!]! m[s[ 9]!]!
  let v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  let v := mix v 2 7  8 13 m[s[12]!]! m[s[13]!]!
  let v := mix v 3 4  9 14 m[s[14]!]! m[s[15]!]!
  v

/-- Apply rounds `0 .. n-1`. -/
def rounds (m : Array Word) : Nat → Vec → Vec
  | 0, v => v
  | n + 1, v => round (rounds m n v) m n

/-- RFC 7693 §3.2 initial working vector for chain value `h`, offset counter `t`
(64 bits, low word `t0`) and finalization flag `f`. -/
def initVec (h : Array Word) (t : Nat) (f : Bool) : Vec :=
  let t0 : Word := BitVec.ofNat 32 t
  let t1 : Word := BitVec.ofNat 32 (t / 2 ^ 32)
  let v := h ++ IV
  let v := v.set! 12 (v[12]! ^^^ t0)
  let v := v.set! 13 (v[13]! ^^^ t1)
  if f then v.set! 14 (v[14]! ^^^ 0xFFFFFFFF#32) else v

/-- RFC 7693 §3.2 compression function `F(h, m, t, f)`: ten rounds, then
`h[i] ^= v[i] ^ v[i + 8]`. `m` is the 16 message words of the block. -/
def compress (h m : Array Word) (t : Nat) (f : Bool) : Array Word :=
  let v := rounds m 10 (initVec h t f)
  (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- Little-endian word from four bytes. -/
def wordOfBytes (b0 b1 b2 b3 : Byte) : Word :=
  b0.setWidth 32 ||| (b1.setWidth 32 <<< 8) ||| (b2.setWidth 32 <<< 16) ||| (b3.setWidth 32 <<< 24)

/-- Little-endian words from a byte list; trailing bytes beyond a multiple of 4 are ignored. -/
def wordsOfBytes : List Byte → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => wordOfBytes b0 b1 b2 b3 :: wordsOfBytes rest
  | _ => []

/-- Little-endian serialization of one word. -/
def bytesOfWord (w : Word) : List Byte :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- RFC 7693 §3.3: the final block is padded with zeros to 64 bytes. -/
def pad (bs : List Byte) : List Byte :=
  bs ++ List.replicate (64 - bs.length) 0#8

/-- Message words of a (possibly partial) block, zero padded to 16 words. -/
def blockWords (bs : List Byte) : Array Word :=
  (wordsOfBytes (pad bs)).toArray

/-- RFC 7693 §2.5, §3.3 initial chain value: `h[0] = IV[0] ^ 0x01010000 ^ (kk << 8) ^ nn`
with `kk = 0` (unkeyed) and `nn = 32`. -/
def h0 : Array Word := IV.set! 0 (IV[0]! ^^^ 0x01010020#32)

/-- Serialization of the chain value as the 32-byte digest, little endian. -/
def digestOf (h : Array Word) : List Byte :=
  (h.toList.take 8).flatMap bytesOfWord

/-- RFC 7693 §3.3 main loop on the remaining message `msg`, with `c` bytes already
compressed: every block except the last is compressed with `t = c + 64` and `f = false`;
the last block (1 to 64 bytes, or the empty message) is padded and compressed with
`t = c + length` and `f = true`. -/
def loop (h : Array Word) (c : Nat) (msg : List Byte) : Array Word :=
  if hl : 64 < msg.length then
    loop (compress h (blockWords (msg.take 64)) (c + 64) false) (c + 64) (msg.drop 64)
  else
    compress h (blockWords msg) (c + msg.length) true
termination_by msg.length
decreasing_by simp; omega

/-- RFC 7693 BLAKE2s-256, unkeyed: the digest of the byte list. -/
def blake2s (msg : List Byte) : List Byte :=
  digestOf (loop h0 0 msg)

/-! ## Streaming state -/

/-- Chain value, bytes compressed so far, and the bytes not yet compressed. A full block
stays in `pending` until a further byte arrives. -/
structure State where
  h : Array Word
  count : Nat
  pending : List Byte

/-- The empty stream. -/
def State.init : State := ⟨h0, 0, []⟩

/-- Absorb one byte: a full pending block is first compressed as a non-final block. -/
def State.push (s : State) (b : Byte) : State :=
  if s.pending.length = 64 then
    ⟨compress s.h (blockWords s.pending) (s.count + 64) false, s.count + 64, [b]⟩
  else
    ⟨s.h, s.count, s.pending ++ [b]⟩

/-- Absorb a byte list. -/
def absorb (s : State) (bs : List Byte) : State := bs.foldl State.push s

/-- Compress the pending bytes as the final block and emit the digest. -/
def finish (s : State) : List Byte :=
  digestOf (compress s.h (blockWords s.pending) (s.count + s.pending.length) true)

theorem loop_short (h : Array Word) (c : Nat) (msg : List Byte) (hl : msg.length ≤ 64) :
    loop h c msg = compress h (blockWords msg) (c + msg.length) true := by
  rw [loop]; simp; omega

theorem loop_long (h : Array Word) (c : Nat) (msg : List Byte) (hl : 64 < msg.length) :
    loop h c msg = loop (compress h (blockWords (msg.take 64)) (c + 64) false) (c + 64)
      (msg.drop 64) := by
  rw [loop]; simp [hl]

theorem push_length (s : State) (b : Byte) (hs : s.pending.length ≤ 64) :
    (s.push b).pending.length ≤ 64 := by
  unfold State.push; split <;> simp <;> omega

theorem absorb_length (bs : List Byte) : ∀ (s : State), s.pending.length ≤ 64 →
    (absorb s bs).pending.length ≤ 64 := by
  induction bs with
  | nil => intro s h; simpa [absorb] using h
  | cons b bs ih => intro s h; simp only [absorb, List.foldl_cons]; exact ih _ (push_length s b h)

/-- The streaming state computes the RFC loop on the pending bytes followed by the rest. -/
theorem finish_absorb_gen (bs : List Byte) : ∀ (s : State), s.pending.length ≤ 64 →
    digestOf (loop s.h s.count (s.pending ++ bs)) = finish (absorb s bs) := by
  induction bs with
  | nil =>
    intro s hs
    simp only [absorb, List.foldl_nil, List.append_nil, finish]
    rw [loop_short _ _ _ hs]
  | cons b bs ih =>
    intro s hs
    simp only [absorb, List.foldl_cons]
    by_cases hp : s.pending.length = 64
    · have hlong : 64 < (s.pending ++ b :: bs).length := by simp; omega
      rw [loop_long _ _ _ hlong]
      have ht : (s.pending ++ b :: bs).take 64 = s.pending := by
        rw [List.take_append_of_le_length (by omega)]
        exact List.take_of_length_le (by omega)
      have hd : (s.pending ++ b :: bs).drop 64 = [b] ++ bs := by
        rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
        rfl
      rw [ht, hd]
      have := ih (s.push b) (push_length s b hs)
      simp only [State.push, hp, ite_true] at this
      simpa [absorb, State.push, hp] using this
    · have := ih (s.push b) (push_length s b hs)
      simp only [State.push, hp, ite_false] at this
      have e : s.pending ++ b :: bs = (s.pending ++ [b]) ++ bs := by simp
      rw [e]
      simpa [absorb, State.push, hp] using this

/-- RFC 7693 `blake2s` equals the streaming description on any input. -/
theorem finish_absorb (msg : List Byte) : finish (absorb State.init msg) = blake2s msg := by
  have := finish_absorb_gen msg State.init (by simp [State.init])
  simpa [State.init, blake2s] using this.symm

/-- Any partition of a message into `update` calls gives the digest of the message. -/
theorem stream_partition (parts : List (List Byte)) :
    finish (parts.foldl absorb State.init) = blake2s parts.flatten := by
  rw [← finish_absorb]
  congr 1
  have : ∀ (s : State) (ps : List (List Byte)), ps.foldl absorb s = absorb s ps.flatten := by
    intro s ps
    induction ps generalizing s with
    | nil => simp [absorb]
    | cons p ps ih => simp [ih, absorb, List.foldl_append]
  exact this _ _

theorem flatMap_bytesOfWord_length (l : List Word) : (l.flatMap bytesOfWord).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, bytesOfWord, ih]; omega

/-- The digest of an eight-word chain value has 32 bytes. -/
theorem digestOf_length (h : Array Word) (hh : h.size = 8) : (digestOf h).length = 32 := by
  have : (h.toList.take 8).length = 8 := by simp [hh]
  simp only [digestOf, flatMap_bytesOfWord_length, this]

end M0Crypto.Spec.Blake2s
