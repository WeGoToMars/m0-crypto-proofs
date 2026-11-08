/-
ChaCha20 reference specification following RFC 8439, sections 2.1-2.3.

This file is the independent specification. It is written from the RFC text,
not from any assembly schedule, and must not import the machine model.
Executable checks against the RFC test vectors are in
`M0Crypto.Spec.ChaCha20Vectors`.
-/

namespace M0Crypto.Spec.ChaCha20

/-- A 32-bit ChaCha word. -/
abbrev Word := BitVec 32

/-- A byte. -/
abbrev Byte := BitVec 8

/-- RFC 8439 §2.1 `<<<`: left rotation, written as `(a << n) | (a >> (32 - n))`. -/
def rotl (x : Word) (n : Nat) : Word :=
  (x <<< n) ||| (x >>> (32 - n))

/-- RFC 8439 §2.1 quarter round on four words, returned as `(a, b, c, d)`. -/
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  let a := a + b
  let d := d ^^^ a
  let d := rotl d 16
  let c := c + d
  let b := b ^^^ c
  let b := rotl b 12
  let a := a + b
  let d := d ^^^ a
  let d := rotl d 8
  let c := c + d
  let b := b ^^^ c
  let b := rotl b 7
  (a, b, c, d)

/-- The 16-word ChaCha state. Functions below preserve size 16. -/
abbrev State := Array Word

/-- RFC 8439 §2.2 `QUARTERROUND(x, y, z, w)` applied to state indices. -/
def qround (s : State) (x y z w : Nat) : State :=
  let (a, b, c, d) := quarterRound s[x]! s[y]! s[z]! s[w]!
  ((s.set! x a).set! y b |>.set! z c).set! w d

/-- RFC 8439 §2.3.1 `inner_block`: one column round and one diagonal round. -/
def innerBlock (s : State) : State :=
  let s := qround s 0 4  8 12
  let s := qround s 1 5  9 13
  let s := qround s 2 6 10 14
  let s := qround s 3 7 11 15
  let s := qround s 0 5 10 15
  let s := qround s 1 6 11 12
  let s := qround s 2 7  8 13
  let s := qround s 3 4  9 14
  s

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

/-- RFC 8439 §2.3 constants "expand 32-byte k". -/
def constants : List Word :=
  [0x61707865#32, 0x3320646e#32, 0x79622d32#32, 0x6b206574#32]

/-- RFC 8439 §2.3 initial state from a 32-byte key, 32-bit block counter and 12-byte nonce. -/
def initState (key : List Byte) (counter : Word) (nonce : List Byte) : State :=
  (constants ++ wordsOfBytes key ++ [counter] ++ wordsOfBytes nonce).toArray

/-- Apply `innerBlock` `n` times. -/
def innerBlocks : Nat → State → State
  | 0, s => s
  | n + 1, s => innerBlocks n (innerBlock s)

/-- RFC 8439 §2.3 block function as 16 output words (before serialization). -/
def blockWords (key : List Byte) (counter : Word) (nonce : List Byte) : State :=
  let s := initState key counter nonce
  let w := innerBlocks 10 s
  (List.range 16).toArray.map fun i => s[i]! + w[i]!

/-- RFC 8439 §2.3 block function: 64 serialized keystream bytes.
Preconditions (not enforced): `key.length = 32`, `nonce.length = 12`. -/
def block (key : List Byte) (counter : Word) (nonce : List Byte) : List Byte :=
  (blockWords key counter nonce).toList.flatMap bytesOfWord

/-! Size contracts for composition with the machine proofs. The raw Array/list
functions above remain available for the existing refinement bridges. -/

theorem qround_size (s : State) (a b c d : Nat) :
    (qround s a b c d).size = s.size := by
  simp [qround]

theorem innerBlock_size (s : State) : (innerBlock s).size = s.size := by
  simp only [innerBlock, qround_size]

theorem innerBlocks_size (n : Nat) (s : State) : (innerBlocks n s).size = s.size := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [innerBlocks, ih, innerBlock_size]

theorem wordsOfBytes_length (bs : List Byte) :
    (wordsOfBytes bs).length = bs.length / 4 := by
  match bs with
  | [] => rfl
  | [_] => simp [wordsOfBytes]
  | [_, _] => simp [wordsOfBytes]
  | [_, _, _] => simp [wordsOfBytes]
  | _ :: _ :: _ :: _ :: rest =>
    simp only [wordsOfBytes, List.length_cons, wordsOfBytes_length rest]
    omega

theorem initState_size (key nonce : List Byte) (counter : Word)
    (hk : key.length = 32) (hn : nonce.length = 12) :
    (initState key counter nonce).size = 16 := by
  simp [initState, constants, wordsOfBytes_length, hk, hn]

theorem block_length (key nonce : List Byte) (counter : Word) :
    (block key counter nonce).length = 64 := by
  simp [block, blockWords, bytesOfWord, List.range_succ]

/-- Inputs whose lengths are enforced at the specification boundary. -/
abbrev Key := { bs : List Byte // bs.length = 32 }
abbrev Nonce := { bs : List Byte // bs.length = 12 }
abbrev SizedState := { s : State // s.size = 16 }

/-- Construct a valid state without leaving length obligations to callers. -/
def initSized (key : Key) (counter : Word) (nonce : Nonce) : SizedState :=
  ⟨initState key.val counter nonce.val, initState_size _ _ _ key.property nonce.property⟩

/-- Double round preserving the state-size invariant. -/
def innerBlockSized (s : SizedState) : SizedState :=
  ⟨innerBlock s.val, (innerBlock_size s.val).trans s.property⟩

/-- Iterated double rounds preserving the state-size invariant. -/
def innerBlocksSized (n : Nat) (s : SizedState) : SizedState :=
  ⟨innerBlocks n s.val, (innerBlocks_size n s.val).trans s.property⟩

/-- Length-checked entry point for the existing RFC block specification. -/
def blockSized (key : Key) (counter : Word) (nonce : Nonce) :
    { bs : List Byte // bs.length = 64 } :=
  ⟨block key.val counter nonce.val, block_length _ _ _⟩

end M0Crypto.Spec.ChaCha20
