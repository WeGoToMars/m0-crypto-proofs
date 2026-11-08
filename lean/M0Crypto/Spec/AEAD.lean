import M0Crypto.Spec.ChaCha20

/-!
RFC 8439 specifications for ChaCha20 encryption (§2.4), Poly1305 (§2.5) and the
ChaCha20-Poly1305 AEAD (§2.8), as direct transcriptions over `Nat` and byte lists.

These are the statements the machine-code proofs refine. They are checked here
only against the RFC's published vectors (compiled `#guard` evaluations, not
kernel proofs). Length preconditions (32-byte keys, 12-byte nonces) are stated
by the API theorems, not enforced by these functions.
-/

namespace M0Crypto.Spec.AEAD

open M0Crypto.Spec.ChaCha20 (Byte Word block)

/-! ## ChaCha20 encryption (§2.4) -/

/-- Key stream of `n` bytes starting at block `counter`. Block counters are taken
modulo 2^32 here; the library rejects calls whose counter would wrap. -/
def keystream (key : List Byte) (counter : Nat) (nonce : List Byte) (n : Nat) : List Byte :=
  ((List.range ((n + 63) / 64)).flatMap fun i =>
    block key (BitVec.ofNat 32 (counter + i)) nonce).take n

/-- RFC 8439 §2.4: `msg XOR keystream`. Encryption and decryption are the same. -/
def chacha20 (key : List Byte) (counter : Nat) (nonce : List Byte) (msg : List Byte) :
    List Byte :=
  (msg.zip (keystream key counter nonce msg.length)).map fun (a, b) => a ^^^ b

/-- The call is accepted iff every block counter it needs is below 2^32. -/
def counterOk (counter len : Nat) : Bool := counter + (len + 63) / 64 ≤ 2 ^ 32

/-! ## Poly1305 (§2.5) -/

def p : Nat := 2 ^ 130 - 5

/-- Little-endian integer of a byte list. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- Little-endian bytes of `x mod 256^n`. -/
def leBytes (n x : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- RFC 8439 §2.5 clamp. -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- 16-byte chunks; the last may be shorter (and is nonempty). -/
def chunks16 : List Byte → List (List Byte)
  | [] => []
  | b :: rest => (b :: rest).take 16 :: chunks16 ((b :: rest).drop 16)
termination_by bs => bs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Accumulator after absorbing `msg` (each chunk with its 0x01 byte appended). -/
def polyAcc (r : Nat) (msg : List Byte) : Nat :=
  (chunks16 msg).foldl (fun acc c => (acc + leNat (c ++ [1#8])) * r % p) 0

/-- RFC 8439 §2.5 Poly1305 MAC with a 32-byte one-time key `r || s`. -/
def poly1305 (key : List Byte) (msg : List Byte) : List Byte :=
  let r := clamp (leNat (key.take 16))
  let s := leNat (key.drop 16 |>.take 16)
  leBytes 16 (polyAcc r msg + s)

/-! ## AEAD (§2.8) -/

def pad16 (bs : List Byte) : List Byte := List.replicate ((16 - bs.length % 16) % 16) 0#8

/-- RFC 8439 §2.8 MAC input. -/
def macData (aad ct : List Byte) : List Byte :=
  aad ++ pad16 aad ++ ct ++ pad16 ct ++ leBytes 8 aad.length ++ leBytes 8 ct.length

/-- RFC 8439 §2.6 one-time Poly1305 key: the first 32 bytes of block 0. -/
def polyKey (key nonce : List Byte) : List Byte := (block key 0#32 nonce).take 32

/-- RFC 8439 §2.8 encryption: ciphertext and tag. -/
def encrypt (key nonce aad pt : List Byte) : List Byte × List Byte :=
  let ct := chacha20 key 1 nonce pt
  (ct, poly1305 (polyKey key nonce) (macData aad ct))

/-- RFC 8439 §2.8 decryption: the plaintext if the tag verifies, else `none`. -/
def decrypt (key nonce aad ct tag : List Byte) : Option (List Byte) :=
  if poly1305 (polyKey key nonce) (macData aad ct) = tag then some (chacha20 key 1 nonce ct)
  else none

/-! ## RFC 8439 vectors (compiled evaluation) -/

def ofStr (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

def sunscreen : List Byte := ofStr
  "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."

-- §2.4.2: key 00..1f, nonce 00:00:00:00:00:00:00:4a:00:00:00:00, counter 1.
#guard (chacha20 ((List.range 32).map (BitVec.ofNat 8)) 1 [0,0,0,0,0,0,0,0x4a,0,0,0,0]
  sunscreen).take 16 ==
  [0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80, 0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d, 0x69, 0x81]

-- §2.5.2 Poly1305.
#guard poly1305
  [0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
   0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b]
  (ofStr "Cryptographic Forum Research Group") ==
  [0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6, 0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9]

def rfc2_8_2Key : List Byte := (List.range 32).map fun i => BitVec.ofNat 8 (0x80 + i)
def rfc2_8_2Nonce : List Byte := [0x07, 0, 0, 0, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]
def rfc2_8_2Aad : List Byte := [0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7]
def rfc2_8_2Tag : List Byte :=
  [0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a, 0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91]

-- §2.8.2 AEAD: ciphertext prefix and tag, and that `decrypt` inverts `encrypt`.
#guard (encrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad sunscreen).1.take 8 ==
  [0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb]
#guard (encrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad sunscreen).2 == rfc2_8_2Tag
#guard decrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad
  (encrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad sunscreen).1 rfc2_8_2Tag == some sunscreen
#guard decrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad
  (encrypt rfc2_8_2Key rfc2_8_2Nonce rfc2_8_2Aad sunscreen).1 (rfc2_8_2Tag.set 15 0) == none

end M0Crypto.Spec.AEAD
