/-!
# SHA-512 (FIPS 180-4), as used by Ed25519

SHA-512 of a byte string, written from FIPS 180-4 with its names and in its order. Core Lean
only. SHA-512 is internal to the Ed25519 asset (constraint C5 of `ed25519.md`), so this module
belongs to the Ed25519 family. Messages are whole bytes; FIPS 180-4 allows any bit length.

Reading guide, against FIPS 180-4:
* `ROTR`, `SHR`: section 3.2, with `w = 64`. Word addition `+` is addition modulo 2^64.
* `Ch`, `Maj`, `Sigma0`, `Sigma1`, `sigma0`, `sigma1`: section 4.1.3.
* `K`: section 4.2.3. `H0`: section 5.3.5. Both are listed in hexadecimal as in the standard;
  `Ed25519Sha512Vectors` checks them against their definition (fractional parts of cube and
  square roots of the first primes) in the kernel.
* `pad`: section 5.1.2. `parse`: section 5.2.2. `schedule`, `compress`: section 6.4.2, steps
  1 to 4. `hash`, `sha512`: section 6.4.2, the loop over the blocks and the final hash value.
-/

namespace M0Crypto.Spec.Sha512

abbrev Byte := BitVec 8
abbrev Word := BitVec 64

/-! ## Functions and constants -/

/-- `ROTR^n(x) = (x >> n) ∨ (x << w - n)`. -/
def ROTR (n : Nat) (x : Word) : Word := (x >>> n) ||| (x <<< (64 - n))

/-- `SHR^n(x) = x >> n`. -/
def SHR (n : Nat) (x : Word) : Word := x >>> n

def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0^{512}`. -/
def Sigma0 (x : Word) : Word := ROTR 28 x ^^^ ROTR 34 x ^^^ ROTR 39 x

/-- `Σ1^{512}`. -/
def Sigma1 (x : Word) : Word := ROTR 14 x ^^^ ROTR 18 x ^^^ ROTR 41 x

/-- `σ0^{512}`. -/
def sigma0 (x : Word) : Word := ROTR 1 x ^^^ ROTR 8 x ^^^ SHR 7 x

/-- `σ1^{512}`. -/
def sigma1 (x : Word) : Word := ROTR 19 x ^^^ ROTR 61 x ^^^ SHR 6 x

/-- Section 4.2.3: `K_0 ... K_79`, the first 64 bits of the fractional parts of the cube roots
of the first eighty prime numbers. -/
def K : Array Word := #[
    0x428a2f98d728ae22#64, 0x7137449123ef65cd#64, 0xb5c0fbcfec4d3b2f#64, 0xe9b5dba58189dbbc#64,
    0x3956c25bf348b538#64, 0x59f111f1b605d019#64, 0x923f82a4af194f9b#64, 0xab1c5ed5da6d8118#64,
    0xd807aa98a3030242#64, 0x12835b0145706fbe#64, 0x243185be4ee4b28c#64, 0x550c7dc3d5ffb4e2#64,
    0x72be5d74f27b896f#64, 0x80deb1fe3b1696b1#64, 0x9bdc06a725c71235#64, 0xc19bf174cf692694#64,
    0xe49b69c19ef14ad2#64, 0xefbe4786384f25e3#64, 0x0fc19dc68b8cd5b5#64, 0x240ca1cc77ac9c65#64,
    0x2de92c6f592b0275#64, 0x4a7484aa6ea6e483#64, 0x5cb0a9dcbd41fbd4#64, 0x76f988da831153b5#64,
    0x983e5152ee66dfab#64, 0xa831c66d2db43210#64, 0xb00327c898fb213f#64, 0xbf597fc7beef0ee4#64,
    0xc6e00bf33da88fc2#64, 0xd5a79147930aa725#64, 0x06ca6351e003826f#64, 0x142929670a0e6e70#64,
    0x27b70a8546d22ffc#64, 0x2e1b21385c26c926#64, 0x4d2c6dfc5ac42aed#64, 0x53380d139d95b3df#64,
    0x650a73548baf63de#64, 0x766a0abb3c77b2a8#64, 0x81c2c92e47edaee6#64, 0x92722c851482353b#64,
    0xa2bfe8a14cf10364#64, 0xa81a664bbc423001#64, 0xc24b8b70d0f89791#64, 0xc76c51a30654be30#64,
    0xd192e819d6ef5218#64, 0xd69906245565a910#64, 0xf40e35855771202a#64, 0x106aa07032bbd1b8#64,
    0x19a4c116b8d2d0c8#64, 0x1e376c085141ab53#64, 0x2748774cdf8eeb99#64, 0x34b0bcb5e19b48a8#64,
    0x391c0cb3c5c95a63#64, 0x4ed8aa4ae3418acb#64, 0x5b9cca4f7763e373#64, 0x682e6ff3d6b2b8a3#64,
    0x748f82ee5defb2fc#64, 0x78a5636f43172f60#64, 0x84c87814a1f0ab72#64, 0x8cc702081a6439ec#64,
    0x90befffa23631e28#64, 0xa4506cebde82bde9#64, 0xbef9a3f7b2c67915#64, 0xc67178f2e372532b#64,
    0xca273eceea26619c#64, 0xd186b8c721c0c207#64, 0xeada7dd6cde0eb1e#64, 0xf57d4f7fee6ed178#64,
    0x06f067aa72176fba#64, 0x0a637dc5a2c898a6#64, 0x113f9804bef90dae#64, 0x1b710b35131c471b#64,
    0x28db77f523047d84#64, 0x32caab7b40c72493#64, 0x3c9ebe0a15c9bebc#64, 0x431d67c49c100d4c#64,
    0x4cc5d4becb3e42b6#64, 0x597f299cfc657e2a#64, 0x5fcb6fab3ad6faec#64, 0x6c44198c4a475817#64]

/-! ## Preprocessing -/

/-- `n` bytes of `x`, most significant first. -/
def bytesBE (n x : Nat) : List Byte :=
  (List.range n).reverse.map fun i => BitVec.ofNat 8 (x / 2 ^ (8 * i))

/-- Section 5.1.2: append the bit 1, then `k` zero bits, where `k` is the smallest `k ≥ 0` with
`l + 1 + k ≡ 896 (mod 1024)`, then the length `l` in bits as a 128-bit big-endian integer. On
whole bytes, `k ≡ 7 (mod 8)`: the bit 1 and seven zero bits are the byte `0x80`, followed by
`(k - 7) / 8` zero bytes. -/
def pad (M : List Byte) : List Byte :=
  let l := 8 * M.length
  let k := (896 + 1023 - l % 1024) % 1024
  M ++ [0x80#8] ++ List.replicate ((k - 7) / 8) 0#8 ++ bytesBE 16 l

/-- A 64-bit word from bytes, the first byte most significant (section 3.1). -/
def toWord (bs : List Byte) : Word :=
  BitVec.ofNat 64 (bs.foldl (fun a b => 256 * a + b.toNat) 0)

/-- Section 5.2.2: the sixteen 64-bit words `M_0 ... M_15` of a 1024-bit (128-byte) block. -/
def parse (block : List Byte) : Array Word :=
  ((List.range 16).map fun j => toWord ((block.drop (8 * j)).take 8)).toArray

/-- Section 5.3.5: the initial hash value `H(0)`, the first 64 bits of the fractional parts of
the square roots of the first eight prime numbers. -/
def H0 : Array Word :=
  #[0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
    0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-! ## Hash computation (section 6.4.2) -/

/-- Step 1, the message schedule: `W_t = M_t` for `t < 16`, then
`W_t = σ1(W_{t-2}) + W_{t-7} + σ0(W_{t-15}) + W_{t-16}` for `16 ≤ t ≤ 79`. -/
def schedule (M : Array Word) : Array Word :=
  (List.range' 16 64).foldl
    (fun W t => W.push (sigma1 W[t - 2]! + W[t - 7]! + sigma0 W[t - 15]! + W[t - 16]!)) M

/-- The eight working variables. -/
structure Vars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

/-- Step 3, iteration `t`. -/
def round (W : Array Word) (v : Vars) (t : Nat) : Vars :=
  let T1 := v.h + Sigma1 v.e + Ch v.e v.f v.g + K[t]! + W[t]!
  let T2 := Sigma0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T1, d := v.c, c := v.b, b := v.a, a := T1 + T2 }

/-- Steps 1 to 4 for one block: schedule, initialise the working variables with `H(i-1)`,
eighty rounds, and `H(i)_j = v_j + H(i-1)_j`. -/
def compress (H : Array Word) (block : List Byte) : Array Word :=
  let W := schedule (parse block)
  let v := (List.range 80).foldl (round W) ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
  #[v.a + H[0]!, v.b + H[1]!, v.c + H[2]!, v.d + H[3]!,
    v.e + H[4]!, v.f + H[5]!, v.g + H[6]!, v.h + H[7]!]

/-- The loop `for i = 1 to N` over the 128-byte blocks of the padded message. -/
def hash (H : Array Word) : List Byte → Array Word
  | [] => H
  | b :: M => hash (compress H ((b :: M).take 128)) ((b :: M).drop 128)
termination_by M => M.length
decreasing_by simp; omega

/-- SHA-512 of a byte string: the 512-bit digest `H(N)_0 || ... || H(N)_7`, as 64 bytes. -/
def sha512 (M : List Byte) : List Byte :=
  (hash H0 (pad M)).toList.flatMap fun w => bytesBE 8 w.toNat

end M0Crypto.Spec.Sha512
