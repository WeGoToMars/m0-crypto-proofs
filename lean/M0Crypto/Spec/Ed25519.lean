import M0Crypto.Spec.Ed25519Sha512

/-!
# Ed25519 (RFC 8032 section 5.1)

Pure Ed25519 (no context, no prehash) as RFC 8032 section 5.1 states it, with the RFC's names
and in its order. Core Lean only. Field elements and scalars are natural numbers; every field
operation is reduced modulo `p` (`% p`) and the scalar `S` modulo `L`.

Points are the RFC's extended homogeneous coordinates `(X, Y, Z, T)` of section 5.1.4, added
with its formulas. Doubling uses the same formulas with equal points, as section 5.1.4 allows
("because of completeness, such substitution is valid"). Scalar multiplication is
double-and-add. A point `(X, Y, Z, T)` stands for `(x, y) = (X/Z, Y/Z)`: encoding and the
verification equation use `(x, y)`.

Nothing here is a statement about curves or groups: the claims proved about the code are
equalities with these functions.

Reading guide, against RFC 8032:
* `p`, `d`, `L`, `B`: table 1 of section 5.1. `Ed25519Vectors` checks `d = -121665/121666`
  and that `B` is on the curve with `y = 4/5`.
* `powp`, `inv`: section 5.1.1, `x^-1 = x^(p-2) (mod p)`.
* `encodeInt`, `decodeInt`, `encodePoint`: section 5.1.2. `decodePoint`: section 5.1.3, steps
  1 to 4 with every rejection.
* `Point`, `add`, `scalarMul`: section 5.1.4, and `[s]P`.
* `secretScalar`, `publicKey`: section 5.1.5.
* `signWith`, `sign`: section 5.1.6. `signWith` takes the public key `A` from the caller, as the
  library's `m0c_ed25519_sign` does; `sign` is `signWith` with `A` derived from the private key.
* `verify`: section 5.1.7, with the cofactorless check `[S]B = R + [k]A'` that step 3 allows.
  It uses `k mod L` (see `verify`).
-/

namespace M0Crypto.Spec.Ed25519

open M0Crypto.Spec.Sha512 (sha512)

abbrev Byte := BitVec 8

/-! ## Parameters (table 1) -/

/-- The field prime `2^255 - 19`. -/
def p : Nat := 2 ^ 255 - 19

/-- `d = -121665/121666` in GF(p). -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The order of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-! ## Modular arithmetic (section 5.1.1) -/

/-- `a - b` in GF(p). -/
def fsub (a b : Nat) : Nat := (a + p - b % p) % p

/-- `x^e` in GF(p). -/
def powp (x e : Nat) : Nat := x ^ e % p

/-! ### Evaluation

`x ^ e` as written cannot be evaluated for `e` near `p`. `powp_eq_fast` (a theorem, marked
`@[csimp]`) lets compiled code, such as the test vectors, compute `powp` by square-and-multiply
modulo `p`. It changes only how code is evaluated: `powp` and every theorem about it keep the
power. It precedes the uses of `powp` so that their compiled code uses it. -/

/-- `x ^ e` modulo `p`, by square-and-multiply. -/
def powpFast (x e : Nat) : Nat :=
  if e = 0 then 1 % p else
    let r := powpFast x (e / 2)
    if e % 2 = 0 then r * r % p else r * r % p * x % p
termination_by e
decreasing_by omega

theorem powpFast_eq (x e : Nat) : powpFast x e = x ^ e % p := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powpFast]
    by_cases h0 : e = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte, ih (e / 2) (by omega)]
      have hsq : x ^ (e / 2) % p * (x ^ (e / 2) % p) % p = x ^ (e / 2 * 2) % p := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      by_cases he : e % 2 = 0
      · simp only [he, ↓reduceIte, hsq]; congr 2; omega
      · simp only [he, ↓reduceIte, hsq]
        rw [Nat.mod_mul_mod, ← Nat.pow_succ]; congr 2; omega

@[csimp] theorem powp_eq_fast : @powp = @powpFast := by
  funext x e; rw [powpFast_eq, powp]

/-- `x^-1 = x^(p-2)` in GF(p). -/
def inv (x : Nat) : Nat := powp x (p - 2)

/-! ## Points (section 5.1.4) -/

/-- A point in extended homogeneous coordinates: `x = X/Z`, `y = Y/Z`, `x * y = T/Z`. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat
  deriving Repr

/-- The point `(x, y)`, with `Z = 1`. -/
def Point.ofXY (x y : Nat) : Point := ⟨x, y, 1, x * y % p⟩

/-- The neutral point `(0, 1)`. -/
def neutral : Point := ⟨0, 1, 1, 0⟩

/-- The affine coordinates `(x, y) = (X/Z, Y/Z)`. -/
def Point.xy (P : Point) : Nat × Nat := (P.X * inv P.Z % p, P.Y * inv P.Z % p)

/-- The base point `B` of table 1. -/
def B : Point := .ofXY
  15112221349535400772501151409588531511454012693041857206046113283949847762202
  46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- `(x3, y3) = (x1, y1) + (x2, y2)`, by the formulas of section 5.1.4. -/
def add (P Q : Point) : Point :=
  let A := fsub P.Y P.X * fsub Q.Y Q.X % p
  let B := (P.Y + P.X) * (Q.Y + Q.X) % p
  let C := P.T * 2 * d * Q.T % p
  let D := P.Z * 2 * Q.Z % p
  let E := fsub B A
  let F := fsub D C
  let G := (D + C) % p
  let H := (B + A) % p
  { X := E * F % p, Y := G * H % p, T := E * H % p, Z := F * G % p }

/-- `[s]P`, by double-and-add: `[s]P = [s / 2]([2]P) + [s mod 2]P`. -/
def scalarMul (s : Nat) (P : Point) : Point :=
  if s = 0 then neutral else
    let Q := scalarMul (s / 2) (add P P)
    if s % 2 = 1 then add Q P else Q
termination_by s
decreasing_by omega

/-! ## Encoding (section 5.1.2) and decoding (section 5.1.3) -/

/-- The little-endian integer `h[0] + 2^8 * h[1] + ...` of an octet string. -/
def decodeInt : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeInt bs

/-- The 32-octet little-endian encoding of an integer (its value modulo `2^256`). -/
def encodeInt (n : Nat) : List Byte :=
  (List.range 32).map fun i => BitVec.ofNat 8 (n / 2 ^ (8 * i))

/-- Section 5.1.2: `y` as 32 octets, with the least significant bit of `x` copied to the most
significant bit of the final octet. -/
def encodePoint (P : Point) : List Byte :=
  let (x, y) := P.xy
  encodeInt (y + 2 ^ 255 * (x % 2))

/-- Section 5.1.3: decode a 32-octet string to a point, or fail (`none`). -/
def decodePoint (s : List Byte) : Option Point :=
  -- 1. Bit 255 is `x_0`; clearing it gives `y`, which must be below `p`.
  let n := decodeInt s
  let x_0 := n / 2 ^ 255 % 2
  let y := n % 2 ^ 255
  if y ≥ p then none else
  -- 2. `u = y^2 - 1`, `v = d y^2 + 1`, and the candidate root `x = u v^3 (u v^7)^((p-5)/8)`.
  let u := fsub (y ^ 2) 1
  let v := (d * y ^ 2 + 1) % p
  let x := u * v ^ 3 * powp (u * v ^ 7) ((p - 5) / 8) % p
  -- 3. `v x^2 = u`: `x` is a square root; `v x^2 = -u`: `x * 2^((p-1)/4)` is; otherwise fail.
  let x? :=
    if v * x ^ 2 % p = u then some x
    else if v * x ^ 2 % p = fsub 0 u then some (x * powp 2 ((p - 1) / 4) % p)
    else none
  match x? with
  | none => none
  | some x =>
    -- 4. Fail if `x = 0` and `x_0 = 1`; otherwise take `p - x` if `x_0 ≠ x mod 2`.
    if x = 0 ∧ x_0 = 1 then none
    else if x_0 ≠ x % 2 then some (.ofXY (p - x) y)
    else some (.ofXY x y)

/-! ## Key generation (section 5.1.5) -/

/-- Steps 2 and 3: prune the lower 32 bytes of the digest `h` (clear the lowest three bits of the
first octet, clear the highest bit of the last octet, set its second highest bit) and read them
as the little-endian secret scalar `s`. -/
def secretScalar (h : List Byte) : Nat :=
  let buf := h.take 32
  let buf := buf.set 0 (buf.getD 0 0 &&& 0xf8#8)
  let buf := buf.set 31 ((buf.getD 31 0 &&& 0x7f#8) ||| 0x40#8)
  decodeInt buf

/-- The public key `A` of the 32-octet private key `privKey`: the encoding of `[s]B`. -/
def publicKey (privKey : List Byte) : List Byte :=
  let h := sha512 privKey
  let s := secretScalar h
  encodePoint (scalarMul s B)

/-! ## Sign (section 5.1.6) -/

/-- The signature of the message `M` with the private key `privKey`, using the public key `A`
that the caller supplies. Step 1 derives `A` from `privKey`; here it is the argument `A`. `sign`
passes the derived key. -/
def signWith (privKey A M : List Byte) : List Byte :=
  -- 1. `h = SHA-512(privKey)`, the secret scalar `s` and `prefix = h[32], ..., h[63]`.
  let h := sha512 privKey
  let s := secretScalar h
  let «prefix» := h.drop 32
  -- 2. `r = SHA-512(prefix || M)`, little endian.
  let r := decodeInt (sha512 («prefix» ++ M))
  -- 3. `R` is the encoding of `[r]B`, with `r` first reduced modulo `L`.
  let R := encodePoint (scalarMul (r % L) B)
  -- 4. `k = SHA-512(R || A || M)`, little endian.
  let k := decodeInt (sha512 (R ++ A ++ M))
  -- 5. `S = (r + k * s) mod L`.
  let S := (r + k * s) % L
  -- 6. `R || S`, with `S` as 32 little-endian octets.
  R ++ encodeInt S

/-- RFC 8032 section 5.1.6: the signature of `M` with the private key `privKey`. -/
def sign (privKey M : List Byte) : List Byte := signWith privKey (publicKey privKey) M

/-! ## Verify (section 5.1.7) -/

/-- Whether `signature` is a valid signature of the message `M` under the public key `A`.

Step 1 decodes the first half of the signature as the point `R` and the public key as `A'`
(section 5.1.3), and requires the second half, as an integer `S`, to be below `L`. Step 2 forms
`k = SHA-512(R || A || M)`. Step 3 checks `[S]B = R + [k]A'`, the cofactorless form step 3
allows, as equality of the points `(x, y)`. `k` enters reduced modulo `L`, as in the RFC's
section 6 code (`sha512_modq`); the text of step 2 does not reduce it. The two differ only when
`A'` has a component of small order. -/
def verify (signature M A : List Byte) : Bool :=
  let Rs := signature.take 32
  let S := decodeInt (signature.drop 32)
  match decodePoint Rs, decodePoint A with
  | some R, some A' =>
    let k := decodeInt (sha512 (Rs ++ A ++ M))
    S < L && (scalarMul S B).xy == (add R (scalarMul (k % L) A')).xy
  | _, _ => false

end M0Crypto.Spec.Ed25519
