/-!
# X25519 (RFC 7748 section 5)

The function `X25519(k, u)` of RFC 7748, written as the RFC's pseudo-code: same names, same
order. Core Lean only. Field elements are integers; every operation of the ladder is reduced
modulo `p`, as the RFC says ("all calculations are performed in GF(p)"). The final inversion
is written as the RFC writes it, the power `z_2^(p - 2)`.

Nothing here is a statement about curves: the claim proved about the code is equality with
this function, not that it is a secure Diffie-Hellman function.

Reading guide, against RFC 7748:
* `decodeLittleEndian`, `decodeUCoordinate`, `decodeScalar25519`, `encodeUCoordinate`:
  section 5, the Python functions of the same names, for `bits = 255`.
* `cswap`: section 5, `cswap(swap, x_2, x_3)`, with `swap` either 0 or 1.
* `ladderStep`, `ladder`: the loop `for t = bits-1 down to 0`, with `a24 = 121665`.
* `output`, `x25519`: the conditional swap after the loop, `x_2 * (z_2^(p - 2))`, encoding.
-/

namespace M0Crypto.Spec.X25519

abbrev Byte := BitVec 8

/-- The field prime `2^255 - 19`. -/
def p : Int := 2 ^ 255 - 19

/-- `(A - 2) / 4` for curve25519, as RFC 7748 section 5 uses it: 121665. -/
def a24 : Int := 121665

/-- The number of bits of a scalar and of a u-coordinate. -/
def bits : Nat := 255

/-! ## Encoding -/

/-- `sum(b[i] << 8*i for i in range((bits+7)/8))`: little-endian value of a byte list. -/
def decodeLittleEndian : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLittleEndian bs

/-- `decodeUCoordinate(u, 255)`: the 32 bytes with the top bit of the last byte masked
(`u_list[-1] &= (1 << (bits % 8)) - 1`). The value may be `p` or more; it is reduced in the
field arithmetic. -/
def decodeUCoordinate (u : List Byte) : Nat :=
  decodeLittleEndian (u.set 31 (u.getD 31 0 &&& 127#8))

/-- `decodeScalar25519(k)`: clear the three low bits, clear bit 255, set bit 254. -/
def decodeScalar25519 (k : List Byte) : Nat :=
  decodeLittleEndian ((k.set 0 (k.getD 0 0 &&& 248#8)).set 31 ((k.getD 31 0 &&& 127#8) ||| 64#8))

/-- `encodeUCoordinate(u, 255)`: `u % p` as 32 little-endian bytes. -/
def encodeUCoordinate (u : Int) : List Byte :=
  (List.range 32).map fun i => BitVec.ofNat 8 ((u % p).toNat / 2 ^ (8 * i))

/-! ## The ladder -/

/-- `cswap(swap, x_2, x_3)` for `swap` in {0, 1}: swap when `swap = 1`. -/
def cswap (swap : Nat) (x2 x3 : Int) : Int × Int :=
  if swap = 1 then (x3, x2) else (x2, x3)

/-- The ladder variables between iterations. -/
structure LadderState where
  x2 : Int
  z2 : Int
  x3 : Int
  z3 : Int
  swap : Nat
  deriving Repr, DecidableEq

/-- `x_1 = u, x_2 = 1, z_2 = 0, x_3 = u, z_3 = 1, swap = 0`. -/
def ladderInit (u : Int) : LadderState := ⟨1, 0, u, 1, 0⟩

/-- One iteration of the loop body, for bit `t` of `k`, with `x_1 = x1`. -/
def ladderStep (k : Nat) (x1 : Int) (s : LadderState) (t : Nat) : LadderState :=
  let k_t := (k >>> t) &&& 1
  let swap := s.swap ^^^ k_t
  let (x_2, x_3) := cswap swap s.x2 s.x3
  let (z_2, z_3) := cswap swap s.z2 s.z3
  let swap := k_t
  let A := (x_2 + z_2) % p
  let AA := A ^ 2 % p
  let B := (x_2 - z_2) % p
  let BB := B ^ 2 % p
  let E := (AA - BB) % p
  let C := (x_3 + z_3) % p
  let D := (x_3 - z_3) % p
  let DA := D * A % p
  let CB := C * B % p
  let x_3 := (DA + CB) ^ 2 % p
  let z_3 := x1 * (DA - CB) ^ 2 % p
  let x_2 := AA * BB % p
  let z_2 := E * (AA + a24 * E) % p
  ⟨x_2, z_2, x_3, z_3, swap⟩

/-- `for t = bits-1 down to 0`, from the initial state, with `x_1 = u`. -/
def ladder (k : Nat) (u : Int) : LadderState :=
  ((List.range bits).reverse).foldl (ladderStep k u) (ladderInit u)

/-- `x_2 = x_2 * (z_2^(p - 2)); return encodeUCoordinate(x_2)`. -/
def output (x_2 z_2 : Int) : List Byte :=
  encodeUCoordinate (x_2 * z_2 ^ (p - 2).toNat)

/-! ### Evaluation

`z_2^(p - 2)` as written cannot be evaluated. `output_eq_fast` (a theorem, marked `@[csimp]`)
lets compiled code, such as the test vectors, compute `output` by square-and-multiply modulo
`p`. It changes only how code is evaluated: `output` and every theorem about it keep the
power. It precedes `x25519` so that `x25519`'s compiled code uses it. -/

/-- `b ^ e` modulo `p`, by square-and-multiply. -/
def powModP (b : Int) (e : Nat) : Int :=
  if e = 0 then 1 else
    let r := powModP b (e / 2)
    if e % 2 = 0 then r * r % p else r * r % p * b % p
termination_by e
decreasing_by omega

theorem powModP_emod (b : Int) (e : Nat) : powModP b e % p = b ^ e % p := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [powModP]
    by_cases h0 : e = 0
    · subst h0; simp
    · simp only [h0, ↓reduceIte]
      have hr := ih (e / 2) (by omega)
      have hsq : powModP b (e / 2) * powModP b (e / 2) % p = b ^ (e / 2 * 2) % p := by
        rw [Int.mul_emod, hr, ← Int.mul_emod, Nat.mul_two, Int.pow_add]
      by_cases he : e % 2 = 0
      · simp only [he, ↓reduceIte, Int.emod_emod_of_dvd _ (Int.dvd_refl p), hsq]
        congr 2; omega
      · simp only [he, ↓reduceIte]
        have key : ∀ x y : Int, x % p * y % p = x * y % p := by
          intro x y
          rw [Int.mul_emod (x % p) y p, Int.emod_emod_of_dvd x (Int.dvd_refl p), ← Int.mul_emod]
        rw [Int.emod_emod_of_dvd _ (Int.dvd_refl p), hsq, key, ← Int.pow_succ]
        congr 2; omega

/-- `output` with the power computed by `powModP`. -/
def outputFast (x_2 z_2 : Int) : List Byte :=
  encodeUCoordinate (x_2 * powModP z_2 (p - 2).toNat)

@[csimp] theorem output_eq_fast : @output = @outputFast := by
  funext x z
  simp only [output, outputFast, encodeUCoordinate]
  rw [Int.mul_emod x (z ^ _), ← powModP_emod, ← Int.mul_emod]

/-- RFC 7748 `X25519(k, u)` on byte strings: decode, ladder, final swap, output. -/
def x25519 (k u : List Byte) : List Byte :=
  let s := ladder (decodeScalar25519 k) (decodeUCoordinate u)
  let (x_2, _) := cswap s.swap s.x2 s.x3
  let (z_2, _) := cswap s.swap s.z2 s.z3
  output x_2 z_2

end M0Crypto.Spec.X25519
