import M0Crypto.Spec.X25519

/-!
RFC 7748 test vectors for the X25519 specification.

The vectors are compiled `#guard` evaluations: tests of the specification, not kernel proofs.
Compiled code evaluates `output` by square-and-multiply (`output_eq_fast` in `X25519`).

Section 5.2 runs here except its last value: the two vectors and the iterated vector after 1
and 1,000 iterations (about 1.5 s of compiled evaluation). The 1,000,000-iteration value is not
run. Sources: RFC 7748 section 5.2; the second
vector was also recomputed with OpenSSL 4.1.0 (`pkeyutl -derive`) on 2026-11-12.
-/

namespace M0Crypto.Spec.X25519

/-- Hexadecimal string to bytes, for the vectors. -/
def ofHex (s : String) : List Byte :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

-- RFC 7748 section 5.2, first vector.
#guard x25519 (ofHex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
    (ofHex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c") ==
  ofHex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"

-- RFC 7748 section 5.2, second vector (its u-coordinate has the top bit set: masked).
#guard x25519 (ofHex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
    (ofHex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493") ==
  ofHex "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957"

/-- RFC 7748 section 5.2 iteration: `k = u = 9`, then `k, u = X25519(k, u), k`, `n` times. -/
def iterate : Nat → List Byte × List Byte
  | 0 => (9 :: List.replicate 31 0, 9 :: List.replicate 31 0)
  | n + 1 => let (k, u) := iterate n; (x25519 k u, k)

-- After one iteration.
#guard (iterate 1).1 ==
  ofHex "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"

-- After 1,000 iterations.
#guard (iterate 1000).1 ==
  ofHex "684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51"

end M0Crypto.Spec.X25519
