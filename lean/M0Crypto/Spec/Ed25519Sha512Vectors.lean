import M0Crypto.Spec.Ed25519Sha512

/-!
Checks of the SHA-512 specification.

* `K_def`, `H0_def`: the listed constants are the first 64 bits of the fractional parts of the
  cube roots of the first eighty primes and of the square roots of the first eight primes
  (FIPS 180-4 sections 4.2.3 and 5.3.5). Kernel proofs.
* Digests: compiled `#guard` evaluations, tests of the specification, not kernel proofs.
  Expected values from Python `hashlib.sha512` (Python 3, 2026-11-16):
  `python3 -I -c "import hashlib; print(hashlib.sha512(M).hexdigest())"` for `M` = `b''`,
  `b'abc'`, the 896-bit message of FIPS 180-2 appendix C.2, and `bytes(i % 251 for i in
  range(n))` for `n` = 111 (one block, longest), 112 (two blocks, shortest) and 239 (two blocks,
  longest). The `abc` and 896-bit digests are also those of FIPS 180-2 appendix C.
-/

namespace M0Crypto.Spec.Sha512

/-- The prime numbers below 410: the first eighty primes (409 is the eightieth). -/
def primes : List Nat :=
  (List.range 410).filter fun m => 2 ≤ m && (List.range' 2 (m - 2)).all (m % · != 0)

/-- `w` is the first 64 bits of the fractional part of the `k`-th root of `q`: for some integer
part `i`, `c = i * 2^64 + w` satisfies `c^k ≤ q * 2^(64k) < (c + 1)^k`. -/
def fracRoot (k q : Nat) (w : Word) : Bool :=
  (List.range 8).any fun i =>
    let c := i * 2 ^ 64 + w.toNat
    c ^ k ≤ q * 2 ^ (64 * k) && q * 2 ^ (64 * k) < (c + 1) ^ k

theorem K_def : primes.length = 80 ∧ K.size = 80 ∧
    (K.toList.zip primes).all (fun (w, q) => fracRoot 3 q w) := by decide +kernel

theorem H0_def : H0.size = 8 ∧ (H0.toList.zip primes).all (fun (w, q) => fracRoot 2 q w) := by
  decide +kernel

/-- Bytes of a lowercase hex string. -/
def hexBytes (s : String) : List Byte :=
  let digit (c : Char) : Nat := if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (digit a * 16 + digit b) :: go rest
    | _ => []
  go s.toList

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The test message of length `n`: bytes `i % 251`. -/
def testMsg (n : Nat) : List Byte := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

#guard sha512 [] == hexBytes ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce" ++
  "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
#guard sha512 (ascii "abc") == hexBytes ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
  "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
#guard sha512 (ascii ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) ==
  hexBytes ("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
    "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
#guard sha512 (testMsg 111) == hexBytes ("a1a111449b198d9b1f538bad7f3fc1022b3a5b1a5e90a0bc860de8512746cbc3" ++
  "1599e6c834de3a3235327af0b51ff57bf7acf1974a73014d9c3953812edc7c8d")
#guard sha512 (testMsg 112) == hexBytes ("c5fbd731d19d2ae1180f001be72c2c1aaba1d7b094b3748880e24593b8e117a7" ++
  "50e11c1bd867cc2f96dace8c8b74abd2d5c4f236be444e77d30d1916174070b9")
#guard sha512 (testMsg 239) == hexBytes ("cb4c7fd522756d5781ad3a4f590a1d862906b960e7720136cb3fb36b563caa1e" ++
  "a5689134291fa79c80ccc2b4092b41df32ebdcb36dbe79db483440228c1622a8")

end M0Crypto.Spec.Sha512
