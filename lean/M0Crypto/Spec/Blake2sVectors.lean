import M0Crypto.Spec.Blake2s

/-!
Test vectors for the BLAKE2s specification: RFC 7693 Appendix B (`"abc"`) and values
produced by Python `hashlib.blake2s` for the empty message and for the bytes
`i % 251` at lengths 1, 63, 64, 65, 128 and 129 (covering every block boundary case and
all ten message schedule rows). These are compiled `#guard` evaluations: tests of the
specification, not kernel proofs.
-/

namespace M0Crypto.Spec.Blake2s

/-- Bytes of a lowercase hex string. -/
def hexBytes (s : String) : List Byte :=
  let digit (c : Char) : Nat := if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (digit a * 16 + digit b) :: go rest
    | _ => []
  go s.toList

/-- The test message of length `n`: bytes `i % 251`. -/
def testMsg (n : Nat) : List Byte := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

-- RFC 7693 Appendix B.
#guard blake2s ("abc".toList.map fun c => BitVec.ofNat 8 c.toNat) ==
  hexBytes "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
#guard blake2s [] == hexBytes "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
#guard blake2s (testMsg 1) == hexBytes "e34d74dbaf4ff4c6abd871cc220451d2ea2648846c7757fbaac82fe51ad64bea"
#guard blake2s (testMsg 63) == hexBytes "e57cb79487dd57902432b250733813bd96a84efce59f650fac26e6696aefafc3"
#guard blake2s (testMsg 64) == hexBytes "56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e"
#guard blake2s (testMsg 65) == hexBytes "1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472"
#guard blake2s (testMsg 128) == hexBytes "1fa877de67259d19863a2a34bcc6962a2b25fcbf5cbecd7ede8f1fa36688a796"
#guard blake2s (testMsg 129) == hexBytes "5bd169e67c82c2c2e98ef7008bdf261f2ddf30b1c00f9e7f275bb3e8a28dc9a2"

-- The streaming description agrees, for a partition that splits blocks unevenly.
#guard finish ([testMsg 17, testMsg 64, [], testMsg 48].foldl absorb State.init) ==
  blake2s (testMsg 17 ++ testMsg 64 ++ testMsg 48)

end M0Crypto.Spec.Blake2s
