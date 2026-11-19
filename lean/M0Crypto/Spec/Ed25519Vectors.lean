import M0Crypto.Spec.Ed25519

/-!
Checks of the Ed25519 specification.

* `d_def`, `B_onCurve`, `B_y`: the constants of table 1 of RFC 8032 section 5.1 satisfy
  `d = -121665/121666`, `-x^2 + y^2 = 1 + d x^2 y^2` at `B`, and `y = 4/5` at `B`. Kernel proofs.
* Vectors: compiled `#guard` evaluations, tests of the specification, not kernel proofs.
  Compiled code evaluates `powp` by square-and-multiply (`powp_eq_fast` in `Ed25519`).

RFC 8032 section 7.1, tests 1, 2, 3, 1024 and SHA(abc): `publicKey`, `sign` and `signWith` give
the RFC's public key and signature, and `verify` accepts. The bytes were extracted from the RFC
text (rfc-editor.org `rfc8032.txt`, sha256 `ed63657f…c4c3`, fetched 2026-11-16) by an untrusted
script that also checked each key and signature with pyca/cryptography 50.0.2.

The eleven verify verdict cases of `ed25519.md` section 3 (column "RFC §5.1.3"): their bytes are
`cases()` of the library's `bench/ed25519/compare.py` (dev worktree `c03b1ee`), printed with
`uv run --no-project --with unicorn==2.1.4 --with capstone==5.0.9 --with pyelftools python -c
"import compare; [print(n, pk.hex(), m.hex(), s.hex()) for n, pk, m, s in compare.cases()]"`.
The expected verdict is `edref.verify(pk, m, s, edref.recover_x_5_1_3)`, which equals the
column. The case `pk = ecff…ff` is the one where RFC 8032 section 6 decoding accepts and section
5.1.3 rejects.
-/

namespace M0Crypto.Spec.Ed25519

theorem d_def : (d * 121666 + 121665) % p = 0 := by decide +kernel

theorem B_onCurve : (p - B.X ^ 2 % p + B.Y ^ 2) % p = (1 + d * B.X ^ 2 * B.Y ^ 2) % p := by
  decide +kernel

theorem B_y : B.Y * 5 % p = 4 := by decide +kernel

/-- Bytes of a lowercase hex string. -/
def hexBytes (s : String) : List Byte :=
  let digit (c : Char) : Nat := if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (digit a * 16 + digit b) :: go rest
    | _ => []
  go s.toList

/-! ## RFC 8032 section 7.1 -/

/-- A test of section 7.1: secret key, public key, message, signature. -/
structure Vector where
  privKey : List Byte
  A : List Byte
  M : List Byte
  sig : List Byte

/-- Key generation, signing (both forms) and verification agree with the vector. -/
def Vector.ok (t : Vector) : Bool :=
  publicKey t.privKey == t.A && sign t.privKey t.M == t.sig && signWith t.privKey t.A t.M == t.sig &&
    verify t.sig t.M t.A
-- TEST 1
def test1 : Vector :=
  ⟨(hexBytes "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"),
   (hexBytes "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"),
   [],
   (hexBytes ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155" ++
    "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"))⟩

-- TEST 2
def test2 : Vector :=
  ⟨(hexBytes "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"),
   (hexBytes "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"),
   (hexBytes "72"),
   (hexBytes ("92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da" ++
    "085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"))⟩

-- TEST 3
def test3 : Vector :=
  ⟨(hexBytes "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7"),
   (hexBytes "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025"),
   (hexBytes "af82"),
   (hexBytes ("6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac" ++
    "18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a"))⟩

-- TEST 1024
def test1024 : Vector :=
  ⟨(hexBytes "f5e5767cf153319517630f226876b86c8160cc583bc013744c6bf255f5cc0ee5"),
   (hexBytes "278117fc144c72340f67d0f2316e8386ceffbf2b2428c9c51fef7c597f1d426e"),
   (hexBytes ("08b8b2b733424243760fe426a4b54908632110a66c2f6591eabd3345e3e4eb98" ++
    "fa6e264bf09efe12ee50f8f54e9f77b1e355f6c50544e23fb1433ddf73be84d8" ++
    "79de7c0046dc4996d9e773f4bc9efe5738829adb26c81b37c93a1b270b20329d" ++
    "658675fc6ea534e0810a4432826bf58c941efb65d57a338bbd2e26640f89ffbc" ++
    "1a858efcb8550ee3a5e1998bd177e93a7363c344fe6b199ee5d02e82d522c4fe" ++
    "ba15452f80288a821a579116ec6dad2b3b310da903401aa62100ab5d1a36553e" ++
    "06203b33890cc9b832f79ef80560ccb9a39ce767967ed628c6ad573cb116dbef" ++
    "efd75499da96bd68a8a97b928a8bbc103b6621fcde2beca1231d206be6cd9ec7" ++
    "aff6f6c94fcd7204ed3455c68c83f4a41da4af2b74ef5c53f1d8ac70bdcb7ed1" ++
    "85ce81bd84359d44254d95629e9855a94a7c1958d1f8ada5d0532ed8a5aa3fb2" ++
    "d17ba70eb6248e594e1a2297acbbb39d502f1a8c6eb6f1ce22b3de1a1f40cc24" ++
    "554119a831a9aad6079cad88425de6bde1a9187ebb6092cf67bf2b13fd65f270" ++
    "88d78b7e883c8759d2c4f5c65adb7553878ad575f9fad878e80a0c9ba63bcbcc" ++
    "2732e69485bbc9c90bfbd62481d9089beccf80cfe2df16a2cf65bd92dd597b07" ++
    "07e0917af48bbb75fed413d238f5555a7a569d80c3414a8d0859dc65a46128ba" ++
    "b27af87a71314f318c782b23ebfe808b82b0ce26401d2e22f04d83d1255dc51a" ++
    "ddd3b75a2b1ae0784504df543af8969be3ea7082ff7fc9888c144da2af58429e" ++
    "c96031dbcad3dad9af0dcbaaaf268cb8fcffead94f3c7ca495e056a9b47acdb7" ++
    "51fb73e666c6c655ade8297297d07ad1ba5e43f1bca32301651339e22904cc8c" ++
    "42f58c30c04aafdb038dda0847dd988dcda6f3bfd15c4b4c4525004aa06eeff8" ++
    "ca61783aacec57fb3d1f92b0fe2fd1a85f6724517b65e614ad6808d6f6ee34df" ++
    "f7310fdc82aebfd904b01e1dc54b2927094b2db68d6f903b68401adebf5a7e08" ++
    "d78ff4ef5d63653a65040cf9bfd4aca7984a74d37145986780fc0b16ac451649" ++
    "de6188a7dbdf191f64b5fc5e2ab47b57f7f7276cd419c17a3ca8e1b939ae49e4" ++
    "88acba6b965610b5480109c8b17b80e1b7b750dfc7598d5d5011fd2dcc5600a3" ++
    "2ef5b52a1ecc820e308aa342721aac0943bf6686b64b2579376504ccc493d97e" ++
    "6aed3fb0f9cd71a43dd497f01f17c0e2cb3797aa2a2f256656168e6c496afc5f" ++
    "b93246f6b1116398a346f1a641f3b041e989f7914f90cc2c7fff357876e506b5" ++
    "0d334ba77c225bc307ba537152f3f1610e4eafe595f6d9d90d11faa933a15ef1" ++
    "369546868a7f3a45a96768d40fd9d03412c091c6315cf4fde7cb68606937380d" ++
    "b2eaaa707b4c4185c32eddcdd306705e4dc1ffc872eeee475a64dfac86aba41c" ++
    "0618983f8741c5ef68d3a101e8a3b8cac60c905c15fc910840b94c00a0b9d0")),
   (hexBytes ("0aab4c900501b3e24d7cdf4663326a3a87df5e4843b2cbdb67cbf6e460fec350" ++
    "aa5371b1508f9f4528ecea23c436d94b5e8fcd4f681e30a6ac00a9704a188a03"))⟩

-- TEST SHA(abc)
def testShaAbc : Vector :=
  ⟨(hexBytes "833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42"),
   (hexBytes "ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf"),
   (hexBytes ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")),
   (hexBytes ("dc2a4459e7369633a52b1bf277839a00201009a3efbf3ecb69bea2186c26b589" ++
    "09351fc9ac90b3ecfdfbc7c66431e0303dca179c138ac17ad9bef1177331a704"))⟩

#guard test1.ok
#guard test2.ok
#guard test3.ok
#guard test1024.ok
#guard testShaAbc.ok

/-! ## Verify verdicts (`ed25519.md` section 3) -/

/-- The message of the cases with test 1's key: bytes 0 to 63. -/
def msg64 : List Byte := hexBytes
  "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f"

/-- The message of the order-2 public key cases. -/
def msgOrder2 : List Byte := hexBytes "1f28ec017b069509"

/-- The signature with `R` the identity `(0, 1)` and `S = 0`. -/
def sigIdentity : List Byte := hexBytes
  "01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

/-- The point `(0, -1)` of order 2, canonical. -/
def order2 : List Byte := hexBytes "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"

/-- The identity `(0, 1)`, canonical and as `y = p + 1`. -/
def identity : List Byte := hexBytes "0100000000000000000000000000000000000000000000000000000000000000"
def identityPlusP : List Byte := hexBytes "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"

-- valid: accept. The signature is test 1's key on `msg64`.
#guard sign test1.privKey msg64 == hexBytes
  "2dc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71c91b48cb26c2699ce2f56e24ace6dcc51f9cc7fb992a55c833c0889111f4ba03"
#guard verify (hexBytes
  "2dc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71c91b48cb26c2699ce2f56e24ace6dcc51f9cc7fb992a55c833c0889111f4ba03")
  msg64 test1.A
-- R bit flipped: reject.
#guard !verify (hexBytes
  "2cc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71c91b48cb26c2699ce2f56e24ace6dcc51f9cc7fb992a55c833c0889111f4ba03")
  msg64 test1.A
-- S bit flipped: reject.
#guard !verify (hexBytes
  "2dc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71c91b48cb26c2699ce6f56e24ace6dcc51f9cc7fb992a55c833c0889111f4ba03")
  msg64 test1.A
-- S + L: reject.
#guard !verify (hexBytes
  "2dc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71b6ef3d2841257cf4b89266c78ae0bbda1f9cc7fb992a55c833c0889111f4ba13")
  msg64 test1.A
-- message changed (last byte 0x78): reject.
#guard !verify (hexBytes
  "2dc5736c5188aa2a615768c465cf49934f561cbfddc4ebf8cfb6cf323efc2e71c91b48cb26c2699ce2f56e24ace6dcc51f9cc7fb992a55c833c0889111f4ba03")
  (msg64.set 63 0x78) test1.A
-- random signature: reject.
#guard !verify (hexBytes
  "38b4e652e44da7f2370d9e260e27136550a4a3a6d07f5c0c332f8b1224083fd22b902f8911e81818f8c99d5d5d9831957504d90e945de2e8f54ee781cc75f636")
  msg64 test1.A
-- pk = identity, R = identity, s = 0: accept.
#guard verify sigIdentity msg64 identity
-- pk = (0, -1) canonical (y = p - 1), R = identity, s = 0: reject.
#guard !verify sigIdentity msgOrder2 order2
-- pk = ecff…ff (y = p - 1, sign bit 1: x = 0 with x_0 = 1), R = identity, s = 0: reject.
#guard !verify sigIdentity msgOrder2
  (hexBytes "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")
-- pk = identity, R = identity as y + p, s = 0: reject.
#guard !verify (identityPlusP ++ List.replicate 32 0) msg64 identity
-- pk = identity as y + p, R = identity, s = 0: reject.
#guard !verify sigIdentity msg64 identityPlusP

/-! ## `k` reduced modulo `L` in `verify`

Not one of the eleven cases. With `A' = (0, -1)`, `R` the identity and `S = 0`, the check
`[S]B = R + [k]A'` holds when `k` is even. For the message `01`, `k` is odd and `k mod L` is
even (computed with `hashlib`). `verify`, the RFC's section 6 code (`sha512_modq`), `edref.verify`
with section 5.1.3 decoding and the library's code (`m0c_sc_reduce` before `m0c_sc_wnaf`) use
`k mod L` and accept; the unreduced `k` of section 5.1.7 step 2 would reject. -/
#guard verify sigIdentity [0x01] order2

/-! ## Boundaries and the caller's public key

Each rejection boundary checked at equality, and `signWith` with a public key that is not the
derived one (the expected signature was computed independently and by both frozen builds). -/
-- y = p (bit 255 clear): reject.
#guard (decodePoint (encodeInt p)).isNone
-- y = 2: u / v is not a square: reject.
#guard (decodePoint (encodeInt 2)).isNone
-- the identity with its sign bit set (x = 0, x_0 = 1): reject.
#guard (decodePoint (encodeInt (1 + 2 ^ 255))).isNone
-- S = L: reject.
#guard !verify (identity ++ encodeInt L) [] identity
-- test 1's private key, A = 32 zero bytes, message "review caller pk".
#guard signWith test1.privKey (List.replicate 32 0) (hexBytes "7265766965772063616c6c657220706b") ==
  hexBytes ("cb182b6af6b2cd40acfce4212621bc1d5c1768abee6aace9796a54479447eefa" ++
    "036796534fc6100a738c38ba959b14273cc06f897531adb19d5ce6777affc30a")

end M0Crypto.Spec.Ed25519
