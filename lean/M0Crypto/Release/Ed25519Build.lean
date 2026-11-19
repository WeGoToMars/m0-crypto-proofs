import M0Crypto.Artifacts.Ed25519Compact
import M0Crypto.Artifacts.Ed25519Fast

/-!
# The two builds of the Ed25519 asset

The asset has two builds, `compact` (2 combs) and `fast` (16 combs), each a relocation-free
unit with its own artifact module (`Artifacts.Ed25519Compact`, `Artifacts.Ed25519Fast`). A user
links one of them. The claims are stated once, quantified over `b : Build`, about the bytes
`b.bytes` of that build alone at the call's code base: they hold for a user who links only that
build. Every judgment about the code therefore takes the byte list as a parameter; the
workspace's `Artifacts.Release` is empty (see its module) and no Ed25519 statement names it.

The two units differ in the comb table and eight immediates. Every function and every data
label up to the comb table has the same offset in both (`offsets_same`), so a code lemma is
stated once at the `compact` offsets, with the comb count `b.combs` as a parameter.
-/

namespace M0Crypto.Release.Ed25519

open M0Crypto.Artifacts

/-- A build of the asset. -/
inductive Build where
  | compact
  | fast
  deriving DecidableEq, Repr

namespace Build

/-- Number of combs (four teeth each) of the fixed-base table: `C1`. -/
def combs : Build → Nat
  | compact => 2
  | fast => 16

def bytes : Build → List (BitVec 8)
  | compact => Ed25519Compact.bytes
  | fast => Ed25519Fast.bytes

def size : Build → Nat
  | compact => Ed25519Compact.size
  | fast => Ed25519Fast.size

def codeRanges : Build → List (Nat × Nat)
  | compact => Ed25519Compact.codeRanges
  | fast => Ed25519Fast.codeRanges

def dataRanges : Build → List (Nat × Nat)
  | compact => Ed25519Compact.dataRanges
  | fast => Ed25519Fast.dataRanges

theorem bytes_length : ∀ b : Build, b.bytes.length = b.size
  | compact => Ed25519Compact.bytes_length
  | fast => Ed25519Fast.bytes_length

end Build

open Ed25519Compact in
/-- The function offsets of `compact`, in address order. -/
def compactOffsets : List Nat :=
  [fe_mul, fe_sqr, fe_add, fe_sub, fe_canon, fe_eq, cmov, copy, zero, fe_pow, sha512_block,
   sha512_init, sha512_update, sha512_final, mp_mul, sc_reduce, sc_muladd, ge_compress,
   ge_decompress, sc_recode_comb, ge_lookup, ge_mul_base, sbit, sc_wnaf, ge_dsm, ed25519_pubkey,
   ed25519_sign, ed25519_verify, ed_zero, ed_one, ed_d, ed_d2, ed_sqrtm1, ed_mu, ed_l9, sha512_K,
   sha512_IV, ed_odd_b, ed_comb]

open Ed25519Fast in
/-- The same offsets in `fast`. -/
def fastOffsets : List Nat :=
  [fe_mul, fe_sqr, fe_add, fe_sub, fe_canon, fe_eq, cmov, copy, zero, fe_pow, sha512_block,
   sha512_init, sha512_update, sha512_final, mp_mul, sc_reduce, sc_muladd, ge_compress,
   ge_decompress, sc_recode_comb, ge_lookup, ge_mul_base, sbit, sc_wnaf, ge_dsm, ed25519_pubkey,
   ed25519_sign, ed25519_verify, ed_zero, ed_one, ed_d, ed_d2, ed_sqrtm1, ed_mu, ed_l9, sha512_K,
   sha512_IV, ed_odd_b, ed_comb]

/-- Every function and data label lies at the same offset in both builds, and so do the code
ranges: code lemmas name the `compact` offsets. -/
theorem offsets_same :
    compactOffsets = fastOffsets ∧ Ed25519Compact.codeRanges = Ed25519Fast.codeRanges := ⟨rfl, rfl⟩

end M0Crypto.Release.Ed25519
