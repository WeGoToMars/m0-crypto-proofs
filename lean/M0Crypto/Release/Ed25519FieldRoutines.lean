import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.Field25519FeMul
import M0Crypto.Release.Field25519FeSqr
import M0Crypto.Thumb.SeqScan

/-!
# `m0c_fe_mul` and `m0c_fe_sqr` in each Ed25519 build

The `Field25519` proofs are generic in the code bytes (`CodeBytes`): `mul_spec` and `sqr_spec`
hold for any byte list that holds `feMulList` or `feSqrList` at an even offset. Here they are
instantiated with each build's own bytes and the offsets of that build's symbol table, so each
contract assumes only the bytes of the one build the caller links.
-/

namespace M0Crypto.Release.Ed25519

open M0Crypto.Artifacts
open M0Crypto.Thumb
open M0Crypto.Release.Field25519Routines (MulSpec SqrSpec)
open M0Crypto.Release.Field25519Macros (feMulList feSqrList)

/-- The bytes of build `b` as the code of the routine tooling. -/
theorem Build.codeBytes (b : Build) : CodeBytes b.bytes b.size :=
  ⟨b.bytes_length, by cases b <;> decide⟩

theorem compact_mul_spec :
    letI := Build.compact.codeBytes; MulSpec Ed25519Compact.fe_mul (seqSize feMulList) := by
  letI := Build.compact.codeBytes
  exact Field25519FeMul.mul_spec (by rw [seqAt_eq_scan]; decide +kernel) (by decide)

theorem compact_sqr_spec :
    letI := Build.compact.codeBytes; SqrSpec Ed25519Compact.fe_sqr (seqSize feSqrList) := by
  letI := Build.compact.codeBytes
  exact Field25519FeSqr.sqr_spec (by rw [seqAt_eq_scan]; decide +kernel) (by decide)

theorem fast_mul_spec :
    letI := Build.fast.codeBytes; MulSpec Ed25519Fast.fe_mul (seqSize feMulList) := by
  letI := Build.fast.codeBytes
  exact Field25519FeMul.mul_spec (by rw [seqAt_eq_scan]; decide +kernel) (by decide)

theorem fast_sqr_spec :
    letI := Build.fast.codeBytes; SqrSpec Ed25519Fast.fe_sqr (seqSize feSqrList) := by
  letI := Build.fast.codeBytes
  exact Field25519FeSqr.sqr_spec (by rw [seqAt_eq_scan]; decide +kernel) (by decide)

end M0Crypto.Release.Ed25519
