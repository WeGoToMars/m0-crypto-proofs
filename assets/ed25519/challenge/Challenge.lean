import M0Crypto.Release.Ed25519Contract
import M0Crypto.Release.Ed25519TraceSpec

/-! The claims of the Ed25519 release asset without their proofs: the challenge that
`tools/comparator.sh` judges the asset root `M0Crypto.Assets.Ed25519` against. Every claim of
`Audit.lean` except the non-vacuity witnesses, under its own name, with its statement from the
statement files imported above. No module can import this one together with the asset root:
both declare these names. -/

open M0Crypto.Release

-- m0c_ed25519_pubkey
theorem M0Crypto.Release.Ed25519.pubkey_correct : Ed25519.Pubkey.Correct := sorry
theorem M0Crypto.Release.Ed25519.pubkey_constant_time : Ed25519.Pubkey.ConstantTime := sorry
theorem M0Crypto.Release.Ed25519.pubkey_reads : Ed25519.Pubkey.Reads := sorry
theorem M0Crypto.Release.Ed25519.pubkey_stack : Ed25519.Pubkey.Stack := sorry
theorem M0Crypto.Release.Ed25519.pubkey_stack_discipline : Ed25519.Pubkey.StackDiscipline := sorry
theorem M0Crypto.Release.Ed25519.pubkey_interrupted : Ed25519.Pubkey.Interrupted := sorry

-- m0c_ed25519_sign
theorem M0Crypto.Release.Ed25519.sign_correct : Ed25519.Sign.Correct := sorry
theorem M0Crypto.Release.Ed25519.sign_correct_rfc : Ed25519.Sign.CorrectRfc := sorry
theorem M0Crypto.Release.Ed25519.sign_constant_time : Ed25519.Sign.ConstantTime := sorry
theorem M0Crypto.Release.Ed25519.sign_reads : Ed25519.Sign.Reads := sorry
theorem M0Crypto.Release.Ed25519.sign_stack : Ed25519.Sign.Stack := sorry
theorem M0Crypto.Release.Ed25519.sign_stack_discipline : Ed25519.Sign.StackDiscipline := sorry
theorem M0Crypto.Release.Ed25519.sign_interrupted : Ed25519.Sign.Interrupted := sorry

-- m0c_ed25519_verify
theorem M0Crypto.Release.Ed25519.verify_correct : Ed25519.Verify.Correct := sorry
theorem M0Crypto.Release.Ed25519.verify_constant_time : Ed25519.Verify.ConstantTime := sorry
theorem M0Crypto.Release.Ed25519.verify_reads : Ed25519.Verify.Reads := sorry
theorem M0Crypto.Release.Ed25519.verify_stack : Ed25519.Verify.Stack := sorry
theorem M0Crypto.Release.Ed25519.verify_stack_discipline : Ed25519.Verify.StackDiscipline := sorry
theorem M0Crypto.Release.Ed25519.verify_interrupted : Ed25519.Verify.Interrupted := sorry
