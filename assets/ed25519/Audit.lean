import M0Crypto.Assets.Ed25519

/-! Claims of the Ed25519 release asset (see `assets/x25519/Audit.lean` for the policy). One
theorem per claim, quantified over the build (`Release.Ed25519Build`).

The claims of `m0c_ed25519_pubkey`, `m0c_ed25519_sign` and `m0c_ed25519_verify` are proved:
`Correct`, `ConstantTime`, `Reads`, `Stack`, `StackDiscipline` and `Interrupted` of each, and sign's
`CorrectRfc`. The witnesses are proved. -/

-- m0c_ed25519_pubkey
#print axioms M0Crypto.Release.Ed25519.pubkey_correct
#print axioms M0Crypto.Release.Ed25519.pubkey_constant_time
#print axioms M0Crypto.Release.Ed25519.pubkey_reads
#print axioms M0Crypto.Release.Ed25519.pubkey_stack
#print axioms M0Crypto.Release.Ed25519.pubkey_stack_discipline
#print axioms M0Crypto.Release.Ed25519.pubkey_interrupted
#print axioms M0Crypto.Release.Ed25519.NonVacuity.pubkey_pre_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.pubkey_constant_time_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.pubkey_interrupted_nonvacuous

-- m0c_ed25519_sign
#print axioms M0Crypto.Release.Ed25519.sign_correct
#print axioms M0Crypto.Release.Ed25519.sign_correct_rfc
#print axioms M0Crypto.Release.Ed25519.sign_constant_time
#print axioms M0Crypto.Release.Ed25519.sign_reads
#print axioms M0Crypto.Release.Ed25519.sign_stack
#print axioms M0Crypto.Release.Ed25519.sign_stack_discipline
#print axioms M0Crypto.Release.Ed25519.sign_interrupted
#print axioms M0Crypto.Release.Ed25519.NonVacuity.sign_pre_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.sign_constant_time_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.sign_interrupted_nonvacuous

-- m0c_ed25519_verify
#print axioms M0Crypto.Release.Ed25519.verify_correct
#print axioms M0Crypto.Release.Ed25519.verify_constant_time
#print axioms M0Crypto.Release.Ed25519.verify_reads
#print axioms M0Crypto.Release.Ed25519.verify_stack
#print axioms M0Crypto.Release.Ed25519.verify_stack_discipline
#print axioms M0Crypto.Release.Ed25519.verify_interrupted
#print axioms M0Crypto.Release.Ed25519.NonVacuity.verify_pre_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.verify_constant_time_nonvacuous
#print axioms M0Crypto.Release.Ed25519.NonVacuity.verify_interrupted_nonvacuous
