import M0Crypto.Assets.ChaCha20Poly1305

/-! Claims of the ChaCha20-Poly1305 release asset: the audit, the statements file and the trusted-definition
list all start from this list (tools/check.sh steps 6 and 6b, tools/statements.sh,
tools/trusted_defs.sh). check.sh fails unless every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).

The same policy for every asset: for each exported function, a correctness, a constant-time,
a read-bound and a stack-bound theorem, and a non-vacuity witness (`*_nonvacuous`) for each
correctness precondition; then the asset's composition claims. Supporting lemmas are not
listed: `#print axioms` on a claim already covers everything its proof uses. -/

-- m0c_chacha20_xor
#print axioms M0Crypto.Release.ChaCha20Xor.xor_correct
#print axioms M0Crypto.Release.ChaCha20Xor.xor_constant_time
#print axioms M0Crypto.Release.ChaCha20Xor.xor_reads
#print axioms M0Crypto.Release.ChaCha20Xor.xor_stack
#print axioms M0Crypto.Release.NonVacuity.xor_correct_nonvacuous

-- m0c_chacha20poly1305_encrypt (calls the internal Poly1305 routines; this trace covers them)
#print axioms M0Crypto.Release.Aead.encrypt_correct
#print axioms M0Crypto.Release.Aead.encrypt_constant_time
#print axioms M0Crypto.Release.Aead.encrypt_reads
#print axioms M0Crypto.Release.Aead.encrypt_stack
#print axioms M0Crypto.Release.NonVacuity.encrypt_correct_nonvacuous

-- m0c_chacha20poly1305_decrypt (rejected_writes: a rejected call writes only its own stack)
#print axioms M0Crypto.Release.Aead.decrypt_correct
#print axioms M0Crypto.Release.Aead.rejected_writes
#print axioms M0Crypto.Release.Aead.decrypt_constant_time
#print axioms M0Crypto.Release.Aead.decrypt_reads
#print axioms M0Crypto.Release.Aead.decrypt_stack
#print axioms M0Crypto.Release.NonVacuity.decrypt_correct_nonvacuous
