import M0Crypto.Release.ChaCha20Contract
import M0Crypto.Release.AeadContract
import M0Crypto.Release.ChaCha20TraceSpec

/-! The claims of the ChaCha20-Poly1305 release asset without their proofs: the challenge that
`tools/comparator.sh` judges the asset root `M0Crypto.Assets.ChaCha20Poly1305` against. Every claim
of `Audit.lean` except the non-vacuity witnesses, under its own name, with its statement from the
statement files imported above. No module can import this one together with the asset root:
both declare these names. -/

open M0Crypto.Release

-- m0c_chacha20_xor
theorem M0Crypto.Release.ChaCha20Xor.xor_correct : ChaCha20Xor.Correct := sorry
theorem M0Crypto.Release.ChaCha20Xor.xor_constant_time : TraceSpec.ChaCha20XorConstantTime := sorry
theorem M0Crypto.Release.ChaCha20Xor.xor_reads : TraceSpec.ChaCha20XorReads := sorry
theorem M0Crypto.Release.ChaCha20Xor.xor_stack : TraceSpec.ChaCha20XorStack := sorry
theorem M0Crypto.Release.ChaCha20Xor.xor_stack_discipline : TraceSpec.ChaCha20XorStackDiscipline := sorry
theorem M0Crypto.Release.ChaCha20Xor.xor_interrupted : TraceSpec.ChaCha20XorInterrupted := sorry

-- m0c_chacha20poly1305_encrypt
theorem M0Crypto.Release.Aead.encrypt_correct : Aead.EncryptCorrect := sorry
theorem M0Crypto.Release.Aead.encrypt_constant_time : TraceSpec.AeadEncryptConstantTime := sorry
theorem M0Crypto.Release.Aead.encrypt_reads : TraceSpec.AeadEncryptReads := sorry
theorem M0Crypto.Release.Aead.encrypt_stack : TraceSpec.AeadEncryptStack := sorry
theorem M0Crypto.Release.Aead.encrypt_stack_discipline : TraceSpec.AeadEncryptStackDiscipline := sorry
theorem M0Crypto.Release.Aead.encrypt_interrupted : TraceSpec.AeadEncryptInterrupted := sorry

-- m0c_chacha20poly1305_decrypt
theorem M0Crypto.Release.Aead.decrypt_correct : Aead.DecryptCorrect := sorry
theorem M0Crypto.Release.Aead.rejected_writes : Aead.RejectedWrites := sorry
theorem M0Crypto.Release.Aead.decrypt_constant_time : TraceSpec.AeadDecryptConstantTime := sorry
theorem M0Crypto.Release.Aead.decrypt_reads : TraceSpec.AeadDecryptReads := sorry
theorem M0Crypto.Release.Aead.decrypt_stack : TraceSpec.AeadDecryptStack := sorry
theorem M0Crypto.Release.Aead.decrypt_stack_discipline : TraceSpec.AeadDecryptStackDiscipline := sorry
theorem M0Crypto.Release.Aead.decrypt_interrupted : TraceSpec.AeadDecryptInterrupted := sorry
