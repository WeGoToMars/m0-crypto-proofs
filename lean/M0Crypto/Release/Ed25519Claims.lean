import M0Crypto.Release.Ed25519Callees
import M0Crypto.Release.Ed25519SignEffect
import M0Crypto.Release.Ed25519PubkeyRun
import M0Crypto.Release.Ed25519VerifyEffect

/-!
# The claims of `m0c_ed25519_pubkey`, `m0c_ed25519_sign` and `m0c_ed25519_verify`

Each claim holds for both builds. Its proof is the entry's call-program theorem at the callee
adapters `callees b`, and verify's at its adapters `vAd b`.
-/

namespace M0Crypto.Release.Ed25519

open M0Crypto.Release.Ed25519CallProg (callees)

/-! ## `m0c_ed25519_pubkey` -/

theorem pubkey_correct : Pubkey.Correct := Ed25519PubkeyProg.pubkey_correct callees
theorem pubkey_constant_time : Pubkey.ConstantTime := Ed25519PubkeyProg.pubkey_ct callees
theorem pubkey_reads : Pubkey.Reads := Ed25519PubkeyProg.pubkey_reads callees
theorem pubkey_stack : Pubkey.Stack := Ed25519PubkeyProg.pubkey_stack callees
theorem pubkey_stack_discipline : Pubkey.StackDiscipline := Ed25519PubkeyProg.pubkey_discipline callees
theorem pubkey_interrupted : Pubkey.Interrupted := Ed25519PubkeyProg.pubkey_interrupted callees

/-! ## `m0c_ed25519_sign` -/

theorem sign_correct : Sign.Correct := Ed25519CallProg.sign_correct callees
theorem sign_correct_rfc : Sign.CorrectRfc := Ed25519CallProg.sign_correctRfc callees
theorem sign_constant_time : Sign.ConstantTime := Ed25519CallProg.sign_ct callees
theorem sign_reads : Sign.Reads := Ed25519CallProg.sign_reads callees
theorem sign_stack : Sign.Stack := Ed25519CallProg.sign_stack callees
theorem sign_stack_discipline : Sign.StackDiscipline := Ed25519CallProg.sign_discipline callees
theorem sign_interrupted : Sign.Interrupted := Ed25519CallProg.sign_interrupted callees

/-! ## `m0c_ed25519_verify` -/

theorem verify_correct : Verify.Correct := Ed25519VerifyProg.verify_correct
theorem verify_constant_time : Verify.ConstantTime := Ed25519VerifyProg.verify_ct
theorem verify_reads : Verify.Reads := Ed25519VerifyProg.verify_reads
theorem verify_stack : Verify.Stack := Ed25519VerifyProg.verify_stack
theorem verify_stack_discipline : Verify.StackDiscipline := Ed25519VerifyProg.verify_discipline
theorem verify_interrupted : Verify.Interrupted := Ed25519VerifyProg.verify_interrupted

end M0Crypto.Release.Ed25519
