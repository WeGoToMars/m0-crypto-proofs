import M0Crypto.Assets.Blake2s

/-! Claims of the BLAKE2s release asset: the audit, the statements file and the trusted-definition
list all start from this list (tools/check.sh steps 6 and 6b, tools/statements.sh,
tools/trusted_defs.sh). check.sh fails unless every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).

The same policy for every asset: for each exported function, a correctness, a constant-time,
a read-bound and a stack-bound theorem, and a non-vacuity witness (`*_nonvacuous`) for each
correctness precondition, passed to its correctness theorem; then the asset's composition claims. Supporting lemmas are not
listed: `#print axioms` on a claim already covers everything its proof uses. The internal
routines `m0c_blake2s_compress` and `m0c_blake2s_copy` (local symbols) are not claims: their
contracts are proved and used inside the claims of `update` and `final`. -/

-- m0c_blake2s_init
#print axioms M0Crypto.Release.Blake2s.Init.init_correct
#print axioms M0Crypto.Release.Blake2s.Init.init_constant_time
#print axioms M0Crypto.Release.Blake2s.Init.init_reads
#print axioms M0Crypto.Release.Blake2s.Init.init_stack
#print axioms M0Crypto.Release.NonVacuity.init_pre_nonvacuous

-- m0c_blake2s_update
#print axioms M0Crypto.Release.Blake2s.Update.update_correct
#print axioms M0Crypto.Release.Blake2s.Update.update_constant_time
#print axioms M0Crypto.Release.Blake2s.Update.update_reads
#print axioms M0Crypto.Release.Blake2s.Update.update_stack
#print axioms M0Crypto.Release.NonVacuity.update_pre_nonvacuous

-- m0c_blake2s_final
#print axioms M0Crypto.Release.Blake2s.Final.final_correct
#print axioms M0Crypto.Release.Blake2s.Final.final_constant_time
#print axioms M0Crypto.Release.Blake2s.Final.final_reads
#print axioms M0Crypto.Release.Blake2s.Final.final_stack
#print axioms M0Crypto.Release.NonVacuity.final_pre_nonvacuous

-- Composition: a whole init/update.../final sequence (statements in Blake2sStatements.lean:
-- HashCorrect, total correctness; HashConstantTime, constant time over the sequence). The
-- witnesses state HashCorrectHyp at a concrete call and HashConstantTimeHyp for two executions
-- whose update calls get different message bytes.
#print axioms M0Crypto.Release.Blake2s.hash_correct
#print axioms M0Crypto.Release.Blake2s.hash_constant_time
#print axioms M0Crypto.Release.NonVacuity.hash_correct_nonvacuous
#print axioms M0Crypto.Release.NonVacuity.hash_constant_time_nonvacuous
