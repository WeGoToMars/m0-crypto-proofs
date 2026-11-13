import M0Crypto.Assets.Blake2s

/-! Claims of the BLAKE2s release asset: the audit, the statements file and the trusted-definition
list all start from this list (tools/check.sh steps 6 and 6b, tools/statements.sh,
tools/trusted_defs.sh). check.sh fails unless every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).

The same policy for every asset: for each exported function, a correctness, a constant-time,
a read-bound and a stack-bound theorem, and a non-vacuity witness (`*_nonvacuous`) for each
correctness precondition; then the asset's composition claims. Supporting lemmas are not
listed: `#print axioms` on a claim already covers everything its proof uses. The internal
routines `m0c_blake2s_compress` and `m0c_blake2s_copy` (local symbols) are not claims: their
contracts are proved and used inside the claims of `update` and `final`. -/

-- m0c_blake2s_init
#print axioms M0Crypto.Release.Blake2sHash.init_correct
#print axioms M0Crypto.Release.Blake2sInit.init_constant_time
#print axioms M0Crypto.Release.Blake2sInit.init_reads
#print axioms M0Crypto.Release.Blake2sInit.init_stack
#print axioms M0Crypto.Release.NonVacuity.init_correct_nonvacuous

-- m0c_blake2s_update
#print axioms M0Crypto.Release.Blake2sHash.update_correct
#print axioms M0Crypto.Release.Blake2sUpdate.update_constant_time
#print axioms M0Crypto.Release.Blake2sUpdate.update_reads
#print axioms M0Crypto.Release.Blake2sUpdate.update_stack
#print axioms M0Crypto.Release.NonVacuity.update_correct_nonvacuous

-- m0c_blake2s_final
#print axioms M0Crypto.Release.Blake2sHash.final_correct
#print axioms M0Crypto.Release.Blake2sFinal.final_constant_time
#print axioms M0Crypto.Release.Blake2sFinal.final_reads
#print axioms M0Crypto.Release.Blake2sFinal.final_stack
#print axioms M0Crypto.Release.NonVacuity.final_correct_nonvacuous

-- Composition: a whole init/update.../final sequence (Blake2sStatements: C1 correctness, C4
-- constant time over the sequence). The witnesses state C1Hyp at a concrete call and C4Hyp for
-- two executions whose update calls get different message bytes.
#print axioms M0Crypto.Release.Blake2sHash.hash_machine
#print axioms M0Crypto.Release.Blake2sHash.hash_correct
#print axioms M0Crypto.Release.Blake2sHash.hash_constant_time
#print axioms M0Crypto.Release.Blake2sStatements.c1
#print axioms M0Crypto.Release.Blake2sStatements.c4
#print axioms M0Crypto.Release.NonVacuity.c1_nonvacuous
#print axioms M0Crypto.Release.NonVacuity.c4_nonvacuous
