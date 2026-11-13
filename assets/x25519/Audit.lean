import M0Crypto.Assets.X25519

/-! Claims of the X25519 release asset: the audit, the statements file and the trusted-definition
list all start from this list (tools/check.sh steps 6 and 6b, tools/statements.sh,
tools/trusted_defs.sh). check.sh fails unless every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).

The same policy for every asset: for each exported function, a correctness, a constant-time,
a read-bound and a stack-bound theorem, and a non-vacuity witness (`*_nonvacuous`) for each
correctness precondition; then the asset's composition claims. Supporting lemmas are not
listed: `#print axioms` on a claim already covers everything its proof uses. -/

-- m0c_x25519 (the field routines m0c_fe_* are internal: not exported, not listed)
#print axioms M0Crypto.Release.X25519.x25519_correct
#print axioms M0Crypto.Release.X25519.x25519_constant_time
#print axioms M0Crypto.Release.X25519.x25519_reads
#print axioms M0Crypto.Release.X25519.x25519_stack
#print axioms M0Crypto.Release.NonVacuity.x25519_pre_nonvacuous
