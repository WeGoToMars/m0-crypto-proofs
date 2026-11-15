import M0Crypto.Release.X25519Contract
import M0Crypto.Release.X25519TraceSpec

/-! The claims of the X25519 release asset without their proofs: the challenge that
`tools/comparator.sh` judges the asset root `M0Crypto.Assets.X25519` against. Every claim of
`Audit.lean` except the non-vacuity witnesses, under its own name, with its statement from the
statement files imported above. No module can import this one together with the asset root:
both declare these names. -/

open M0Crypto.Release

-- m0c_x25519
theorem M0Crypto.Release.X25519.x25519_correct : X25519.Correct := sorry
theorem M0Crypto.Release.X25519.x25519_constant_time : TraceSpec.X25519ConstantTime := sorry
theorem M0Crypto.Release.X25519.x25519_reads : TraceSpec.X25519Reads := sorry
theorem M0Crypto.Release.X25519.x25519_stack : TraceSpec.X25519Stack := sorry
theorem M0Crypto.Release.X25519.x25519_stack_discipline : TraceSpec.X25519StackDiscipline := sorry
theorem M0Crypto.Release.X25519.x25519_interrupted : TraceSpec.X25519Interrupted := sorry
