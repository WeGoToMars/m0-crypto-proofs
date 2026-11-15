import M0Crypto.Release.Blake2sContract
import M0Crypto.Release.Blake2sTraceSpec
import M0Crypto.Release.Blake2sStatements

/-! The claims of the BLAKE2s release asset without their proofs: the challenge that
`tools/comparator.sh` judges the asset root `M0Crypto.Assets.Blake2s` against. Every claim of
`Audit.lean` except the non-vacuity witnesses, under its own name, with its statement from the
statement files imported above. No module can import this one together with the asset root:
both declare these names. -/

open M0Crypto.Release

-- m0c_blake2s_init
theorem M0Crypto.Release.Blake2s.Init.init_correct : Blake2s.Init.Correct := sorry
theorem M0Crypto.Release.Blake2s.Init.init_constant_time : TraceSpec.Blake2sInitConstantTime := sorry
theorem M0Crypto.Release.Blake2s.Init.init_reads : TraceSpec.Blake2sInitReads := sorry
theorem M0Crypto.Release.Blake2s.Init.init_stack : TraceSpec.Blake2sInitStack := sorry
theorem M0Crypto.Release.Blake2s.Init.init_stack_discipline : TraceSpec.Blake2sInitStackDiscipline := sorry
theorem M0Crypto.Release.Blake2s.Init.init_interrupted : TraceSpec.Blake2sInitInterrupted := sorry

-- m0c_blake2s_update
theorem M0Crypto.Release.Blake2s.Update.update_correct : Blake2s.Update.Correct := sorry
theorem M0Crypto.Release.Blake2s.Update.update_constant_time : TraceSpec.Blake2sUpdateConstantTime := sorry
theorem M0Crypto.Release.Blake2s.Update.update_reads : TraceSpec.Blake2sUpdateReads := sorry
theorem M0Crypto.Release.Blake2s.Update.update_stack : TraceSpec.Blake2sUpdateStack := sorry
theorem M0Crypto.Release.Blake2s.Update.update_stack_discipline : TraceSpec.Blake2sUpdateStackDiscipline := sorry
theorem M0Crypto.Release.Blake2s.Update.update_interrupted : TraceSpec.Blake2sUpdateInterrupted := sorry

-- m0c_blake2s_final
theorem M0Crypto.Release.Blake2s.Final.final_correct : Blake2s.Final.Correct := sorry
theorem M0Crypto.Release.Blake2s.Final.final_constant_time : TraceSpec.Blake2sFinalConstantTime := sorry
theorem M0Crypto.Release.Blake2s.Final.final_reads : TraceSpec.Blake2sFinalReads := sorry
theorem M0Crypto.Release.Blake2s.Final.final_stack : TraceSpec.Blake2sFinalStack := sorry
theorem M0Crypto.Release.Blake2s.Final.final_stack_discipline : TraceSpec.Blake2sFinalStackDiscipline := sorry
theorem M0Crypto.Release.Blake2s.Final.final_interrupted : TraceSpec.Blake2sFinalInterrupted := sorry

-- Composition: a whole init/update.../final sequence
theorem M0Crypto.Release.Blake2s.hash_correct : Blake2s.HashCorrect := sorry
theorem M0Crypto.Release.Blake2s.hash_constant_time : Blake2s.HashConstantTime := sorry
