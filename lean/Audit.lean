import M0Crypto

/-! Axiom audit, run by tools/check.sh. The script fails unless every listed
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
(in particular: no `sorryAx` and no `Lean.ofReduceBool` native evaluation). -/

#print axioms M0Crypto.Spec.ChaCha20.quarterRound_rfc8439_2_1_1
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.decodes
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.run_eq
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.exec_all_regs
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.exec_all_frame
#print axioms M0Crypto.Proofs.ChaCha20QuarterRound.qr_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.decodes
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.run_eq
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.core_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.block_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.block_mem_other
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.dround_view
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.innerBlock_toArr
#print axioms M0Crypto.Proofs.ChaCha20DoubleRound.dround_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.decodes
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.run_eq
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.keep_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.have_spec
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.dround_view
#print axioms M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.dround_spec

#print axioms M0Crypto.Spec.ChaCha20.qround_size
#print axioms M0Crypto.Spec.ChaCha20.innerBlock_size
#print axioms M0Crypto.Spec.ChaCha20.innerBlocks_size
#print axioms M0Crypto.Spec.ChaCha20.wordsOfBytes_length
#print axioms M0Crypto.Spec.ChaCha20.initState_size
#print axioms M0Crypto.Spec.ChaCha20.block_length

-- Whole-function model infrastructure (M0Crypto.Thumb).
#print axioms M0Crypto.Thumb.decode_at
#print axioms M0Crypto.Thumb.step_of_instrAt
#print axioms M0Crypto.Thumb.exec_mem_other
#print axioms M0Crypto.Thumb.step_mem_other
#print axioms M0Crypto.Thumb.runFast_eq
#print axioms M0Crypto.Artifacts.Release.bytes_length

-- Proof infrastructure (Harvard view, straight-line blocks) and release ChaCha20 round.
#print axioms M0Crypto.Thumb.step_of_stepH
#print axioms M0Crypto.Thumb.runUntil_of_runH
#print axioms M0Crypto.Thumb.runH_add
#print axioms M0Crypto.Thumb.runH_seq
#print axioms M0Crypto.Thumb.runSeq_eq
#print axioms M0Crypto.Thumb.execAll_mem
#print axioms M0Crypto.Thumb.execAll_regs_other
#print axioms M0Crypto.Release.ChaCha20Round.dround_at
#print axioms M0Crypto.Release.ChaCha20Round.core_regs
#print axioms M0Crypto.Release.ChaCha20Round.qr_effect
#print axioms M0Crypto.Thumb.alignedAll_sp
#print axioms M0Crypto.Thumb.execAll_mem_sp
#print axioms M0Crypto.Thumb.traceAll_sp_congr
#print axioms M0Crypto.Release.ChaCha20Round.qr_view
#print axioms M0Crypto.Release.ChaCha20Round.dround_view
#print axioms M0Crypto.Release.ChaCha20Round.dround_aligned
#print axioms M0Crypto.Release.ChaCha20Round.dround_mem
#print axioms M0Crypto.Release.ChaCha20Round.dround_regs
#print axioms M0Crypto.Release.ChaCha20Round.dround_trace_congr
#print axioms M0Crypto.Thumb.runH_block
#print axioms M0Crypto.Thumb.stepH_of_instr
#print axioms M0Crypto.Thumb.traceAll_writes_sp
#print axioms M0Crypto.Release.ChaCha20Loop.loop
#print axioms M0Crypto.Release.ChaCha20Loop.iter_toArr
#print axioms M0Crypto.Release.Reach.runUntil
#print axioms M0Crypto.Release.ChaCha20Spec.chacha20_get
#print axioms M0Crypto.Release.ChaCha20Spec.block_get
#print axioms M0Crypto.Release.ChaCha20Return.ret
#print axioms M0Crypto.Release.ChaCha20Setup.checks
#print axioms M0Crypto.Release.ChaCha20Init.init
#print axioms M0Crypto.Release.ChaCha20Block.block_setup
#print axioms M0Crypto.Release.ChaCha20Block.block_keystream
#print axioms M0Crypto.Release.ChaCha20Block.block_rounds
#print axioms M0Crypto.Release.ChaCha20Output.output_byte_eq
#print axioms M0Crypto.Release.ChaCha20Output.block_post
#print axioms M0Crypto.Release.ChaCha20Output.block_output
#print axioms M0Crypto.Release.ChaCha20Xor.loop_next
#print axioms M0Crypto.Release.ChaCha20Xor.blocks
#print axioms M0Crypto.Release.ChaCha20Xor.xor_reach
#print axioms M0Crypto.Release.ChaCha20Xor.xor_correct
#print axioms M0Crypto.Release.ChaCha20Xor.result_output

-- Gate 5: Poly1305.
#print axioms M0Crypto.Release.Poly1305Arith.mul_fold
#print axioms M0Crypto.Release.Poly1305Arith.carry_fold
#print axioms M0Crypto.Release.Poly1305Arith.block_arith
#print axioms M0Crypto.Release.Poly1305Spec.polyBlocks_append
#print axioms M0Crypto.Release.Poly1305Spec.polyAcc_eq
#print axioms M0Crypto.Release.Poly1305Spec.step_mod
#print axioms M0Crypto.Release.Poly1305Spec.leNat_bytesAt16
#print axioms M0Crypto.Release.Poly1305Spec.clamp_words
#print axioms M0Crypto.Release.Poly1305Spec.tag_byte
#print axioms M0Crypto.Release.Poly1305Spec.tag_reduce
#print axioms M0Crypto.Release.Poly1305Init.init_reach
#print axioms M0Crypto.Release.Poly1305Init.init_correct
#print axioms M0Crypto.Release.Poly1305Mac.mac_run
#print axioms M0Crypto.Release.Poly1305Mac.narrow_run
#print axioms M0Crypto.Release.Poly1305Mac.colend_run

-- Gate 5: blocks execution layer (RFC refinement is audited below).
#print axioms M0Crypto.Release.Poly1305Blocks.segments_at
#print axioms M0Crypto.Release.Poly1305Blocks.prologue_at
#print axioms M0Crypto.Release.Poly1305Blocks.setup_at
#print axioms M0Crypto.Release.Poly1305Blocks.epilogue_at
#print axioms M0Crypto.Release.Poly1305Blocks.load_words
#print axioms M0Crypto.Release.Poly1305Blocks.mac4_v
#print axioms M0Crypto.Release.Poly1305Blocks.body_run
#print axioms M0Crypto.Release.Poly1305Blocks.one_run
#print axioms M0Crypto.Release.Poly1305Blocks.loop_run
#print axioms M0Crypto.Release.Poly1305Blocks.loop_mem
#print axioms M0Crypto.Release.Poly1305Blocks.blocks_ret
#print axioms M0Crypto.Release.Poly1305Blocks.publish_effect
#print axioms M0Crypto.Release.Poly1305Blocks.blocks_reach
#print axioms M0Crypto.Release.Poly1305Blocks.blocks_execution
#print axioms M0Crypto.Release.Poly1305Blocks.result_frame
#print axioms M0Crypto.Release.Poly1305Blocks.result_cleared
#print axioms M0Crypto.Release.Poly1305Blocks.result_h
#print axioms M0Crypto.Release.Poly1305Blocks.result_zero
#print axioms M0Crypto.Release.Poly1305Blocks.result_key_preserved
#print axioms M0Crypto.Release.Poly1305Blocks.blocks_execution_safe

-- Gate 5: machine arithmetic refined to the RFC block fold.
#print axioms M0Crypto.Release.Poly1305Carry.adc5
#print axioms M0Crypto.Release.Poly1305Carry.adc5_mod
#print axioms M0Crypto.Release.Poly1305Blocks.addMsg_h
#print axioms M0Crypto.Release.Poly1305Blocks.fold_h
#print axioms M0Crypto.Release.Poly1305Blocks.body_correct
#print axioms M0Crypto.Release.Poly1305Blocks.one_correct
#print axioms M0Crypto.Release.Poly1305Blocks.loop_correct
#print axioms M0Crypto.Release.Poly1305Blocks.result_blocks_correct
#print axioms M0Crypto.Release.Poly1305Blocks.blocks_correct

-- Gate 5: finish and context invariant preservation.
#print axioms M0Crypto.Release.Poly1305Finish.segments_at
#print axioms M0Crypto.Release.Poly1305Finish.carry_correct
#print axioms M0Crypto.Release.Poly1305Finish.arithmetic_correct
#print axioms M0Crypto.Release.Poly1305Finish.tagMem_bytes
#print axioms M0Crypto.Release.Poly1305Finish.pop_ret
#print axioms M0Crypto.Release.Poly1305Finish.emit_writes
#print axioms M0Crypto.Release.Poly1305Finish.finish_reach
#print axioms M0Crypto.Release.Poly1305Finish.result_tag
#print axioms M0Crypto.Release.Poly1305Finish.result_frame
#print axioms M0Crypto.Release.Poly1305Finish.finish_correct
#print axioms M0Crypto.Release.Poly1305Context.init_keyOk
#print axioms M0Crypto.Release.Poly1305Context.init_acc
#print axioms M0Crypto.Release.Poly1305Context.init_key
#print axioms M0Crypto.Release.Poly1305Context.init_pad
#print axioms M0Crypto.Release.Poly1305Context.blocks_words
#print axioms M0Crypto.Release.Poly1305Context.blocks_keyOk
#print axioms M0Crypto.Release.Poly1305Context.blocks_pad
#print axioms M0Crypto.Release.Poly1305Context.finish_bound
#print axioms M0Crypto.Release.Poly1305Context.finish_acc
#print axioms M0Crypto.Release.Poly1305Context.finish_pad
#print axioms M0Crypto.Release.Poly1305Context.key_split
#print axioms M0Crypto.Release.Poly1305Context.poly1305_chain

-- Gate 6: AEAD composition.
#print axioms M0Crypto.Release.Aead.mac_padded
#print axioms M0Crypto.Release.Aead.aead_setup
#print axioms M0Crypto.Release.Aead.crypt_reach
#print axioms M0Crypto.Release.Aead.bytesAt_le64
#print axioms M0Crypto.Release.Aead.lengthMem_bytes
#print axioms M0Crypto.Release.Aead.lengths_reach
#print axioms M0Crypto.Release.Aead.finish_call
#print axioms M0Crypto.Release.Aead.clear_reach
#print axioms M0Crypto.Release.Aead.epilogue_reach
#print axioms M0Crypto.Release.Aead.mac_phase
#print axioms M0Crypto.Release.Aead.finish_phase
#print axioms M0Crypto.Release.Aead.encrypt_reach
#print axioms M0Crypto.Release.Aead.encrypt_correct
#print axioms M0Crypto.Release.Aead.crypt_reach_narrow
#print axioms M0Crypto.Release.Aead.clear_return
#print axioms M0Crypto.Release.Aead.compare_loop
#print axioms M0Crypto.Release.Aead.compare_reach
#print axioms M0Crypto.Release.Aead.decrypt_reach
#print axioms M0Crypto.Release.Aead.decrypt_correct
#print axioms M0Crypto.Release.Aead.rejected_writes

-- Conditional analysis components and contract consequences.

-- Approach C: mirror symbolic executor.
#print axioms M0Crypto.Sym.symExec_sound
#print axioms M0Crypto.Sym.sound_basic
#print axioms M0Crypto.Sym.sound_dp
#print axioms M0Crypto.Sym.sound_lslImm
#print axioms M0Crypto.Sym.sound_lsrImm

-- Approach C, H3 part A: memory and stack forms, and every falling-through instruction.
#print axioms M0Crypto.Sym.sound_ldrLit
#print axioms M0Crypto.Sym.sound_ldrSp
#print axioms M0Crypto.Sym.sound_strSp
#print axioms M0Crypto.Sym.sound_memImm
#print axioms M0Crypto.Sym.sound_memReg
#print axioms M0Crypto.Sym.sound_push
#print axioms M0Crypto.Sym.sound_pop
#print axioms M0Crypto.Sym.sound_stm
#print axioms M0Crypto.Sym.sound_ldm
#print axioms M0Crypto.Sym.sound_of_falls

-- Approach C, H3 part B: symbolic accesses, symbolic traces and alignment.
#print axioms M0Crypto.Sym.symAccesses_sound
#print axioms M0Crypto.Sym.symTrace_sound
#print axioms M0Crypto.Sym.alignedAll_sym

-- Approach C, layer 3 template: normaliser and register bridge.
#print axioms M0Crypto.Sym.norm_sound
#print axioms M0Crypto.Sym.read32_write32_far
#print axioms M0Crypto.Sym.execAll_regs_norm
#print axioms M0Crypto.Sym.demo

-- Approach C, H1.5: carry/rotation rules, known registers, ChaCha core pilot.
#print axioms M0Crypto.Sym.awcK_sound
#print axioms M0Crypto.Sym.rorK_sound
#print axioms M0Crypto.Sym.initK_denote
#print axioms M0Crypto.Sym.execAll_regs_normK
#print axioms M0Crypto.Sym.core_regs_sym

-- Approach C, H5a: double-round pilot through the symbolic checker.
#print axioms M0Crypto.Sym.read32_execAll_normK
#print axioms M0Crypto.Sym.innerBlockF_hi
#print axioms M0Crypto.Sym.inner_view
#print axioms M0Crypto.Sym.denote_innerS
#print axioms M0Crypto.Sym.view_wordS
#print axioms M0Crypto.Sym.dword_0
#print axioms M0Crypto.Sym.dword_15
#print axioms M0Crypto.Sym.dround_word
#print axioms M0Crypto.Sym.dround_view_sym

-- Approach C, H5b: second block family (ChaCha output word) through the checker.
#print axioms M0Crypto.Release.ChaCha20Output.ach_mem_sym
#print axioms M0Crypto.Release.ChaCha20Output.ach_regs_sym
#print axioms M0Crypto.Release.ChaCha20Output.ach_effect

-- Approach C, H7a: alignment and write-region checkers, their soundness, and Reach.symBlock.
#print axioms M0Crypto.Sym.peel_sound
#print axioms M0Crypto.Sym.add_toNat_mod_of_dvd
#print axioms M0Crypto.Sym.accAligned_sound
#print axioms M0Crypto.Sym.add_sub_rearr
#print axioms M0Crypto.Sym.accCovered_sound
#print axioms M0Crypto.Sym.alignChk_sound
#print axioms M0Crypto.Sym.writeChk_sound
#print axioms M0Crypto.Release.Reach.symBlock
#print axioms M0Crypto.Release.Reach.aligned_one
#print axioms M0Crypto.Release.Reach.region_one

#print axioms M0Crypto.Release.ChaCha20Xor.clear_mem
#print axioms M0Crypto.Release.ChaCha20Xor.clear_regs
#print axioms M0Crypto.Release.ChaCha20Xor.clear_accesses
#print axioms M0Crypto.Release.ChaCha20Xor.clear_aligned
