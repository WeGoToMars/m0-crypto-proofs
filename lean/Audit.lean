import M0Crypto

/-! Axiom audit, run by tools/check.sh. The script fails unless every listed
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
(in particular: no `sorryAx` and no `Lean.ofReduceBool` native evaluation). -/

#print axioms M0Crypto.Spec.ChaCha20.quarterRound_rfc8439_2_1_1
#print axioms M0Crypto.Proofs.ChaCha20QR.decodes
#print axioms M0Crypto.Proofs.ChaCha20QR.run_eq
#print axioms M0Crypto.Proofs.ChaCha20QR.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20QR.exec_all_regs
#print axioms M0Crypto.Proofs.ChaCha20QR.exec_all_frame
#print axioms M0Crypto.Proofs.ChaCha20QR.qr_spec
#print axioms M0Crypto.Proofs.ChaCha20DRound.decodes
#print axioms M0Crypto.Proofs.ChaCha20DRound.run_eq
#print axioms M0Crypto.Proofs.ChaCha20DRound.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20DRound.core_spec
#print axioms M0Crypto.Proofs.ChaCha20DRound.block_spec
#print axioms M0Crypto.Proofs.ChaCha20DRound.block_mem_other
#print axioms M0Crypto.Proofs.ChaCha20DRound.dround_view
#print axioms M0Crypto.Proofs.ChaCha20DRound.innerBlock_toArr
#print axioms M0Crypto.Proofs.ChaCha20DRound.dround_spec
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.decodes
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.run_eq
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.trace_independent
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.keep_spec
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.have_spec
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.dround_view
#print axioms M0Crypto.Proofs.ChaCha20DRoundV2.dround_spec

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
#print axioms M0Crypto.Release.ChaChaRound.dround_at
#print axioms M0Crypto.Release.ChaChaRound.core_regs
#print axioms M0Crypto.Release.ChaChaRound.qr_effect
#print axioms M0Crypto.Thumb.alignedAll_sp
#print axioms M0Crypto.Thumb.execAll_mem_sp
#print axioms M0Crypto.Thumb.traceAll_sp_congr
#print axioms M0Crypto.Release.ChaChaRound.qr_view
#print axioms M0Crypto.Release.ChaChaRound.dround_view
#print axioms M0Crypto.Release.ChaChaRound.dround_aligned
#print axioms M0Crypto.Release.ChaChaRound.dround_mem
#print axioms M0Crypto.Release.ChaChaRound.dround_regs
#print axioms M0Crypto.Release.ChaChaRound.dround_trace_congr
#print axioms M0Crypto.Thumb.runH_block
#print axioms M0Crypto.Thumb.stepH_of_instr
#print axioms M0Crypto.Thumb.traceAll_writes_sp
#print axioms M0Crypto.Release.ChaChaLoop.loop
#print axioms M0Crypto.Release.ChaChaLoop.iter_toArr
#print axioms M0Crypto.Release.Reach.runUntil
#print axioms M0Crypto.Release.ChaChaSpec.chacha20_get
#print axioms M0Crypto.Release.ChaChaSpec.block_get
#print axioms M0Crypto.Release.ChaChaRet.ret
#print axioms M0Crypto.Release.ChaChaSetup.checks
#print axioms M0Crypto.Release.ChaChaInit.init
#print axioms M0Crypto.Release.ChaChaBlock.bsetup
#print axioms M0Crypto.Release.ChaChaBlock.block_ks
#print axioms M0Crypto.Release.ChaChaBlock.bround
#print axioms M0Crypto.Release.ChaChaOut.outB_eq
#print axioms M0Crypto.Release.ChaChaOut.bpost
#print axioms M0Crypto.Release.ChaChaOut.bout
#print axioms M0Crypto.Release.ChaChaXor.lnext
#print axioms M0Crypto.Release.ChaChaXor.blocks
#print axioms M0Crypto.Release.ChaChaXor.xor_reach
#print axioms M0Crypto.Release.ChaChaXor.chacha20_xor_correct
#print axioms M0Crypto.Release.ChaChaXor.result_output

-- Gate 5: Poly1305.
#print axioms M0Crypto.Release.PolyArith.mul_fold
#print axioms M0Crypto.Release.PolyArith.carry_fold
#print axioms M0Crypto.Release.PolyArith.block_arith
#print axioms M0Crypto.Release.PolySpec.polyBlocks_append
#print axioms M0Crypto.Release.PolySpec.polyAcc_eq
#print axioms M0Crypto.Release.PolySpec.step_mod
#print axioms M0Crypto.Release.PolySpec.leNat_bytesAt16
#print axioms M0Crypto.Release.PolySpec.clamp_words
#print axioms M0Crypto.Release.PolySpec.tag_byte
#print axioms M0Crypto.Release.PolySpec.tag_reduce
#print axioms M0Crypto.Release.PolyInit.init_reach
#print axioms M0Crypto.Release.PolyInit.init_correct
#print axioms M0Crypto.Release.PolyMac.mac_run
#print axioms M0Crypto.Release.PolyMac.narrow_run
#print axioms M0Crypto.Release.PolyMac.colend_run

-- Gate 5: blocks execution layer (RFC refinement is audited below).
#print axioms M0Crypto.Release.PolyBlocks.segments_at
#print axioms M0Crypto.Release.PolyBlocks.prologue_at
#print axioms M0Crypto.Release.PolyBlocks.setup_at
#print axioms M0Crypto.Release.PolyBlocks.epilogue_at
#print axioms M0Crypto.Release.PolyBlocks.load_words
#print axioms M0Crypto.Release.PolyBlocks.mac4_v
#print axioms M0Crypto.Release.PolyBlocks.body_run
#print axioms M0Crypto.Release.PolyBlocks.one_run
#print axioms M0Crypto.Release.PolyBlocks.loop_run
#print axioms M0Crypto.Release.PolyBlocks.loop_mem
#print axioms M0Crypto.Release.PolyBlocks.blocks_ret
#print axioms M0Crypto.Release.PolyBlocks.publish_effect
#print axioms M0Crypto.Release.PolyBlocks.blocks_reach
#print axioms M0Crypto.Release.PolyBlocks.blocks_execution
#print axioms M0Crypto.Release.PolyBlocks.result_frame
#print axioms M0Crypto.Release.PolyBlocks.result_cleared
#print axioms M0Crypto.Release.PolyBlocks.result_h
#print axioms M0Crypto.Release.PolyBlocks.result_zero
#print axioms M0Crypto.Release.PolyBlocks.result_key_preserved
#print axioms M0Crypto.Release.PolyBlocks.blocks_execution_safe

-- Gate 5: machine arithmetic refined to the RFC block fold.
#print axioms M0Crypto.Release.PolyCarry.adc5
#print axioms M0Crypto.Release.PolyCarry.adc5_mod
#print axioms M0Crypto.Release.PolyBlocks.addMsg_h
#print axioms M0Crypto.Release.PolyBlocks.fold_h
#print axioms M0Crypto.Release.PolyBlocks.body_correct
#print axioms M0Crypto.Release.PolyBlocks.one_correct
#print axioms M0Crypto.Release.PolyBlocks.loop_correct
#print axioms M0Crypto.Release.PolyBlocks.result_blocks_correct
#print axioms M0Crypto.Release.PolyBlocks.blocks_correct

-- Gate 5: finish and context invariant preservation.
#print axioms M0Crypto.Release.PolyFinish.segments_at
#print axioms M0Crypto.Release.PolyFinish.carry_correct
#print axioms M0Crypto.Release.PolyFinish.arithmetic_correct
#print axioms M0Crypto.Release.PolyFinish.tagMem_bytes
#print axioms M0Crypto.Release.PolyFinish.pop_ret
#print axioms M0Crypto.Release.PolyFinish.emit_writes
#print axioms M0Crypto.Release.PolyFinish.finish_reach
#print axioms M0Crypto.Release.PolyFinish.result_tag
#print axioms M0Crypto.Release.PolyFinish.result_frame
#print axioms M0Crypto.Release.PolyFinish.finish_correct
#print axioms M0Crypto.Release.PolyContext.init_keyOK
#print axioms M0Crypto.Release.PolyContext.init_acc
#print axioms M0Crypto.Release.PolyContext.init_key
#print axioms M0Crypto.Release.PolyContext.init_pad
#print axioms M0Crypto.Release.PolyContext.blocks_words
#print axioms M0Crypto.Release.PolyContext.blocks_keyOK
#print axioms M0Crypto.Release.PolyContext.blocks_pad
#print axioms M0Crypto.Release.PolyContext.finish_bound
#print axioms M0Crypto.Release.PolyContext.finish_acc
#print axioms M0Crypto.Release.PolyContext.finish_pad
#print axioms M0Crypto.Release.PolyContext.key_split
#print axioms M0Crypto.Release.PolyContext.poly1305_chain

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
#print axioms M0Crypto.Release.ChaChaOut.ach_mem_sym
#print axioms M0Crypto.Release.ChaChaOut.ach_regs_sym
#print axioms M0Crypto.Release.ChaChaOut.ach_effect

-- Approach C, H7a: alignment and write-region checkers, their soundness, and Reach.symBlock.
#print axioms M0Crypto.Sym.peel_sound
#print axioms M0Crypto.Sym.add_toNat_mod_of_dvd
#print axioms M0Crypto.Sym.accAligned_sound
#print axioms M0Crypto.Sym.add_sub_rearr
#print axioms M0Crypto.Sym.accCovered_sound
#print axioms M0Crypto.Sym.alignChk_sound
#print axioms M0Crypto.Sym.writeChk_sound
#print axioms M0Crypto.Release.Reach.symBlock
#print axioms M0Crypto.Release.Reach.alOne
#print axioms M0Crypto.Release.Reach.rgOne

#print axioms M0Crypto.Release.ChaChaXor.clr_mem
#print axioms M0Crypto.Release.ChaChaXor.clr_regs
#print axioms M0Crypto.Release.ChaChaXor.clr_accesses
#print axioms M0Crypto.Release.ChaChaXor.clr_aligned
