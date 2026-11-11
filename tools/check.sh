#!/bin/sh
# Full check: pinned build, byte/artifact correspondence (proof fixtures and the
# release library), ISA rejection, Lean proofs and release-artifact model checks
# (lake build), model decoder vs llvm-objdump, axiom audit, QEMU tests. Exits non-zero on any failure.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
# The library sources live in the parent repository (this directory is its `proofs`
# submodule); override with M0C_LIB=/path/to/m0-crypto.
LIB=${M0C_LIB:-$ROOT/..}
export M0C_LIB="$LIB"
[ -f "$LIB/src/m0crypto.S" ] || { echo "library sources not found at $LIB (set M0C_LIB)" >&2; exit 1; }
LLVM_BIN=${LLVM_BIN:-/opt/homebrew/opt/llvm/bin}
PATH="$HOME/.elan/bin:$PATH"
KERNELS=$(grep -v '^#' tools/kernels.txt | grep .)
artifact_path() { echo "lean/$(echo "$1" | tr . /).lean"; }

echo "== 1. pinned build"
tools/build.sh

echo "== 2. checked-in Lean artifacts match the linked ELFs"
echo "$KERNELS" | while read -r stem symbol module; do
    python3 -I tools/extract_artifact.py "build/$stem.elf" "$symbol" "$module" \
        "$(artifact_path "$module")" --check
done

echo "== 2b. release library: relocation-free unit, checked-in Lean artifact matches"
mkdir -p build
"$LIB/tools/build_lib.sh" speed > build/lib-check.txt 2>&1 || {
    cat build/lib-check.txt; echo "FAIL: release library" >&2; exit 1; }
python3 -I tools/extract_release.py "$LIB/build/lib/speed/m0crypto.o" \
    lean/M0Crypto/Artifacts/Release.lean --check
grep -E '^(text_sha256|text_bytes)' build/lib-check.txt
if "$LIB/tools/build_lib.sh" protection 2>/dev/null; then
    echo "FAIL: build_lib accepted the unimplemented protection profile" >&2; exit 1
fi
echo "refused: protection profile"

echo "== 3. assembler rejects non-ARMv6-M instructions"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
for insn in "ror r0, r0, #3" "add.w r0, r0, r1" "eor r0, r1, r2" "cbz r0, ."; do
    printf '.syntax unified\n.thumb\n%s\n' "$insn" > "$TMP/bad.S"
    if "$LLVM_BIN/clang" --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
        -c "$TMP/bad.S" -o "$TMP/bad.o" 2>/dev/null; then
        echo "FAIL: assembler accepted '$insn'" >&2
        exit 1
    fi
    echo "rejected: $insn"
done

echo "== 4. Lean proofs"
if [ "$(cat lean-toolchain)" != "$(sed -n 's/^lean=//p' tools/versions.txt)" ]; then
    echo "FAIL: lean-toolchain does not match tools/versions.txt" >&2
    exit 1
fi
START=$(date +%s)
lake build
END=$(date +%s)
echo "lake build: $((END - START)) s (incremental if .lake is warm)"

echo "== 4b. model decoder agrees with llvm-objdump on every release instruction"
python3 -I tools/check_listing.py "$LLVM_BIN/llvm-objdump" "$LIB/build/lib/speed/m0crypto.o"

echo "== 5. no admissions or custom axioms in sources"
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|extern)\b' lean/M0Crypto lean/M0Crypto.lean; then
    echo "FAIL: forbidden construct in Lean sources" >&2
    exit 1
fi

echo "== 6. axiom audit"
# Fail closed: Lean must exit 0, and every expected theorem must appear exactly once
# with an axiom list drawn only from the allowed set.
lake env lean lean/Audit.lean > "$TMP/axioms.txt"
cat "$TMP/axioms.txt"
EXPECTED="M0Crypto.Spec.ChaCha20.qround_size
M0Crypto.Spec.ChaCha20.innerBlock_size
M0Crypto.Spec.ChaCha20.innerBlocks_size
M0Crypto.Spec.ChaCha20.wordsOfBytes_length
M0Crypto.Spec.ChaCha20.initState_size
M0Crypto.Spec.ChaCha20.block_length
M0Crypto.Spec.ChaCha20.quarterRound_rfc8439_2_1_1
M0Crypto.Proofs.ChaCha20QuarterRound.decodes
M0Crypto.Proofs.ChaCha20QuarterRound.run_eq
M0Crypto.Proofs.ChaCha20QuarterRound.trace_independent
M0Crypto.Proofs.ChaCha20QuarterRound.exec_all_regs
M0Crypto.Proofs.ChaCha20QuarterRound.exec_all_frame
M0Crypto.Proofs.ChaCha20QuarterRound.qr_spec
M0Crypto.Proofs.ChaCha20DoubleRound.decodes
M0Crypto.Proofs.ChaCha20DoubleRound.run_eq
M0Crypto.Proofs.ChaCha20DoubleRound.trace_independent
M0Crypto.Proofs.ChaCha20DoubleRound.core_spec
M0Crypto.Proofs.ChaCha20DoubleRound.block_spec
M0Crypto.Proofs.ChaCha20DoubleRound.block_mem_other
M0Crypto.Proofs.ChaCha20DoubleRound.dround_view
M0Crypto.Proofs.ChaCha20DoubleRound.innerBlock_toArr
M0Crypto.Proofs.ChaCha20DoubleRound.dround_spec
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.decodes
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.run_eq
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.trace_independent
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.keep_spec
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.have_spec
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.dround_view
M0Crypto.Proofs.ChaCha20DoubleRoundKeep15.dround_spec
M0Crypto.Thumb.decode_at
M0Crypto.Thumb.step_of_instrAt
M0Crypto.Thumb.exec_mem_other
M0Crypto.Thumb.step_mem_other
M0Crypto.Thumb.runFast_eq
M0Crypto.Artifacts.Release.bytes_length
M0Crypto.Thumb.step_of_stepH
M0Crypto.Thumb.runUntil_of_runH
M0Crypto.Thumb.runH_add
M0Crypto.Thumb.runH_seq
M0Crypto.Thumb.runSeq_eq
M0Crypto.Thumb.execAll_mem
M0Crypto.Thumb.execAll_regs_other
M0Crypto.Release.ChaCha20Round.dround_at
M0Crypto.Release.ChaCha20Round.core_regs
M0Crypto.Release.ChaCha20Round.qr_effect
M0Crypto.Thumb.alignedAll_sp
M0Crypto.Thumb.execAll_mem_sp
M0Crypto.Thumb.traceAll_sp_congr
M0Crypto.Release.ChaCha20Round.qr_view
M0Crypto.Release.ChaCha20Round.dround_view
M0Crypto.Release.ChaCha20Round.dround_aligned
M0Crypto.Release.ChaCha20Round.dround_mem
M0Crypto.Release.ChaCha20Round.dround_regs
M0Crypto.Release.ChaCha20Round.dround_trace_congr
M0Crypto.Thumb.runH_block
M0Crypto.Thumb.stepH_of_instr
M0Crypto.Thumb.traceAll_writes_sp
M0Crypto.Release.ChaCha20Loop.loop
M0Crypto.Release.ChaCha20Loop.iter_toArr
M0Crypto.Release.Reach.runUntil
M0Crypto.Release.ChaCha20Spec.chacha20_get
M0Crypto.Release.ChaCha20Spec.block_get
M0Crypto.Release.ChaCha20Return.ret
M0Crypto.Release.ChaCha20Setup.checks
M0Crypto.Release.ChaCha20Init.init
M0Crypto.Release.ChaCha20Block.block_setup
M0Crypto.Release.ChaCha20Block.block_keystream
M0Crypto.Release.ChaCha20Block.block_rounds
M0Crypto.Release.ChaCha20Output.output_byte_eq
M0Crypto.Release.ChaCha20Output.block_post
M0Crypto.Release.ChaCha20Output.block_output
M0Crypto.Release.ChaCha20Xor.loop_next
M0Crypto.Release.ChaCha20Xor.blocks
M0Crypto.Release.ChaCha20Xor.xor_reach
M0Crypto.Release.ChaCha20Xor.xor_correct
M0Crypto.Release.ChaCha20Xor.result_output
M0Crypto.Release.Poly1305Arith.mul_fold
M0Crypto.Release.Poly1305Arith.carry_fold
M0Crypto.Release.Poly1305Arith.block_arith
M0Crypto.Release.Poly1305Spec.polyBlocks_append
M0Crypto.Release.Poly1305Spec.polyAcc_eq
M0Crypto.Release.Poly1305Spec.step_mod
M0Crypto.Release.Poly1305Spec.leNat_bytesAt16
M0Crypto.Release.Poly1305Spec.clamp_words
M0Crypto.Release.Poly1305Spec.tag_byte
M0Crypto.Release.Poly1305Spec.tag_reduce
M0Crypto.Release.Poly1305Init.init_reach
M0Crypto.Release.Poly1305Init.init_correct
M0Crypto.Release.Poly1305Mac.mac_run
M0Crypto.Release.Poly1305Mac.narrow_run
M0Crypto.Release.Poly1305Mac.colend_run
M0Crypto.Release.Poly1305Blocks.segments_at
M0Crypto.Release.Poly1305Blocks.prologue_at
M0Crypto.Release.Poly1305Blocks.setup_at
M0Crypto.Release.Poly1305Blocks.epilogue_at
M0Crypto.Release.Poly1305Blocks.load_words
M0Crypto.Release.Poly1305Blocks.mac4_v
M0Crypto.Release.Poly1305Blocks.body_run
M0Crypto.Release.Poly1305Blocks.one_run
M0Crypto.Release.Poly1305Blocks.loop_run
M0Crypto.Release.Poly1305Blocks.loop_mem
M0Crypto.Release.Poly1305Blocks.blocks_ret
M0Crypto.Release.Poly1305Blocks.publish_effect
M0Crypto.Release.Poly1305Blocks.blocks_reach
M0Crypto.Release.Poly1305Blocks.blocks_execution
M0Crypto.Release.Poly1305Blocks.result_frame
M0Crypto.Release.Poly1305Blocks.result_cleared
M0Crypto.Release.Poly1305Blocks.result_h
M0Crypto.Release.Poly1305Blocks.result_zero
M0Crypto.Release.Poly1305Blocks.result_key_preserved
M0Crypto.Release.Poly1305Blocks.blocks_execution_safe
M0Crypto.Release.Poly1305Carry.adc5
M0Crypto.Release.Poly1305Carry.adc5_mod
M0Crypto.Release.Poly1305Blocks.addMsg_h
M0Crypto.Release.Poly1305Blocks.fold_h
M0Crypto.Release.Poly1305Blocks.body_correct
M0Crypto.Release.Poly1305Blocks.one_correct
M0Crypto.Release.Poly1305Blocks.loop_correct
M0Crypto.Release.Poly1305Blocks.result_blocks_correct
M0Crypto.Release.Poly1305Blocks.blocks_correct
M0Crypto.Release.Poly1305Finish.segments_at
M0Crypto.Release.Poly1305Finish.carry_correct
M0Crypto.Release.Poly1305Finish.arithmetic_correct
M0Crypto.Release.Poly1305Finish.tagMem_bytes
M0Crypto.Release.Poly1305Finish.pop_ret
M0Crypto.Release.Poly1305Finish.emit_writes
M0Crypto.Release.Poly1305Finish.finish_reach
M0Crypto.Release.Poly1305Finish.result_tag
M0Crypto.Release.Poly1305Finish.result_frame
M0Crypto.Release.Poly1305Finish.finish_correct
M0Crypto.Release.Poly1305Context.init_keyOk
M0Crypto.Release.Poly1305Context.init_acc
M0Crypto.Release.Poly1305Context.init_key
M0Crypto.Release.Poly1305Context.init_pad
M0Crypto.Release.Poly1305Context.blocks_words
M0Crypto.Release.Poly1305Context.blocks_keyOk
M0Crypto.Release.Poly1305Context.blocks_pad
M0Crypto.Release.Poly1305Context.finish_bound
M0Crypto.Release.Poly1305Context.finish_acc
M0Crypto.Release.Poly1305Context.finish_pad
M0Crypto.Release.Poly1305Context.key_split
M0Crypto.Release.Poly1305Context.poly1305_chain
M0Crypto.Release.Aead.mac_padded
M0Crypto.Release.Aead.aead_setup
M0Crypto.Release.Aead.crypt_reach
M0Crypto.Release.Aead.bytesAt_le64
M0Crypto.Release.Aead.lengthMem_bytes
M0Crypto.Release.Aead.lengths_reach
M0Crypto.Release.Aead.finish_call
M0Crypto.Release.Aead.clear_reach
M0Crypto.Release.Aead.epilogue_reach
M0Crypto.Release.Aead.mac_phase
M0Crypto.Release.Aead.finish_phase
M0Crypto.Release.Aead.encrypt_reach
M0Crypto.Release.Aead.encrypt_correct
M0Crypto.Release.Aead.crypt_reach_narrow
M0Crypto.Release.Aead.clear_return
M0Crypto.Release.Aead.compare_loop
M0Crypto.Release.Aead.compare_reach
M0Crypto.Release.Aead.decrypt_reach
M0Crypto.Release.Aead.decrypt_correct
M0Crypto.Release.Aead.rejected_writes"
ALLOWED="(propext|Classical\.choice|Quot\.sound)"
for name in $EXPECTED; do
    n=$(grep -c -F "'$name' " "$TMP/axioms.txt" || true)
    if [ "$n" != 1 ]; then
        echo "FAIL: expected one axiom report for $name, found $n" >&2
        exit 1
    fi
    if ! grep -F "'$name' " "$TMP/axioms.txt" | grep -q -E \
        "^'[^']+' (does not depend on any axioms|depends on axioms: \[$ALLOWED(, $ALLOWED)*\])\$"; then
        echo "FAIL: unexpected axioms for $name" >&2
        exit 1
    fi
done
# Lines beyond EXPECTED (theorems added to lean/Audit.lean by later work) must also be
# axiom reports drawn only from the allowed set.
if grep -v -E "^'[^']+' (does not depend on any axioms|depends on axioms: \[$ALLOWED(, $ALLOWED)*\])\$" "$TMP/axioms.txt"; then
    echo "FAIL: audit output has a line that is not an allowed axiom report" >&2
    exit 1
fi

echo "== 6b. audited theorem statements match the release baseline"
tools/statements.sh > "$TMP/statements.txt"
diff -u tools/statements.golden "$TMP/statements.txt"

echo "== 7. library primitive on QEMU Cortex-M0 (behaviour only, not timing)"
"$LIB/tools/test_qemu.sh" > "$TMP/qemu.txt" 2>&1 || { cat "$TMP/qemu.txt"; echo "FAIL: QEMU primitive tests" >&2; exit 1; }
grep -E 'peak stack|RESULT' "$TMP/qemu.txt"

echo "== 8. diagnostic disassembly (not part of the trusted chain)"
echo "$KERNELS" | while read -r stem _symbol _module; do
    "$LLVM_BIN/llvm-objdump" -d --triple=thumbv6m-none-eabi "build/$stem.elf" | sed -n '/<m0c_/,$p' | head -24
    echo "..."
done

echo "== hashes"
echo "$KERNELS" | while read -r stem _symbol module; do
    shasum -a 256 "build/$stem.elf"
    sed -n "s/^-- Fragment sha256: /  fragment: /p" "$(artifact_path "$module")"
done
echo "OK"
