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
M0Crypto.Proofs.ChaCha20QR.decodes
M0Crypto.Proofs.ChaCha20QR.run_eq
M0Crypto.Proofs.ChaCha20QR.trace_independent
M0Crypto.Proofs.ChaCha20QR.exec_all_regs
M0Crypto.Proofs.ChaCha20QR.exec_all_frame
M0Crypto.Proofs.ChaCha20QR.qr_spec
M0Crypto.Proofs.ChaCha20DRound.decodes
M0Crypto.Proofs.ChaCha20DRound.run_eq
M0Crypto.Proofs.ChaCha20DRound.trace_independent
M0Crypto.Proofs.ChaCha20DRound.core_spec
M0Crypto.Proofs.ChaCha20DRound.block_spec
M0Crypto.Proofs.ChaCha20DRound.block_mem_other
M0Crypto.Proofs.ChaCha20DRound.dround_view
M0Crypto.Proofs.ChaCha20DRound.innerBlock_toArr
M0Crypto.Proofs.ChaCha20DRound.dround_spec
M0Crypto.Proofs.ChaCha20DRoundV2.decodes
M0Crypto.Proofs.ChaCha20DRoundV2.run_eq
M0Crypto.Proofs.ChaCha20DRoundV2.trace_independent
M0Crypto.Proofs.ChaCha20DRoundV2.keep_spec
M0Crypto.Proofs.ChaCha20DRoundV2.have_spec
M0Crypto.Proofs.ChaCha20DRoundV2.dround_view
M0Crypto.Proofs.ChaCha20DRoundV2.dround_spec
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
M0Crypto.Release.ChaChaRound.dround_at
M0Crypto.Release.ChaChaRound.core_regs
M0Crypto.Release.ChaChaRound.qr_effect
M0Crypto.Thumb.alignedAll_sp
M0Crypto.Thumb.execAll_mem_sp
M0Crypto.Thumb.traceAll_sp_congr
M0Crypto.Release.ChaChaRound.qr_view
M0Crypto.Release.ChaChaRound.dround_view
M0Crypto.Release.ChaChaRound.dround_aligned
M0Crypto.Release.ChaChaRound.dround_mem
M0Crypto.Release.ChaChaRound.dround_regs
M0Crypto.Release.ChaChaRound.dround_trace_congr
M0Crypto.Thumb.runH_block
M0Crypto.Thumb.stepH_of_instr
M0Crypto.Thumb.traceAll_writes_sp
M0Crypto.Release.ChaChaLoop.loop
M0Crypto.Release.ChaChaLoop.iter_toArr
M0Crypto.Release.Reach.runUntil
M0Crypto.Release.ChaChaSpec.chacha20_get
M0Crypto.Release.ChaChaSpec.block_get
M0Crypto.Release.ChaChaRet.ret
M0Crypto.Release.ChaChaSetup.checks
M0Crypto.Release.ChaChaInit.init
M0Crypto.Release.ChaChaBlock.bsetup
M0Crypto.Release.ChaChaBlock.block_ks
M0Crypto.Release.ChaChaBlock.bround
M0Crypto.Release.ChaChaOut.outB_eq
M0Crypto.Release.ChaChaOut.bpost
M0Crypto.Release.ChaChaOut.bout
M0Crypto.Release.ChaChaXor.lnext
M0Crypto.Release.ChaChaXor.blocks
M0Crypto.Release.ChaChaXor.xor_reach
M0Crypto.Release.ChaChaXor.chacha20_xor_correct
M0Crypto.Release.ChaChaXor.result_output
M0Crypto.Release.PolyArith.mul_fold
M0Crypto.Release.PolyArith.carry_fold
M0Crypto.Release.PolyArith.block_arith
M0Crypto.Release.PolySpec.polyBlocks_append
M0Crypto.Release.PolySpec.polyAcc_eq
M0Crypto.Release.PolySpec.step_mod
M0Crypto.Release.PolySpec.leNat_bytesAt16
M0Crypto.Release.PolySpec.clamp_words
M0Crypto.Release.PolySpec.tag_byte
M0Crypto.Release.PolySpec.tag_reduce
M0Crypto.Release.PolyInit.init_reach
M0Crypto.Release.PolyInit.init_correct
M0Crypto.Release.PolyMac.mac_run
M0Crypto.Release.PolyMac.narrow_run
M0Crypto.Release.PolyMac.colend_run
M0Crypto.Release.PolyBlocks.segments_at
M0Crypto.Release.PolyBlocks.prologue_at
M0Crypto.Release.PolyBlocks.setup_at
M0Crypto.Release.PolyBlocks.epilogue_at
M0Crypto.Release.PolyBlocks.load_words
M0Crypto.Release.PolyBlocks.mac4_v
M0Crypto.Release.PolyBlocks.body_run
M0Crypto.Release.PolyBlocks.one_run
M0Crypto.Release.PolyBlocks.loop_run
M0Crypto.Release.PolyBlocks.loop_mem
M0Crypto.Release.PolyBlocks.blocks_ret
M0Crypto.Release.PolyBlocks.publish_effect
M0Crypto.Release.PolyBlocks.blocks_reach
M0Crypto.Release.PolyBlocks.blocks_execution
M0Crypto.Release.PolyBlocks.result_frame
M0Crypto.Release.PolyBlocks.result_cleared
M0Crypto.Release.PolyBlocks.result_h
M0Crypto.Release.PolyBlocks.result_zero
M0Crypto.Release.PolyBlocks.result_key_preserved
M0Crypto.Release.PolyBlocks.blocks_execution_safe
M0Crypto.Release.PolyCarry.adc5
M0Crypto.Release.PolyCarry.adc5_mod
M0Crypto.Release.PolyBlocks.addMsg_h
M0Crypto.Release.PolyBlocks.fold_h
M0Crypto.Release.PolyBlocks.body_correct
M0Crypto.Release.PolyBlocks.one_correct
M0Crypto.Release.PolyBlocks.loop_correct
M0Crypto.Release.PolyBlocks.result_blocks_correct
M0Crypto.Release.PolyBlocks.blocks_correct
M0Crypto.Release.PolyFinish.segments_at
M0Crypto.Release.PolyFinish.carry_correct
M0Crypto.Release.PolyFinish.arithmetic_correct
M0Crypto.Release.PolyFinish.tagMem_bytes
M0Crypto.Release.PolyFinish.pop_ret
M0Crypto.Release.PolyFinish.emit_writes
M0Crypto.Release.PolyFinish.finish_reach
M0Crypto.Release.PolyFinish.result_tag
M0Crypto.Release.PolyFinish.result_frame
M0Crypto.Release.PolyFinish.finish_correct
M0Crypto.Release.PolyContext.init_keyOK
M0Crypto.Release.PolyContext.init_acc
M0Crypto.Release.PolyContext.init_key
M0Crypto.Release.PolyContext.init_pad
M0Crypto.Release.PolyContext.blocks_words
M0Crypto.Release.PolyContext.blocks_keyOK
M0Crypto.Release.PolyContext.blocks_pad
M0Crypto.Release.PolyContext.finish_bound
M0Crypto.Release.PolyContext.finish_acc
M0Crypto.Release.PolyContext.finish_pad
M0Crypto.Release.PolyContext.key_split
M0Crypto.Release.PolyContext.poly1305_chain
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
