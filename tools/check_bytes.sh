#!/bin/sh
# Byte-level checks of the release assets, without Lean: pinned build, the checked-in Lean
# artifacts equal the built bytes (proof fixtures and each asset's release object), generated
# assembly matches its generator, ISA rejection, library tests on QEMU. Exits non-zero on any
# failure. tools/check.sh runs it before tools/check_proofs.sh, which reads the objects and test
# images it builds.
#
# Usage: tools/check_bytes.sh [ASSET...]     (default: all; ASSET: chacha20poly1305 blake2s x25519 ed25519)
# Steps for one asset only run when that asset is selected.
. "$(dirname "$0")/check_env.sh"
KERNELS=$(grep -v '^#' tools/kernels.txt | grep .)
artifact_path() { echo "lean/$(echo "$1" | tr . /).lean"; }

if has chacha20poly1305; then
echo "== 1. pinned build (ChaCha20 kernel fixtures)"
tools/build.sh

echo "== 2. checked-in Lean artifacts match the linked ELFs"
python3 -I tools/test_extract_artifact.py
echo "$KERNELS" | while read -r stem symbol module; do
    python3 -I tools/extract_artifact.py "build/$stem.elf" "$symbol" "$module" \
        "$(artifact_path "$module")" --check
done
fi

echo "== 2b. release assets: relocation-free units, checked-in Lean artifacts match"
if has x25519; then
    # src/x25519.S is generated; the plain library build uses the checked-in copy.
    python3 -I "$LIB/tools/gen_x25519.py" build/x25519.S
    cmp build/x25519.S "$LIB/src/x25519.S" || {
        echo "FAIL: src/x25519.S differs from tools/gen_x25519.py output" >&2; exit 1; }
fi
if has ed25519; then
    # src/ed25519_compact.S and src/ed25519_fast.S are generated, like src/x25519.S.
    for b in compact fast; do
        python3 -I "$LIB/tools/gen_ed25519.py" "$b" "build/ed25519_$b.S"
        cmp "build/ed25519_$b.S" "$LIB/src/ed25519_$b.S" || {
            echo "FAIL: src/ed25519_$b.S differs from tools/gen_ed25519.py output" >&2; exit 1; }
    done
fi
"$LIB/tools/build_lib.sh" $ASSETS > build/lib-check.txt 2>&1 || {
    cat build/lib-check.txt; echo "FAIL: release library" >&2; exit 1; }
for a in $ASSETS; do
    for u in $(units "$a"); do
        m=$(echo "$u" | cut -d: -f2)
        python3 -I tools/extract_release.py "${u%%:*}" "assets/$a/artifact/M0Crypto/Artifacts/$m.lean" \
            --module "M0Crypto.Artifacts.$m" --check
    done
done
grep -E '^(m0-crypto release asset|text_sha256|text_bytes)' build/lib-check.txt

echo "== 3. assembler rejects non-ARMv6-M instructions"
for insn in "ror r0, r0, #3" "add.w r0, r0, r1" "eor r0, r1, r2" "cbz r0, ."; do
    printf '.syntax unified\n.thumb\n%s\n' "$insn" > "$TMP/bad.S"
    if clang --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
        -c "$TMP/bad.S" -o "$TMP/bad.o" 2>/dev/null; then
        echo "FAIL: assembler accepted '$insn'" >&2
        exit 1
    fi
    echo "rejected: $insn"
done

echo "== 7. library primitives on QEMU Cortex-M0 (behaviour only, not timing)"
"$LIB/tools/test_qemu.sh" $ASSETS > "$TMP/qemu.txt" 2>&1 || { cat "$TMP/qemu.txt"; echo "FAIL: QEMU primitive tests" >&2; exit 1; }
grep -E 'peak stack|RESULT' "$TMP/qemu.txt"

if has chacha20poly1305; then
echo "== 8. diagnostic disassembly (not part of the trusted chain)"
echo "$KERNELS" | while read -r stem _symbol _module; do
    llvm-objdump -d --triple=thumbv6m-none-eabi "build/$stem.elf" | sed -n '/<m0c_/,$p' | head -24
    echo "..."
done

echo "== hashes"
echo "$KERNELS" | while read -r stem _symbol module; do
    shasum -a 256 "build/$stem.elf"
    sed -n "s/^-- Fragment sha256: /  fragment: /p" "$(artifact_path "$module")"
done
fi
echo "OK: bytes"
