#!/bin/sh
# Full check of the release assets: pinned build, byte/artifact correspondence (proof
# fixtures and each asset's release object), ISA rejection, Lean proofs and release-artifact
# model checks (lake build in each asset's workspace), model decoder vs llvm-objdump,
# specification vs external vectors, axiom audit, QEMU tests, model vs QEMU instruction by
# instruction. Exits non-zero on any failure.
#
# Usage: tools/check.sh [ASSET...]     (default: all; ASSET: chacha20poly1305 blake2s x25519)
# Each asset is checked on its own: its object, its Lake workspace assets/ASSET (which
# compiles the shared sources in lean/ against that asset's artifact), its audit and its
# statements. Steps for one asset only run when that asset is selected.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
# The library sources live in the parent repository (this directory is its `proofs`
# submodule); override with M0C_LIB=/path/to/m0-crypto.
LIB=${M0C_LIB:-$ROOT/..}
export M0C_LIB="$LIB"
[ -f "$LIB/src/m0crypto_chacha20poly1305.S" ] || { echo "library sources not found at $LIB (set M0C_LIB)" >&2; exit 1; }
ALL_ASSETS="chacha20poly1305 blake2s x25519"
ASSETS=${*:-$ALL_ASSETS}
for a in $ASSETS; do
    case " $ALL_ASSETS " in *" $a "*) ;; *) echo "usage: tools/check.sh [$ALL_ASSETS]" >&2; exit 2 ;; esac
done
has() { case " $ASSETS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
LLVM_BIN=${LLVM_BIN:-/opt/homebrew/opt/llvm/bin}
PATH="$HOME/.elan/bin:$PATH"
KERNELS=$(grep -v '^#' tools/kernels.txt | grep .)
artifact_path() { echo "lean/$(echo "$1" | tr . /).lean"; }

if has chacha20poly1305; then
echo "== 1. pinned build (ChaCha20 kernel fixtures)"
tools/build.sh

echo "== 2. checked-in Lean artifacts match the linked ELFs"
echo "$KERNELS" | while read -r stem symbol module; do
    python3 -I tools/extract_artifact.py "build/$stem.elf" "$symbol" "$module" \
        "$(artifact_path "$module")" --check
done
fi

echo "== 2b. release assets: relocation-free units, checked-in Lean artifacts match"
mkdir -p build
if has x25519; then
    # src/x25519.S is generated; the plain library build uses the checked-in copy.
    python3 -I "$LIB/tools/gen_x25519.py" build/x25519.S
    cmp build/x25519.S "$LIB/src/x25519.S" || {
        echo "FAIL: src/x25519.S differs from tools/gen_x25519.py output" >&2; exit 1; }
fi
"$LIB/tools/build_lib.sh" $ASSETS > build/lib-check.txt 2>&1 || {
    cat build/lib-check.txt; echo "FAIL: release library" >&2; exit 1; }
for a in $ASSETS; do
    python3 -I tools/extract_release.py "$LIB/build/lib/$a/m0crypto_$a.o" \
        "assets/$a/artifact/M0Crypto/Artifacts/Release.lean" --check
done
grep -E '^(m0-crypto release asset|text_sha256|text_bytes)' build/lib-check.txt

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

echo "== 4. Lean proofs, one Lake workspace per asset"
for a in $ASSETS; do
    for t in lean-toolchain "assets/$a/lean-toolchain"; do
        if [ "$(cat "$t")" != "$(sed -n 's/^lean=//p' tools/versions.txt)" ]; then
            echo "FAIL: $t does not match tools/versions.txt" >&2
            exit 1
        fi
    done
    START=$(date +%s)
    (cd "assets/$a" && lake build)
    END=$(date +%s)
    echo "lake build $a: $((END - START)) s (incremental if assets/$a/.lake is warm)"
done

echo "== 4b. model decoder agrees with llvm-objdump on every release instruction"
for a in $ASSETS; do
    python3 -I tools/check_listing.py "$LLVM_BIN/llvm-objdump" "$LIB/build/lib/$a/m0crypto_$a.o" "$a"
done

if has chacha20poly1305; then
echo "== 4c. specification agrees with the library's test vectors (RFC 8439, Wycheproof, pyca/cryptography)"
python3 -I tools/spec_vectors.py "$LIB/tests/aead_vectors.h"
fi

echo "== 5. no admissions or custom axioms in sources"
if grep -rnE '\b(sorry|admit|axiom|native_decide|implemented_by|extern)\b' lean/M0Crypto assets/*/artifact; then
    echo "FAIL: forbidden construct in Lean sources" >&2
    exit 1
fi

echo "== 6. axiom audit"
# Fail closed: Lean must exit 0, every claim in assets/ASSET/Audit.lean must have exactly one
# report, and every report must draw its axioms only from the allowed set.
ALLOWED="(propext|Classical\.choice|Quot\.sound)"
for a in $ASSETS; do
    echo "-- $a"
    (cd "assets/$a" && lake env lean Audit.lean) > "$TMP/axioms-$a.txt"
    cat "$TMP/axioms-$a.txt"
    for name in $(sed -n 's/^#print axioms \(M0Crypto[^ ]*\)$/\1/p' "assets/$a/Audit.lean"); do
        n=$(grep -c -F "'$name' " "$TMP/axioms-$a.txt" || true)
        if [ "$n" != 1 ]; then
            echo "FAIL: $a: expected one axiom report for $name, found $n" >&2
            exit 1
        fi
    done
    if grep -v -E "^'[^']+' (does not depend on any axioms|depends on axioms: \[$ALLOWED(, $ALLOWED)*\])\$" "$TMP/axioms-$a.txt"; then
        echo "FAIL: $a: audit output has a line that is not an allowed axiom report" >&2
        exit 1
    fi
done

echo "== 6b. claim statements and trusted definitions match each asset's release baseline"
for a in $ASSETS; do
    tools/statements.sh "$a" > "$TMP/statements-$a.txt"
    diff -u "assets/$a/statements.golden" "$TMP/statements-$a.txt"
done

echo "== 7. library primitives on QEMU Cortex-M0 (behaviour only, not timing)"
"$LIB/tools/test_qemu.sh" > "$TMP/qemu.txt" 2>&1 || { cat "$TMP/qemu.txt"; echo "FAIL: QEMU primitive tests" >&2; exit 1; }
grep -E 'peak stack|RESULT' "$TMP/qemu.txt"

echo "== 7b. machine model agrees with QEMU after every instruction of sampled calls"
FIRST=${ASSETS%% *}
if has chacha20poly1305; then
    python3 -I tools/qemu_steps.py chacha20poly1305 "${QEMU:-qemu-system-arm}" "$LLVM_BIN/llvm-nm" \
        "$LIB/build/lib/chacha20poly1305/text.bin" \
        "$LIB/build/test/test_chacha20.elf" m0c_chacha20_xor \
        "$LIB/build/test/test_aead.elf" m0c_chacha20poly1305_encrypt,m0c_chacha20poly1305_decrypt
fi
if has blake2s; then
    python3 -I tools/qemu_steps.py blake2s "${QEMU:-qemu-system-arm}" "$LLVM_BIN/llvm-nm" \
        "$LIB/build/lib/blake2s/text.bin" \
        "$LIB/build/test/test_blake2s.elf" m0c_blake2s_init,m0c_blake2s_update,m0c_blake2s_final
fi
# SBCS has no traced release call short enough to single-step, so a fixture covers it:
# carry in and out 0 and 1, signed overflow, zero, Rdn = Rm.
for src in fixtures/sbcs_steps.S "$LIB/tests/startup.S"; do
    "$LLVM_BIN/clang" --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
        -c "$src" -o "$TMP/$(basename "$src").o"
done
"${LLD_BIN:-/opt/homebrew/opt/lld/bin}/ld.lld" -T "$LIB/tests/microbit.ld" --build-id=none \
    -o "$TMP/sbcs.elf" "$TMP/startup.S.o" "$TMP/sbcs_steps.S.o"
"$LLVM_BIN/llvm-objcopy" -O binary -j .text.sbcs_fixture "$TMP/sbcs_steps.S.o" "$TMP/sbcs.bin"
python3 -I tools/qemu_steps.py "$FIRST" "${QEMU:-qemu-system-arm}" "$LLVM_BIN/llvm-nm" "$TMP/sbcs.bin" \
    "$TMP/sbcs.elf" sbcs_fixture
# A whole m0c_x25519 call is about three million instructions: sampled windows instead
# (prologue, one ladder step, each loop exit, epilogue).
if has x25519; then
    python3 -I tools/qemu_x25519_windows.py --obj "$LIB/build/lib/x25519/m0crypto_x25519.o" \
        --work "$TMP/x25519-windows"
fi

if has chacha20poly1305; then
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
fi
echo "OK"
