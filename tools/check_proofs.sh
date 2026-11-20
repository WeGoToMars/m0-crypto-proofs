#!/bin/sh
# Lean checks of the release assets: proofs built in each asset's Lake workspace, model decoder
# vs llvm-objdump, specification vs external vectors, source scan, axiom audit, claim statements
# vs the golden baseline, model vs QEMU instruction by instruction. Exits non-zero on any
# failure. It reads the release objects and test images that tools/check_bytes.sh builds and
# checks, so run that first on the same tree (tools/check.sh runs both).
#
# Usage: tools/check_proofs.sh [ASSET...]     (default: all; ASSET: chacha20poly1305 blake2s x25519 ed25519)
# Each asset is checked on its own: its Lake workspace assets/ASSET (which compiles the shared
# sources in lean/ against that asset's artifact), its audit and its statements.
. "$(dirname "$0")/check_env.sh"
for a in $ASSETS; do
    for u in $(units "$a"); do
        [ -f "${u%%:*}" ] || { echo "${u%%:*} not found: run tools/check_bytes.sh first" >&2; exit 1; }
    done
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
    for u in $(units "$a"); do
        python3 -I tools/check_listing.py llvm-objdump "${u%%:*}" "$a" ${u##*:}
    done
done

if has chacha20poly1305; then
echo "== 4c. specification agrees with the library's test vectors (RFC 8439, Wycheproof, pyca/cryptography)"
python3 -I tools/spec_vectors.py "$LIB/tests/aead_vectors.h" "$LIB/tests/chacha20_vectors.h"
fi
if has blake2s; then
echo "== 4c. BLAKE2s specification agrees with the library's test vectors (Python hashlib)"
python3 -I tools/spec_vectors.py "$LIB/tests/blake2s_vectors.h"
fi
if has x25519; then
echo "== 4c. X25519 specification agrees with the library's test vectors (RFC 7748, Wycheproof)"
python3 -I tools/spec_vectors.py "$LIB/tests/x25519_vectors.h"
fi
if has ed25519; then
echo "== 4d. Ed25519 entries and internal routines of both builds in the model (tests, native)"
(cd assets/ed25519 && lake build release_check && .lake/build/bin/release_check 2)
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
    (cd "assets/$a" && lake env lean Audit.lean) > "$TMP/axioms-raw-$a.txt"
    cat "$TMP/axioms-raw-$a.txt"
    # Lean wraps a long report over several lines: join each continuation line to its report.
    awk '/^\047/ && NR > 1 {print r; r = ""} {l = $0; if (r != "") {sub(/^ +/, "", l); r = r " " l} else r = l}
         END {if (NR) print r}' "$TMP/axioms-raw-$a.txt" > "$TMP/axioms-$a.txt"
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

echo "== 7b. machine model agrees with QEMU after every instruction a call can execute"
FIRST=${ASSETS%% *}
if has chacha20poly1305; then
    python3 -I tools/qemu_steps.py --cover "$LIB/build/lib/chacha20poly1305/m0crypto_chacha20poly1305.o" chacha20poly1305 "${QEMU:-qemu-system-arm}" llvm-nm \
        "$LIB/build/lib/chacha20poly1305/text.bin" \
        "$LIB/build/test/test_chacha20.elf" m0c_chacha20_xor \
        "$LIB/build/test/test_aead.elf" \
        m0c_chacha20poly1305_encrypt,m0c_chacha20poly1305_decrypt,m0c_poly1305_blocks
fi
if has blake2s; then
    python3 -I tools/qemu_steps.py --cover "$LIB/build/lib/blake2s/m0crypto_blake2s.o" blake2s "${QEMU:-qemu-system-arm}" llvm-nm \
        "$LIB/build/lib/blake2s/text.bin" \
        "$LIB/build/test/test_blake2s.elf" m0c_blake2s_init,m0c_blake2s_update,m0c_blake2s_final
fi
# Fixtures cover forms no traced release call executes in a short call: SBCS (carry in and
# out 0 and 1, signed overflow, zero, Rdn = Rm), and LSLS/LSRS by register, ASRS (immediate),
# REV and ADD Rdn, PC (edge shift amounts, carries, register classes, both PC alignments).
clang --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
    -c "$LIB/tests/startup.S" -o "$TMP/startup.S.o"
for fx in sbcs ed25519_forms; do
    clang --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
        -c "fixtures/${fx}_steps.S" -o "$TMP/$fx.o"
    ld.lld -T "$LIB/tests/microbit.ld" --build-id=none \
        -o "$TMP/$fx.elf" "$TMP/startup.S.o" "$TMP/$fx.o"
    llvm-objcopy -O binary -j ".text.${fx}_fixture" "$TMP/$fx.o" "$TMP/$fx.bin"
    python3 -I tools/qemu_steps.py "$FIRST" "${QEMU:-qemu-system-arm}" llvm-nm "$TMP/$fx.bin" \
        "$TMP/$fx.elf" "${fx}_fixture"
done
# A whole m0c_x25519 call is too long to single-step: sampled windows instead
# (prologue, one ladder step, each loop exit, epilogue).
if has x25519; then
    python3 -I tools/qemu_x25519_windows.py --obj "$LIB/build/lib/x25519/m0crypto_x25519.o" \
        --work "$TMP/x25519-windows"
fi
echo "OK: proofs"
