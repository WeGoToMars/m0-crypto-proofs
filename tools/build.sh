#!/bin/sh
# Assemble and link the proof kernels with pinned LLVM tools.
#
# Usage: tools/build.sh            (writes build/<stem>.elf for each kernel)
# clang and ld.lld come from PATH.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
CLANG=clang
LLD=ld.lld

# Pinned versions (see tools/versions.txt). Refuse to build with anything else.
EXPECT_CLANG=$(sed -n 's/^clang=//p' "$ROOT/tools/versions.txt")
EXPECT_LLD=$(sed -n 's/^lld=//p' "$ROOT/tools/versions.txt")
GOT_CLANG=$("$CLANG" --version | sed -n '1s/.*clang version \([0-9.]*\).*/\1/p')
GOT_LLD=$("$LLD" --version | sed -n 's/.*LLD \([0-9.]*\).*/\1/p')
if [ "$GOT_CLANG" != "$EXPECT_CLANG" ] || [ "$GOT_LLD" != "$EXPECT_LLD" ]; then
    echo "toolchain mismatch: clang $GOT_CLANG (want $EXPECT_CLANG), lld $GOT_LLD (want $EXPECT_LLD)" >&2
    exit 1
fi

LIB=${M0C_LIB:-$ROOT/..}
OUT="$ROOT/build"
mkdir -p "$OUT"

# One ELF per kernel (tools/kernels.txt). thumbv6m + cortex-m0plus: the assembler
# rejects instructions outside ARMv6-M.
grep -v '^#' "$ROOT/tools/kernels.txt" | while read -r stem symbol _module; do
    [ -n "$stem" ] || continue
    "$CLANG" --target=thumbv6m-none-eabi -mcpu=cortex-m0plus -mthumb \
        -ffile-prefix-map="$ROOT"=. -I "$LIB/src" \
        -c "$ROOT/fixtures/$stem.S" -o "$OUT/$stem.o"
    "$LLD" -T "$ROOT/link/proof-fixture.ld" -e "$symbol" --build-id=none -nostdlib \
        "$OUT/$stem.o" -o "$OUT/$stem.elf"
    echo "built $OUT/$stem.elf"
done
