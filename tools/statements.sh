#!/bin/sh
# Print the full statement of every theorem listed in lean/Audit.lean of a git ref
# (default: the working tree). Compared with tools/statements.golden by tools/check.sh.
# Usage: tools/statements.sh [ref]
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
PATH="$HOME/.elan/bin:$PATH"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
if [ $# -ge 1 ]; then git show "$1:lean/Audit.lean" > "$TMP/audit.lean"; else cp lean/Audit.lean "$TMP/audit.lean"; fi
{
    echo "import M0Crypto"
    echo "set_option pp.fullNames true"
    echo "set_option pp.deepTerms true"
    echo "set_option pp.proofs true"
    sed -n 's/^#print axioms \(.*\)$/#check @\1/p' "$TMP/audit.lean"
} > "$TMP/S.lean"
lake env lean "$TMP/S.lean"
