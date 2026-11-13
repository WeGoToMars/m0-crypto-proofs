#!/bin/sh
# Print what assets/ASSET/statements.golden locks, for a git ref (default: the working tree):
# the full statement of every theorem in assets/ASSET/Audit.lean, then every trusted definition
# those statements reach (tools/trusted_defs.lean, printTrusted). Compared by tools/check.sh.
# Usage: tools/statements.sh ASSET [ref]     (ASSET: chacha20poly1305, blake2s or x25519)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
[ $# -ge 1 ] && [ -d "$ROOT/assets/$1" ] || { echo "usage: tools/statements.sh ASSET [ref]" >&2; exit 2; }
A=$1
. "$ROOT/tools/claims.sh"
cd "$ROOT/assets/$A"
PATH="$HOME/.elan/bin:$PATH"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
if [ $# -ge 2 ]; then git show "$2:./Audit.lean" > "$TMP/audit.lean"; else cp Audit.lean "$TMP/audit.lean"; fi
{
    echo "import $(asset_root "$TMP/audit.lean")"
    cat "$ROOT/tools/trusted_defs.lean"
    echo "set_option pp.fullNames true"
    echo "set_option pp.deepTerms true"
    echo "set_option pp.proofs true"
    sed -n 's/^#print axioms \(.*\)$/#check @\1/p' "$TMP/audit.lean"
    echo "#eval printTrusted $(claim_roots "$TMP/audit.lean")"
} > "$TMP/S.lean"
lake env lean "$TMP/S.lean"
