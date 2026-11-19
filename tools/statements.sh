#!/bin/sh
# Print what assets/ASSET/statements.golden locks, for a git ref (default: the working tree):
# the full statement of every theorem in assets/ASSET/Audit.lean, then every trusted definition
# those statements reach (tools/trusted_defs.lean, printTrusted), each followed by the sha256 of
# its kernel terms (printFingerprint). Compared by tools/check.sh.
# Usage: tools/statements.sh ASSET [ref]     (ASSET: chacha20poly1305, blake2s, x25519 or ed25519)
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
    echo "import Lean"
    cat "$ROOT/tools/trusted_defs.lean"
    echo "set_option pp.fullNames true"
    echo "set_option pp.deepTerms true"
    echo "set_option pp.proofs true"
    for n in $(sed -n 's/^#print axioms \(.*\)$/\1/p' "$TMP/audit.lean"); do
        echo "#check @$n"
        echo "#eval printFingerprint \`$n (value := false)"
    done
    echo "#eval printTrusted $(claim_roots "$TMP/audit.lean")"
} > "$TMP/S.lean"
lake env lean "$TMP/S.lean" > "$TMP/S.out" || { cat "$TMP/S.out"; exit 1; }
python3 -I -c 'import hashlib, sys
for l in sys.stdin:
    if l.startswith("@@sha256 "):
        print("sha256", hashlib.sha256(l[9:].rstrip("\n").encode()).hexdigest())
    else:
        sys.stdout.write(l)' < "$TMP/S.out"
