#!/bin/sh
# Judge each asset root against its challenge with the pinned toolchain's `lake comparator`, run by
# the library's CI on every push and not by check.sh. assets/ASSET/challenge/Challenge.lean states every claim of
# assets/ASSET/Audit.lean except the non-vacuity witnesses, under the same name, over the statement
# files only, with `sorry`. `lake comparator` builds and exports the challenge and the asset root and
# accepts only if each claim of the asset root states the same term as the challenge, every
# declaration those statements reach is the same declaration in both, the proofs use no axiom but
# propext, Quot.sound and Classical.choice, and Lean's kernel accepts the export of the claims and
# everything they use, Lean core included, in an empty environment. `lake check` then does the same
# kernel replay for every declaration the asset root reaches, the witnesses included. Both run in a
# bwrap sandbox where bwrap is available (Linux), and otherwise with --inadvisably-no-sandbox.
# The sandbox hides /home, /root and /tmp, and the asset workspaces read ../../lean, so under
# bwrap the proofs tree has to lie outside those directories.
# One asset at a time: 5 to 11 minutes and up to about 5 GB each.
#
# Usage: tools/comparator.sh [ASSET...]     (default: chacha20poly1305 blake2s x25519)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
. "$ROOT/tools/claims.sh"
PATH="$HOME/.elan/bin:$PATH"
SANDBOX=--inadvisably-no-sandbox
command -v "${COMPARATOR_BWRAP:-bwrap}" > /dev/null 2>&1 && SANDBOX=
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
for a in ${*:-chacha20poly1305 blake2s x25519}; do
    audit="$ROOT/assets/$a/Audit.lean"
    quote() { sed 's/.*/"&"/' | paste -s -d, -; }
    printf '{"challenge_module": "Challenge", "solution_module": "%s",\n "theorem_names": [%s],\n "permitted_axioms": [%s]}\n' \
        "$(asset_root "$audit")" "$(claim_names "$audit" | quote)" \
        "$(echo $permitted_axioms | tr ' ' '\n' | quote)" > "$TMP/$a.json"
    (cd "$ROOT/assets/$a" && lake comparator --config="$TMP/$a.json" $SANDBOX && lake check $SANDBOX)
    echo "comparator $a: OK"
done
