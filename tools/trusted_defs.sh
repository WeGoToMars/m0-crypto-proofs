#!/bin/sh
# List the trusted definitions of one release asset (tools/trusted_defs.lean). The roots are the
# claims in assets/ASSET/Audit.lean, without the non-vacuity witnesses.
# Usage: tools/trusted_defs.sh ASSET     (ASSET: chacha20poly1305, blake2s or x25519)
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
[ $# -eq 1 ] && [ -d "$ROOT/assets/$1" ] || { echo "usage: tools/trusted_defs.sh ASSET" >&2; exit 2; }
. "$ROOT/tools/claims.sh"
PATH="$HOME/.elan/bin:$PATH"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
{ echo "import $(asset_root "$ROOT/assets/$1/Audit.lean")"; cat "$ROOT/tools/trusted_defs.lean"
  echo "#eval report $(claim_roots "$ROOT/assets/$1/Audit.lean")"; } > "$TMP/T.lean"
cd "$ROOT/assets/$1"
lake env lean "$TMP/T.lean"
