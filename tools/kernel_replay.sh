#!/bin/sh
# Kernel replay, run on request and not by check.sh: adds every constant an asset root
# reaches, Lean core included, to an empty kernel environment with the pinned toolchain's
# leanchecker. A declaration that entered the build without a kernel check fails here.
# One asset at a time: 2 to 5 minutes and up to about 6 GB each. Keep --fresh: without it
# leanchecker replays every module in parallel and needs several times that memory.
#
# Usage: tools/kernel_replay.sh [ASSET...]     (default: chacha20poly1305 blake2s x25519)
set -eu
cd "$(dirname "$0")/.."
PATH="$HOME/.elan/bin:$PATH"
for a in ${*:-chacha20poly1305 blake2s x25519}; do
    mod=$(sed -n 's/^import //p' "assets/$a/Audit.lean")
    (cd "assets/$a" && lake build && lake env leanchecker --fresh "$mod")
    echo "kernel replay $mod: OK"
done
