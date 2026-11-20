#!/bin/sh
# Full check of the release assets: tools/check_bytes.sh (steps 1-3, 7 and 8: pinned build,
# byte/artifact correspondence, ISA rejection, QEMU tests, without Lean), then
# tools/check_proofs.sh (steps 4-6b and 7b: Lean proofs and release-artifact model checks, model
# decoder vs llvm-objdump, specification vs external vectors, axiom audit, statements, model vs
# QEMU instruction by instruction), on the same assets. Exits non-zero on any failure.
#
# Usage: tools/check.sh [ASSET...]     (default: all; ASSET: chacha20poly1305 blake2s x25519 ed25519)
# Each asset is checked on its own: its object, its Lake workspace assets/ASSET (which
# compiles the shared sources in lean/ against that asset's artifact), its audit and its
# statements. Steps for one asset only run when that asset is selected. The asset ed25519 has two
# builds, compact and fast, each with its own object and artifact module.
set -eu
D=$(dirname "$0")
"$D/check_bytes.sh" "$@"
"$D/check_proofs.sh" "$@"
echo "OK"
