# Shared by tools/check_bytes.sh and tools/check_proofs.sh (sourced, not run): the asset
# arguments, the library location and the helpers both scripts use. Leaves the shell in the
# proofs root.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
# The library sources live in the parent repository (this directory is its `proofs`
# submodule); override with M0C_LIB=/path/to/m0-crypto.
LIB=${M0C_LIB:-$ROOT/..}
export M0C_LIB="$LIB"
[ -f "$LIB/src/m0crypto_chacha20poly1305.S" ] || { echo "library sources not found at $LIB (set M0C_LIB)" >&2; exit 1; }
ALL_ASSETS="chacha20poly1305 blake2s x25519 ed25519"
ASSETS=${*:-$ALL_ASSETS}
for a in $ASSETS; do
    case " $ALL_ASSETS " in *" $a "*) ;; *) echo "usage: $0 [$ALL_ASSETS]" >&2; exit 2 ;; esac
done
has() { case " $ASSETS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
PATH="$HOME/.elan/bin:$PATH"
# An asset's builds as OBJECT:ARTIFACT_MODULE:BUILD (BUILD empty for a single-build asset).
units() {
    case $1 in
        ed25519) for b in compact fast; do
            B=$(echo "$b" | sed 's/^c/C/; s/^f/F/')
            echo "$LIB/build/lib/ed25519/$b/m0crypto_ed25519_$b.o:Ed25519$B:$b"
        done ;;
        *) echo "$LIB/build/lib/$1/m0crypto_$1.o:Release:" ;;
    esac
}
mkdir -p build
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
