# Shared by tools/statements.sh and tools/trusted_defs.sh (sourced, not run).
# An asset's claims are the `#print axioms` lines of its Audit.lean; the roots of its trusted
# definitions are those claims without the non-vacuity witnesses (`*_nonvacuous`).

# asset_root AUDIT: the asset root module imported by AUDIT.
asset_root() { sed -n 's/^import \(M0Crypto\.Assets\..*\)$/\1/p' "$1"; }

# claim_roots AUDIT: the roots as a Lean list literal, [`A, `B, ...].
claim_roots() {
    sed -n 's/^#print axioms \(M0Crypto[^ ]*\)$/`\1/p' "$1" | grep -v '_nonvacuous$' \
        | paste -s -d, - | sed 's/^/[/; s/$/]/'
}
