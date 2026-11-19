# Shared by tools/statements.sh, tools/trusted_defs.sh and tools/comparator.sh (sourced, not run).
# An asset's claims are the `#print axioms` lines of its Audit.lean; the roots of its trusted
# definitions are those claims without the non-vacuity witnesses (`*_nonvacuous`).

# asset_root AUDIT: the asset root module imported by AUDIT.
asset_root() { sed -n 's/^import \(M0Crypto\.Assets\..*\)$/\1/p' "$1"; }

# claim_names AUDIT: the roots, one per line.
claim_names() { sed -n 's/^#print axioms \(M0Crypto[^ ]*\)$/\1/p' "$1" | grep -v '_nonvacuous$'; }

# claim_roots AUDIT: the roots as a Lean list literal, [`A, `B, ...] ([] for an asset without claims).
claim_roots() { echo "[$(claim_names "$1" | sed 's/^/`/' | paste -s -d, -)]"; }

# The axioms a claim may depend on (check.sh step 6 allows the same three).
permitted_axioms="propext Quot.sound Classical.choice"
