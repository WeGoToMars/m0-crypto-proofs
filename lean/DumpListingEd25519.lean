import M0Crypto.Thumb.Listing
import M0Crypto.Artifacts.Ed25519Compact
import M0Crypto.Artifacts.Ed25519Fast

/-! Print the model's decoding of one Ed25519 build, `compact` or `fast`
(`tools/check_listing.py … ed25519 BUILD`). -/

open M0Crypto.Artifacts M0Crypto.Thumb.Listing in
def main : List String → IO Unit
  | ["compact"] => IO.print (listingOf Ed25519Compact.bytes Ed25519Compact.codeRanges)
  | ["fast"] => IO.print (listingOf Ed25519Fast.bytes Ed25519Fast.codeRanges)
  | _ => IO.print "error: expected the build, compact or fast\n"
