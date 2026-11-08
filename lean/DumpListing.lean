import M0Crypto.Thumb.Listing

/-! Print the model's decoding of the release artifact (`tools/check_listing.py`). -/

def main : IO Unit := IO.print M0Crypto.Thumb.Listing.listing
