import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck

private def check (r : Option String) : IO Unit :=
  match r with | some e => throw (IO.userError e) | none => pure ()

/-- `len` cut into pieces of `k` bytes (the last one shorter). -/
private def cut (len k : Nat) : List Nat :=
  (List.range ((len + k - 1) / k)).map fun i => min k (len - i * k)

-- C1: length 4096, one-shot, 17-byte and 64-byte pieces
#eval do
  check (b2sStreamCase 4096 0 0 [4096] 4096)
  check (b2sStreamCase 4096 1 3 (cut 4096 17) 4097)
  check (b2sStreamCase 4096 2 2 (cut 4096 64) 4098)

end M0Crypto.Thumb.ReleaseCheck
