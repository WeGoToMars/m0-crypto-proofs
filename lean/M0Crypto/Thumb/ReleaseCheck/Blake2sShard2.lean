import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck

private def check (r : Option String) : IO Unit :=
  match r with | some e => throw (IO.userError e) | none => pure ()

/-- `len` cut into pieces of `k` bytes (the last one shorter). -/
private def cut (len k : Nat) : List Nat :=
  (List.range ((len + k - 1) / k)).map fun i => min k (len - i * k)

-- C1: lengths 1024 and 1025, every partition, all offsets
#eval do
  for len in [1024, 1025] do
    for off in [0, 1, 2, 3] do
      check (b2sStreamCase len off ((off + 2) % 4) [len] (len + off))
    for k in [1, 17, 64] do
      check (b2sStreamCase len 3 1 (cut len k) (len + k))

-- the partition boundary cases of the buffering logic
#eval do
  for (a, b) in [(63, 1), (64, 64), (1, 64), (65, 63), (0, 64), (64, 0), (127, 1), (1, 127), (128, 1)] do
    check (b2sStreamCase (a + b) 1 1 [a, b] (a * 7 + b))

end M0Crypto.Thumb.ReleaseCheck
