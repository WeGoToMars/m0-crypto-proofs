import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

namespace M0Crypto.Thumb.ReleaseCheck

private def check (r : Option String) : IO Unit :=
  match r with | some e => throw (IO.userError e) | none => pure ()

/-- `len` cut into pieces of `k` bytes (the last one shorter). -/
private def cut (len k : Nat) : List Nat :=
  (List.range ((len + k - 1) / k)).map fun i => min k (len - i * k)

-- hash: lengths 71-200, one-shot and partitions 1, 17, 64
#eval do
  for len in List.range' 71 130 do
    for off in [0, 3] do
      check (b2sStreamCase len off (3 - off) [len] (len + off))
    check (b2sStreamCase len 1 2 (cut len 17) len)
    check (b2sStreamCase len 2 1 (cut len 64) len)

end M0Crypto.Thumb.ReleaseCheck
