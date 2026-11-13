import M0Crypto.Spec.Blake2s

/-!
Evaluate the BLAKE2s specification on external test vectors (`tools/spec_vectors.py`, run in
the BLAKE2s asset's workspace `assets/blake2s`).

Each line of the input file is one vector, fields separated by spaces, bytes in hex (`-` for
the empty message):

* `blake2s MESSAGE DIGEST`: both the one-shot `blake2s MESSAGE` and the streaming state that
  the claims use (`finish (absorb State.init MESSAGE)`) must equal `DIGEST`.

This is a test of `M0Crypto.Spec.Blake2s` (compiled evaluation), not a proof.
-/

open M0Crypto.Spec.Blake2s

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes (s : String) : Option (List Byte) :=
  if s = "-" then some [] else go s.toList
where
  go : List Char → Option (List Byte)
    | [] => some []
    | a :: b :: rest => do
      let x ← hexDigit a
      let y ← hexDigit b
      (BitVec.ofNat 8 (16 * x + y) :: ·) <$> go rest
    | _ => none

/-- Whether the specification agrees with one vector; `none` if the line is malformed. -/
def checkLine (line : String) : Option Bool := do
  match line.splitOn " " with
  | ["blake2s", msg, digest] =>
    let (msg, digest) := (← hexBytes msg, ← hexBytes digest)
    some (blake2s msg == digest && finish (absorb State.init msg) == digest)
  | _ => none

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: SpecVectorsBlake2s FILE"; return 2
  let lines ← IO.FS.lines path
  let mut bad := 0
  for h : i in [0:lines.size] do
    match checkLine lines[i] with
    | some true => pure ()
    | some false => bad := bad + 1; IO.eprintln s!"vector {i + 1}: the specification disagrees"
    | none => bad := bad + 1; IO.eprintln s!"vector {i + 1}: malformed line"
  if bad = 0 ∧ lines.size > 0 then
    IO.println s!"ok: the BLAKE2s specification (one-shot and streaming) agrees with {lines.size} vectors"
    return 0
  IO.eprintln s!"spec vectors: {bad} of {lines.size} vectors failed"
  return 1
