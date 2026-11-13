import M0Crypto.Spec.X25519

/-!
Evaluate the X25519 specification on external test vectors (`tools/spec_vectors.py`, run in
the X25519 asset's workspace `assets/x25519`).

Each line of the input file is one vector, fields separated by spaces, bytes in hex:

* `x25519 SOURCE ID SCALAR POINT SHARED`: `x25519 SCALAR POINT` must equal `SHARED`.
  `SOURCE` and `ID` only label failures.

This is a test of `M0Crypto.Spec.X25519.x25519` (evaluated with the `output_eq_fast`
`csimp` lemma), not a proof.
-/

open M0Crypto.Spec.X25519

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Exactly 32 bytes of hex, or `none`. -/
def hex32 (s : String) : Option (List Byte) := do
  let bs ← go s.toList
  if bs.length = 32 then some bs else none
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
  | ["x25519", _source, _id, k, u, r] => some (x25519 (← hex32 k) (← hex32 u) == (← hex32 r))
  | _ => none

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: SpecVectorsX25519 FILE"; return 2
  let lines ← IO.FS.lines path
  let mut bad := 0
  for h : i in [0:lines.size] do
    match checkLine lines[i] with
    | some true => pure ()
    | some false => bad := bad + 1; IO.eprintln s!"vector {i + 1} {(lines[i].splitOn " ").take 3}: the specification disagrees"
    | none => bad := bad + 1; IO.eprintln s!"vector {i + 1}: malformed line"
  if bad = 0 ∧ lines.size > 0 then
    IO.println s!"ok: the X25519 specification agrees with {lines.size} vectors"
    return 0
  IO.eprintln s!"spec vectors: {bad} of {lines.size} vectors failed"
  return 1
