import M0Crypto.Spec.Aead

/-!
Evaluate the specification on external test vectors (`tools/spec_vectors.py`).

Each line of the input file is one vector, fields separated by spaces, bytes in hex (`-` for
none):

* `aead VALID KEY NONCE AAD PLAINTEXT CIPHERTEXT TAG`. A valid vector must encrypt to the
  ciphertext and tag and decrypt back to the plaintext; an invalid one must be rejected.
* `poly KEY MESSAGE TAG`.

This is a test of `M0Crypto.Spec.Aead` (compiled evaluation), not a proof.
-/

open M0Crypto.Spec.Aead
open M0Crypto.Spec.ChaCha20 (Byte)

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
  | ["aead", valid, key, nonce, aad, pt, ct, tag] =>
    let (key, nonce, aad) := (← hexBytes key, ← hexBytes nonce, ← hexBytes aad)
    let (pt, ct, tag) := (← hexBytes pt, ← hexBytes ct, ← hexBytes tag)
    if valid = "1" then
      some (encrypt key nonce aad pt == (ct, tag) && decrypt key nonce aad ct tag == some pt)
    else some (decrypt key nonce aad ct tag == none)
  | ["poly", key, msg, tag] => some (poly1305 (← hexBytes key) (← hexBytes msg) == (← hexBytes tag))
  | _ => none

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: SpecVectors FILE"; return 2
  let lines ← IO.FS.lines path
  let mut bad := 0
  for h : i in [0:lines.size] do
    match checkLine lines[i] with
    | some true => pure ()
    | some false => bad := bad + 1; IO.eprintln s!"vector {i + 1}: the specification disagrees"
    | none => bad := bad + 1; IO.eprintln s!"vector {i + 1}: malformed line"
  if bad = 0 ∧ lines.size > 0 then
    let n (k : String) := (lines.filter (·.startsWith k)).size
    IO.println s!"ok: the specification agrees with {n "aead 1"} valid and {n "aead 0"} invalid AEAD vectors and {n "poly"} Poly1305 vectors"
    return 0
  IO.eprintln s!"spec vectors: {bad} of {lines.size} vectors failed"
  return 1
