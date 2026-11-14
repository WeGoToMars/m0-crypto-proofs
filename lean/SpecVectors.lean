import M0Crypto.Spec.Aead

/-!
Evaluate the specification on external test vectors (`tools/spec_vectors.py`).

Each line of the input file is one vector, fields separated by spaces, bytes in hex (`-` for
none):

* `aead VALID KEY NONCE AAD PLAINTEXT CIPHERTEXT TAG`. A valid vector must encrypt to the
  ciphertext and tag and decrypt back to the plaintext; an invalid one must be rejected.
* `aead-tag KEY NONCE AAD PLAINTEXT TAG`: as a valid `aead` vector, with only the tag given.
* `poly KEY MESSAGE TAG`.
* `chacha KEY NONCE COUNTER INPUT OUTPUT`: the call is accepted (`counterOk`) and its output
  is `chacha20` from block COUNTER (decimal).
* `counter VALID COUNTER LENGTH`: whether `counterOk` accepts the call (decimal numbers).

This is a test of `M0Crypto.Spec.Aead` (compiled evaluation), not a proof.
-/

open M0Crypto.Spec.Aead
open M0Crypto.Spec.ChaCha20 (Byte)

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes (s : String) : Option (List Byte) := Id.run do
  if s = "-" then return some []
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then return none
  let mut out : Array Byte := #[]
  for i in [0:cs.size / 2] do
    match hexDigit cs[2 * i]!, hexDigit cs[2 * i + 1]! with
    | some x, some y => out := out.push (BitVec.ofNat 8 (16 * x + y))
    | _, _ => return none
  return some out.toList

/-- Whether the specification agrees with one vector; `none` if the line is malformed. -/
def checkLine (line : String) : Option Bool := do
  match line.splitOn " " with
  | ["aead", valid, key, nonce, aad, pt, ct, tag] =>
    let (key, nonce, aad) := (← hexBytes key, ← hexBytes nonce, ← hexBytes aad)
    let (pt, ct, tag) := (← hexBytes pt, ← hexBytes ct, ← hexBytes tag)
    if valid = "1" then
      some (encrypt key nonce aad pt == (ct, tag) && decrypt key nonce aad ct tag == some pt)
    else some (decrypt key nonce aad ct tag == none)
  | ["aead-tag", key, nonce, aad, pt, tag] =>
    let (key, nonce, aad, pt, tag) := (← hexBytes key, ← hexBytes nonce, ← hexBytes aad,
      ← hexBytes pt, ← hexBytes tag)
    let (ct, t) := encrypt key nonce aad pt
    some (t == tag && decrypt key nonce aad ct tag == some pt)
  | ["poly", key, msg, tag] => some (poly1305 (← hexBytes key) (← hexBytes msg) == (← hexBytes tag))
  | ["chacha", key, nonce, counter, input, output] =>
    let (key, nonce, input, output) := (← hexBytes key, ← hexBytes nonce, ← hexBytes input,
      ← hexBytes output)
    let counter ← counter.toNat?
    some (counterOk counter input.length && chacha20 key counter nonce input == output)
  | ["counter", valid, counter, len] =>
    some (counterOk (← counter.toNat?) (← len.toNat?) == (valid == "1"))
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
    IO.println s!"ok: the specification agrees with {n "aead 1"} valid and {n "aead 0"} invalid AEAD vectors, {n "aead-tag"} AEAD tags of long inputs, {n "poly"} Poly1305 vectors, {n "chacha"} ChaCha20 vectors and {n "counter"} counter-rule vectors"
    return 0
  IO.eprintln s!"spec vectors: {bad} of {lines.size} vectors failed"
  return 1
