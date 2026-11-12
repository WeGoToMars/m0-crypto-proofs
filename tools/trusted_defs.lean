/-
Lists every definition that the statements of the headline theorems depend on: the
trusted part of the proofs, which must be reviewed by a person (see docs/REVIEW.md).

It starts from each root theorem's *statement* (its type), follows the bodies of
definitions, structures and constructors transitively, and never enters a theorem's
proof. Proofs are checked by the Lean kernel and need no review.

Run from the proofs root, after `lake build`:
  lake env lean tools/trusted_defs.lean
Output: one line per declaration, `module<TAB>first line<TAB>last line<TAB>kind<TAB>name`,
then one `FILE` line per module with its number of declarations and source lines.
docs/REVIEW.md section 3 names the files a reviewer reads; the `FILE` lines must name the same
files. Update `roots` when a headline theorem is added or renamed (it fails if a root is
missing).
-/
import M0Crypto.Release.ChaCha20Xor
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.ChaCha20XorConstantTime
import M0Crypto.Release.ChaCha20XorReads
import M0Crypto.Release.ChaCha20XorStack
import M0Crypto.Release.AeadEncryptConstantTime
import M0Crypto.Release.AeadDecryptConstantTime
import M0Crypto.Release.AeadEncryptStack
import M0Crypto.Release.AeadDecryptStack
import M0Crypto.Release.AeadReads
open Lean Meta

def roots : List Name :=
  [`M0Crypto.Release.ChaCha20Xor.xor_correct, `M0Crypto.Release.Aead.encrypt_correct,
   `M0Crypto.Release.Aead.decrypt_correct,
   `M0Crypto.Release.ChaCha20Xor.xor_constant_time, `M0Crypto.Release.ChaCha20Xor.xor_reads,
   `M0Crypto.Release.ChaCha20Xor.xor_stack, `M0Crypto.Release.Aead.encrypt_constant_time,
   `M0Crypto.Release.Aead.encrypt_reads, `M0Crypto.Release.Aead.encrypt_stack,
   `M0Crypto.Release.Aead.decrypt_constant_time, `M0Crypto.Release.Aead.decrypt_reads,
   `M0Crypto.Release.Aead.decrypt_stack]

/-- Constants reachable from `start` through types, and through the bodies of everything
except theorems. -/
partial def closure (env : Environment) (start : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := start
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut es : Array Expr := #[ci.type]
    match ci with
    | .defnInfo d => es := es.push d.value
    | .inductInfo i => todo := i.ctors ++ todo
    | .ctorInfo c => todo := c.induct :: todo
    | _ => pure ()
    for e in es do
      for c in e.getUsedConstants do
        if !seen.contains c then todo := c :: todo
  return seen

def report : MetaM Unit := do
  let env ← getEnv
  for r in roots do
    if (env.find? r).isNone then throwError s!"missing root {r}"
  let mut out : Array (String × Nat × Nat × String × String) := #[]
  for n in (closure env roots).toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    if !(`M0Crypto).isPrefixOf m then continue
    let some ci := env.find? n | continue
    -- Theorems are reached only through their statements. Constructors, fields and
    -- recursors lie inside the range of their type, which is listed.
    let kind := match ci with
      | .defnInfo _ => "def" | .inductInfo _ => "type" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | _ => ""
    if kind == "" then continue
    let some r ← findDeclarationRanges? n | continue
    out := out.push (m.toString, r.range.pos.line, r.range.endPos.line, kind, n.toString)
  -- Order by module and first line; on a tie the longer range first, a type before its
  -- generated helpers.
  let sorted := out.qsort fun (m, a, b, k, _) (m', a', b', k', _) =>
    if m != m' then m < m' else if a != a' then a < a' else if b != b' then b > b'
    else k == "type" && k' != "type"
  -- Drop declarations inside the range of a listed one (structure fields, `where` helpers,
  -- generated eliminators).
  let mut top : Array (String × Nat × Nat × String × String) := #[]
  for d in sorted do
    let (m, a, b, _, _) := d
    if top.any fun (m', a', b', _, _) => m' == m && a' ≤ a && b ≤ b' then continue
    top := top.push d
  for (m, a, b, k, n) in top do IO.println s!"{m}\t{a}\t{b}\t{k}\t{n}"
  let mods := (top.map (·.1)).toList.eraseDups
  for m in mods do
    let ds := top.filter (·.1 == m)
    let lines := ds.foldl (fun acc (_, a, b, _, _) => acc + (b - a + 1)) 0
    IO.println s!"FILE\t{m}\t{ds.size} declarations\t{lines} lines"

#eval report
