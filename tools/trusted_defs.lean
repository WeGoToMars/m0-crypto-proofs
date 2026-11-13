/-
Lists every definition that the statements of the top-level theorems depend on: the
trusted part of the proofs, which must be reviewed by a person (see docs/REVIEW.md).

It starts from each root theorem's *statement* (its type), follows the bodies of
definitions, structures and constructors transitively, and never enters a theorem's
proof. Proofs are checked by the Lean kernel and need no review.

Run for one release asset, after its `lake build` (in assets/ASSET):
  tools/trusted_defs.sh ASSET
which imports the asset root `M0Crypto.Assets.*` and evaluates `report` on the asset's claims:
every theorem in `assets/ASSET/Audit.lean` except the non-vacuity witnesses (`*_nonvacuous`),
whose witness values are checked by the kernel, not trusted. `tools/statements.sh` evaluates
`printTrusted` on the same roots to print every trusted definition into `statements.golden`.
A definition by structural or well-founded recursion is compiled to a term that only names its
generated helpers (`Nat.brecOn … f._f`, `WellFounded.fix … f._unary`), which are not printed.
For such a definition `printTrusted` also prints its unfolding theorem `f.eq_def`
(`Lean.Meta.getUnfoldEqnFor?`), which Lean derives from the compiled definition and which states
the body as written, recursive calls included. So the golden file changes whenever that body
changes, as it does for a non-recursive definition.
Output: one line per declaration, `module<TAB>first line<TAB>last line<TAB>kind<TAB>name`,
then one `FILE` line per module with its number of declarations and source lines.
docs/REVIEW.md section 3 names the files a reviewer reads; the `FILE` lines must name the same
files. The roots come from `Audit.lean`, so there is no second list to update.
-/
open Lean Meta

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

def report (roots : List Name) : MetaM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "no roots: unknown asset"
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


/-- The trusted declarations printed into `statements.golden`: every definition, opaque and
inductive type of `M0Crypto` reached from the statements of `roots`, except the artifact module
(its bytes are pinned by `tools/extract_release.py --check`) and compiler-generated helpers
(matchers, recursion and constructor-index helpers, projections; they are part of what they
belong to). A recursive definition is printed with its compiled value and then its unfolding
theorem `f.eq_def`, the only place its body appears (the compiled value names the helper
`f._f` or `f._unary` instead). `getUnfoldEqnFor? (nonRec := false)` returns none for a
non-recursive definition, whose value already is its body.
Ordered by module and source line. -/
def printTrusted (roots : List Name) : MetaM Unit := do
  let env ← getEnv
  for r in roots do
    if (env.find? r).isNone then throwError s!"missing root {r}"
  let mut out : Array (String × Nat × Name) := #[]
  for n in (closure env roots).toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    if !(`M0Crypto).isPrefixOf m || m == `M0Crypto.Artifacts.Release then continue
    if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || env.isProjectionFn n
        || n.getString! == "ctorIdx" then continue
    let some ci := env.find? n | continue
    match ci with
    | .defnInfo _ | .inductInfo _ | .opaqueInfo _ | .axiomInfo _ => pure ()
    | _ => continue
    let line := ((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0
    out := out.push (m.toString, line, n)
  let sorted := out.qsort fun (m, a, n) (m', a', n') =>
    if m != m' then m < m' else if a != a' then a < a' else n.toString < n'.toString
  for (_, _, n) in sorted do
    let some ci := env.find? n | continue
    let ty ← ppExpr ci.type
    match ci with
    | .defnInfo d =>
      IO.println s!"def {n} : {ty} :=\n  {← ppExpr d.value}"
      if let some eq ← getUnfoldEqnFor? n (nonRec := false) then
        IO.println s!"unfold {eq} : {← ppExpr (← getConstInfo eq).type}"
      -- Fail closed: a value that goes through a generated helper definition of its own other
      -- than a matcher (`n._f`, `n._unary`, ...) is recursive and must have had an unfolding
      -- theorem above.
      else if d.value.getUsedConstants.any fun c => c != n && n.isPrefixOf c && c.isInternalDetail
          && !isMatcherCore env c && (env.find? c matches some (.defnInfo _)) then
        throwError s!"{n} is compiled through a helper but has no unfolding theorem"
    | .opaqueInfo d => IO.println s!"opaque {n} : {ty} :=\n  {← ppExpr d.value}"
    | .axiomInfo _ => IO.println s!"axiom {n} : {ty}"
    | .inductInfo i =>
      IO.println s!"inductive {n} : {ty}"
      for c in i.ctors do
        let some cc := env.find? c | continue
        IO.println s!"  | {c} : {← ppExpr cc.type}"
    | _ => pure ()
