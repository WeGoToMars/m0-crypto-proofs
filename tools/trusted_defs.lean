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
`printTrusted` on the same roots to print every trusted definition into `statements.golden`, each
with a fingerprint of its kernel terms.
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
    | .opaqueInfo d => es := es.push d.value
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


/-! ## Term fingerprints

`printFingerprint` writes one declaration as kernel terms, which `tools/statements.sh` replaces by
their sha256: the text above it can print two different terms alike (a coercion, an implicit
argument, a numeral's type, a universe level), the fingerprint cannot. Each expression node is one
line naming its children by line number, so a shared subterm is written once; names, universe
levels and literals are written in full, binder info is kept. Binder names and metadata are left
out: the kernel ignores them, and the text shows the binder names. -/

/-- An expression compared with `Expr.equal`, which also compares binder info and names. -/
structure FpKey where
  e : Expr
instance : BEq FpKey := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable FpKey := ⟨fun a => hash a.e⟩

structure FpState where
  lines : Array String := #[]
  ids : Std.HashMap String Nat := {}
  memo : Std.HashMap FpKey Nat := {}
  /-- Helpers to write after the declaration, in order of first use. -/
  todo : Array Name := #[]
  seen : NameSet := {}

abbrev FpM := StateT FpState MetaM

def fpName : Name → String
  | .anonymous => "_"
  | .str p s => fpName p ++ "." ++ s.quote
  | .num p i => fpName p ++ "." ++ toString i

def fpLevel : Level → String
  | .zero => "0"
  | .succ l => s!"S({fpLevel l})"
  | .max a b => s!"M({fpLevel a},{fpLevel b})"
  | .imax a b => s!"I({fpLevel a},{fpLevel b})"
  | .param n => s!"P{fpName n}"
  | .mvar _ => "?"

def fpLine (l : String) : FpM Nat := do
  if let some i := (← get).ids[l]? then return i
  let i := (← get).lines.size
  modify fun s => { s with lines := s.lines.push l, ids := s.ids.insert l i }
  return i

/-- The generated artifact modules, which `printTrusted` does not print: their bytes, offsets
and sizes are compared with the library object by `extract_release.py --check`. -/
def artifactModules : List Name :=
  [`M0Crypto.Artifacts.Release, `M0Crypto.Artifacts.Ed25519Compact, `M0Crypto.Artifacts.Ed25519Fast]

/-- A compiler-generated helper (matcher, recursion helper, auxiliary recursor, projection,
constructor index). A `private` declaration's name starts with `_private`, which
`isInternalDetail` alone counts as generated, so the test reads the name without that prefix. -/
def generated (env : Environment) (n : Name) : Bool :=
  (privateToUserName n).isInternalDetail || isAuxRecursor env n || isNoConfusion env n
    || env.isProjectionFn n || n.getString! == "ctorIdx"

/-- The generated helpers that `printTrusted` does not print on their own (matchers, recursion
helpers, auxiliary recursors, projections) of the modules it prints. They are written into the
fingerprint of each declaration that uses them. -/
def fpHelper (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some mi =>
    let m := env.header.moduleNames[mi.toNat]!
    (`M0Crypto).isPrefixOf m && !artifactModules.contains m && generated env n

partial def fpExpr (e : Expr) : FpM Nat := do
  if let some i := (← get).memo[FpKey.mk e]? then return i
  let bi : BinderInfo → String
    | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"
  let i ← match e with
    | .mdata _ b => fpExpr b
    | .bvar k => fpLine s!"b {k}"
    | .sort l => fpLine s!"s {fpLevel l}"
    | .const n us => do
      if fpHelper (← getEnv) n && !(← get).seen.contains n then
        modify fun s => { s with todo := s.todo.push n, seen := s.seen.insert n }
      fpLine s!"c {fpName n} {us.map fpLevel}"
    | .app f a => do let f ← fpExpr f; let a ← fpExpr a; fpLine s!"a {f} {a}"
    | .lam _ t b k => do let t ← fpExpr t; let b ← fpExpr b; fpLine s!"l {bi k} {t} {b}"
    | .forallE _ t b k => do let t ← fpExpr t; let b ← fpExpr b; fpLine s!"p {bi k} {t} {b}"
    | .letE _ t v b _ => do
      let t ← fpExpr t; let v ← fpExpr v; let b ← fpExpr b; fpLine s!"z {t} {v} {b}"
    | .lit (.natVal k) => fpLine s!"n {k}"
    | .lit (.strVal s) => fpLine s!"t {s.quote}"
    | .proj s k b => do let b ← fpExpr b; fpLine s!"j {fpName s} {k} {b}"
    | .fvar _ | .mvar _ => throwError "fingerprint: open term"
  modify fun s => { s with memo := s.memo.insert ⟨e⟩ i }
  return i

def fpSafety : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

/-- One constant: name, universe parameters and type; for a definition or opaque also its value
(when `value`), for an inductive type its parameters, indices and constructors. -/
def fpConst (n : Name) (value : Bool) : FpM Unit := do
  let ci ← getConstInfo n
  let head := s!"{fpName n} {ci.levelParams.map fpName} {← fpExpr ci.type}"
  match ci, value with
  | .defnInfo d, true => discard <| fpLine s!"D {head} {← fpExpr d.value} {fpSafety d.safety}"
  | .opaqueInfo d, true => discard <| fpLine s!"O {head} {← fpExpr d.value} {d.isUnsafe}"
  | .inductInfo i, _ =>
    let cs ← i.ctors.mapM fun c => do return s!"{fpName c}:{← fpExpr (← getConstInfo c).type}"
    discard <| fpLine s!"I {head} {i.numParams} {i.numIndices} {i.all.map fpName} {cs}"
  | _, _ => discard <| fpLine s!"T {head}"

/-- Print the fingerprint input of `n` (with its value when `value`) and of every helper it
reaches, as one line `@@sha256 …` that `tools/statements.sh` replaces by `sha256 <hex>`. -/
def printFingerprint (n : Name) (value : Bool := true) : MetaM Unit := do
  let go : FpM Unit := do
    modify fun s => { s with seen := s.seen.insert n }
    fpConst n value
    let mut k := 0
    while k < (← get).todo.size do
      fpConst (← get).todo[k]! true
      k := k + 1
  let ((), s) ← go.run {}
  IO.println s!"@@sha256 {"\t".intercalate s.lines.toList}"


/-- The trusted declarations printed into `statements.golden`: every definition, opaque and
inductive type of `M0Crypto` reached from the statements of `roots`, except the artifact module
(its bytes are pinned by `tools/extract_release.py --check`) and compiler-generated helpers
(matchers, recursion and constructor-index helpers, projections; they are part of what they
belong to). A recursive definition is printed with its compiled value and then its unfolding
theorem `f.eq_def`, the only place its body appears (the compiled value names the helper
`f._f` or `f._unary` instead). `getUnfoldEqnFor? (nonRec := false)` returns none for a
non-recursive definition, whose value already is its body. Each declaration is followed by its
fingerprint (`printFingerprint`). Ordered by module and source line. -/
def printTrusted (roots : List Name) : MetaM Unit := do
  let env ← getEnv
  if roots.isEmpty then throwError "no roots: unknown asset"
  for r in roots do
    if (env.find? r).isNone then throwError s!"missing root {r}"
  let mut out : Array (String × Nat × Name) := #[]
  for n in (closure env roots).toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    if !(`M0Crypto).isPrefixOf m || artifactModules.contains m then continue
    if generated env n then continue
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
      printFingerprint n
    | .opaqueInfo d =>
      IO.println s!"opaque {n} : {ty} :=\n  {← ppExpr d.value}"
      printFingerprint n
    | .axiomInfo _ =>
      IO.println s!"axiom {n} : {ty}"
      printFingerprint n
    | .inductInfo i =>
      IO.println s!"inductive {n} : {ty}"
      for c in i.ctors do
        let some cc := env.find? c | continue
        IO.println s!"  | {c} : {← ppExpr cc.type}"
      printFingerprint n
    | _ => pure ()
