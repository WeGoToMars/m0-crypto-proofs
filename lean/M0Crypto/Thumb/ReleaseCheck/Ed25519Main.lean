import M0Crypto.Thumb.ReleaseCheck.Ed25519Entries
import M0Crypto.Thumb.ReleaseCheck.Ed25519Routines

/-! `main` of the Ed25519 asset's native release-check executable (`lake exe release_check
[WORKERS [FILTER]]`, run by `tools/check.sh`): every entry and routine case on both builds, in
`WORKERS` threads (default 2), only the cases whose name contains `FILTER` if given. Exit status
1 if any case fails, if a build schedules fewer cases of a family than `required` or if no case
matches `FILTER`. -/

open M0Crypto.Thumb.ReleaseCheck.Ed25519
open M0Crypto.Release.Ed25519 (Build)

def bname : Build → String
  | .compact => "compact"
  | .fast => "fast"

/-- The cases each build must schedule, by family (the word after the build in a case name). -/
def required (b : Build) : List (String × Nat) :=
  [("non-vacuity", 1), ("pubkey", 9), ("sign", 11), ("verify", 22)] ++
  ["fe_add", "fe_sub", "fe_mul", "fe_sqr"].map (·, 356) ++
  [("fe_canon", 134), ("fe_eq", 256), ("fe_pow", 40), ("cmov", 60), ("copy", 60), ("zero", 30),
   ("sha512_block", 42), ("sha512", 18), ("mp_mul", 290), ("sc_reduce", 234), ("sc_muladd", 222),
   ("ge_compress", 13), ("ge_decompress", 24), ("sc_recode_comb", 69), ("sbit", 1792),
   ("sc_wnaf", 95), ("ge_lookup", 17 * (b.combs + 1)), ("ge_mul_base", 11), ("ge_dsm", 6)]

def main (args : List String) : IO UInt32 := do
  let workers := ((args.head? >>= String.toNat?).getD 2).max 1
  let filter := args.getD 1 ""
  let all := [Build.compact, .fast].flatMap fun b =>
    let g : Cases := [(s!"{bname b} non-vacuity", fun _ => guards b <|> routineGuards b)]
    let e : Cases := entryCases.map fun c => (s!"{bname b} {c.name}", fun _ => c.check b)
    g ++ e ++ (routineCases b).map fun (n, c) => (s!"{bname b} {n}", c)
  let fams := all.map fun (n, _) => (n.splitOn " ").take 2
  let counts := [Build.compact, .fast].map fun b => (b, (required b).map fun (f, k) =>
    (f, k, (fams.filter (· == [bname b, f])).length))
  let short := counts.flatMap fun (b, cs) => cs.filterMap fun (f, k, n) =>
    if n < k then some s!"{bname b} {f}: {n} cases scheduled, {k} required" else none
  if !short.isEmpty then
    for e in short do IO.eprintln s!"release check manifest FAILED: {e}"
    return 1
  let cases := all.filter fun (n, _) => (n.splitOn filter).length > 1 || filter.isEmpty
  if cases.isEmpty then
    IO.eprintln s!"release check FAILED: no case matches {filter}"
    return 1
  let rc ← runCases workers cases
  if rc == 0 then
    IO.println s!"release check ed25519: {cases.length} cases pass ({entryCases.length} entry cases and \
      {(routineCases .compact).length} + {(routineCases .fast).length} routine cases per build)"
    for (b, cs) in counts do
      IO.println s!"  {bname b}: {", ".intercalate (cs.map fun (f, _, n) => s!"{f} {n}")}"
  return rc
