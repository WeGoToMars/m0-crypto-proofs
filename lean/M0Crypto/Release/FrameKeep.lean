import M0Crypto.Release.Footprint

/-!
# Carrying memory facts across frames

A chain of rules leaves frame facts `MemEq f m m'`: the memory `m'` equals `m` outside the
footprint `f`. A fact about `m` (a slot loaded before the calls, a table word) is then rewritten
by hand across each frame whose footprint misses it. `keep_simp` does it at once: it rewrites
every read of a later memory to the earlier one, through every frame fact in the context, as long
as `fp_tac` shows the read bytes apart from that frame's footprint.

`keep_simp [e₁, …] with [r₁, …] at l`:
* the frame facts are the hypotheses `MemEq f m m'` (with `m'` not `m`) and the terms `eᵢ`;
  `keep_simp only [e₁, …]` takes the terms `eᵢ` alone;
* the reads are `read32` and `bytesAt` (`MemEq.read32`, `MemEq.bytes`) and the readers `rᵢ`, each
  a lemma `MemEq f m m' → Sep [⟨a, n⟩] f → g m' a = g m a`;
* each rewrite's side condition goes to `fp_tac`, so layout facts must be hypotheses. It runs
  inside `first`, without error recovery: a failed side condition leaves the read as it is.
-/

namespace M0Crypto.Release.Footprint

open Lean Meta Elab Tactic

/-- Every footprint is apart from the empty one (a frame of a block that writes nothing). -/
theorem sep_nil_right (f : List Rgn) : Sep f [] := fun _ _ _ h => absurd h List.not_mem_nil

/-- `keep_simp [frame facts] with [readers] at l` (see the module doc). -/
syntax "keep_simp" (&" only")? (" [" term,* "]")? (" with" " [" ident,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

/-- The frame facts of the context, as terms. -/
def frameFacts : TacticM (Array Expr) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``MemEq 3 && ty.getArg! 1 != ty.getArg! 2 then
      out := out.push d.toExpr
  return out

elab_rules : tactic
  | `(tactic| keep_simp $[only%$o]? $[[$ts,*]]? $[with [$rs,*]]? $[$loc]?) => withMainContext do
    let mut facts ← if o.isSome then pure #[] else frameFacts
    for t in (ts.map (·.getElems) |>.getD #[]) do
      facts := facts.push (← Term.elabTerm t none)
    let readers := #[mkIdent ``MemEq.read32, mkIdent ``MemEq.bytes] ++ (rs.map (·.getElems) |>.getD #[])
    let mut args : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    for h in facts do
      let hs ← Term.exprToSyntax h
      for r in readers do
        args := args.push (← `(Lean.Parser.Tactic.simpLemma| ($r $hs)))
    if args.isEmpty then throwError "keep_simp: no frame facts"
    evalTactic (← `(tactic| simp (disch := first | exact sep_nil_right _ | fp_tac | fail) only [$args,*] $[$loc]?))

end M0Crypto.Release.Footprint
