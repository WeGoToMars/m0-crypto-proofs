import Std.Data.HashMap
import M0Crypto.Release.ConstantTime.Cert

/-!
# Certificate generator with keyed maps (build time only)

`genFast` computes the same kind of certificate as `gen` (`Cert.lean`) and is equally
untrusted: the kernel checks its output with `certOk`, and no theorem mentions it.

`gen` keeps the state of every visited point in an association list and appends to its
worklist, so each visit costs time proportional to the number of points. On a unit whose
callees are analysed once per call site (X25519: 47 call sites, about 46,000 points per
pass) that is quadratic and does not finish. `genFast` differs only in data structures and
in two parameters:

* point states in a `Std.HashMap`, the worklist in an `Array` read from the front;
* the instructions decoded once into an array indexed by offset;
* `widenAt`, the number of growing joins at one point before widening (`gen` uses
  `widenAfter`), so an entry whose loop counters change on every pass can widen early;
* `progress`, which prints the visit count to standard error every 100,000 visits, so a
  long run cannot look hung.

The fixpoint is the same chaotic iteration, so the result may differ from `gen` only in
block order and in where widening happens. Either way `certOk` decides acceptance.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Thumb
open Std (HashMap)

/-- The instruction at every offset of the artifact, decoded once. -/
def instrTable (bytes : List (BitVec 8)) : Array (Option Instr) :=
  let a := bytes.toArray
  let hw (off : Nat) : BitVec 16 := a.getD (off + 1) 0 ++ a.getD off 0
  (Array.range a.size).map fun off => decode (hw off) (hw (off + 2))

/-- Result of the fixpoint: state and join count at every point, and the visit count. -/
structure FixResult where
  states : HashMap Pt (AbsState × Nat)
  visits : Nat

/-- Pointwise fixpoint over a FIFO worklist, as `fix` but with keyed maps. -/
def fixFast (env : Env) (tbl : Array (Option Instr)) (widenAt : Nat) (progress : Bool) :
    Nat → Nat → Array (Pt × AbsState) → HashMap Pt (AbsState × Nat) → Nat →
      Except String FixResult
  | 0, _, _, _, _ => .error "analysis fuel exhausted"
  | fuel + 1, i, wl, m, visits =>
    if h : i < wl.size then
      let (p, s) := wl[i]
      let visits := visits + 1
      let visits := if progress && visits % 100000 == 0 then
          dbgTrace s!"ct gen: {visits} visits, {m.size} points, worklist {wl.size - i}"
            fun _ => visits
        else visits
      let next : Option (AbsState × Nat) := match m[p]? with
        | none => some (s, 0)
        | some (cur, k) =>
          if s.le cur then none
          else match AbsState.join env.win cur s with
            | none => some (cur, k)  -- reported by the checker
            | some j => some (if k ≥ widenAt then widen env.win cur j else j, k + 1)
      match next with
      | none => fixFast env tbl widenAt progress fuel (i + 1) wl m visits
      | some (st, k) =>
        match tbl.getD p.1 none with
        | none => .error s!"no instruction at {p.1}"
        | some ins =>
          match xfer env p.1 p.2 ins st with
          | .error e => .error s!"pc {p.1} ctx {p.2}: {e}"
          | .ok o =>
            let wl := o.succs.foldl (init := wl) fun acc (t, s') => match t with
              | .pt off ctx => acc.push ((off, ctx), s')
              | .exit => acc
            fixFast env tbl widenAt progress fuel (i + 1) wl (m.insert p (st, k)) visits
    else .ok ⟨m, visits⟩

/-- Cut the fixpoint into blocks, as `blocks` but with keyed maps. Blocks are sorted by
offset and context so the certificate does not depend on hash order. -/
def blocksFast (env : Env) (tbl : Array (Option Instr)) (entry : Nat)
    (m : HashMap Pt (AbsState × Nat)) : Except String Cert := do
  let pts := m.toList
  let succ : HashMap Pt (List Pt) ← pts.foldlM (init := {}) fun acc (p, st, _) => do
    let some i := tbl.getD p.1 none | .error s!"no instruction at {p.1}"
    match xfer env p.1 p.2 i st with
    | .error e => .error e
    | .ok o => pure (acc.insert p (o.succs.filterMap fun (t, _) => match t with
        | .pt off ctx => some (off, ctx)
        | .exit => none))
  let preds : HashMap Pt (List Pt) := succ.fold (init := {}) fun acc p qs =>
    qs.foldl (init := acc) fun acc q => acc.insert q (p :: acc.getD q [])
  let size (p : Pt) : Nat := match tbl.getD p.1 none with
    | some i => i.size
    | none => 0
  let falls : Pt → Bool := fun p => match succ[p]? with
    | some [q] => q == (p.1 + size p, p.2) && size p != 0
    | _ => false
  let isHead : Pt → Bool := fun q =>
    q == (entry, none) || match preds.getD q [] with
      | [p] => !falls p
      | _ => true
  let rec walk : Nat → Pt → List Instr
    | 0, _ => []
    | fuel + 1, p => match tbl.getD p.1 none with
      | none => []
      | some i =>
        let q := (p.1 + i.size, p.2)
        if falls p && !isHead q && m.contains q then i :: walk fuel q else [i]
  let heads := (pts.filter fun (p, _, _) => isHead p).toArray.qsort fun (a, _) (b, _) =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.getD 0) < (b.2.getD 0))
  pure <| heads.toList.map fun (p, st, _) => ⟨p.1, p.2, st, walk tbl.size p⟩

/-- `gen` with keyed maps, a widening threshold and optional progress output. -/
def genFast (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState)
    (fuel : Nat) (widenAt : Nat := widenAfter) (progress : Bool := false) : Except String Cert := do
  let tbl := instrTable bytes
  let r ← fixFast env tbl widenAt progress fuel 0 #[((entry, none), init)] {} 0
  blocksFast env tbl entry r.states

/-- Visit and point counts of a fixpoint run, for measuring the generator. -/
def genStats (env : Env) (bytes : List (BitVec 8)) (entry : Nat) (init : AbsState)
    (fuel : Nat) (widenAt : Nat := widenAfter) (progress : Bool := false) :
    Except String (Nat × Nat) := do
  let r ← fixFast env (instrTable bytes) widenAt progress fuel 0 #[((entry, none), init)] {} 0
  pure (r.visits, r.states.size)

end M0Crypto.Release.ConstantTime
