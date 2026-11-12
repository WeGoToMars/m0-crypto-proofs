import M0Crypto.Thumb.Exec
import M0Crypto.Artifacts.Release

/-!
# Shared contract vocabulary

Statement file: definitions only, no proofs. Together with `ChaCha20Contract`, `AeadContract`
and `TraceSpec` it holds every definition of `Release/` that a headline theorem's statement
depends on. These files import only the specification, the machine model and the generated
artifact, never a proof file. Review them against the public headers (see `docs/REVIEW.md`).
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-- The release bytes. -/
abbrev B := Artifacts.Release.bytes

/-- `y` is one of the `n` bytes starting at address `a`, that is `y = a + o` for some
`o < n`, with addresses taken modulo 2^32. Every buffer, code and stack region of the
contracts is written with it. -/
abbrev Region (a : Word) (n : Nat) (y : Word) : Prop := (y - a).toNat < n

/-- Every write of the trace lies in `Wr`. -/
def WritesTo (Wr : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Writes e.accesses y → Wr y

/-- Run until PC = `stop` (checked before each step), with at most `fuel` steps.
Returns the list of all visited states (starting with `s` and ending with the state
where PC = `stop`) and the trace of executed events. -/
def runStates (stop : Word) : Nat → State → Except Fault (List State × List Event)
  | fuel, s =>
    if s.pc = stop then .ok ([s], [])
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step s with
        | .error e => .error e
        | .ok (s', e) =>
          match runStates stop n s' with
          | .error e' => .error e'
          | .ok (states, es) => .ok (s :: states, e :: es)

end M0Crypto.Release

namespace M0Crypto.Release.Frame

open M0Crypto.Armv6M (Word)

/-- `[a, a + n)` and `[b, b + m)` do not wrap and do not overlap. -/
def Disj (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 32 ∧ b.toNat + m ≤ 2 ^ 32 ∧ (a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)

end M0Crypto.Release.Frame
