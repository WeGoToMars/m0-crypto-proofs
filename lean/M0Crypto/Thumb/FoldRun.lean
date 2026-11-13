import M0Crypto.Thumb.FastRun

/-!
`runFast` with the trace folded as it is produced, proved equal to folding the trace of
`runUntil` (`runFold_eq`).

`runFast` builds the trace by non-tail recursion; a call of several million steps, such as
`m0c_x25519`, overflows the evaluator's stack and holds gigabytes of events. `runFold` is
tail-recursive and keeps only an accumulator, so executable checks can audit long runs.
-/

namespace M0Crypto.Thumb

open M0Crypto.Armv6M

def runFoldAux {β : Type} (stop : Word) (base : Mem) (f : β → Event → β) :
    Nat → Tbl → State → β → Except Fault (State × β)
  | fuel, t, s, b =>
    if s.pc = stop then .ok (s, b)
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step s with
        | .error e => .error e
        | .ok (s1, e) =>
          let t1 := record s1.mem (writtenAddrs e.accesses) t
          runFoldAux stop base f n t1 (flatten base t1 s1) (f b e)

theorem runFoldAux_eq {β : Type} (stop : Word) (base : Mem) (f : β → Event → β) (fuel : Nat)
    (t : Tbl) (s : State) (b : β) (hi : Inv base t s) :
    runFoldAux stop base f fuel t s b = (runUntil stop fuel s).map fun r => (r.1, r.2.foldl f b) := by
  induction fuel generalizing t s b with
  | zero => rw [runFoldAux, runUntil]; split <;> rfl
  | succ n ih =>
    rw [runFoldAux, runUntil]
    split
    · rfl
    · simp only
      split
      · rename_i e h; simp [h, Except.map]
      · rename_i s1 e h
        have hi1 := inv_step hi h
        rw [flatten_eq hi1, ih _ _ _ hi1, h]
        simp only
        cases runUntil stop n s1 <;> rfl

/-- Run from `s` folding `f` over the trace from `b`. -/
def runFold {β : Type} (stop : Word) (fuel : Nat) (f : β → Event → β) (b : β) (s : State) :
    Except Fault (State × β) :=
  runFoldAux stop s.mem f fuel {} (flatten s.mem {} s) b

theorem runFold_eq {β : Type} (stop : Word) (fuel : Nat) (f : β → Event → β) (b : β) (s : State) :
    runFold stop fuel f b s = (runUntil stop fuel s).map fun r => (r.1, r.2.foldl f b) := by
  have hi : Inv s.mem {} s := by funext y; simp [view]
  unfold runFold
  rw [flatten_eq hi, runFoldAux_eq stop s.mem f fuel {} s b hi]

end M0Crypto.Thumb
