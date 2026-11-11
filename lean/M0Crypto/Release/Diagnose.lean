import M0Crypto.Release.Frame
import M0Crypto.Release.Poly1305BlocksCode

/-!
Failure companions for the Boolean checks `Frame.frameWB` and `Poly1305Blocks.stable`.

Each `…Failure` function returns `none` exactly when its check holds, and otherwise the
first failing site: the index in the list, the instruction, and a short reason. The
`…_eq_none` lemmas prove each companion agrees with its check. The per-instruction tests
are the same `match` expressions as the checks, and the `…_cons_split` lemmas hold by
`rfl`, so nothing is re-stated.

Use with `#eval` after a `decide` or `cbv` check reports `false`.
-/

namespace M0Crypto.Release.Frame

open M0Crypto.Thumb

/-- The per-instruction test that `frameWB` applies to each instruction. -/
def frameWBOk (n : Nat) (i : Instr) : Bool := match i with
  | .strSp _ k => decide (k.toNat < n)
  | i => !i.writesMem && !(i.dsts.contains 13)

theorem frameWB_cons_split (n : Nat) (i : Instr) (is : List Instr) :
    frameWB n (i :: is) = (frameWBOk n i && frameWB n is) := rfl

/-- Why `frameWBOk` rejects an instruction. Only meaningful when the test fails. -/
def frameWBReason (n : Nat) : Instr → String
  | .strSp _ k => s!"str to slot {k.toNat} is outside the {n}-word frame"
  | i => if i.writesMem then "writes memory other than a frame str" else "writes SP"

/-- Scan `is` from index `k`; see `frameWBFailure`. -/
def frameWBFailureFrom (n : Nat) : Nat → List Instr → Option (Nat × Instr × String)
  | _, [] => none
  | k, i :: is =>
    if frameWBOk n i then frameWBFailureFrom n (k + 1) is else some (k, i, frameWBReason n i)

/-- The first instruction in `is` that `frameWB n` rejects: its index, the instruction and a
reason. `none` exactly when `frameWB n is` holds. -/
def frameWBFailure (n : Nat) (is : List Instr) : Option (Nat × Instr × String) :=
  frameWBFailureFrom n 0 is

theorem frameWBFailureFrom_eq_none (n : Nat) (is : List Instr) :
    ∀ k, frameWBFailureFrom n k is = none ↔ frameWB n is = true := by
  induction is with
  | nil => intro k; simp [frameWBFailureFrom, frameWB]
  | cons i is ih =>
    intro k
    rw [frameWB_cons_split]
    by_cases h : frameWBOk n i = true
    · simp [frameWBFailureFrom, h, ih]
    · have h' : frameWBOk n i = false := by simpa using h
      simp [frameWBFailureFrom, h']

theorem frameWBFailure_eq_none (n : Nat) (is : List Instr) :
    frameWBFailure n is = none ↔ frameWB n is = true :=
  frameWBFailureFrom_eq_none n is 0

end M0Crypto.Release.Frame

namespace M0Crypto.Release.Poly1305Blocks

open M0Crypto.Thumb

theorem stable_cons_split (i : Instr) (is : List Instr) :
    stable (i :: is) = (stableInstr i && stable is) := rfl

/-- Why `stableInstr` rejects an instruction. Only meaningful when the test fails. -/
def stableReason (i : Instr) : String :=
  if i.dsts.contains 13 then "writes SP"
  else if i.dsts.contains 7 then "writes r7, the base of word loads"
  else match i with
    | .memImm _ _ _ _ => "immediate-offset store, or word load whose base is not r7"
    | _ => "not SP-neutral (Instr.spRel is not some [])"

/-- Scan `is` from index `k`; see `stableFailure`. -/
def stableFailureFrom : Nat → List Instr → Option (Nat × Instr × String)
  | _, [] => none
  | k, i :: is => if stableInstr i then stableFailureFrom (k + 1) is else some (k, i, stableReason i)

/-- The first instruction in `is` that `stable` rejects: its index, the instruction and a
reason. `none` exactly when `stable is` holds. -/
def stableFailure (is : List Instr) : Option (Nat × Instr × String) := stableFailureFrom 0 is

theorem stableFailureFrom_eq_none (is : List Instr) :
    ∀ k, stableFailureFrom k is = none ↔ stable is = true := by
  induction is with
  | nil => intro k; simp [stableFailureFrom, stable]
  | cons i is ih =>
    intro k
    rw [stable_cons_split]
    by_cases h : stableInstr i = true
    · simp [stableFailureFrom, h, ih]
    · have h' : stableInstr i = false := by simpa using h
      simp [stableFailureFrom, h']

theorem stableFailure_eq_none (is : List Instr) :
    stableFailure is = none ↔ stable is = true :=
  stableFailureFrom_eq_none is 0

end M0Crypto.Release.Poly1305Blocks
