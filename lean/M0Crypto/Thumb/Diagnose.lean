import M0Crypto.Thumb.Seq

/-!
Failure companions for the Boolean checks `Instr.falls` and `seqAt` (Seq.lean).

Each `…Failure` function returns `none` exactly when its check holds, and otherwise the
first failing site: the index in the list (and, for `seqAt`, the byte offset), the
instruction, and a short reason. The `…_eq_none` lemmas tie each companion to its check,
so the diagnostic cannot silently disagree with the check it explains.

Use with `#eval` after a `decide` or `cbv` check reports `false`.
-/

namespace M0Crypto.Thumb

/-- Why a non-falling instruction changes PC. Only meaningful when `falls` is false. -/
def Instr.fallsReason : Instr → String
  | .bcond _ _ => "conditional branch changes PC"
  | .b _ => "unconditional branch changes PC"
  | .bl _ => "branch with link changes PC"
  | .pop _ _ => "pop with PC in the list loads PC"
  | .movHi _ _ => "mov into PC changes PC"
  | _ => "falls through"

/-- Scan `is` from index `k`; see `fallsFailure`. -/
def fallsFailureFrom : Nat → List Instr → Option (Nat × Instr × String)
  | _, [] => none
  | k, i :: is => if i.falls then fallsFailureFrom (k + 1) is else some (k, i, i.fallsReason)

/-- The first instruction in `is` that does not fall through: its index, the instruction
and a reason. `none` exactly when `is.all Instr.falls` holds. -/
def fallsFailure (is : List Instr) : Option (Nat × Instr × String) := fallsFailureFrom 0 is

theorem fallsFailureFrom_eq_none (is : List Instr) :
    ∀ k, fallsFailureFrom k is = none ↔ is.all Instr.falls = true := by
  induction is with
  | nil => intro k; simp [fallsFailureFrom]
  | cons i is ih =>
    intro k
    by_cases h : i.falls = true
    · simp [fallsFailureFrom, h, ih]
    · have h' : i.falls = false := by simpa using h
      simp [fallsFailureFrom, h']

theorem fallsFailure_eq_none (is : List Instr) :
    fallsFailure is = none ↔ is.all Instr.falls = true :=
  fallsFailureFrom_eq_none is 0

/-- Scan `is` from index `k` at byte offset `off`; see `seqAtFailure`. -/
def seqAtFailureFrom (bytes : List (BitVec 8)) :
    Nat → Nat → List Instr → Option (Nat × Nat × Instr × String)
  | _, _, [] => none
  | k, off, i :: is =>
    if instrAt bytes off != some i then
      some (k, off, i, s!"decodes to {reprStr (instrAt bytes off)}, not this instruction")
    else if bytes.length < off + i.size then
      some (k, off, i, s!"{i.size}-byte instruction runs past the end of the artifact")
    else seqAtFailureFrom bytes (k + 1) (off + i.size) is

/-- The first place where `is` is not laid out at consecutive offsets from `off`: its index,
its byte offset, the listed instruction and a reason. `none` exactly when `seqAt` holds. -/
def seqAtFailure (bytes : List (BitVec 8)) (off : Nat) (is : List Instr) :
    Option (Nat × Nat × Instr × String) :=
  seqAtFailureFrom bytes 0 off is

theorem seqAtFailureFrom_eq_none (bytes : List (BitVec 8)) (is : List Instr) :
    ∀ k off, seqAtFailureFrom bytes k off is = none ↔ seqAt bytes off is = true := by
  induction is with
  | nil => intro k off; simp [seqAtFailureFrom, seqAt]
  | cons i is ih =>
    intro k off
    by_cases h1 : instrAt bytes off = some i
    · by_cases h2 : off + i.size ≤ bytes.length
      · have h3 : ¬ bytes.length < off + i.size := by omega
        simp [seqAtFailureFrom, seqAt, h1, h2, h3, ih]
      · have h3 : bytes.length < off + i.size := by omega
        simp [seqAtFailureFrom, seqAt, h1, h2, h3]
    · simp [seqAtFailureFrom, seqAt, h1]

theorem seqAtFailure_eq_none (bytes : List (BitVec 8)) (off : Nat) (is : List Instr) :
    seqAtFailure bytes off is = none ↔ seqAt bytes off is = true :=
  seqAtFailureFrom_eq_none bytes is 0 off

end M0Crypto.Thumb
