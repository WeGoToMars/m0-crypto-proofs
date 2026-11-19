import M0Crypto.Release.RoutinePieces
import M0Crypto.Thumb.Diagnose

/-!
Failure companions of the routine tooling's decided checks (rule 3 of the maintainability
lessons): each returns `none` exactly when its check holds, and otherwise names what fails.

* `piecesAtFailure bytes o ps`: the first piece of `ps` not laid out at its offset, as
  `some (piece index, byte offset, instruction, reason)` (from `seqAtFailure`).
* `siteOkFailure …`: the first failing condition of `Routine.siteOk`, by name.
-/

namespace M0Crypto.Release.RoutineDiagnose

open M0Crypto.Armv6M (Word Reg)
open M0Crypto.Thumb
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

def piecesAtFailureFrom (bytes : List (BitVec 8)) :
    Nat → Nat → List Piece → Option (Nat × Nat × Instr × String)
  | _, _, [] => none
  | k, o, p :: ps =>
    match seqAtFailure bytes o (p.instrs o) with
    | some (_, off, i, why) => some (k, off, i, why)
    | none => piecesAtFailureFrom bytes (k + 1) (o + p.size) ps

/-- The first piece of `ps` that is not at its offset from `o`: its index, the byte offset and
listed instruction that fail, and a reason. `none` exactly when `piecesAt` holds. -/
def piecesAtFailure (bytes : List (BitVec 8)) (o : Nat) (ps : List Piece) :
    Option (Nat × Nat × Instr × String) :=
  piecesAtFailureFrom bytes 0 o ps

theorem piecesAtFailureFrom_eq_none (bytes : List (BitVec 8)) :
    ∀ (ps : List Piece) (k o : Nat), piecesAtFailureFrom bytes k o ps = none ↔ piecesAt bytes o ps = true
  | [], _, _ => by simp [piecesAtFailureFrom, piecesAt]
  | p :: ps, k, o => by
    have ih := piecesAtFailureFrom_eq_none bytes ps (k + 1) (o + p.size)
    have hs := seqAtFailure_eq_none bytes o (p.instrs o)
    simp only [piecesAtFailureFrom, piecesAt, Bool.and_eq_true]
    cases h : seqAtFailure bytes o (p.instrs o) with
    | none => simp only [ih]; simp [hs.mp h]
    | some x =>
      obtain ⟨_, _, _, _⟩ := x
      simp only [reduceCtorEq, false_iff, not_and]
      intro e; rw [hs.mpr e] at h; cases h

theorem piecesAtFailure_eq_none (bytes : List (BitVec 8)) (o : Nat) (ps : List Piece) :
    piecesAtFailure bytes o ps = none ↔ piecesAt bytes o ps = true :=
  piecesAtFailureFrom_eq_none bytes ps 0 o

/-- The name of the first condition that is `false`. -/
def firstFalse : List (String × Bool) → Option String
  | [] => none
  | (n, b) :: cs => if b then firstFalse cs else some n

theorem firstFalse_eq_none : ∀ cs : List (String × Bool), firstFalse cs = none ↔ cs.all (·.2) = true
  | [] => by simp [firstFalse]
  | (n, b) :: cs => by cases b <;> simp [firstFalse, firstFalse_eq_none cs]

/-- The first failing condition of `siteOk cs f g o d N imm al wg rg`, by name, in the order
of `siteOk`. -/
def siteOkFailure [CodeBytes B BS] (cs : List (Nat × Nat)) (f : Routine) (g : List Instr) (o d N : Nat)
    (imm : BitVec 25) (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) : Option String :=
  firstFalse
    [("glue offset is odd", o % 2 == 0),
     ("bl offset is odd", (o + seqSize g) % 2 == 0),
     ("glue does not fall through (fallsFailure)", g.all Instr.falls),
     ("glue writes r4-r11 or sp", keepsHi g),
     ("glue access not aligned (alignChk)", Sym.alignChk al g),
     ("glue writes outside wg (writeChk)", Sym.writeChk wg g),
     ("glue reads outside rg (readChk)", Sym.readChk (fun _ => true) rg g),
     ("glue and bl outside the caller's code", rangesSub [(o, o + seqSize g + 4)] cs),
     ("callee code outside the caller's code", rangesSub f.code cs),
     ("return offset inside the callee's code", outside f.code (o + seqSize g + 4)),
     ("return offset past the artifact", decide (o + seqSize g + 4 ≤ BS)),
     ("bl does not reach the callee's entry",
       decide (BitVec.ofNat 32 (o + seqSize g) + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 f.entry)),
     ("callee window exceeds the caller's N bytes", decide (d + f.stack ≤ N)),
     ("sp offset d not a multiple of 4", d % 4 == 0)]

theorem siteOkFailure_eq_none (cs : List (Nat × Nat)) (f : Routine) (g : List Instr) (o d N : Nat)
    (imm : BitVec 25) (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) :
    siteOkFailure cs f g o d N imm al wg rg = none ↔ siteOk cs f g o d N imm al wg rg = true := by
  rw [siteOkFailure, firstFalse_eq_none, siteOk]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

end M0Crypto.Release.RoutineDiagnose
