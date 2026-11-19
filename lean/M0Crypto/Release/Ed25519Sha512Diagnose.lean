import M0Crypto.Release.Ed25519Sha512Block
import M0Crypto.Release.RoutineDiagnose

/-!
Failure companions of the decided checks of `m0c_sha512_block` (rule 3 of the maintainability
lessons). Each returns `none` exactly when its check holds (`_eq_none`), and otherwise names what
fails. Nothing here is used by a proof.

* `blockAtFailure o pool bytes size`: the first piece of `blockAt` not at its offset (before or
  after the pool, from `piecesAtFailure`), or the layout equation that fails.
* `kFailure B`: the first `K` index whose pair in the table differs, with the pair read and the
  constant.
* `litFailure`: the literal's offset and word, the pc it is added to, and the address it gives
  against `sha512_K`.

```
#eval Ed25519Sha512Diagnose.blockAtFailure Ed25519Compact.sha512_block pool Build.compact.bytes size
```
-/

namespace M0Crypto.Release.Ed25519Sha512Diagnose

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release.Routine (litOff)
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.RoutineDiagnose
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Block (wordL kOk litOk)
open M0Crypto.Artifacts

def blockAtFailure (o pool : Nat) (bytes : List (BitVec 8)) (size : Nat) : Option String :=
  match piecesAtFailure bytes o (piecesA o pool) with
  | some (k, off, _, why) => some s!"before the pool: piece {k} at byte {off}: {why}"
  | none => match piecesAtFailure bytes (oR2 pool) (piecesB o pool) with
    | some (k, off, _, why) => some s!"after the pool: piece {k} at byte {off}: {why}"
    | none => firstFalse
      [(s!"the code before the pool ends at {o + piecesSize (piecesA o pool)}, not at the pool {pool}",
          o + piecesSize (piecesA o pool) == pool),
       (s!"the function ends at {oPost o pool + seqSize post}, not at {o + size}",
          oPost o pool + seqSize post == o + size)]

theorem blockAtFailure_eq_none (o pool : Nat) (bytes : List (BitVec 8)) (size : Nat) :
    blockAtFailure o pool bytes size = none ↔ blockAt o pool bytes size = true := by
  have hA := piecesAtFailure_eq_none bytes o (piecesA o pool)
  have hB := piecesAtFailure_eq_none bytes (oR2 pool) (piecesB o pool)
  unfold blockAtFailure blockAt
  cases h : piecesAtFailure bytes o (piecesA o pool) with
  | some x =>
    obtain ⟨_, _, _, _⟩ := x
    simp only [reduceCtorEq, false_iff, Bool.and_eq_true]
    exact fun hc => by rw [hA.mpr hc.1.1.1] at h; cases h
  | none =>
    cases h' : piecesAtFailure bytes (oR2 pool) (piecesB o pool) with
    | some x =>
      obtain ⟨_, _, _, _⟩ := x
      simp only [reduceCtorEq, false_iff, Bool.and_eq_true]
      exact fun hc => by rw [hB.mpr hc.1.1.2] at h'; cases h'
    | none => simp [firstFalse_eq_none, hA.mp h, hB.mp h']

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The pair of entry `i` of the table at `sha512_K`, high word first. -/
def kPair (B : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  wordL ((B.drop Ed25519Compact.sha512_K).take (8 * 80)) (8 * i + 4) ++
    wordL ((B.drop Ed25519Compact.sha512_K).take (8 * 80)) (8 * i)

def kFailure (B : List (BitVec 8)) : Option (Nat × BitVec 64 × BitVec 64) :=
  ((List.range 80).find? fun i => kPair B i != M0Crypto.Spec.Sha512.K[i]!).map fun i =>
    (i, kPair B i, M0Crypto.Spec.Sha512.K[i]!)

theorem kFailure_eq_none (B : List (BitVec 8)) : kFailure B = none ↔ kOk B = true := by
  simp [kFailure, kOk, kPair, List.find?_eq_none, List.all_eq_true]

/-- The literal's offset, its word, the pc of `add r7, pc`, their sum and `sha512_K`. -/
def litFailure : Option (Nat × Word × Word × Word × Word) :=
  if litOk (B := B) then none else
    some (litOff (oLit Ed25519Sha512Pass.O) (litImm Ed25519Sha512Pass.O pool),
      Frame.codeWord (B := B) (litOff (oLit Ed25519Sha512Pass.O) (litImm Ed25519Sha512Pass.O pool)),
      BitVec.ofNat 32 (oLit Ed25519Sha512Pass.O + 2 + 4),
      Frame.codeWord (B := B) (litOff (oLit Ed25519Sha512Pass.O) (litImm Ed25519Sha512Pass.O pool)) +
        BitVec.ofNat 32 (oLit Ed25519Sha512Pass.O + 2 + 4),
      BitVec.ofNat 32 Ed25519Compact.sha512_K)

theorem litFailure_eq_none : litFailure (B := B) = none ↔ litOk (B := B) = true := by
  unfold litFailure; split <;> simp_all

end

end M0Crypto.Release.Ed25519Sha512Diagnose
