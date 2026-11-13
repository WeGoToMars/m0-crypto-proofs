import M0Crypto.Thumb.ReleaseCheck.Cases
import M0Crypto.Thumb.FoldRun
import M0Crypto.Spec.X25519Vectors

/-!
Executable checks of `m0c_x25519` and its three field routines in the whole-function model
(plan phase 5). These are tests, not proofs: they evaluate the artifact on chosen inputs.

Runs use `runFold`, equal to folding the trace of `runUntil` (`runFold_eq`), because a call of
about three million steps is too long for `runFast`'s trace.

* Entry cases check the `Result` of `Release/X25519Contract.lean`: the output against
  `Spec.X25519.x25519` of the bytes in memory at entry, SP and `r4`-`r11` restored, `r0`-`r3`
  and `r12` zero, the 480 wiped stack bytes zero, every read in `scalar`, `point`, the code or
  the 516-byte stack window, and every write in `out` or the stack window (so all other memory
  is unchanged).
* Routine cases check the contracts of `Release/X25519Routines.lean`: the result congruent
  modulo `p` to the routine's function, SP restored, reads in the inputs, the code and the
  routine's stack bytes, writes in `dst` and those stack bytes.
-/

namespace M0Crypto.Thumb.ReleaseCheck.X25519

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Thumb.ReleaseCheck
open M0Crypto.Spec.X25519 (Byte)

/-- Sizes of the internal routines, from `llvm-nm -S` of the release object. The routines lie
back to back directly below `m0c_x25519` (`fe_mul`, `fe_sqr`, `fe_mulc_add`), so their offsets
follow from the entry offset. `X25519Macros` checks every size and placement against the
decoded bytes. -/
def feMulSize : Nat := 0x974
def feSqrSize : Nat := 0x66e
def feMulcAddSize : Nat := 0x13e
def feMulcAdd : Nat := Artifacts.Release.x25519 - feMulcAddSize
def feSqr : Nat := feMulcAdd - feSqrSize
def feMul : Nat := feSqr - feMulSize

def pNat : Nat := 2 ^ 255 - 19

/-! ## Folded audit -/

/-- What a run keeps of its trace: steps, the first bad access, the deepest stack write. -/
structure Audit where
  steps : Nat := 0
  bad : Option String := none
  peak : Nat := 0

def auditEvent (reads writes : List (Nat × Nat)) (a : Audit) (e : Event) : Audit :=
  let bad := match a.bad with
    | some b => some b
    | none => auditAccesses [e] reads writes
  let peak := e.accesses.foldl (fun m x =>
    if x.kind = .write ∧ x.addr.toNat < entrySp ∧ entrySp - x.addr.toNat ≤ 4096 then
      max m (entrySp - x.addr.toNat) else m) a.peak
  ⟨a.steps + 1, bad, peak⟩

def regsFor (entry : Nat) (args : List Nat) : Reg → Word := fun r =>
  if h : r.val < args.length then BitVec.ofNat 32 args[r.val]
  else match r.val with
    | 13 => BitVec.ofNat 32 entrySp
    | 14 => retAddr ||| 1#32
    | 15 => BitVec.ofNat 32 (codeBase + entry)
    | i => sentinel i

/-- Call `entry` with `args` on `mem`, auditing every access. -/
def callAudit (entry : Nat) (args : List Nat) (mem : Mem) (reads writes : List (Nat × Nat))
    (fuel : Nat) : Except String (State × Audit) :=
  match runFold retAddr fuel (auditEvent reads writes) {} ⟨regsFor entry args, false, false, false,
      false, mem⟩ with
  | .error e => .error s!"fault {repr e}"
  | .ok r => .ok r

def code : Nat × Nat := (codeBase, codeArr.size)

def reg (s : State) (i : Nat) : Word := if h : i < 16 then s.regs ⟨i, h⟩ else 0

/-! ## The entry -/

def stackBytes : Nat := 516
def wipeBytes : Nat := 480

def readM (m : Mem) (a n : Nat) : List Byte :=
  (List.range n).map fun i => m (BitVec.ofNat 32 (a + i))

/-- One call of `m0c_x25519`. `scalar` and `point` are written first, then `out`'s initial
bytes where they do not overlap; the specification takes the bytes in memory at entry.
`outLen` narrows the allowed write range, for the non-vacuity guard. -/
def entryCase (tag : String) (outA scalarA pointA : Nat) (k u : List Byte) (outLen : Nat := 32) :
    Option String :=
  let rs : Regions := [(scalarA, k), (pointA, u), (outA, gen 32 7)]
  let mem := mkMem rs
  let kIn := readM mem scalarA 32
  let uIn := readM mem pointA 32
  let win := (entrySp - stackBytes, stackBytes)
  match callAudit Artifacts.Release.x25519 [outA, scalarA, pointA] mem
      [(scalarA, 32), (pointA, 32), code, win] [(outA, outLen), win] 4000000 with
  | .error e => some s!"{tag}: {e}"
  | .ok (s, a) =>
    if let some b := a.bad then some s!"{tag}: {b}"
    else if s.regs 13 != BitVec.ofNat 32 entrySp then some s!"{tag}: SP not restored"
    else if !((List.range 8).all fun i => reg s (i + 4) == sentinel (i + 4)) then
      some s!"{tag}: r4-r11 changed"
    else if ![0, 1, 2, 3, 12].all (fun i => reg s i == 0) then
      some s!"{tag}: r0-r3 or r12 not zero"
    else if a.peak > stackBytes then some s!"{tag}: stack {a.peak}"
    else if readM s.mem (entrySp - stackBytes) wipeBytes != List.replicate wipeBytes 0 then
      some s!"{tag}: stack not wiped"
    else if readM s.mem outA 32 != Spec.X25519.x25519 kIn uIn then
      some s!"{tag}: output differs from the specification"
    else none

/-- `n` as 32 little-endian bytes. -/
def le256 (n : Nat) : List Byte := (List.range 32).map fun i => BitVec.ofNat 8 (n / 256 ^ i)

/-- Pseudo-random bytes (a 64-bit linear congruential generator, top byte). -/
def rnd (n seed : Nat) : List Byte :=
  ((List.range n).foldl (fun (x, acc) _ =>
    let x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    (x, BitVec.ofNat 8 (x / 2 ^ 56) :: acc)) (seed, [])).2.reverse

def vk1 := Spec.X25519.ofHex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
def vu1 := Spec.X25519.ofHex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
def vk2 := Spec.X25519.ofHex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d"
def vu2 := Spec.X25519.ofHex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"
def nine : List Byte := 9 :: List.replicate 31 0

def bufO : Nat := 0x20001000
def bufS : Nat := 0x20001100
def bufP : Nat := 0x20001200

/-- Entry cases: (tag, out, scalar, point, k, u). -/
def entryInputs : List (String × Nat × Nat × Nat × List Byte × List Byte) := [
  ("RFC 7748 vector 1", bufO, bufS, bufP, vk1, vu1),
  ("RFC 7748 vector 2", bufO + 1, bufS + 2, bufP + 3, vk2, vu2),
  ("RFC 7748 iteration 1", bufO, bufS, bufP, nine, nine),
  ("u = 0", bufO + 3, bufS + 1, bufP, rnd 32 1, le256 0),
  ("u = 1", bufO, bufS, bufP + 1, rnd 32 2, le256 1),
  ("u = p - 1", bufO, bufS, bufP, rnd 32 3, le256 (pNat - 1)),
  ("u = p", bufO, bufS, bufP, rnd 32 4, le256 pNat),
  ("u = p + 1", bufO, bufS, bufP, rnd 32 5, le256 (pNat + 1)),
  ("u = 2^256 - 1", bufO, bufS, bufP, rnd 32 6, le256 (2 ^ 256 - 1)),
  ("k = 0", bufO, bufS, bufP, le256 0, rnd 32 7),
  ("k = 2^256 - 1", bufO, bufS, bufP, le256 (2 ^ 256 - 1), rnd 32 8),
  ("out = scalar", bufS, bufS, bufP, rnd 32 9, rnd 32 10),
  ("out = point", bufP, bufS, bufP, rnd 32 11, rnd 32 12),
  ("scalar = point = out", bufS, bufS, bufS, rnd 32 13, rnd 32 13),
  ("out overlaps scalar by 27", bufS + 5, bufS, bufP + 2, rnd 32 14, rnd 32 15),
  ("random", bufO + 2, bufS + 3, bufP + 1, rnd 32 16, rnd 32 17)]

/-! ## The routines -/

def feVal (bs : List Byte) : Nat := Spec.X25519.decodeLittleEndian bs

/-- One routine call: `dst`, `a`, `b` aligned; checks the value modulo `p` and the audit. -/
def routineCase (name : String) (off size frame : Nat) (useB : Bool) (f : Nat → Nat → Nat)
    (dstA aA bA : Nat) (x y : List Byte) : Option String :=
  let rs : Regions := [(aA, x), (bA, y), (dstA, gen 32 3)]
  let mem := mkMem rs
  let xa := feVal (readM mem aA 32)
  let yb := feVal (readM mem bA 32)
  let win := (entrySp - frame, frame)
  let reads := [(aA, 32)] ++ (if useB then [(bA, 32)] else []) ++ [code, win]
  let tag := s!"{name} dst {dstA} a {aA} b {bA} x {xa} y {yb}"
  if dstA % 4 != 0 ∨ aA % 4 != 0 ∨ bA % 4 != 0 then some s!"{tag}: unaligned case" else
  match callAudit off [dstA, aA, bA] mem reads [(dstA, 32), win] 100000 with
  | .error e => some s!"{tag}: {e}"
  | .ok (s, a) =>
    if let some b := a.bad then some s!"{tag}: {b}"
    else if s.regs 13 != BitVec.ofNat 32 entrySp then some s!"{tag}: SP not restored"
    else if a.peak > frame then some s!"{tag}: stack {a.peak}"
    else if feVal (readM s.mem dstA 32) % pNat != f xa yb % pNat then
      some s!"{tag}: value not congruent"
    else if (s.regs 15).toNat != retAddr.toNat then some s!"{tag}: wrong return"
    else if (codeBase + off ≤ retAddr.toNat ∧ retAddr.toNat < codeBase + off + size) then
      some s!"{tag}: return inside the routine"
    else none

/-- Edge values below 2^256. -/
def edges : List Nat :=
  [0, 1, 2, 19, 38, pNat - 1, pNat, pNat + 1, 2 * pNat - 1, 2 * pNat, 2 ^ 255 - 1, 2 ^ 255,
   2 ^ 256 - 38, 2 ^ 256 - 19, 2 ^ 256 - 1, 2 ^ 128 - 1, 2 ^ 224 + 2 ^ 32 - 1]

/-- Operand pairs: all edge pairs and 120 pseudo-random pairs. -/
def pairs : List (List Byte × List Byte) :=
  (edges.flatMap fun x => edges.map fun y => (le256 x, le256 y)) ++
  (List.range 120).map fun i => (rnd 32 (1000 + 2 * i), rnd 32 (1001 + 2 * i))

def ra : Nat := 0x20001100
def rb : Nat := 0x20001200
def rd : Nat := 0x20001300

/-- Aliasing layouts: (dst, a, b). -/
def layouts : List (Nat × Nat × Nat) := [(rd, ra, rb), (ra, ra, rb), (rb, ra, rb), (rd, ra, ra),
  (ra, ra, ra)]

def mulF (x y : Nat) : Nat := x * y
def sqrF (x _ : Nat) : Nat := x * x
def mulcF (x y : Nat) : Nat := 121666 * x + y

def routineCases (name : String) (off size frame : Nat) (useB : Bool) (f : Nat → Nat → Nat) :
    List (Option String) :=
  (pairs.zipIdx).map fun ((x, y), i) =>
    let (d, a, b) := layouts[i % layouts.length]!
    routineCase name off size frame useB f d a b x y

def mulCases (_ : Unit) := routineCases "fe_mul" feMul feMulSize 148 true mulF
def sqrCases (_ : Unit) := routineCases "fe_sqr" feSqr feSqrSize 148 false sqrF
def mulcCases (_ : Unit) := routineCases "fe_mulc_add" feMulcAdd feMulcAddSize 4 true mulcF

def entryShardCount : Nat := 4

#guard entryInputs.length == 16
#guard coveredExactlyOnce entryShardCount (entryInputs.map fun (t, _) => t)

def runEntryShard (shard : Fin entryShardCount) : IO Unit :=
  run s!"x25519 shard {shard.val}" ((partitionCases entryShardCount shard.val entryInputs).map
    fun ((t, o, k, u, kb, ub), _) => entryCase t o k u kb ub)

def runRoutines : IO Unit := do
  run "x25519 fe_mul" (mulCases ())
  run "x25519 fe_sqr" (sqrCases ())
  run "x25519 fe_mulc_add" (mulcCases ())

/-- Every check that `X25519Routines` and the entry shards `#eval`. -/
def allChecks : List (IO Unit) := runRoutines :: (List.finRange entryShardCount).map runEntryShard

end M0Crypto.Thumb.ReleaseCheck.X25519
