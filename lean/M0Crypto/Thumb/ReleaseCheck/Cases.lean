import M0Crypto.Thumb.FastRun
import M0Crypto.Artifacts.Release

/-!
Shared harness of the executable checks of the release artifact in the whole-function model.

Each case loads `Artifacts.Release.bytes` at a 4-byte-aligned address, calls an exported
function the way the AAPCS does (r0-r3, then stack arguments, LR = a return address outside
the code), runs it to the return, and checks, per function (`ChaCha20Cases`, `Blake2sCases`,
`X25519Cases`):

* the result against the specification;
* **every data access in the trace** against the function's buffers, the code (literal pools)
  and the stack window. This is the exact-range audit the QEMU guard bytes cannot do for reads;
* r4-r11 and SP restored, the documented volatile-register clearing, and the peak stack depth
  against the documented bound.

These are evaluations (`#eval` that throws on any failure, so the build fails), not proofs.
They test the artifact under the model; the model itself is a transcription of the ARM
pseudocode (`Exec.lean`).
-/

namespace M0Crypto.Thumb.ReleaseCheck

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Artifacts


def codeBase : Nat := 0x00006000
def codeArr : Array (BitVec 8) := Release.bytes.toArray
def retAddr : Word := 0x7ffffff0#32
def entrySp : Nat := 0x20007f00

/-- Byte regions of the initial memory: (address, contents). -/
abbrev Regions := List (Nat × List (BitVec 8))

def mkMem (rs : Regions) : Mem := fun a =>
  let x := a.toNat
  if codeBase ≤ x ∧ x < codeBase + codeArr.size then codeArr[x - codeBase]!
  else match rs.find? (fun (b, bs) => b ≤ x ∧ x < b + bs.length) with
    | some (b, bs) => bs[x - b]!
    | none => 0xee#8

/-- Little-endian bytes of a 32-bit value. -/
def le32 (x : Nat) : List (BitVec 8) := (List.range 4).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

def sentinel (i : Nat) : Word := BitVec.ofNat 32 (0x5e000000 + i * 0x010101)
def sentinel2 (i : Nat) : Word := BitVec.ofNat 32 (0x7a000000 + i * 0x030303)

structure Outcome where
  final : State
  trace : List Event

/-- Call the function at artifact offset `entry` with specific caller registers r4-r12. -/
def callWithRegs (entry : Nat) (regArgs : List Nat) (stackArgs : List Nat) (rs : Regions)
    (callerRegs : Nat → Word := sentinel) :
    Except String Outcome :=
  let stack := stackArgs.flatMap le32
  let mem := mkMem ((entrySp, stack) :: rs)
  let regs : Reg → Word := fun r =>
    if h : r.val < regArgs.length then BitVec.ofNat 32 regArgs[r.val]
    else match r.val with
      | 13 => BitVec.ofNat 32 entrySp
      | 14 => retAddr ||| 1#32
      | 15 => BitVec.ofNat 32 (codeBase + entry)
      | i => callerRegs i
  -- `runFast_eq`: this is exactly `runUntil retAddr 2000000`, evaluated quickly.
  match runFast retAddr 2000000 ⟨regs, false, false, false, false, mem⟩ with
  | .error e => .error s!"fault {repr e}"
  | .ok (s, tr) => .ok ⟨s, tr⟩

/-- Call the function at artifact offset `entry`. -/
def call (entry : Nat) (regArgs : List Nat) (stackArgs : List Nat) (rs : Regions) :
    Except String Outcome :=
  callWithRegs entry regArgs stackArgs rs sentinel

def inRange (a : Nat) (rs : List (Nat × Nat)) : Bool := rs.any fun (b, n) => b ≤ a ∧ a < b + n

/-- Every byte of every access lies in an allowed range for its kind. -/
def auditAccesses (tr : List Event) (reads writes : List (Nat × Nat)) : Option String :=
  tr.findSome? fun e => e.accesses.findSome? fun acc =>
    let ok := (List.range acc.width).all fun k =>
      let a := (acc.addr + BitVec.ofNat 32 k).toNat
      match acc.kind with
      | .read => inRange a reads
      | .write => inRange a writes
    if ok then none else some s!"{repr acc.kind} {acc.addr.toNat} width {acc.width} at pc {e.pc.toNat - codeBase}"

/-- Deepest stack byte written, as a depth below the entry SP. Only writes in the
4 KiB below the entry SP count; the buffers are far below that. -/
def peakStack (tr : List Event) : Nat :=
  tr.foldl (fun m e => e.accesses.foldl (fun m a =>
    if a.kind = .write ∧ a.addr.toNat < entrySp ∧ entrySp - a.addr.toNat ≤ 4096 then
      max m (entrySp - a.addr.toNat) else m) m) 0

def readMem (s : State) (a n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => s.mem (BitVec.ofNat 32 (a + i))

/-- Shared post-conditions: return to the caller, callee-saved registers and SP
restored, volatile registers in `cleared` zero, stack within `maxStack`, and the
access audit. -/
def common (o : Outcome) (reads writes : List (Nat × Nat)) (maxStack : Nat)
    (cleared : List Nat) : Option String :=
  let s := o.final
  if s.regs 13 != BitVec.ofNat 32 entrySp then some "SP not restored"
  else if !((List.finRange 8).all fun i => s.regs ⟨i.val + 4, by omega⟩ == sentinel (i.val + 4)) then
    some "callee-saved register changed"
  else if !(cleared.all fun i => if h : i < 16 then s.regs ⟨i, h⟩ == 0 else true) then
    some s!"volatile register not cleared: {cleared.filter fun i => if h : i < 16 then s.regs ⟨i, h⟩ != 0 else false}"
  else if peakStack o.trace > maxStack then some s!"stack {peakStack o.trace} > {maxStack}"
  else auditAccesses o.trace reads writes

/-- What the caller can observe of a returned call besides r0-r12 and its own
buffers: the stack window below the entry SP and the NZCV flags. -/
def residue (o : Outcome) (maxStack : Nat) : List (BitVec 8) × List Bool :=
  (readMem o.final (entrySp - maxStack) maxStack, [o.final.n, o.final.z, o.final.c, o.final.v])

/-- Secret-residue check: two calls with the same public inputs (lengths, pointers,
counter, verdict) but different secrets must leave identical residues. Any key,
key stream, plaintext or tag byte left on the stack or in the flags shows up as a
difference (unless the two secrets happen to agree there). -/
def sameResidue (a b : Except String Outcome) (maxStack : Nat) : Option String :=
  match a, b with
  | .ok x, .ok y =>
    let (sx, fx) := residue x maxStack
    let (sy, fy) := residue y maxStack
    if fx != fy then some "flags at return depend on secrets"
    else match ((List.range maxStack).zip (sx.zip sy)).find? (fun (_, u, v) => u != v) with
      | some (i, _) => some s!"secret-dependent stack residue at depth {maxStack - i}"
      | none => none
  | .error e, _ | _, .error e => some e

def sameTrace (a b : Except String Outcome) : Option String :=
  match a, b with
  | .ok x, .ok y =>
    if x.trace != y.trace then some s!"trace differs between runs (lengths {x.trace.length} vs {y.trace.length})"
    else none
  | .error e, _ | _, .error e => some e

def gen (n seed : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => BitVec.ofNat 8 ((i * 131 + seed * 197 + 89) % 256)

def stackWin (maxStack nArgs : Nat) : Nat × Nat := (entrySp - maxStack, maxStack + 4 * nArgs)

def run (name : String) (cases : List (Option String)) : IO Unit := do
  match cases.findSome? id with
  | some e => throw (IO.userError s!"release check FAILED: {e}")
  | none => IO.println s!"release check {name}: {cases.length} cases pass"

/-- `run` for cases that are evaluated one at a time, stopping at the first failure: a broken
artifact can make every case run to the step limit. -/
def runLazy (name : String) (cases : List (Unit → Option String)) : IO Unit := do
  match cases.findSome? (· ()) with
  | some e => throw (IO.userError s!"release check FAILED: {e}")
  | none => IO.println s!"release check {name}: {cases.length} cases pass"

/-- A named boolean check in the form `run` takes. -/
def guardCase (name : String) (ok : Bool) : Option String := if ok then none else some name

/-- `main` of an asset's native release-check executable: runs the same checks the shard
modules `#eval`, as parallel tasks, and returns 1 if any of them failed. The mutation scripts
use it; the proofs build keeps the interpreted `#eval`s. -/
def exeMain (checks : List (IO Unit)) : IO UInt32 := do
  let tasks ← checks.mapM fun c => IO.asTask c
  let mut rc : UInt32 := 0
  for t in tasks do
    if let .error e := t.get then
      IO.eprintln e
      rc := 1
  return rc

/-- Keep original indices so duplicate or missing descriptors are detectable. -/
def partitionCases {α : Type} (count shard : Nat) (xs : List α) : List (α × Nat) :=
  xs.zipIdx.filter fun (_, i) => i % count == shard

/-- Sorting the partitioned indexed descriptors must recover the original list. -/
def coveredExactlyOnce {α : Type} [BEq α] (count : Nat) (xs : List α) : Bool :=
  (((List.range count).flatMap fun s => partitionCases count s xs).mergeSort
    fun a b => a.2 ≤ b.2) == xs.zipIdx

end M0Crypto.Thumb.ReleaseCheck
