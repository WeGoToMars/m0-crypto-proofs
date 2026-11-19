import M0Crypto.Thumb.FoldRun
import M0Crypto.Release.Ed25519Contract

/-!
Harness of the executable checks of the Ed25519 asset (plan phase 5). These are tests, not
proofs: they evaluate the bytes of a build in the whole-function model on chosen inputs.

A call loads `b.bytes` of the build `b` at `codeBase`, sets r0-r3 to the arguments, r4-r12 to
distinct caller values, SP to `sp0` and LR to a return address outside the code, and runs to the
return with `runFold` (equal to folding the trace of `runUntil`, `runFold_eq`). The fold audits
every data access as it happens:

* every byte read lies in the caller's read ranges, the code or the stack window;
* writes below `sp0` in the 4 KiB stack area only lower the deepest written byte `low`; every
  other write is kept (`outW`), so a check can require it to lie in an output buffer.

Memory the run does not write is the initial memory (the model's step changes memory only at the
addresses it writes, `step_mem_other`), so "writes only in the window and the outputs" is the
`MemOut` / `WrOk` frame of the contract.
-/

namespace M0Crypto.Thumb.ReleaseCheck.Ed25519

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519 (Build)

abbrev Byte := BitVec 8

def codeBase : Nat := 0x00006000
def retAddr : Word := 0x7ffffff0#32
def sp0 : Nat := 0x20007f00
/-- The stack area whose writes count as stack writes; buffers lie below it. -/
def stackArea : Nat := 4096

/-- The caller's value of register `i`. -/
def callerReg (i : Nat) : Word := BitVec.ofNat 32 (0x5e000000 + i * 0x010101)

def compactCode : Array Byte := Build.compact.bytes.toArray
def fastCode : Array Byte := Build.fast.bytes.toArray

def codeOf : Build → Array Byte
  | .compact => compactCode
  | .fast => fastCode

def code (b : Build) : Nat × Nat := (codeBase, b.size)

/-- Initial memory: the build at `codeBase`, then the byte regions (the first region holding an
address wins), else a fill that depends on the address. -/
def mkMem (b : Build) (rs : List (Nat × List Byte)) : Mem := fun a =>
  let x := a.toNat
  let c := codeOf b
  if codeBase ≤ x ∧ x < codeBase + c.size then c[x - codeBase]!
  else match rs.find? (fun (y, bs) => y ≤ x ∧ x < y + bs.length) with
    | some (y, bs) => bs[x - y]!
    | none => BitVec.ofNat 8 (x * 37 + 11)

def inRange (a : Nat) (rs : List (Nat × Nat)) : Bool := rs.any fun (y, n) => y ≤ a ∧ a < y + n

def readM (m : Mem) (a n : Nat) : List Byte := (List.range n).map fun i => m (BitVec.ofNat 32 (a + i))

/-- The little-endian number of the `n` bytes at `a`. -/
def valM (m : Mem) (a n : Nat) : Nat := Spec.Ed25519.decodeInt (readM m a n)

/-- `x` as `n` little-endian bytes. -/
def le (n x : Nat) : List Byte := (List.range n).map fun i => BitVec.ofNat 8 (x / 256 ^ i)

/-- Pseudo-random bytes (a 64-bit linear congruential generator, top byte). -/
def rnd (n seed : Nat) : List Byte :=
  ((List.range n).foldl (fun (x, acc) _ =>
    let x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    (x, BitVec.ofNat 8 (x / 2 ^ 56) :: acc)) (seed, [])).2.reverse

def rndNat (n seed : Nat) : Nat := Spec.Ed25519.decodeInt (rnd n seed)

/-! ## A run -/

structure Run where
  final : State
  steps : Nat := 0
  /-- The first read outside the read ranges. -/
  rd : Option String := none
  /-- Writes outside the stack area: (address, width, code offset). -/
  outW : List (Nat × Nat × Nat) := []
  /-- The deepest stack byte written. -/
  low : Nat := sp0

def auditEvent (reads : List (Nat × Nat)) (r : Run) (e : Event) : Run :=
  let pc := e.pc.toNat - codeBase
  e.accesses.foldl (fun r a =>
    let x := a.addr.toNat
    match a.kind with
    | .read =>
      if r.rd.isSome || (List.range a.width).all (fun k => inRange (x + k) reads) then r
      else { r with rd := some s!"read {x} width {a.width} at code offset {pc}" }
    | .write =>
      if sp0 - stackArea ≤ x ∧ x + a.width ≤ sp0 then { r with low := min r.low x }
      else { r with outW := (x, a.width, pc) :: r.outW }) { r with steps := r.steps + 1 }

/-- Call offset `off` of build `b` with `args` in r0-r3 on memory `m`. Reads may hit `reads`,
the code and the `n` bytes below `sp0`. -/
def callAt (b : Build) (off : Nat) (args : List Nat) (m : Mem) (reads : List (Nat × Nat)) (n : Nat)
    (fuel : Nat := 30000000) : Except String Run :=
  let regs : Reg → Word := fun r =>
    if h : r.val < args.length then BitVec.ofNat 32 args[r.val]
    else match r.val with
      | 13 => BitVec.ofNat 32 sp0
      | 14 => retAddr ||| 1#32
      | 15 => BitVec.ofNat 32 (codeBase + off)
      | i => callerReg i
  let s : State := ⟨regs, false, false, false, false, m⟩
  match runFold retAddr fuel (auditEvent (reads ++ [code b, (sp0 - n, n)])) { final := s } s with
  | .error e => .error s!"fault {repr e}"
  | .ok (t, r) => .ok { r with final := t }

def reg (s : State) (i : Nat) : Word := if h : i < 16 then s.regs ⟨i, h⟩ else 0

/-- The writes of a run lie in an `n`-byte window below `sp0` and in `outs`. -/
def writesIn (r : Run) (n : Nat) (outs : List (Nat × Nat)) : Option String :=
  if r.low < sp0 - n then some s!"stack write {sp0 - r.low} bytes below SP0, window {n}"
  else (r.outW.find? fun (x, w, _) => !(List.range w).all fun k => inRange (x + k) outs).map
    fun (x, w, pc) => s!"write {x} width {w} at code offset {pc}"

/-- Run the cases in `workers` dedicated threads; print every failure. -/
def runCases (workers : Nat) (cases : List (String × (Unit → Option String))) : IO UInt32 := do
  let parts := (List.range workers).map fun w =>
    (cases.zipIdx.filter fun (_, i) => i % workers == w).map (·.1)
  let tasks ← parts.mapM fun part => IO.asTask (prio := .dedicated) do
    let mut fails : Array String := #[]
    for (name, c) in part do
      if let some e := c () then fails := fails.push s!"{name}: {e}"
    return fails
  let mut rc : UInt32 := 0
  for t in tasks do
    match t.get with
    | .error e => IO.eprintln s!"release check FAILED: {e}"; rc := 1
    | .ok fails => for f in fails do IO.eprintln s!"release check FAILED: {f}"; rc := 1
  return rc

end M0Crypto.Thumb.ReleaseCheck.Ed25519
