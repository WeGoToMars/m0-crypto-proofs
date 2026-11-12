import M0Crypto.Thumb.ReleaseCheck.Cases
import M0Crypto.Spec.Blake2s

/-!
Executable checks of the BLAKE2s entries of the release artifact (C1, C2 under the model).

A streaming case runs `init; update*; final` on one context, threading memory between the
calls, and checks per call: the exact read and write ranges of the trace, `r4-r11` and `SP`
restored, the stack bound; and the digest against `Spec.Blake2s.blake2s`. Compression cases
run `m0c_blake2s_compress` directly against `Spec.Blake2s.compress` on chosen `t` and `f0`.
-/

namespace M0Crypto.Thumb.ReleaseCheck

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (Byte)
open M0Crypto.Artifacts

/-- Call the function at artifact offset `entry` on an explicit memory. -/
def callMem (mem : Mem) (entry : Nat) (regArgs : List Nat) (callerRegs : Nat → Word := sentinel) :
    Except String Outcome :=
  let regs : Reg → Word := fun r =>
    if h : r.val < regArgs.length then BitVec.ofNat 32 regArgs[r.val]
    else match r.val with
      | 13 => BitVec.ofNat 32 entrySp
      | 14 => retAddr ||| 1#32
      | 15 => BitVec.ofNat 32 (codeBase + entry)
      | i => callerRegs i
  match runFast retAddr 40000000 ⟨regs, false, false, false, false, mem⟩ with
  | .error e => .error s!"fault {repr e}"
  | .ok (s, tr) => .ok ⟨s, tr⟩

def b2sInitStack : Nat := 4
def b2sStreamStack : Nat := 160
def b2sCompressStack : Nat := 136
def b2sCopyStack : Nat := 20
def ctxA : Nat := 0x20004000
def ctxSize : Nat := 112

/-- Run one call and check its audit; return the next memory. -/
def stepCheck (name : String) (mem : Mem) (entry : Nat) (args : List Nat)
    (reads writes : List (Nat × Nat)) (maxStack : Nat) : Except String Outcome :=
  match callMem mem entry args with
  | .error e => .error s!"{name}: {e}"
  | .ok o =>
    match common o (reads ++ [(codeBase, codeArr.size), stackWin maxStack 0])
        (writes ++ [stackWin maxStack 0]) maxStack [] with
    | some e => .error s!"{name}: {e}"
    | none => .ok o

def updateAll (inA : Nat) : List Nat → Nat → Mem → Except String Mem
  | [], _, mem => .ok mem
  | n :: ps, pos, mem =>
    match stepCheck s!"update {n}@{pos}" mem Release.blake2s_update [ctxA, inA + pos, n]
        [(ctxA, ctxSize), (inA + pos, n)] [(ctxA, ctxSize)] b2sStreamStack with
    | .error e => .error e
    | .ok o => updateAll inA ps (pos + n) o.final.mem

/-- One streaming case. `parts` must sum to `len`. -/
def b2sStreamCase (len inOff outOff : Nat) (parts : List Nat) (seed : Nat) : Option String :=
  let inA := 0x20001000 + inOff
  let outA := 0x20002000 + outOff
  let msg := gen len seed
  let mem0 := mkMem [(ctxA, gen ctxSize (seed + 9)), (inA, msg), (outA, gen 32 (seed + 5))]
  let tag := s!"blake2s len {len} in+{inOff} out+{outOff} parts {parts}"
  if parts.sum != len then some s!"{tag}: bad partition" else
  match stepCheck "init" mem0 Release.blake2s_init [ctxA] [] [(ctxA, ctxSize)] b2sInitStack with
  | .error e => some s!"{tag}: {e}"
  | .ok o0 =>
    match updateAll inA parts 0 o0.final.mem with
    | .error e => some s!"{tag}: {e}"
    | .ok mem1 =>
      match stepCheck "final" mem1 Release.blake2s_final [ctxA, outA]
          [(ctxA, ctxSize)] [(ctxA, ctxSize), (outA, 32)] b2sStreamStack with
      | .error e => some s!"{tag}: {e}"
      | .ok o =>
        if readMem o.final outA 32 != M0Crypto.Spec.Blake2s.blake2s msg then
          some s!"{tag}: digest differs from the spec"
        else none

/-- One compression case against the specification. -/
def b2sCompressCase (t0 t1 f0 : Nat) (seed : Nat) : Option String :=
  let hA := 0x20001000; let bA := 0x20002000
  let h := gen 32 seed; let blk := gen 64 (seed + 1)
  let mem := mkMem [(entrySp, le32 f0), (hA, h), (bA, blk)]
  let name := s!"compress t0 {t0} t1 {t1} f0 {f0}"
  match stepCheck name mem Release.blake2s_compress [hA, bA, t0, t1]
      [(hA, 32), (bA, 64), (entrySp, 4)] [(hA, 32)] b2sCompressStack with
  | .error e => some e
  | .ok o =>
    -- RFC 7693 F with f0 = 0 or 0xffffffff
    let t := t0 + 2 ^ 32 * t1
    let spec := M0Crypto.Spec.Blake2s.compress (M0Crypto.Spec.Blake2s.wordsOfBytes h).toArray
      (M0Crypto.Spec.Blake2s.wordsOfBytes blk).toArray t (f0 != 0)
    let got := readMem o.final hA 32
    if f0 != 0 ∧ f0 != 0xffffffff then none
    else if got != M0Crypto.Spec.Blake2s.digestOf spec then some s!"{name}: differs from the spec"
    else if readMem o.final bA 64 != blk then some s!"{name}: block modified"
    else none

/-- The concatenated traces of `init; update*; final`, with chosen message, context garbage and
caller registers. -/
def b2sSeqTrace (len inOff outOff : Nat) (parts : List Nat) (msgSeed ctxSeed : Nat)
    (regs : Nat → Word) : Except String (List Event) :=
  let inA := 0x20001000 + inOff
  let outA := 0x20002000 + outOff
  let mem0 := mkMem [(ctxA, gen ctxSize ctxSeed), (inA, gen len msgSeed), (outA, gen 32 ctxSeed)]
  match callMem mem0 Release.blake2s_init [ctxA] regs with
  | .error e => .error e
  | .ok o0 =>
    let rec go : List Nat → Nat → Mem → List Event → Except String (Mem × List Event)
      | [], _, mem, tr => .ok (mem, tr)
      | n :: ps, pos, mem, tr =>
        match callMem mem Release.blake2s_update [ctxA, inA + pos, n] regs with
        | .error e => .error e
        | .ok o => go ps (pos + n) o.final.mem (tr ++ o.trace)
    match go parts 0 o0.final.mem o0.trace with
    | .error e => .error e
    | .ok (mem, tr) =>
      match callMem mem Release.blake2s_final [ctxA, outA] regs with
      | .error e => .error e
      | .ok o => .ok (tr ++ o.trace)

end M0Crypto.Thumb.ReleaseCheck
