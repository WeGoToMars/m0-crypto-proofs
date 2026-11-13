import M0Crypto.Thumb.ReleaseCheck.Cases
import M0Crypto.Spec.Blake2s

/-!
Executable checks of the BLAKE2s entries of the release artifact (hash and compress, under the model).

A streaming case runs `init; update*; final` on one context, threading memory between the
calls, and checks per call: the exact read and write ranges of the trace, `r4-r11` and `SP`
restored, the stack bound; and the digest against `Spec.Blake2s.blake2s`. Compression cases
run `m0c_blake2s_compress` directly against `Spec.Blake2s.compress` on chosen `t` and `f0`.
-/

namespace M0Crypto.Thumb.ReleaseCheck

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Spec.Blake2s (Byte)
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

/-! ## The cases, grouped as the shard modules run them -/

/-- `len` cut into pieces of `k` bytes (the last one shorter). -/
def cut (len k : Nat) : List Nat :=
  (List.range ((len + k - 1) / k)).map fun i => min k (len - i * k)

/-- compress: chosen counters and finalization words, including carries. -/
def b2sCompressCases : List (Unit → Option String) :=
  [(0, 0), (64, 0), (0xffffffc0, 0), (0xffffffc0, 1), (0xffffffff, 0xffffffff), (128, 5)].flatMap
    fun (t0, t1) => [0, 0xffffffff].map fun f0 _ => b2sCompressCase t0 t1 f0 (t0 + f0)

/-- hash: one-shot lengths 0-70 at input/output offsets 0-3. -/
def b2sShard0Cases : List (Unit → Option String) :=
  (List.range 71).flatMap fun len =>
    [0, 1, 2, 3].map fun off _ => b2sStreamCase len off ((off + 1) % 4) [len] (len + off)

/-- hash: lengths 71-200, one-shot and partitions 1, 17, 64. -/
def b2sShard1Cases : List (Unit → Option String) :=
  (List.range' 71 130).flatMap fun len =>
    ([0, 3].map fun off _ => b2sStreamCase len off (3 - off) [len] (len + off)) ++
    [fun _ => b2sStreamCase len 1 2 (cut len 17) len, fun _ => b2sStreamCase len 2 1 (cut len 64) len]

/-- hash: lengths 1024 and 1025, every partition, all offsets; then the partition boundary
cases of the buffering logic. -/
def b2sShard2Cases : List (Unit → Option String) :=
  ([1024, 1025].flatMap fun len =>
    ([0, 1, 2, 3].map fun off _ => b2sStreamCase len off ((off + 2) % 4) [len] (len + off)) ++
    ([1, 17, 64].map fun k _ => b2sStreamCase len 3 1 (cut len k) (len + k))) ++
  ([(63, 1), (64, 64), (1, 64), (65, 63), (0, 64), (64, 0), (127, 1), (1, 127), (128, 1)].map
    fun (a, b) _ => b2sStreamCase (a + b) 1 1 [a, b] (a * 7 + b))

/-- hash: length 4096, one-shot, 17-byte and 64-byte pieces. -/
def b2sShard3Cases : List (Unit → Option String) :=
  [fun _ => b2sStreamCase 4096 0 0 [4096] 4096, fun _ => b2sStreamCase 4096 1 3 (cut 4096 17) 4097,
   fun _ => b2sStreamCase 4096 2 2 (cut 4096 64) 4098]

/-- Same pointers and same sequence of lengths; different message bytes, different context
garbage, different caller registers: the traces must be equal. -/
def b2sSameTrace (len inOff outOff : Nat) (parts : List Nat) : Bool :=
  match b2sSeqTrace len inOff outOff parts 1 2 sentinel,
        b2sSeqTrace len inOff outOff parts 101 202 sentinel2 with
  | .ok a, .ok b => a == b
  | _, _ => false

def b2sPairwiseCases : List (Unit → Option String) :=
  [(0, 0, 0, [0]), (1, 1, 2, [1]), (63, 0, 0, [63]), (64, 3, 1, [64]), (65, 2, 2, [65]),
   (200, 1, 3, [200]), (200, 0, 0, [63, 1, 64, 72]), (130, 3, 1, [17, 17, 17, 17, 17, 17, 17, 11]),
   (1025, 1, 1, [1025]), (1025, 2, 3, [500, 525]), (129, 0, 0, [64, 1, 64])].map
    fun (len, inOff, outOff, parts) _ =>
      guardCase s!"traces differ: len {len} in+{inOff} out+{outOff} parts {parts}"
        (b2sSameTrace len inOff outOff parts)

def runB2sShard0 : IO Unit := do
  runLazy "blake2s compress" b2sCompressCases
  runLazy "blake2s shard 0" b2sShard0Cases
def runB2sShard1 : IO Unit := runLazy "blake2s shard 1" b2sShard1Cases
def runB2sShard2 : IO Unit := runLazy "blake2s shard 2" b2sShard2Cases
def runB2sShard3 : IO Unit := runLazy "blake2s shard 3" b2sShard3Cases
def runB2sPairwise : IO Unit := runLazy "blake2s pairwise" b2sPairwiseCases

/-- Every check that the shard modules and `Blake2sPairwise` `#eval`. -/
def b2sAllChecks : List (IO Unit) :=
  [runB2sShard0, runB2sShard1, runB2sShard2, runB2sShard3, runB2sPairwise]

end M0Crypto.Thumb.ReleaseCheck
