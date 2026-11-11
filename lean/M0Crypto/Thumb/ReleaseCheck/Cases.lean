import M0Crypto.Thumb.FastRun
import M0Crypto.Spec.Aead
import M0Crypto.Artifacts.Release

/-!
Executable checks of the release artifact in the whole-function model.

Each case loads `Artifacts.Release.bytes` at a 4-byte-aligned address, calls an
exported function the way the AAPCS does (r0-r3, then stack arguments, LR = a
return address outside the code), runs it to the return, and checks:

* the result against the RFC 8439 specification (`M0Crypto.Spec.Aead`);
* **every data access in the trace**: reads only from the input buffers, the key,
  nonce, AAD and tag, the code (literal pools) and the stack window; writes only
  to `out`, the tag (encrypt) and the stack below the entry SP. This is the
  exact-range audit the QEMU guard bytes cannot do for reads;
* r4-r11 and SP restored, the documented volatile-register clearing, and the
  peak stack depth against the documented bound;
* rejected calls (counter overflow, authentication failure) write nothing outside
  the stack.

These are evaluations (`#eval` that throws on any failure, so the build fails),
not proofs. They test the artifact under the model; the model itself is a
transcription of the ARM pseudocode (`Exec.lean`).
-/

namespace M0Crypto.Thumb.ReleaseCheck

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Spec.Aead
open M0Crypto.Spec.ChaCha20 (Byte)
open M0Crypto.Artifacts

def codeBase : Nat := 0x00006000
def codeArr : Array Byte := Release.bytes.toArray
def retAddr : Word := 0x7ffffff0#32
def entrySp : Nat := 0x20007f00

/-- Byte regions of the initial memory: (address, contents). -/
abbrev Regions := List (Nat × List Byte)

def mkMem (rs : Regions) : Mem := fun a =>
  let x := a.toNat
  if codeBase ≤ x ∧ x < codeBase + codeArr.size then codeArr[x - codeBase]!
  else match rs.find? (fun (b, bs) => b ≤ x ∧ x < b + bs.length) with
    | some (b, bs) => bs[x - b]!
    | none => 0xee#8

def le32 (x : Nat) : List Byte := leBytes 4 x

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

def readMem (s : State) (a n : Nat) : List Byte :=
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
def residue (o : Outcome) (maxStack : Nat) : List Byte × List Bool :=
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

def gen (n seed : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 ((i * 131 + seed * 197 + 89) % 256)

def stackWin (maxStack nArgs : Nat) : Nat × Nat := (entrySp - maxStack, maxStack + 4 * nArgs)

/-! ## ChaCha20 -/

def chacha20Stack : Nat := 176

/-- One `m0c_chacha20_xor` case. `outOff`/`inOff` are offsets from aligned bases;
`inPlace` uses the input buffer as output. -/
def chacha20Case (len outOff inOff : Nat) (inPlace : Bool) (ctr seed : Nat) : Option String :=
  let inA := 0x20001000 + inOff
  let outA := if inPlace then inA else 0x20002000 + outOff
  let keyA := 0x20003001; let nonceA := 0x20003103
  let msg := gen len seed; let key := gen 32 (seed + 1); let nonce := gen 12 (seed + 2)
  let run := fun (m k n : List Byte) (regs : Nat → Word) =>
    callWithRegs Release.chacha20_xor [outA, inA, len, keyA] [nonceA, ctr] [(inA, m), (keyA, k), (nonceA, n)] regs
  let r1 := run msg key nonce sentinel
  let r_res := run (gen len (seed + 50)) (gen 32 (seed + 51)) (gen 12 (seed + 52)) sentinel
  let r_ct := run (gen len (seed + 50)) (gen 32 (seed + 51)) (gen 12 (seed + 52)) sentinel2
  match r1 with
  | .error e => some e
  | .ok o =>
    let accept := counterOk ctr len
    let reads := [(inA, len), (keyA, 32), (nonceA, 12), (codeBase, codeArr.size),
      stackWin chacha20Stack 2]
    let writes := (if accept then [(outA, len)] else []) ++ [stackWin chacha20Stack 0]
    let ret := o.final.regs 0
    let tag := s!"chacha20 len {len} out+{outOff} in+{inOff} inplace {inPlace} ctr {ctr}"
    if accept ∧ ret != 0 then some s!"{tag}: returned {ret.toNat}"
    else if ¬accept ∧ ret != BitVec.ofNat 32 (2 ^ 32 - 1) then some s!"{tag}: not rejected"
    else if accept ∧ readMem o.final outA len != chacha20 key ctr nonce msg then
      some s!"{tag}: output differs from the spec"
    else ((common o reads writes chacha20Stack []) <|>
      sameResidue r1 r_res chacha20Stack <|>
      sameTrace r1 r_ct
      ).map fun e => s!"{tag}: {e}"

/-! ## AEAD -/

def aeadStack : Nat := 320

def aeadCase (len aadLen outOff inOff : Nat) (inPlace : Bool) (seed : Nat) : Option String :=
  let inA := 0x20001000 + inOff
  let outA := if inPlace then inA else 0x20002000 + outOff
  let tagA := 0x20003201; let aadA := 0x20003302; let keyA := 0x20003001; let nonceA := 0x20003103
  let pt := gen len seed; let aad := gen aadLen (seed + 3)
  let key := gen 32 (seed + 1); let nonce := gen 12 (seed + 2)
  let (ct, tag) := encrypt key nonce aad pt
  let name := s!"aead len {len} aad {aadLen} out+{outOff} in+{inOff} inplace {inPlace}"
  let reads := fun (extra : List (Nat × Nat)) => extra ++ [(inA, len), (aadA, aadLen), (keyA, 32),
    (nonceA, 12), (codeBase, codeArr.size), stackWin aeadStack 4]
  -- encrypt
  let encRun := fun (p a k n : List Byte) (regs : Nat → Word) => callWithRegs Release.chacha20poly1305_encrypt
    [outA, tagA, inA, len] [aadA, aadLen, keyA, nonceA] [(inA, p), (aadA, a), (keyA, k), (nonceA, n)] regs
  -- second secrets for residue checks (same registers) and trace checks (different caller registers)
  let pt' := gen len (seed + 50); let aad' := gen aadLen (seed + 53)
  let key' := gen 32 (seed + 51); let nonce' := gen 12 (seed + 52)
  let (ct', tag') := encrypt key' nonce' aad' pt'
  let enc1 := encRun pt aad key nonce sentinel
  let enc_res := encRun pt' aad' key' nonce' sentinel
  let enc_ct := encRun pt' aad' key' nonce' sentinel2
  let enc := match enc1 with
    | .error e => some s!"{name} encrypt: {e}"
    | .ok o =>
      if o.final.regs 0 != 0 then some s!"{name} encrypt: returned {(o.final.regs 0).toNat}"
      else if readMem o.final outA len != ct then some s!"{name} encrypt: ciphertext differs"
      else if readMem o.final tagA 16 != tag then some s!"{name} encrypt: tag differs"
      -- encrypt MACs the ciphertext as written, so it may read `out` too
      else (common o (reads [(outA, len)]) [(outA, len), (tagA, 16), stackWin aeadStack 0] aeadStack
        [1, 2, 3, 12] <|> sameResidue enc1 enc_res aeadStack <|> sameTrace enc1 enc_ct
        ).map fun e => s!"{name} encrypt: {e}"
  -- decrypt: valid, then each of a tag, ciphertext and AAD bit flip
  let decRun := fun (c a t k n : List Byte) (regs : Nat → Word) => callWithRegs Release.chacha20poly1305_decrypt
    [outA, tagA, inA, len] [aadA, aadLen, keyA, nonceA]
    ([(inA, c), (aadA, a), (tagA, t), (keyA, k), (nonceA, n)] ++
      (if inPlace then [] else [(outA, List.replicate len 0x5a#8)])) regs
  let decCase := fun (what : String) (c a t : List Byte) (valid : Bool)
      (c' a' t' : List Byte) =>
    let d1 := decRun c a t key nonce sentinel
    let d_res := decRun c' a' t' key' nonce' sentinel
    let d_ct := decRun c' a' t' key' nonce' sentinel2
    match d1 with
    | .error e => some s!"{name} decrypt {what}: {e}"
    | .ok o =>
      let r := o.final.regs 0
      let before := if inPlace then c else List.replicate len 0x5a#8
      if valid ∧ r != 0 then some s!"{name} decrypt {what}: rejected"
      else if valid ∧ readMem o.final outA len != pt then some s!"{name} decrypt {what}: plaintext differs"
      else if ¬valid ∧ r != BitVec.ofNat 32 (2 ^ 32 - 2) then some s!"{name} decrypt {what}: accepted"
      else if ¬valid ∧ readMem o.final outA len != before then some s!"{name} decrypt {what}: out written"
      else (common o (reads [(tagA, 16)]) ((if valid then [(outA, len)] else []) ++
        [stackWin aeadStack 0]) aeadStack [1, 2, 3, 12] <|>
        sameResidue d1 d_res aeadStack <|> sameTrace d1 d_ct
        ).map fun e => s!"{name} decrypt {what}: {e}"
  let flip := fun (l : List Byte) (i : Nat) => l.modify i (· ^^^ 1#8)
  enc <|> decCase "valid" ct aad tag true ct' aad' tag' <|>
    decCase "tag" ct aad (flip tag 15) false ct' aad' (flip tag' 15) <|>
    (if len > 0 then decCase "ct" (flip ct (len - 1)) aad tag false (flip ct' (len - 1)) aad' tag'
     else none) <|>
    (if aadLen > 0 then decCase "aad" ct (flip aad 0) tag false ct' (flip aad' 0) tag' else none)

/-! ## Cases and checked partitions

Partition descriptors before executing the model. Each index must occur exactly
once across the shards; the import root also checks the IDs actually scheduled.
-/

abbrev ChaCha20Args := Nat × Nat × Nat × Bool × Nat × Nat
abbrev AeadArgs := Nat × Nat × Nat × Nat × Bool × Nat

def chacha20Inputs : List ChaCha20Args :=
  let lens := [0, 1, 15, 16, 63, 64, 65, 127, 128, 129, 200]
  let aligns := [(0, 0, false), (1, 3, false), (2, 2, false), (0, 1, false), (3, 0, false),
    (0, 0, true), (1, 1, true)]
  (lens.flatMap fun l => aligns.map fun (o, i, ip) => (l, o, i, ip, 1, l)) ++
  -- Last valid block counter and the first rejected calls, unchanged from the suite.
  [(64, 0, 0, false, 2 ^ 32 - 1, 5), (65, 0, 0, false, 2 ^ 32 - 1, 6),
   (1, 0, 0, false, 2 ^ 32 - 1, 7), (129, 1, 2, false, 2 ^ 32 - 2, 8),
   (128, 0, 0, false, 2 ^ 32 - 2, 9), (0, 0, 0, false, 2 ^ 32 - 1, 10)]

def aeadInputs : List AeadArgs :=
  let shapes := [(0, 0), (0, 13), (1, 0), (15, 16), (16, 1), (17, 17), (64, 12), (65, 0), (130, 31)]
  let aligns := [(0, 0, false), (1, 3, false), (0, 2, false), (0, 0, true), (3, 3, true)]
  shapes.flatMap fun (l, a) => aligns.map fun (o, i, ip) => (l, a, o, i, ip, l + a)

def checkChaCha20 (args : ChaCha20Args) : Option String :=
  let (l, o, i, ip, ctr, seed) := args
  chacha20Case l o i ip ctr seed

def checkAead (args : AeadArgs) : Option String :=
  let (l, a, o, i, ip, seed) := args
  aeadCase l a o i ip seed

def chacha20Cases (_ : Unit) : List (Option String) := chacha20Inputs.map checkChaCha20
def aeadCases (_ : Unit) : List (Option String) := aeadInputs.map checkAead

def run (name : String) (cases : List (Option String)) : IO Unit := do
  match cases.findSome? id with
  | some e => throw (IO.userError s!"release check FAILED: {e}")
  | none => IO.println s!"release check {name}: {cases.length} cases pass"

/-- Keep original indices so duplicate or missing descriptors are detectable. -/
def partitionCases {α : Type} (count shard : Nat) (xs : List α) : List (α × Nat) :=
  xs.zipIdx.filter fun (_, i) => i % count == shard

/-- Sorting the partitioned indexed descriptors must recover the original list. -/
def coveredExactlyOnce {α : Type} [BEq α] (count : Nat) (xs : List α) : Bool :=
  (((List.range count).flatMap fun s => partitionCases count s xs).mergeSort
    fun a b => a.2 ≤ b.2) == xs.zipIdx

def chacha20ShardCount : Nat := 4
def aeadShardCount : Nat := 8

#guard chacha20Inputs.length == 83
#guard aeadInputs.length == 45
#guard coveredExactlyOnce chacha20ShardCount chacha20Inputs
#guard coveredExactlyOnce aeadShardCount aeadInputs

def runChaCha20Shard (shard : Fin chacha20ShardCount) : IO Unit :=
  run s!"chacha20 shard {shard.val}" ((partitionCases chacha20ShardCount shard.val chacha20Inputs).map
    fun (args, _) => checkChaCha20 args)

def runAeadShard (shard : Fin aeadShardCount) : IO Unit :=
  run s!"aead shard {shard.val}" ((partitionCases aeadShardCount shard.val aeadInputs).map
    fun (args, _) => checkAead args)

end M0Crypto.Thumb.ReleaseCheck
