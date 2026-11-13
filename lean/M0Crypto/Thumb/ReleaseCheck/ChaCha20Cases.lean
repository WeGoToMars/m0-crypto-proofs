import M0Crypto.Thumb.ReleaseCheck.Cases
import M0Crypto.Spec.Aead

/-!
Executable checks of `m0c_chacha20_xor`, `m0c_chacha20poly1305_encrypt` and
`m0c_chacha20poly1305_decrypt` in the whole-function model (harness: `Cases`): the result
against the RFC 8439 specification (`M0Crypto.Spec.Aead`); reads only from the input buffers,
key, nonce, AAD, tag, code and stack window; writes only to `out`, the tag (encrypt) and the
stack below the entry SP; rejected calls (counter overflow, authentication failure) write
nothing outside the stack.
-/

namespace M0Crypto.Thumb.ReleaseCheck

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Spec.Aead
open M0Crypto.Spec.ChaCha20 (Byte)
open M0Crypto.Artifacts

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

/-! ## Pairwise constant-time checks -/

/-- Pairwise ChaCha20 trace equality with different keys, nonces, inputs, caller registers. -/
def chacha20TraceEqual (_ : Unit) : Bool :=
  let o1 := callWithRegs Release.chacha20_xor [0x20002000, 0x20001000, 64, 0x20003000]
    [0x20003100, 1] [(0x20001000, gen 64 1), (0x20003000, gen 32 2), (0x20003100, gen 12 3)] sentinel
  let o2 := callWithRegs Release.chacha20_xor [0x20002000, 0x20001000, 64, 0x20003000]
    [0x20003100, 1] [(0x20001000, gen 64 10), (0x20003000, gen 32 20), (0x20003100, gen 12 30)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

/-- Pairwise Encrypt trace equality with different keys, nonces, plaintexts, AAD, caller registers. -/
def encryptTraceEqual (_ : Unit) : Bool :=
  let o1 := callWithRegs Release.chacha20poly1305_encrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, gen 32 1), (0x20003300, gen 16 2), (0x20003000, gen 32 3), (0x20003100, gen 12 4)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_encrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, gen 32 10), (0x20003300, gen 16 20), (0x20003000, gen 32 30), (0x20003100, gen 12 40)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

/-- Pairwise Decrypt trace equality when both calls accept. -/
def decryptAcceptTraceEqual (_ : Unit) : Bool :=
  let k1 := gen 32 1; let n1 := gen 12 2; let a1 := gen 16 3; let p1 := gen 32 4
  let (ct1, t1) := encrypt k1 n1 a1 p1
  let k2 := gen 32 10; let n2 := gen 12 20; let a2 := gen 16 30; let p2 := gen 32 40
  let (ct2, t2) := encrypt k2 n2 a2 p2
  let o1 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct1), (0x20003300, a1), (0x20003200, t1), (0x20003000, k1), (0x20003100, n1)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct2), (0x20003300, a2), (0x20003200, t2), (0x20003000, k2), (0x20003100, n2)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

/-- Pairwise Decrypt trace equality when both calls reject. -/
def decryptRejectTraceEqual (_ : Unit) : Bool :=
  let k1 := gen 32 1; let n1 := gen 12 2; let a1 := gen 16 3; let p1 := gen 32 4
  let (ct1, t1) := encrypt k1 n1 a1 p1
  let badTag1 := t1.modify 0 (· ^^^ 1#8)
  let k2 := gen 32 10; let n2 := gen 12 20; let a2 := gen 16 30; let p2 := gen 32 40
  let (ct2, t2) := encrypt k2 n2 a2 p2
  let badTag2 := t2.modify 0 (· ^^^ 1#8)
  let o1 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct1), (0x20003300, a1), (0x20003200, badTag1), (0x20003000, k1), (0x20003100, n1)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct2), (0x20003300, a2), (0x20003200, badTag2), (0x20003000, k2), (0x20003100, n2)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

/-- Decryptions with different verdicts take different traces.
This documents why the declassification is needed and that it is the only one. -/
def decryptVerdictTraceDiffers (_ : Unit) : Bool :=
  let k := gen 32 1; let n := gen 12 2; let a := gen 16 3; let p := gen 32 4
  let (ct, tag) := encrypt k n a p
  let badTag := tag.modify 0 (· ^^^ 1#8)
  let oAccept := call Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct), (0x20003300, a), (0x20003200, tag), (0x20003000, k), (0x20003100, n)]
  let oReject := call Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct), (0x20003300, a), (0x20003200, badTag), (0x20003000, k), (0x20003100, n)]
  match oAccept, oReject with
  | .ok rA, .ok rR => rA.trace != rR.trace
  | _, _ => false

def pairwiseCases (_ : Unit) : List (Option String) :=
  [guardCase "chacha20 traces differ" (chacha20TraceEqual ()),
   guardCase "encrypt traces differ" (encryptTraceEqual ()),
   guardCase "accepting decrypt traces differ" (decryptAcceptTraceEqual ()),
   guardCase "rejecting decrypt traces differ" (decryptRejectTraceEqual ()),
   guardCase "accept and reject decrypt traces are equal" (decryptVerdictTraceDiffers ())]

/-- Every check that the shard modules and `ChaCha20Pairwise` `#eval`. -/
def allChecks : List (IO Unit) :=
  (List.finRange chacha20ShardCount).map runChaCha20Shard ++
  (List.finRange aeadShardCount).map runAeadShard ++ [run "pairwise" (pairwiseCases ())]

end M0Crypto.Thumb.ReleaseCheck
