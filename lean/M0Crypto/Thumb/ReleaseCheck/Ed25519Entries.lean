import M0Crypto.Thumb.ReleaseCheck.Ed25519Harness
import M0Crypto.Spec.Ed25519Vectors

/-!
Executable checks of the three Ed25519 entries in both builds (plan phase 5). Tests, not
proofs.

Each case writes its buffers, calls the entry with the AAPCS arguments of its `Entry`, and checks
the run with `checkResult`, a boolean form of the entry's `Result` and `WrOk`
(`Release/Ed25519Contract.lean`):

* `Returned`: the call returns to LR, SP and r4-r11 hold the caller's values;
* pubkey and sign, `Wiped`: r1-r3 and r12 zero, the window below the saved registers zero, word
  `i` of the 36 saved bytes the caller's `savedRegs[i]`;
* `MemOut`: the output holds the specification of the bytes in memory at entry
  (`publicKey`, `signWith` with the caller's public key); verify: r0 is 0 or `0xffffffff` as
  `Spec.Ed25519.verify` accepts or rejects;
* `WrOk`: every write lies in the stack window or the output, so all other memory is unchanged;
  and every read lies in the entry's `ReadRegion` (`Ed25519TraceSpec`).

`valid` checks the premises of `Valid`: arguments are words, the code and SP are 4-aligned, the
stack window does not wrap, `Frame.Disj` (no wrap, no overlap) for the code, the window and each
buffer, LR outside the code, and `len < 2^32 - 64` for sign and verify.
-/

namespace M0Crypto.Thumb.ReleaseCheck.Ed25519

open M0Crypto.Armv6M (Word Mem)
open M0Crypto.Release.Ed25519 (Build savedBytes savedRegs)
open M0Crypto.Spec.Ed25519 (hexBytes test1 test2 test3 test1024 testShaAbc msg64 msgOrder2
  sigIdentity order2 identity identityPlusP)

/-- What `Result` and `WrOk` require of a run, for an `n`-byte window. -/
structure Want where
  n : Nat
  /-- The output buffer and the bytes it must hold (empty for verify). -/
  out : Nat × List Byte := (0, [])
  wiped : Bool
  r0 : Option Word := none

def checkResult (w : Want) (r : Run) : Option String :=
  let s := r.final
  let fp := sp0 - w.n
  (r.rd) <|>
  (if reg s 13 != BitVec.ofNat 32 sp0 then some "SP not restored" else none) <|>
  (if !((List.range 8).all fun i => reg s (i + 4) == callerReg (i + 4)) then some "r4-r11 changed"
   else none) <|>
  (if w.wiped && ![1, 2, 3, 12].all (reg s · == 0) then some "r1-r3 or r12 not zero" else none) <|>
  (if w.wiped && readM s.mem fp (w.n - savedBytes) != List.replicate (w.n - savedBytes) 0 then
     some "stack window not wiped" else none) <|>
  (if w.wiped && !((List.range 9).all fun i =>
      valM s.mem (fp + w.n - savedBytes + 4 * i) 4 ==
        (if savedRegs[i]! = 14 then (retAddr ||| 1#32).toNat else (callerReg savedRegs[i]!.val).toNat))
   then some "saved registers not the caller's" else none) <|>
  writesIn r w.n [(w.out.1, w.out.2.length)] <|>
  (if readM s.mem w.out.1 w.out.2.length != w.out.2 then some "output differs from the specification"
   else none) <|>
  (match w.r0 with
   | some v => if reg s 0 != v then some s!"r0 = {reg s 0}, specification {v}" else none
   | none => none)

/-- `Frame.Disj`. -/
def disj (a n c m : Nat) : Bool := a + n ≤ 2 ^ 32 && c + m ≤ 2 ^ 32 && (a + n ≤ c || c + m ≤ a)

/-- One entry call: its buffers (first region wins), arguments, read ranges and the wanted
result from the memory at entry. -/
structure Case where
  name : String
  off : Build → Nat
  args : List Nat
  rs : List (Nat × List Byte)
  reads : List (Nat × Nat)
  /-- The buffer premises of `Pre`: stack window `n`, outputs `outs`, inputs `ins`. -/
  n : Nat
  outs : List (Nat × Nat)
  ins : List (Nat × Nat)
  /-- The message length of sign and verify. -/
  len : Nat := 0
  want : Mem → Want

/-- Only the message can be empty, and an empty one may lie anywhere (`msgS`). -/
def Case.valid (b : Build) (c : Case) : Bool :=
  let fp := sp0 - c.n
  c.args.all (· < 2 ^ 32) && c.len < 2 ^ 32 - 64 && codeBase % 4 == 0 && sp0 % 4 == 0 && c.n ≤ sp0 &&
    disj codeBase b.size fp c.n && !inRange retAddr.toNat [code b] &&
    c.outs.all (fun (a, k) => disj a k fp c.n && disj codeBase b.size a k) &&
    c.ins.all fun (a, k) => k == 0 || disj a k fp c.n

def Case.run (b : Build) (c : Case) : Except String Run :=
  callAt b (c.off b) c.args (mkMem b c.rs) c.reads c.n

def Case.check (b : Build) (c : Case) : Option String :=
  if !c.valid b then some "layout outside Pre" else
  match c.run b with
  | .error e => some e
  | .ok r => checkResult (c.want (mkMem b c.rs)) r

open M0Crypto.Release.Ed25519 in
def pubkey (name : String) (pk seed : Nat) (rs : List (Nat × List Byte)) : Case :=
  { name, off := Build.pubkeyAt, args := [pk, seed], rs, reads := [(seed, 32)],
    n := Pubkey.stackBytes, outs := [(pk, 32)], ins := [(seed, 32)],
    want := fun m => { n := Pubkey.stackBytes, wiped := true,
                       out := (pk, Spec.Ed25519.publicKey (readM m seed 32)) } }

open M0Crypto.Release.Ed25519 in
def sign (name : String) (sig msg len sk : Nat) (rs : List (Nat × List Byte)) : Case :=
  { name, off := Build.signAt, args := [sig, msg, len, sk], rs, reads := [(sk, 64), (msg, len)],
    n := Sign.stackBytes, outs := [(sig, 64)], ins := [(sk, 64), (msg, len)], len,
    want := fun m => { n := Sign.stackBytes, wiped := true, out :=
      (sig, Spec.Ed25519.signWith (readM m sk 32) (readM m (sk + 32) 32) (readM m msg len)) } }

open M0Crypto.Release.Ed25519 in
def verify (name : String) (sig msg len pk : Nat) (rs : List (Nat × List Byte)) : Case :=
  { name, off := Build.verifyAt, args := [sig, msg, len, pk], rs,
    reads := [(sig, 64), (msg, len), (pk, 32)], n := Verify.stackBytes, outs := [],
    ins := [(sig, 64), (msg, len), (pk, 32)], len,
    want := fun m =>
      { n := Verify.stackBytes, wiped := false,
        r0 := some (if Spec.Ed25519.verify (readM m sig 64) (readM m msg len) (readM m pk 32) then 0
          else 0xffffffff#32) } }

/-! ## Cases -/

def bufA : Nat := 0x20001000
def bufB : Nat := 0x20001400
def bufC : Nat := 0x20001800
/-- A message pointer inside every entry's stack window (allowed for an empty message). -/
def inWindow : Nat := sp0 - 200

def rfc : List (String × Spec.Ed25519.Vector) :=
  [("1", test1), ("2", test2), ("3", test3), ("1024", test1024), ("SHA(abc)", testShaAbc)]

/-- The accepted signature of the verdict cases: test 1's key on `msg64`. -/
def validSig : List Byte := Spec.Ed25519.sign test1.privKey msg64

def randomSig : List Byte := hexBytes
  ("38b4e652e44da7f2370d9e260e27136550a4a3a6d07f5c0c332f8b1224083fd2" ++
   "2b902f8911e81818f8c99d5d5d9831957504d90e945de2e8f54ee781cc75f636")

def pubkeyCases : List Case :=
  (rfc.map fun (t, v) => pubkey s!"pubkey RFC 8032 test {t}" bufA bufB [(bufB, v.privKey)]) ++
  [pubkey "pubkey odd pk and seed" (bufA + 3) (bufB + 1) [(bufB + 1, test2.privKey)],
   pubkey "pubkey pk = seed" bufB bufB [(bufB, test3.privKey)],
   pubkey "pubkey pk = seed + 5" (bufB + 5) bufB [(bufB, rnd 32 1)],
   pubkey "pubkey seed in the code" bufA (codeBase + 0x101) []]

def signCases : List Case :=
  (rfc.map fun (t, v) => sign s!"sign RFC 8032 test {t}" bufA bufB v.M.length bufC
    [(bufB, v.M), (bufC, v.privKey ++ v.A)]) ++
  [sign "sign caller pk not the public key" bufA bufB 16 bufC
     [(bufB, hexBytes "7265766965772063616c6c657220706b"), (bufC, test1.privKey ++ List.replicate 32 0)],
   sign "sign odd buffers" (bufA + 1) (bufB + 3) 64 (bufC + 2) [(bufB + 3, msg64), (bufC + 2, test1.privKey ++ test1.A)],
   sign "sign sig = msg, overlapping sk" bufB bufB 100 (bufB + 70) [(bufB, rnd 170 2)],
   sign "sign sig = sk" bufC bufB 5 bufC [(bufB, rnd 5 3), (bufC, test2.privKey ++ test2.A)],
   sign "sign empty message inside the stack window" bufA inWindow 0 bufC [(bufC, test3.privKey ++ test3.A)],
   sign "sign message in the code" bufA (codeBase + 3) 100 bufC [(bufC, rnd 64 4)]]

def verifyAt (name : String) (sig : List Byte) (msg : List Byte) (pk : List Byte) : Case :=
  verify s!"verify {name}" bufA bufB msg.length bufC [(bufA, sig), (bufB, msg), (bufC, pk)]

def verifyCases : List Case :=
  (rfc.map fun (t, v) => verifyAt s!"RFC 8032 test {t}" v.sig v.M v.A) ++
  [verifyAt "valid" validSig msg64 test1.A,
   verifyAt "R bit flipped" (validSig.set 0 (validSig[0]! ^^^ 1)) msg64 test1.A,
   verifyAt "S bit flipped" (validSig.set 40 (validSig[40]! ^^^ 4)) msg64 test1.A,
   verifyAt "S + L" (validSig.take 32 ++ Spec.Ed25519.encodeInt
     (Spec.Ed25519.decodeInt (validSig.drop 32) + Spec.Ed25519.L)) msg64 test1.A,
   verifyAt "message changed" validSig (msg64.set 63 0x78) test1.A,
   verifyAt "random signature" randomSig msg64 test1.A,
   verifyAt "pk = R = identity, S = 0" sigIdentity msg64 identity,
   verifyAt "pk = (0, -1)" sigIdentity msgOrder2 order2,
   verifyAt "pk = ecff..ff" sigIdentity msgOrder2 (hexBytes
     "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
   verifyAt "R = identity as y + p" (identityPlusP ++ List.replicate 32 0) msg64 identity,
   verifyAt "pk = identity as y + p" sigIdentity msg64 identityPlusP,
   verifyAt "k odd, k mod L even" sigIdentity [0x01] order2,
   verifyAt "S = L" (identity ++ Spec.Ed25519.encodeInt Spec.Ed25519.L) [] identity,
   verify "verify empty message inside the stack window" bufA inWindow 0 bufC
     [(bufA, test1.sig), (bufC, test1.A)],
   verify "verify odd buffers" (bufA + 1) (bufB + 2) 1 (bufC + 3)
     [(bufA + 1, test2.sig), (bufB + 2, test2.M), (bufC + 3, test2.A)],
   verify "verify msg = sig, pk inside sig" bufA bufA 64 (bufA + 32) [(bufA, test3.sig)],
   verify "verify message in the code" bufA (codeBase + 1) 300 bufC [(bufA, test1.sig), (bufC, test1.A)]]

def entryCases : List Case := pubkeyCases ++ signCases ++ verifyCases

/-! ## Non-vacuity: `check` rejects a wrong output, a narrower window and a wrong status word,
`valid` a wrapping output and a too long message -/

def guardsOn (pk vf : Case) (r v : Run) (b : Build) : Option String :=
  let w := pk.want (mkMem b pk.rs)
  let wv := vf.want (mkMem b vf.rs)
  let bad := [checkResult { w with out := (w.out.1, w.out.2.set 0 (w.out.2[0]! ^^^ 1)) } r,
    checkResult { w with n := w.n - 4 } r, checkResult { w with out := (w.out.1, w.out.2.take 31) } r,
    checkResult { wv with r0 := some 0xffffffff#32 } v]
  if bad.all Option.isSome then none else some "check accepts a wrong result"

def guards (b : Build) : Option String :=
  if (pubkey "" (2 ^ 32 - 16) bufB []).valid b || (sign "" bufA sp0 (2 ^ 32 - 64) bufC []).valid b then
    some "valid accepts a layout outside Valid" else
  match pubkeyCases, verifyCases with
  | pk :: _, vf :: _ =>
    match pk.run b, vf.run b with
    | .ok r, .ok v => guardsOn pk vf r v b
    | .error e, _ => some e
    | _, .error e => some e
  | _, _ => some "no cases"

end M0Crypto.Thumb.ReleaseCheck.Ed25519
