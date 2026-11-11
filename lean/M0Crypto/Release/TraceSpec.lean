import M0Crypto.Release.Frame
import M0Crypto.Release.ChaCha20Setup
import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.AeadPrologue
import M0Crypto.Release.AeadCrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.RunStates
import M0Crypto.Release.TraceSpecDefs

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Aead
open M0Crypto.Release

namespace M0Crypto.Release.Frame.Ctx

/-- Inputs of a ChaCha20 call an observer may know: entry SP, LR, link base, every
pointer, length and block counter. Buffer contents, the caller's r4-r11/r12 and all
other memory are secret. -/
def pub (c : Ctx) :=
  (c.base, c.sp0, c.regs0 14, c.out, c.inp, c.len, c.key, c.nonce, c.ctr)

/-- Return address of a ChaCha20 call. -/
def ret (c : Ctx) : Word := c.regs0 14 &&& ~~~1#32

end M0Crypto.Release.Frame.Ctx

namespace M0Crypto.Release.Aead.ACall

/-- Inputs of an AEAD call an observer may know: entry SP, LR, link base, and every
pointer and length argument. Buffer contents, the caller's r4-r11/r12 and all other
memory are secret. -/
def pub (c : ACall) :=
  (c.base, c.sp0, c.regs0 14, c.out, c.tag, c.inp, c.len, c.aad, c.alen, c.key, c.nonce)

/-- Return address of an AEAD call. -/
def ret (c : ACall) : Word := c.regs0 14 &&& ~~~1#32

/-- Decryption acceptance verdict: whether computed tag equals provided tag. -/
def verdict (c : ACall) : Prop := c.expected = c.tagB

end M0Crypto.Release.Aead.ACall

namespace M0Crypto.Release.TraceSpec

/-!
# Constant-time trace, read and stack specifications

This file contains specification statements only (`def ... : Prop`, no proofs).
It states the properties proved for the three public entry points:
- `m0c_chacha20_xor`
- `m0c_chacha20poly1305_encrypt`
- `m0c_chacha20poly1305_decrypt`

Under the functional entry contracts:
1. Constant-time trace independence (equal traces for equal public inputs; decrypt also
   conditioned on equal authentication verdict).
2. Read bounds (all reads are confined to the caller-provided buffers, code and stack window;
   the decryption bound also admits the output buffer).
3. Stack bounds (SP remains within the entry's stack window at every step).
-/

/-! The named stack bound constants `aeadStackBytes` and `chacha20StackBytes` are in
`TraceSpecDefs`. -/

/-! ## Read access model -/

/-- Byte addresses read by an access list. -/
def Reads (acc : List Access) (y : Word) : Prop :=
  ∃ a ∈ acc, a.kind = .read ∧ ∃ k < a.width, y = a.addr + BitVec.ofNat 32 k

/-- Every read of the trace lies in `Rd`. -/
def ReadsFrom (Rd : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y

/-- Allowed readable regions for `m0c_chacha20_xor`: input buffer, key, nonce,
code, and the function's stack window including caller stack arguments. -/
def ChaCha20XorReadRegion (c : Ctx) (y : Word) : Prop :=
  (∃ o < c.len.toNat, y = c.inp + BitVec.ofNat 32 o) ∨
  (∃ o < 32, y = c.key + BitVec.ofNat 32 o) ∨
  (∃ o < 12, y = c.nonce + BitVec.ofNat 32 o) ∨
  (∃ o < Artifacts.Release.size, y = c.base + BitVec.ofNat 32 o) ∨
  (∃ o < ChaCha20Layout.chStackBytes + 8,
    y = c.sp0 - BitVec.ofNat 32 ChaCha20Layout.chStackBytes + BitVec.ofNat 32 o)


/-- Allowed readable regions for `m0c_chacha20poly1305_encrypt`: input buffer, AAD, key,
nonce, output buffer (MAC reads ciphertext), code, and the AEAD stack window including
caller stack arguments. -/
def AeadEncryptReadRegion (c : ACall) (y : Word) : Prop :=
  (∃ o < c.len.toNat, y = c.inp + BitVec.ofNat 32 o) ∨
  (∃ o < c.alen.toNat, y = c.aad + BitVec.ofNat 32 o) ∨
  (∃ o < 32, y = c.key + BitVec.ofNat 32 o) ∨
  (∃ o < 12, y = c.nonce + BitVec.ofNat 32 o) ∨
  (∃ o < c.len.toNat, y = c.out + BitVec.ofNat 32 o) ∨
  (∃ o < Artifacts.Release.size, y = c.base + BitVec.ofNat 32 o) ∨
  (∃ o < aeadStackBytes + 16,
    y = c.sp0 - BitVec.ofNat 32 aeadStackBytes + BitVec.ofNat 32 o)


/-- Allowed readable regions for `m0c_chacha20poly1305_decrypt`: the encrypt set plus
tag[0, 16). This over-approximates what decryption reads (it also admits `out[0, len)`; the proof
does not show that decryption avoids it); the claim bounds the set of read addresses, not their order. -/
def AeadDecryptReadRegion (c : ACall) (y : Word) : Prop :=
  AeadEncryptReadRegion c y ∨ (∃ o < 16, y = c.tag + BitVec.ofNat 32 o)


/-! ## Stack window containment -/

/-- SP lies in the entry's stack window `[sp0 - stackBytes, sp0]`. -/
def InStackWindow (sp0 : Word) (stackBytes : Nat) (sp : Word) : Prop :=
  ∃ o ≤ stackBytes, sp = sp0 - BitVec.ofNat 32 o

/-! ## ChaCha20 specifications -/

/-- ChaCha20 constant-time trace theorem: executions from two valid entry states with
equal public inputs produce identical traces for all fuel values. -/
def ChaCha20XorConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂,
    Valid c₁ → ChaCha20Setup.Entry c₁ s₁ → (c₁.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₁.ret ≠ c₁.base + BitVec.ofNat 32 i) →
    Valid c₂ → ChaCha20Setup.Entry c₂ s₂ → (c₂.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₂.ret ≠ c₂.base + BitVec.ofNat 32 i) →
    c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd


/-- ChaCha20 read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def ChaCha20XorReads : Prop :=
  ∀ c s,
    Valid c → ChaCha20Setup.Entry c s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (ChaCha20XorReadRegion c) tr


/-- ChaCha20 stack bounds: at every step of execution, SP remains within `[sp0 - 176, sp0]`. -/
def ChaCha20XorStack : Prop :=
  ∀ c s,
    Valid c → ChaCha20Setup.Entry c s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 ChaCha20Layout.chStackBytes (st.regs 13)


/-! ## AEAD encrypt specifications -/

/-- AEAD encrypt constant-time trace theorem: executions from two valid entry states with
equal public inputs produce identical traces for all fuel values. -/
def AeadEncryptConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂,
    AValid c₁ → ABuf c₁ → AEntry c₁ encOff s₁ → (c₁.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₁.ret ≠ c₁.base + BitVec.ofNat 32 i) →
    AValid c₂ → ABuf c₂ → AEntry c₂ encOff s₂ → (c₂.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₂.ret ≠ c₂.base + BitVec.ofNat 32 i) →
    c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- AEAD encrypt read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def AeadEncryptReads : Prop :=
  ∀ c s,
    AValid c → ABuf c → AEntry c encOff s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (AeadEncryptReadRegion c) tr

/-- AEAD encrypt stack bounds: at every step of execution, SP remains within `[sp0 - 320, sp0]`. -/
def AeadEncryptStack : Prop :=
  ∀ c s,
    AValid c → ABuf c → AEntry c encOff s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 aeadStackBytes (st.regs 13)

/-! ## AEAD decrypt specifications -/

/-- AEAD decrypt constant-time trace theorem: executions from two valid entry states with
equal public inputs and equal authentication verdicts produce identical traces for all fuel values. -/
def AeadDecryptConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂,
    AValid c₁ → ABuf c₁ → AEntry c₁ decOff s₁ → (c₁.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₁.ret ≠ c₁.base + BitVec.ofNat 32 i) →
    AValid c₂ → ABuf c₂ → AEntry c₂ decOff s₂ → (c₂.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c₂.ret ≠ c₂.base + BitVec.ofNat 32 i) →
    c₁.pub = c₂.pub →
    (c₁.verdict = c₂.verdict) →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- AEAD decrypt read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def AeadDecryptReads : Prop :=
  ∀ c s,
    AValid c → ABuf c → AEntry c decOff s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (AeadDecryptReadRegion c) tr

/-- AEAD decrypt stack bounds: at every step of execution, SP remains within `[sp0 - 320, sp0]`. -/
def AeadDecryptStack : Prop :=
  ∀ c s,
    AValid c → ABuf c → AEntry c decOff s → (c.regs0 14).getLsbD 0 = true →
    (∀ i < Artifacts.Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i) →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 aeadStackBytes (st.regs 13)

end M0Crypto.Release.TraceSpec
