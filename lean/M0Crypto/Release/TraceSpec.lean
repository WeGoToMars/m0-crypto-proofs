import M0Crypto.Release.ChaCha20Contract
import M0Crypto.Release.AeadContract
import M0Crypto.Release.X25519Contract

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

end M0Crypto.Release.Frame.Ctx

namespace M0Crypto.Release.Aead.ACall

/-- Inputs of an AEAD call an observer may know: entry SP, LR, link base, and every
pointer and length argument. Buffer contents, the caller's r4-r11/r12 and all other
memory are secret. -/
def pub (c : ACall) :=
  (c.base, c.sp0, c.regs0 14, c.out, c.tag, c.inp, c.len, c.aad, c.alen, c.key, c.nonce)

/-- Decryption acceptance verdict: whether computed tag equals provided tag. -/
def verdict (c : ACall) : Prop := c.expected = c.tagB

end M0Crypto.Release.Aead.ACall

namespace M0Crypto.Release.X25519.Ctx

/-- Inputs of an X25519 call an observer may know: link base, entry SP, LR and the three
pointers. The scalar and point bytes, the caller's other registers and all other memory are
secret. -/
def pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.out, c.scalar, c.point)

end M0Crypto.Release.X25519.Ctx

namespace M0Crypto.Release.TraceSpec

/-!
# Constant-time trace, read and stack specifications

This file contains specification statements only (`def ... : Prop`, no proofs).
It states the properties proved for these public entry points:
- `m0c_chacha20_xor`
- `m0c_chacha20poly1305_encrypt`
- `m0c_chacha20poly1305_decrypt`
- `m0c_x25519`

Each assumes a valid call (`ChaCha20Xor.Pre`, `Aead.APre`, `X25519.Pre`), the same hypothesis as the
functional theorems:
1. Constant-time trace independence (equal traces for equal public inputs; decrypt also
   conditioned on equal authentication verdict).
2. Read bounds (all reads are confined to the caller-provided buffers, code and stack window;
   the decryption bound also admits the output buffer).
3. Stack bounds (SP remains within the entry's stack window at every step).
-/

/-- Stack bytes allocated by the AEAD entry points (`m0c_chacha20poly1305_encrypt`
and `m0c_chacha20poly1305_decrypt`), matching `AValid.spLo`. -/
def aeadStackBytes : Nat := 320

/-! ## Read access model -/

/-- Every read of the trace lies in `Rd`. -/
def ReadsFrom (Rd : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y

/-- Allowed readable regions for `m0c_chacha20_xor`: input buffer, key, nonce,
code, and the function's stack window including the 8 bytes of caller stack arguments. -/
def ChaCha20XorReadRegion (c : Ctx) (y : Word) : Prop :=
  Region c.inp c.len.toNat y ∨ Region c.key 32 y ∨ Region c.nonce 12 y ∨
  Region c.base Artifacts.Release.size y ∨
  Region c.fp (ChaCha20Layout.chStackBytes + 8) y

/-- Allowed readable regions for `m0c_chacha20poly1305_encrypt`: input buffer, AAD, key,
nonce, output buffer (MAC reads ciphertext), code, and the AEAD stack window including
the 16 bytes of caller stack arguments. -/
def AeadEncryptReadRegion (c : ACall) (y : Word) : Prop :=
  Region c.inp c.len.toNat y ∨ Region c.aad c.alen.toNat y ∨ Region c.key 32 y ∨
  Region c.nonce 12 y ∨ Region c.out c.len.toNat y ∨
  Region c.base Artifacts.Release.size y ∨
  Region (c.sp0 - BitVec.ofNat 32 aeadStackBytes) (aeadStackBytes + 16) y

/-- Allowed readable regions for `m0c_chacha20poly1305_decrypt`: the encrypt set plus
tag[0, 16). This over-approximates what decryption reads (it also admits `out[0, len)`; the proof
does not show that decryption avoids it); the claim bounds the set of read addresses, not their order. -/
def AeadDecryptReadRegion (c : ACall) (y : Word) : Prop :=
  AeadEncryptReadRegion c y ∨ Region c.tag 16 y

/-! ## Stack window containment -/

/-- SP lies in the entry's stack window `[sp0 - stackBytes, sp0]`. -/
def InStackWindow (sp0 : Word) (stackBytes : Nat) (sp : Word) : Prop :=
  ∃ o ≤ stackBytes, sp = sp0 - BitVec.ofNat 32 o

/-! ## ChaCha20 specifications -/

/-- ChaCha20 constant-time trace theorem: two valid calls with equal public inputs produce
identical traces for all fuel values. -/
def ChaCha20XorConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, ChaCha20Xor.Pre c₁ s₁ → ChaCha20Xor.Pre c₂ s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- ChaCha20 read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def ChaCha20XorReads : Prop :=
  ∀ c s, ChaCha20Xor.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (ChaCha20XorReadRegion c) tr

/-- ChaCha20 stack bounds: at every step of execution, SP remains within `[sp0 - 176, sp0]`. -/
def ChaCha20XorStack : Prop :=
  ∀ c s, ChaCha20Xor.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 ChaCha20Layout.chStackBytes (st.regs 13)

/-! ## AEAD encrypt specifications -/

/-- AEAD encrypt constant-time trace theorem: two valid calls with equal public inputs
produce identical traces for all fuel values. -/
def AeadEncryptConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, APre c₁ encOff s₁ → APre c₂ encOff s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- AEAD encrypt read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def AeadEncryptReads : Prop :=
  ∀ c s, APre c encOff s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (AeadEncryptReadRegion c) tr

/-- AEAD encrypt stack bounds: at every step of execution, SP remains within `[sp0 - 320, sp0]`. -/
def AeadEncryptStack : Prop :=
  ∀ c s, APre c encOff s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 aeadStackBytes (st.regs 13)

/-! ## AEAD decrypt specifications -/

/-- AEAD decrypt constant-time trace theorem: two valid calls with equal public inputs and
equal authentication verdicts produce identical traces for all fuel values. -/
def AeadDecryptConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, APre c₁ decOff s₁ → APre c₂ decOff s₂ → c₁.pub = c₂.pub →
    c₁.verdict = c₂.verdict →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- AEAD decrypt read bounds: every data read in the execution trace lies in the
caller-provided readable regions. -/
def AeadDecryptReads : Prop :=
  ∀ c s, APre c decOff s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (AeadDecryptReadRegion c) tr

/-- AEAD decrypt stack bounds: at every step of execution, SP remains within `[sp0 - 320, sp0]`. -/
def AeadDecryptStack : Prop :=
  ∀ c s, APre c decOff s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 aeadStackBytes (st.regs 13)

/-! ## X25519 specifications (claims X4-X6) -/

/-- Allowed readable regions for `m0c_x25519`: `scalar`, `point`, code and the call's stack
window. -/
def X25519ReadRegion (c : X25519.Ctx) (y : Word) : Prop :=
  Region c.scalar 32 y ∨ Region c.point 32 y ∨ Region c.base Artifacts.Release.size y ∨
  Region c.fp X25519.stackBytes y

/-- X25519 constant-time trace theorem: two valid calls with equal public inputs produce
identical traces for all fuel values. -/
def X25519ConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, X25519.Pre c₁ s₁ → X25519.Pre c₂ s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- X25519 read bounds: every data read in the execution trace lies in the allowed regions. -/
def X25519Reads : Prop :=
  ∀ c s, X25519.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (X25519ReadRegion c) tr

/-- X25519 stack bounds: at every step of execution, SP remains within `[sp0 - 516, sp0]`. -/
def X25519Stack : Prop :=
  ∀ c s, X25519.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 X25519.stackBytes (st.regs 13)

end M0Crypto.Release.TraceSpec
