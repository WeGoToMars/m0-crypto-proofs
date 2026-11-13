import M0Crypto.Release.TraceSpec
import M0Crypto.Release.Blake2sContract

open M0Crypto.Armv6M (Word)
open M0Crypto.Thumb
open M0Crypto.Release

/-! ## Public inputs -/

namespace M0Crypto.Release.Blake2s.Init.Ctx

/-- Inputs of an `init` call an observer may know: link base, entry SP, LR and the context
pointer. The context bytes, the caller's other registers and all other memory are secret. -/
def pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.context)

end M0Crypto.Release.Blake2s.Init.Ctx

namespace M0Crypto.Release.Blake2s.Update.Ctx

/-- Inputs of an `update` call an observer may know: link base, entry SP, LR, the context and
input pointers, the input length, and the number of bytes the context holds pending (its `used`
word, a function of the lengths absorbed so far). The input bytes, the chain value, the byte
count, the pending bytes, the caller's other registers and all other memory are secret. -/
def pub (c : Ctx) :=
  (c.base, c.sp0, c.regs0 14, c.context, c.input, c.len, c.stream.pending.length)

end M0Crypto.Release.Blake2s.Update.Ctx

namespace M0Crypto.Release.Blake2s.Final.Ctx

/-- Inputs of a `final` call an observer may know: link base, entry SP, LR, the context and
output pointers, and the number of bytes the context holds pending. The chain value, the byte
count, the pending bytes, the caller's other registers and all other memory are secret. -/
def pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.context, c.out, c.stream.pending.length)

end M0Crypto.Release.Blake2s.Final.Ctx

namespace M0Crypto.Release.TraceSpec

/-!
# BLAKE2s trace, read and stack specifications

Statement file: definitions only. Each assumes a valid call (`Blake2s.Init.Pre`,
`Blake2s.Update.Pre`, `Blake2s.Final.Pre`), the hypothesis of the function's correctness theorem.
The read model and stack window are in `TraceSpec`. The stack bounds include the frames of the
internal callees `m0c_blake2s_compress` and `m0c_blake2s_copy`.
-/

open M0Crypto.Release.Blake2s (contextBytes initStackBytes streamStackBytes)

/-! ## `m0c_blake2s_init` -/

/-- Allowed readable regions for `init`: code and the call's stack window. -/
def Blake2sInitReadRegion (c : Blake2s.Init.Ctx) (y : Word) : Prop :=
  Region c.base Artifacts.Release.size y ∨ Region c.fp initStackBytes y

/-- `init` constant-time trace theorem: two valid calls with equal public inputs produce
identical traces for all fuel values. -/
def Blake2sInitConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, Blake2s.Init.Pre c₁ s₁ → Blake2s.Init.Pre c₂ s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- `init` read bounds: every data read in the execution trace lies in the allowed regions. -/
def Blake2sInitReads : Prop :=
  ∀ c s, Blake2s.Init.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (Blake2sInitReadRegion c) tr

/-- `init` stack bounds: at every step of execution, SP remains within `[sp0 - 4, sp0]`. -/
def Blake2sInitStack : Prop :=
  ∀ c s, Blake2s.Init.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 initStackBytes (st.regs 13)

/-! ## `m0c_blake2s_update` -/

/-- Allowed readable regions for `update`: the context, the input, code and the call's stack
window. -/
def Blake2sUpdateReadRegion (c : Blake2s.Update.Ctx) (y : Word) : Prop :=
  Region c.context contextBytes y ∨ Region c.input c.len.toNat y ∨
  Region c.base Artifacts.Release.size y ∨ Region c.fp streamStackBytes y

/-- `update` constant-time trace theorem: two valid calls with equal public inputs produce
identical traces for all fuel values. -/
def Blake2sUpdateConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, Blake2s.Update.Pre c₁ s₁ → Blake2s.Update.Pre c₂ s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- `update` read bounds: every data read in the execution trace lies in the allowed regions. -/
def Blake2sUpdateReads : Prop :=
  ∀ c s, Blake2s.Update.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (Blake2sUpdateReadRegion c) tr

/-- `update` stack bounds: at every step of execution, SP remains within `[sp0 - 160, sp0]`. -/
def Blake2sUpdateStack : Prop :=
  ∀ c s, Blake2s.Update.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 streamStackBytes (st.regs 13)

/-! ## `m0c_blake2s_final` -/

/-- Allowed readable regions for `final`: the context, code and the call's stack window. -/
def Blake2sFinalReadRegion (c : Blake2s.Final.Ctx) (y : Word) : Prop :=
  Region c.context contextBytes y ∨ Region c.base Artifacts.Release.size y ∨
  Region c.fp streamStackBytes y

/-- `final` constant-time trace theorem: two valid calls with equal public inputs produce
identical traces for all fuel values. -/
def Blake2sFinalConstantTime : Prop :=
  ∀ c₁ c₂ s₁ s₂, Blake2s.Final.Pre c₁ s₁ → Blake2s.Final.Pre c₂ s₂ → c₁.pub = c₂.pub →
    ∀ fuel, (Thumb.runUntil c₁.ret fuel s₁).map Prod.snd =
            (Thumb.runUntil c₂.ret fuel s₂).map Prod.snd

/-- `final` read bounds: every data read in the execution trace lies in the allowed regions. -/
def Blake2sFinalReads : Prop :=
  ∀ c s, Blake2s.Final.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ t tr, Thumb.runUntil c.ret fuel s = .ok (t, tr) ∧ ReadsFrom (Blake2sFinalReadRegion c) tr

/-- `final` stack bounds: at every step of execution, SP remains within `[sp0 - 160, sp0]`. -/
def Blake2sFinalStack : Prop :=
  ∀ c s, Blake2s.Final.Pre c s →
    ∃ n, ∀ fuel, n ≤ fuel →
      ∃ states tr, runStates c.ret fuel s = .ok (states, tr) ∧
        ∀ st ∈ states, InStackWindow c.sp0 streamStackBytes (st.regs 13)

end M0Crypto.Release.TraceSpec
