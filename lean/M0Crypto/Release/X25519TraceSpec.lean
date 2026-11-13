import M0Crypto.Release.TraceSpec
import M0Crypto.Release.X25519Contract

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release

namespace M0Crypto.Release.X25519.Ctx

/-- Inputs of an X25519 call an observer may know: link base, entry SP, LR and the three
pointers. The scalar and point bytes, the caller's other registers and all other memory are
secret. -/
def pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.out, c.scalar, c.point)

end M0Crypto.Release.X25519.Ctx

namespace M0Crypto.Release.TraceSpec

/-!
# X25519 trace, read and stack specifications

Statement file: definitions only. Each assumes a valid call (`X25519.Pre`), the hypothesis of
`X25519.x25519_correct`. The read model and stack window are in `TraceSpec`.
-/

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
