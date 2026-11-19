import M0Crypto.Release.TraceSpec
import M0Crypto.Release.Ed25519Contract

/-!
# Ed25519 trace, read and stack specifications

Statement file: definitions only. Five forms, each assuming an entry's `Pre`, the hypothesis of
its `Correct`, and each stated once for the three entries: constant time (`TraceEq`), reads
(`ReadsIn`), stack (`StackIn`), stack discipline (`DisciplineIn`) and interrupted calls
(`InterruptedIn`). The read model, stack window, discipline and interrupts are those of
`TraceSpec`, as for X25519.

Public values (C6). Pubkey and sign: the pointers, `n`, SP, LR and the code base; the seed, `sk`,
the message bytes, the caller's other registers and all other memory are secret. Verify: the
same and the bytes of `sig`, `pk` and the message; everything else is secret. Both calls of
`TraceEq` run the same build.
-/

open M0Crypto.Armv6M (Word State)
open M0Crypto.Release.TraceSpec

namespace M0Crypto.Release.Ed25519

section
variable {C P : Type} (Pre : Build → C → State → Prop) (call : C → Call)

/-- Two valid calls of the same build with equal public values `pub` produce identical traces
for all fuel values. -/
def TraceEq (pub : C → P) : Prop :=
  ∀ b c₁ c₂ s₁ s₂, Pre b c₁ s₁ → Pre b c₂ s₂ → pub c₁ = pub c₂ →
    ∀ fuel, (Thumb.runUntil (call c₁).ret fuel s₁).map Prod.snd =
            (Thumb.runUntil (call c₂).ret fuel s₂).map Prod.snd

/-- Every data read of a valid call's run lies in `Rd`. -/
def ReadsIn (Rd : Build → C → Word → Prop) : Prop :=
  ∀ b c s, Pre b c s → ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
    Thumb.runUntil (call c).ret fuel s = .ok (t, tr) ∧ ReadsFrom (Rd b c) tr

/-- At every step of a valid call, SP lies in `[sp0 - n, sp0]`. -/
def StackIn (n : Nat) : Prop :=
  ∀ b c s, Pre b c s → ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr,
    runStates (call c).ret fuel s = .ok (states, tr) ∧
      ∀ st ∈ states, InStackWindow (call c).sp0 n (st.regs 13)

/-- A valid call keeps the stack discipline over the `n` bytes below the entry SP. -/
def DisciplineIn (n : Nat) : Prop :=
  ∀ b c s, Pre b c s → ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr,
    runStates (call c).ret fuel s = .ok (states, tr) ∧ StackDiscipline (call c).sp0 n states tr

/-- A valid call that may read or write `P` returns as `InterruptedCall` states, for every
handler room `K` below its `n`-byte stack window. -/
def InterruptedIn (n : Nat) (P : Build → C → Word → Prop) (Result : C → State → Prop) : Prop :=
  ∀ K b c s, Pre b c s → InterruptedCall K n (call c).sp0 (call c).ret s (P b c) (Result c)

end

namespace Pubkey

def Ctx.pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.pk, c.seed)

/-- `seed`, the code and the stack window. -/
def ReadRegion (b : Build) (c : Ctx) (y : Word) : Prop :=
  Region c.seed 32 y ∨ Region c.base b.size y ∨ Region c.fp stackBytes y

def ConstantTime : Prop := TraceEq Pre Ctx.toCall Ctx.pub
def Reads : Prop := ReadsIn Pre Ctx.toCall ReadRegion
def Stack : Prop := StackIn Pre Ctx.toCall stackBytes
def StackDiscipline : Prop := DisciplineIn Pre Ctx.toCall stackBytes
def Interrupted : Prop :=
  InterruptedIn Pre Ctx.toCall stackBytes (fun b c y => ReadRegion b c y ∨ WrOk c y) Result

end Pubkey

namespace Sign

def Ctx.pub (c : Ctx) := (c.base, c.sp0, c.regs0 14, c.sig, c.msg, c.len, c.sk)

/-- `sk`, the message, the code and the stack window. -/
def ReadRegion (b : Build) (c : Ctx) (y : Word) : Prop :=
  Region c.sk 64 y ∨ Region c.msg c.len.toNat y ∨ Region c.base b.size y ∨
  Region c.fp stackBytes y

def ConstantTime : Prop := TraceEq Pre Ctx.toCall Ctx.pub
def Reads : Prop := ReadsIn Pre Ctx.toCall ReadRegion
def Stack : Prop := StackIn Pre Ctx.toCall stackBytes
def StackDiscipline : Prop := DisciplineIn Pre Ctx.toCall stackBytes
def Interrupted : Prop :=
  InterruptedIn Pre Ctx.toCall stackBytes (fun b c y => ReadRegion b c y ∨ WrOk c y) Result

end Sign

namespace Verify

/-- Verify is variable time (C4): its trace may depend on every input byte, and on nothing else. -/
def Ctx.pub (c : Ctx) :=
  (c.base, c.sp0, c.regs0 14, c.sig, c.msg, c.len, c.pk, c.sigB, c.msgB, c.pkB)

/-- `sig`, the message, `pk`, the code and the stack window. -/
def ReadRegion (b : Build) (c : Ctx) (y : Word) : Prop :=
  Region c.sig 64 y ∨ Region c.msg c.len.toNat y ∨ Region c.pk 32 y ∨
  Region c.base b.size y ∨ Region c.fp stackBytes y

def ConstantTime : Prop := TraceEq Pre Ctx.toCall Ctx.pub
def Reads : Prop := ReadsIn Pre Ctx.toCall ReadRegion
def Stack : Prop := StackIn Pre Ctx.toCall stackBytes
def StackDiscipline : Prop := DisciplineIn Pre Ctx.toCall stackBytes
def Interrupted : Prop :=
  InterruptedIn Pre Ctx.toCall stackBytes (fun b c y => ReadRegion b c y ∨ WrOk c y) Result

end Verify

end M0Crypto.Release.Ed25519
