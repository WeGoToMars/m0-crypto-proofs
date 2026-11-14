import M0Crypto.Release.Contract

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

namespace M0Crypto.Release.TraceSpec

/-!
# Shared vocabulary of the trace specifications

Statement file: definitions only. The read model (`ReadsFrom`), the stack window
(`InStackWindow`), the stack discipline (`StackDiscipline`) and interrupted calls
(`InterruptedCall`) used by the per-function trace specifications: `ChaCha20TraceSpec`
(`m0c_chacha20_xor` and the AEAD entry points), `Blake2sTraceSpec` and `X25519TraceSpec`
(`m0c_x25519`).
-/

/-! ## Read access model -/

/-- Every read of the trace lies in `Rd`. -/
def ReadsFrom (Rd : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y

/-! ## Stack window containment -/

/-- SP lies in the entry's stack window `[sp0 - stackBytes, sp0]`. -/
def InStackWindow (sp0 : Word) (stackBytes : Nat) (sp : Word) : Prop :=
  ∃ o ≤ stackBytes, sp = sp0 - BitVec.ofNat 32 o

/-! ## Stack discipline

A run is the list of its states and the list of its events: step `k` goes from `states[k]` to
`states[k + 1]` with event `tr[k]`. -/

/-- `y` is one of the `n` bytes below `sp0`. -/
def BelowEntry (sp0 : Word) (n : Nat) (y : Word) : Prop :=
  Region (sp0 - BitVec.ofNat 32 n) n y

/-- `y` lies at or above `sp` and below `sp0`. -/
def AtOrAboveSp (sp0 sp y : Word) : Prop := Region sp (sp0 - sp).toNat y

/-- Every byte that a step reads or writes among the `n` bytes below `sp0` lies at or above
the SP before the step or the SP after it. -/
def StackAccessesAboveSp (sp0 : Word) (n : Nat) (states : List State) (tr : List Event) : Prop :=
  ∀ k e u u', tr[k]? = some e → states[k]? = some u → states[k + 1]? = some u' →
    ∀ y, (Reads e.accesses y ∨ Writes e.accesses y) → BelowEntry sp0 n y →
      AtOrAboveSp sp0 u.sp y ∨ AtOrAboveSp sp0 u'.sp y

/-- Byte `y` was written by a step `j < k`, and SP was at or below `y` in every state from
`states[j + 1]` to `states[k]`. -/
def WrittenSinceAllocated (sp0 : Word) (states : List State) (tr : List Event) (k : Nat)
    (y : Word) : Prop :=
  ∃ j < k, (∃ e, tr[j]? = some e ∧ Writes e.accesses y) ∧
    ∀ i u, j < i → i ≤ k → states[i]? = some u → AtOrAboveSp sp0 u.sp y

/-- Every byte that a step `k` reads among the `n` bytes below `sp0` was written since SP last
moved to or below it. -/
def StackReadsWritten (sp0 : Word) (n : Nat) (states : List State) (tr : List Event) : Prop :=
  ∀ k e, tr[k]? = some e → ∀ y, Reads e.accesses y → BelowEntry sp0 n y →
    WrittenSinceAllocated sp0 states tr k y

/-- The stack discipline of a run below the entry SP `sp0`, over the `n` bytes of its stack
window: accesses at or above SP, and reads only of bytes written since they were allocated. -/
def StackDiscipline (sp0 : Word) (n : Nat) (states : List State) (tr : List Event) : Prop :=
  StackAccessesAboveSp sp0 n states tr ∧ StackReadsWritten sp0 n states tr

/-! ## Interrupts

A handler may run before any instruction of a call. It is modelled by its effect alone: it
restores every register and flag, and it preserves every byte the call may read or write (`P`)
outside the `K` bytes below SP. -/

/-- `t'` has the registers and flags of `t`, and its memory on the bytes of `Q`. -/
def SameOn (Q : Word → Prop) (t t' : State) : Prop :=
  t'.regs = t.regs ∧ t'.n = t.n ∧ t'.z = t.z ∧ t'.c = t.c ∧ t'.v = t.v ∧
    ∀ y, Q y → t'.mem y = t.mem y

/-- `H k` is the handler run before the `k`-th instruction of a call (the identity when no
interrupt is taken there). Run in a state `s`, it restores every register and flag and preserves
every byte of `P` outside the `K` bytes below SP. -/
def Handlers (K : Nat) (P : Word → Prop) (H : Nat → State → State) : Prop :=
  ∀ k s, SameOn (fun y => P y ∧ ¬ Region (s.sp - BitVec.ofNat 32 K) K y) s (H k s)

/-- `runStates` with the handler `H k` run before the `k`-th instruction, counting from `k`.
The states are those before each handler; the events are the call's own steps. -/
def irunStates (H : Nat → State → State) (stop : Word) :
    Nat → Nat → State → Except Fault (List State × List Event)
  | fuel, k, s =>
    if s.pc = stop then .ok ([s], [])
    else match fuel with
      | 0 => .error .fuel
      | n + 1 =>
        match step (H k s) with
        | .error e => .error e
        | .ok (s', e) =>
          match irunStates H stop n (k + 1) s' with
          | .error e' => .error e'
          | .ok (states, es) => .ok (s :: states, e :: es)

/-- The `K` bytes below a call's `n`-byte stack window lie above address 0 and hold no byte in
`P`, the bytes the call may read or write. -/
def HandlerRoom (K n : Nat) (sp0 : Word) (P : Word → Prop) : Prop :=
  n + K ≤ sp0.toNat ∧ ∀ y, Region (sp0 - BitVec.ofNat 32 (n + K)) K y → ¬ P y

/-- A call from `s` with an `n`-byte stack window below `sp0`, that may read or write the bytes
`P`, with handler room `K`, interrupted by any handlers of room `K` for `P`: the uninterrupted
call returns in a state `t₀` with `Result t₀`; the interrupted call returns with the same events,
in a state with the registers and flags of `t₀` and its memory on every byte of `P` outside the
window, and SP lies in the window before each of its instructions. -/
def InterruptedCall (K n : Nat) (sp0 stop : Word) (s : State) (P : Word → Prop)
    (Result : State → Prop) : Prop :=
  HandlerRoom K n sp0 P → ∀ H, Handlers K P H → ∃ m, ∀ fuel, m ≤ fuel → ∃ t₀ tr states t,
    Thumb.runUntil stop fuel s = .ok (t₀, tr) ∧ Result t₀ ∧
    irunStates H stop fuel 0 s = .ok (states, tr) ∧ states.getLast? = some t ∧
    SameOn (fun y => P y ∧ ¬ BelowEntry sp0 n y) t₀ t ∧ ∀ u ∈ states, InStackWindow sp0 n u.sp

end M0Crypto.Release.TraceSpec
