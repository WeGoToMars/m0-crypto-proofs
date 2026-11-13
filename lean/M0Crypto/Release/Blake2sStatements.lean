import M0Crypto.Release.Blake2sTraceSpec

/-!
# The composed BLAKE2s claims, as statements

Statement file: definitions only. A whole hash is `init`, any number of `update` calls and
`final`, all on one context, with arbitrary caller code between calls that leaves the 112
context bytes alone. Each call is stated with the per-function vocabulary of
`Blake2sContract.lean` and `Blake2sTraceSpec.lean`: its call description is read off its entry
state (`*.callAt`), and its obligations are that function's `Pre` for whatever stream the
context holds (`*.EntryOn`).

* `HashCorrect` (total correctness): from a valid `init` call, `init` returns; then every
  `update` call meeting its obligations returns; then every `final` call meeting its
  obligations returns, and the 32 bytes at its output pointer are the RFC 7693 BLAKE2s-256
  digest of the concatenated inputs. No run is assumed.
* `HashConstantTime` (constant time): two executions whose calls have equal public inputs
  (pointers, lengths, SP, LR) run every call with the same event trace, whatever the message
  bytes. The runs are hypotheses here; `HashCorrect` shows they exist.
-/

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Reg State Mem)

/-! ## Calls read off their entry states -/

/-- Return address of a call entered in `s`: LR with the Thumb bit cleared. -/
def returnAddr (s : State) : Word := s.regs 14 &&& ~~~1#32

/-- The input bytes of an `update` call entered in `s` (`n` bytes at `p`). -/
def inputAt (s : State) : List Spec.Blake2s.Byte := bytesAt s.mem (s.regs 1) (s.regs 2).toNat

/-- The `update` call entered in `s` on a context holding `stream`. -/
def Update.callAt (base : Word) (stream : Spec.Blake2s.State) (s : State) : Update.Ctx :=
  ⟨base, s.regs 13, s.regs 0, s.regs 1, s.regs 2, stream, s.mem, s.regs⟩

/-- The `final` call entered in `s` on a context holding `stream`. -/
def Final.callAt (base : Word) (stream : Spec.Blake2s.State) (s : State) : Final.Ctx :=
  ⟨base, s.regs 13, s.regs 0, s.regs 1, stream, s.mem, s.regs⟩

/-- The caller left the context bytes at `c` as they were in `m` when it entered `s`. -/
def ContextKept (c : Word) (m : Mem) (s : State) : Prop :=
  ∀ o < contextBytes, s.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)

/-- `s` enters `update` on the context at `c`, meeting `Update.Pre` for whatever stream the
context holds (as long as the total length stays below 2^64 bytes). -/
def Update.EntryOn (base c : Word) (s : State) : Prop :=
  s.regs 0 = c ∧ ∀ st, ContextHolds s.mem c st →
    st.count + st.pending.length + (s.regs 2).toNat < 2 ^ 64 →
      Update.Pre (Update.callAt base st s) s

/-- `s` enters `final` on the context at `c`, meeting `Final.Pre` for whatever stream the context
holds. -/
def Final.EntryOn (base c : Word) (s : State) : Prop :=
  s.regs 0 = c ∧ ∀ st, ContextHolds s.mem c st → st.count + st.pending.length < 2 ^ 64 →
    Final.Pre (Final.callAt base st s) s

/-! ## Total correctness -/

/-- The `update` calls entered in the states `calls`, in order, on the context at `c`, starting
from memory `m`, each return, and `K` holds of the memory after the last. Each call's entry is
a premise: the caller supplies it after the previous call returned. -/
def UpdatesReturn (base c : Word) : Mem → List State → (Mem → Prop) → Prop
  | m, [], K => K m
  | m, s :: rest, K => ContextKept c m s → Update.EntryOn base c s →
      ∃ fuel w tr, Thumb.runUntil (returnAddr s) fuel s = .ok (w, tr) ∧
        UpdatesReturn base c w.mem rest K

/-- The hypotheses of `HashCorrect`: a valid `init` call and a total input length below 2^64
bytes. -/
structure HashCorrectHyp (ci : Init.Ctx) (s0 : State) (calls : List State) : Prop where
  pre : Init.Pre ci s0
  lengthLt : (calls.map fun s => (s.regs 2).toNat).sum < 2 ^ 64

/-- Composed claim (total correctness of `init; update*; final`). -/
def HashCorrect : Prop :=
  ∀ ci s0 calls, HashCorrectHyp ci s0 calls →
    ∃ fuel t0 tr, Thumb.runUntil ci.ret fuel s0 = .ok (t0, tr) ∧
      UpdatesReturn ci.base ci.context t0.mem calls fun m =>
        ∀ sf, ContextKept ci.context m sf → Final.EntryOn ci.base ci.context sf →
          ∃ fuel tf tr, Thumb.runUntil (returnAddr sf) fuel sf = .ok (tf, tr) ∧
            bytesAt tf.mem (sf.regs 1) digestBytes =
              Spec.Blake2s.blake2s (calls.map inputAt).flatten

/-! ## Constant time -/

/-- The `update` calls `calls` (entry state, returned state), in order, on the context at `c`,
starting from memory `m`: each entry meets `update`'s obligations and runs to its return
address in the returned state given. -/
def UpdatesRan (base c : Word) : Mem → List (State × State) → Prop
  | _, [] => True
  | m, (s, w) :: rest => ContextKept c m s ∧ Update.EntryOn base c s ∧
      (∃ fuel tr, Thumb.runUntil (returnAddr s) fuel s = .ok (w, tr)) ∧
      UpdatesRan base c w.mem rest

/-- The memory the last call returned with (`m` if there are none). -/
def lastMem : Mem → List (State × State) → Mem
  | m, [] => m
  | _, (_, w) :: rest => lastMem w.mem rest

/-- Public inputs of an `update` call entered in `s`: SP, LR, the context and input pointers and
the input length. -/
def Update.pubAt (s : State) := (s.regs 13, s.regs 14, s.regs 0, s.regs 1, s.regs 2)

/-- Public inputs of a `final` call entered in `s`: SP, LR, the context and output pointers. -/
def Final.pubAt (s : State) := (s.regs 13, s.regs 14, s.regs 0, s.regs 1)

/-- The event trace of the call entered in `s`, for each fuel. -/
def traceOf (s : State) (fuel : Nat) : Except Thumb.Fault (List Thumb.Event) :=
  (Thumb.runUntil (returnAddr s) fuel s).map Prod.snd

/-- The hypotheses of `HashConstantTime`: two executions of `init; update*; final` whose calls
have equal public inputs, call by call. -/
structure HashConstantTimeHyp (ci ci' : Init.Ctx) (s0 s0' t0 t0' sf sf' : State)
    (calls calls' : List (State × State)) : Prop where
  pre : Init.Pre ci s0
  pre' : Init.Pre ci' s0'
  pub : ci.pub = ci'.pub
  run : ∃ fuel tr, Thumb.runUntil ci.ret fuel s0 = .ok (t0, tr)
  run' : ∃ fuel tr, Thumb.runUntil ci'.ret fuel s0' = .ok (t0', tr)
  updates : UpdatesRan ci.base ci.context t0.mem calls
  updates' : UpdatesRan ci.base ci.context t0'.mem calls'
  updatesPub : calls.map (fun p => Update.pubAt p.1) = calls'.map (fun p => Update.pubAt p.1)
  lengthLt : (calls.map fun p => (p.1.regs 2).toNat).sum < 2 ^ 64
  finalKept : ContextKept ci.context (lastMem t0.mem calls) sf
  finalKept' : ContextKept ci.context (lastMem t0'.mem calls') sf'
  final : Final.EntryOn ci.base ci.context sf
  final' : Final.EntryOn ci.base ci.context sf'
  finalPub : Final.pubAt sf = Final.pubAt sf'

/-- Composed claim (equal event traces for equal public inputs, composed). -/
def HashConstantTime : Prop :=
  ∀ ci ci' s0 s0' t0 t0' sf sf' calls calls',
    HashConstantTimeHyp ci ci' s0 s0' t0 t0' sf sf' calls calls' →
    traceOf s0 = traceOf s0' ∧
      calls.map (fun p => traceOf p.1) = calls'.map (fun p => traceOf p.1) ∧
      traceOf sf = traceOf sf'

end M0Crypto.Release.Blake2s
