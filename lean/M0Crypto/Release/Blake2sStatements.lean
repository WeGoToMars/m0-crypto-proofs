import M0Crypto.Release.Blake2sTotal
import M0Crypto.Release.Blake2sComposed

/-!
# The composed BLAKE2s claims, as statements

`C1` and `C4` of `docs/design/blake2s-proofs.md` section 1, written out as Props. They are the
text a reader audits; the BLAKE2s asset's `Audit.lean` prints them (and the definitions they use) so
that `assets/blake2s/statements.golden` records them, and the two theorems at the end check that the proofs
prove exactly these Props.

* `C1` (functional correctness, total): from entry states meeting each entry's obligations,
  `init`, every `update` and `final` return, and the 32 bytes at `final`'s output pointer are the
  RFC 7693 BLAKE2s-256 digest of the concatenated inputs. Public: pointers, lengths. The
  caller's code between calls is arbitrary except that it leaves the 112 context bytes alone.
  A return-address precondition (`hreti`) keeps the return address outside the library.
* `C4` (constant time, model): two executions whose calls agree on the public inputs (entry pc,
  `sp`, `lr`, and the argument registers each function takes: init 1, update 3, final 2, see
  `PubEq`) run every call with equal event traces, whatever the message bytes. A secret in an
  argument register a function does not take is allowed; the certificates show the code does not
  read it before overwriting it. The runs are hypotheses here (`hruni`, `Calls`); `C1` shows they exist.

Per-entry statements (C2, C3, per-call C1 and C4) are the theorems listed in `Audit.lean`.
Cycles (C5) are not a Lean claim.
-/

namespace M0Crypto.Release.Blake2sStatements

open M0Crypto.Armv6M (Word State)
open M0Crypto.Release.Blake2sHash
open M0Crypto.Release.Blake2sStream (Ctx bytesAt)
open M0Crypto.Release.Blake2sUpdate (nn UpdateEntry)

/-- The hypotheses of `C1`: a valid `init` entry on the context at `c`, a return address outside
the library, and a total input length below 2^64. Named so that a non-vacuity witness can state
them for a concrete call (`NonVacuity.c1_nonvacuous`). -/
structure C1Hyp (base c : Word) (s0 : State) (calls : List State) : Prop where
  ei : Blake2sInit.InitEntry base s0
  hi0 : s0.regs 0 = c
  hreti : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i
  hlen : (calls.map nn).sum < 2 ^ 64

/-- Claim C1 (total correctness of `init; update*; final`). -/
def C1 : Prop :=
  ∀ {base c : Word} {s0 : State} {calls : List State}, C1Hyp base c s0 calls →
    ∃ fuel t0 tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr) ∧
      CallsTotal base c t0.mem calls (fun m =>
        ∀ sf : State, sf.regs 0 = c →
          (∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) →
          (∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st) →
          (∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) →
          ∃ fuel tf tr, Thumb.runUntil (sf.regs 14 &&& ~~~1#32) fuel sf = .ok (tf, tr) ∧
            bytesAt tf.mem (sf.regs 1) 32 = M0Crypto.Spec.Blake2s.blake2s (inputsOf calls).flatten)

/-- The hypotheses of `C4`: two executions of `init; update*; final` on the context at `c`, with
equal public inputs call by call. Named so that a non-vacuity witness can state them for two
concrete executions with different message bytes (`NonVacuity.c4_nonvacuous`). -/
structure C4Hyp (base c : Word) (s0 t0 s0' t0' sf sf' : State) (calls calls' : List (State × State)) :
    Prop where
  ei : Blake2sInit.InitEntry base s0
  ei' : Blake2sInit.InitEntry base s0'
  hi0 : s0.regs 0 = c
  hreti : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i
  hruni : ∃ fuel tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr)
  hi0' : s0'.regs 0 = c
  hruni' : ∃ fuel tr, Thumb.runUntil (s0'.regs 14 &&& ~~~1#32) fuel s0' = .ok (t0', tr)
  hpubi : PubEq 1 s0 s0'
  hcalls : Calls base c t0.mem calls
  hcalls' : Calls base c t0'.mem calls'
  hpubc : All2 (fun p q => PubEq 3 p.1 q.1) calls calls'
  hlen : ((inputs calls).map List.length).sum < 2 ^ 64
  hlen' : ((inputs calls').map List.length).sum < 2 ^ 64
  hf0 : sf.regs 0 = c
  hf0' : sf'.regs 0 = c
  hfm : ∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = lastMem t0.mem calls (c + BitVec.ofNat 32 o)
  hfm' : ∀ o < 112, sf'.mem (c + BitVec.ofNat 32 o) = lastMem t0'.mem calls' (c + BitVec.ofNat 32 o)
  hfe : ∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st
  hfe' : ∀ st, Ctx sf'.mem (sf'.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf' st
  hretf : ∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i
  hpubf : PubEq 2 sf sf'

/-- Claim C4 (equal event traces for equal public inputs, composed). -/
def C4 : Prop :=
  ∀ {base c : Word} {s0 t0 s0' t0' sf sf' : State} {calls calls' : List (State × State)},
    C4Hyp base c s0 t0 s0' t0' sf sf' calls calls' →
    TraceEq s0 s0' ∧ All2 (fun p q => TraceEq p.1 q.1) calls calls' ∧ TraceEq sf sf'

theorem c1 : C1 := fun h => hash_correct h.ei h.hi0 h.hreti _ h.hlen

theorem c4 : C4 := fun h => hash_constant_time h.ei h.ei' h.hi0 h.hreti h.hruni h.hi0' h.hruni'
  h.hpubi h.hcalls h.hcalls' h.hpubc h.hlen h.hlen' h.hf0 h.hf0' h.hfm h.hfm' h.hfe h.hfe' h.hretf
  h.hpubf

end M0Crypto.Release.Blake2sStatements
