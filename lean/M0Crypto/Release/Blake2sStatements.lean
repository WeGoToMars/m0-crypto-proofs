import M0Crypto.Release.Blake2sTotal
import M0Crypto.Release.Blake2sComposed

/-!
# The composed BLAKE2s claims, as statements

`C1` and `C4` of `docs/design/blake2s-proofs.md` section 1, written out as Props. They are the
text a reader audits; `Audit.lean` prints them (and the definitions they use) so that
`tools/statements.golden` records them, and the two theorems at the end check that the proofs
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

/-- Claim C1 (total correctness of `init; update*; final`). -/
def C1 : Prop :=
  ∀ {base c : Word} {s0 : State} (_ : Blake2sInit.InitEntry base s0) (_ : s0.regs 0 = c)
    (_ : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (calls : List State) (_ : (calls.map nn).sum < 2 ^ 64),
    ∃ fuel t0 tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr) ∧
      CallsTotal base c t0.mem calls (fun m =>
        ∀ sf : State, sf.regs 0 = c →
          (∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) →
          (∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st) →
          (∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) →
          ∃ fuel tf tr, Thumb.runUntil (sf.regs 14 &&& ~~~1#32) fuel sf = .ok (tf, tr) ∧
            bytesAt tf.mem (sf.regs 1) 32 = M0Crypto.Spec.Blake2s.blake2s (inputsOf calls).flatten)

/-- Claim C4 (equal event traces for equal public inputs, composed). -/
def C4 : Prop :=
  ∀ {base c : Word} {s0 t0 s0' t0' sf sf' : State} {calls calls' : List (State × State)}
    (_ : Blake2sInit.InitEntry base s0) (_ : Blake2sInit.InitEntry base s0')
    (_ : s0.regs 0 = c)
    (_ : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (_ : ∃ fuel tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr))
    (_ : s0'.regs 0 = c)
    (_ : ∃ fuel tr, Thumb.runUntil (s0'.regs 14 &&& ~~~1#32) fuel s0' = .ok (t0', tr))
    (_ : PubEq 1 s0 s0')
    (_ : Calls base c t0.mem calls) (_ : Calls base c t0'.mem calls')
    (_ : All2 (fun p q => PubEq 3 p.1 q.1) calls calls')
    (_ : ((inputs calls).map List.length).sum < 2 ^ 64)
    (_ : ((inputs calls').map List.length).sum < 2 ^ 64)
    (_ : sf.regs 0 = c) (_ : sf'.regs 0 = c)
    (_ : ∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = lastMem t0.mem calls (c + BitVec.ofNat 32 o))
    (_ : ∀ o < 112, sf'.mem (c + BitVec.ofNat 32 o) = lastMem t0'.mem calls' (c + BitVec.ofNat 32 o))
    (_ : ∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st)
    (_ : ∀ st, Ctx sf'.mem (sf'.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf' st)
    (_ : ∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (_ : PubEq 2 sf sf'),
    TraceEq s0 s0' ∧ All2 (fun p q => TraceEq p.1 q.1) calls calls' ∧ TraceEq sf sf'

theorem c1 : C1 := @hash_correct

theorem c4 : C4 := @hash_constant_time

end M0Crypto.Release.Blake2sStatements
