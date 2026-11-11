import M0Crypto.Release.ConstantTime.Cert
import M0Crypto.Release.ConstantTime.SemIndexCheck

/-! Certificate-wide diagnostics for invalid abstract-state register indices.

Every block head and every state returned by an instruction transfer is checked. Transfer
errors are retained as diagnostics rather than treated as if no successor existed.
Coverage of actual block paths also requires the separate `certOk` result, which
checks that non-final instructions have exactly one fall-through successor. This
index check alone does not validate certificate control flow.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Thumb

/-- A problem found while walking a certificate's abstract states. `blockOff` identifies
the certificate block; `off` and `ctx` identify the state/transfer site. -/
structure IndexCertIssue where
  blockOff : Nat
  blockCtx : Option Nat
  off : Nat
  ctx : Option Nat
  problem : Sum IndexFailure String
  deriving Repr

def stateIndexIssue (blockOff : Nat) (blockCtx : Option Nat) (off : Nat)
    (ctx : Option Nat) (st : AbsState) : Option IndexCertIssue :=
  (st.indicesFailure).map fun failure =>
    ⟨blockOff, blockCtx, off, ctx, .inl failure⟩

def successorsIndexFailure (b : Blk) (off : Nat) : List (Tgt × AbsState) →
    Option IndexCertIssue
  | [] => none
  | (target, st) :: rest =>
    let point := match target with
      | .pt nextOff nextCtx => (nextOff, nextCtx)
      | .exit => (off, b.ctx)
    match stateIndexIssue b.off b.ctx point.1 point.2 st with
    | some issue => some issue
    | none => successorsIndexFailure b off rest

/-- First index problem in a block. Each transfer is evaluated once; an `xfer` failure
becomes an issue at that instruction. The transfer successor state is checked before the
next instruction, so the block head and all intermediate successors are covered. -/
def blockIndicesFailure (env : Env) (b : Blk) : Option IndexCertIssue :=
  let rec walk : Nat → AbsState → List Instr → Option IndexCertIssue
    | off, st, [] => stateIndexIssue b.off b.ctx off b.ctx st
    | off, st, i :: is =>
      match stateIndexIssue b.off b.ctx off b.ctx st with
      | some issue => some issue
      | none =>
        match xfer env off b.ctx i st with
        | .error e => some ⟨b.off, b.ctx, off, b.ctx, .inr e⟩
        | .ok o =>
          match successorsIndexFailure b off o.succs with
          | some issue => some issue
          | none =>
            match o.succs with
            | [] => walk (off + i.size) st is
            | [(_, nextSt)] => walk (off + i.size) nextSt is
            | _ => walk (off + i.size) st is
  walk b.off b.st b.code

/-- First issue in certificate block order, then instruction/successor order. -/
def certIndicesFailure (c : Cert) (env : Env) : Option IndexCertIssue :=
  c.findSome? (blockIndicesFailure env)

/-- Boolean counterpart to `certIndicesFailure = none`. -/
def certIndicesCheck (c : Cert) (env : Env) : Bool :=
  (certIndicesFailure c env).isNone

theorem certIndicesFailure_eq_none_iff (c : Cert) (env : Env) :
    certIndicesFailure c env = none ↔ certIndicesCheck c env = true := by
  unfold certIndicesCheck
  cases certIndicesFailure c env <;> simp

end M0Crypto.Release.ConstantTime
