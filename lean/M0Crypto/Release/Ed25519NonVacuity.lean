import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.Ed25519TraceSpec
import M0Crypto.Spec.Ed25519Vectors

/-!
# Non-vacuity of the Ed25519 entry contracts

One concrete call per entry and build, with the build at address 0, the entry SP and LR of
`NonVacuityBase` and RFC 8032 section 7.1 test 2 (a one-byte message):

* `pubkey_pre_nonvacuous`: `pk` overlaps `seed` (two bytes apart), both at odd addresses.
* `sign_pre_nonvacuous`: `sk ‖ M` at an odd address and `sig` overlapping both.
* `verify_pre_nonvacuous`: `sig`, `pk` and the message at odd addresses.

`*_constant_time_nonvacuous`: that call and a second one with equal public values and different
secrets (test 1's seed for pubkey; test 1's seed and another message byte for sign; another byte
of unrelated memory for verify). `*_interrupted_nonvacuous`: the first call with 256 bytes of
handler room and the handler `tickBelowSp`. The `#guard`s evaluate the specification on the
witness calls: each expected output is test 2's.
-/

namespace M0Crypto.Release.Ed25519.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.NonVacuity (regsOf stOf sp0 tickBelowSp interruptWitness_of)
open M0Crypto.Spec.Ed25519 (test1 test2)

/-! ## Concrete memory -/

/-- Build `b` at address 0, the given regions `(start, bytes)` above it, zeros elsewhere. -/
def memB (b : Build) (regions : List (Nat × List (BitVec 8))) : Mem := fun a =>
  if a.toNat < b.size then b.bytes.getD a.toNat 0
  else match regions.find? (fun r => decide (r.1 ≤ a.toNat ∧ a.toNat < r.1 + r.2.length)) with
    | some r => r.2.getD (a.toNat - r.1) 0
    | none => 0

theorem codeAtB (b : Build) (rs : List (Nat × List (BitVec 8))) :
    Thumb.CodeAt (memB b rs) 0 b.bytes := by
  intro i hi
  have hs : b.size < 2 ^ 32 := by cases b <;> decide
  have hi' : i < b.size := b.bytes_length ▸ hi
  have e : (0 + BitVec.ofNat 32 i : Word).toNat = i := by
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
  show (if _ then _ else _) = _
  simp only [e, hi', ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- Discharges every concrete premise of a witness `Pre`, for one build. -/
local macro "pre_facts" c:ident : tactic => `(tactic| (
  all_goals first
    | exact codeAtB _ _
    | (simp only [$c:ident, Disj, Pubkey.Ctx.fp, Sign.Ctx.fp, Verify.Ctx.fp, Call.fp,
        Call.ret, Pubkey.stackBytes, Sign.stackBytes, Verify.stackBytes, Build.size, sp0] <;>
        decide +kernel)))

/-! ## `m0c_ed25519_pubkey` -/

def pkCtx (b : Build) (seed : List (BitVec 8)) : Pubkey.Ctx :=
  { base := 0, sp0 := BitVec.ofNat 32 sp0, m0 := memB b [(0x20000401, seed)],
    regs0 := regsOf b.pubkeyAt 0x20000403 0x20000401 0 0, pk := 0x20000403, seed := 0x20000401 }

def pkSt (b : Build) (seed : List (BitVec 8)) : State := stOf (pkCtx b seed).m0 (pkCtx b seed).regs0

theorem pubkey_pre (b : Build) (seed : List (BitVec 8)) :
    Pubkey.Pre b (pkCtx b seed) (pkSt b seed) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ⟨⟨rfl, rfl, ?_, ?_⟩, ?_, ?_⟩⟩ <;>
    cases b <;> pre_facts pkCtx

/-- A valid pubkey call, for each build, on test 2's seed. -/
theorem pubkey_pre_nonvacuous (b : Build) :
    Pubkey.Pre b (pkCtx b test2.privKey) (pkSt b test2.privKey) :=
  pubkey_pre b _

theorem pubkey_constant_time_nonvacuous (b : Build) :
    Pubkey.Pre b (pkCtx b test2.privKey) (pkSt b test2.privKey) ∧
      Pubkey.Pre b (pkCtx b test1.privKey) (pkSt b test1.privKey) ∧
      (pkCtx b test2.privKey).pub = (pkCtx b test1.privKey).pub ∧
      (pkCtx b test2.privKey).seedB ≠ (pkCtx b test1.privKey).seedB :=
  ⟨pubkey_pre b _, pubkey_pre b _, by simp only [Pubkey.Ctx.pub, pkCtx], by cases b <;> decide +kernel⟩

/-! ## `m0c_ed25519_sign` -/

/-- `sk` at 0x20000401, the message after it at 0x20000441, `sig` at 0x20000403. -/
def sgCtx (b : Build) (skM : List (BitVec 8)) : Sign.Ctx :=
  { base := 0, sp0 := BitVec.ofNat 32 sp0, m0 := memB b [(0x20000401, skM)],
    regs0 := regsOf b.signAt 0x20000403 0x20000441 1 0x20000401,
    sig := 0x20000403, msg := 0x20000441, len := 1, sk := 0x20000401 }

def sgSt (b : Build) (skM : List (BitVec 8)) : State := stOf (sgCtx b skM).m0 (sgCtx b skM).regs0

def skM2 : List (BitVec 8) := test2.privKey ++ test2.A ++ test2.M
def skM1 : List (BitVec 8) := test1.privKey ++ test1.A ++ [0#8]

theorem sign_pre (b : Build) (skM : List (BitVec 8)) : Sign.Pre b (sgCtx b skM) (sgSt b skM) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ⟨⟨rfl, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩ <;>
    cases b <;> pre_facts sgCtx

theorem sign_pre_nonvacuous (b : Build) : Sign.Pre b (sgCtx b skM2) (sgSt b skM2) :=
  sign_pre b _

theorem sign_constant_time_nonvacuous (b : Build) :
    Sign.Pre b (sgCtx b skM2) (sgSt b skM2) ∧ Sign.Pre b (sgCtx b skM1) (sgSt b skM1) ∧
      (sgCtx b skM2).pub = (sgCtx b skM1).pub ∧
      (sgCtx b skM2).seedB ≠ (sgCtx b skM1).seedB ∧ (sgCtx b skM2).msgB ≠ (sgCtx b skM1).msgB :=
  ⟨sign_pre b _, sign_pre b _, by simp only [Sign.Ctx.pub, sgCtx], by cases b <;> decide +kernel,
    by cases b <;> decide +kernel⟩

/-! ## `m0c_ed25519_verify` -/

/-- `sig` at 0x20000401, `pk` at 0x20000441, the message at 0x20000461, then `extra`, memory the
call does not read, at 0x20000800. -/
def vfCtx (b : Build) (extra : List (BitVec 8)) : Verify.Ctx :=
  { base := 0, sp0 := BitVec.ofNat 32 sp0,
    m0 := memB b [(0x20000401, test2.sig ++ test2.A ++ test2.M), (0x20000800, extra)],
    regs0 := regsOf b.verifyAt 0x20000401 0x20000461 1 0x20000441,
    sig := 0x20000401, msg := 0x20000461, len := 1, pk := 0x20000441 }

def vfSt (b : Build) (extra : List (BitVec 8)) : State :=
  stOf (vfCtx b extra).m0 (vfCtx b extra).regs0

theorem verify_pre (b : Build) (extra : List (BitVec 8)) :
    Verify.Pre b (vfCtx b extra) (vfSt b extra) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨⟨rfl, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩ <;>
    cases b <;> pre_facts vfCtx

theorem verify_pre_nonvacuous (b : Build) : Verify.Pre b (vfCtx b []) (vfSt b []) :=
  verify_pre b _

theorem verify_constant_time_nonvacuous (b : Build) :
    Verify.Pre b (vfCtx b []) (vfSt b []) ∧ Verify.Pre b (vfCtx b [1]) (vfSt b [1]) ∧
      (vfCtx b []).pub = (vfCtx b [1]).pub ∧
      (vfCtx b []).m0 0x20000800 ≠ (vfCtx b [1]).m0 0x20000800 :=
  ⟨verify_pre b _, verify_pre b _, by
    simp only [Verify.Ctx.pub, Prod.mk.injEq]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> cases b <;> decide +kernel,
    by cases b <;> decide +kernel⟩

/-! ## Interrupts: 256 bytes of handler room below the stack window -/

/-- `tickBelowSp` zeroes the 256 bytes below SP and increments the byte at 0x20002000. -/
local macro "handler_facts" b:ident c:ident fp:ident n:ident : tactic => `(tactic| (
  all_goals first
    | (simp +zetaDelta only [$c:ident, $n:ident, sp0]; decide)
    | (simp +zetaDelta only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true, Disj, $fp:ident, Call.fp, $c:ident, $n:ident, sp0]
       cases $b:ident <;> decide +kernel)))

theorem pubkey_interrupted_nonvacuous (b : Build) :
    Pubkey.Pre b (pkCtx b test2.privKey) (pkSt b test2.privKey) ∧
      TraceSpec.HandlerRoom 256 Pubkey.stackBytes (pkCtx b test2.privKey).sp0
        (fun y => Pubkey.ReadRegion b (pkCtx b test2.privKey) y ∨
          Pubkey.WrOk (pkCtx b test2.privKey) y) ∧
      TraceSpec.Handlers 256 (fun y => Pubkey.ReadRegion b (pkCtx b test2.privKey) y ∨
          Pubkey.WrOk (pkCtx b test2.privKey) y) (tickBelowSp 256 0x20002000#32) := by
  let c := pkCtx b test2.privKey
  refine ⟨pubkey_pre b _, interruptWitness_of
    [(c.seed, 32), (c.base, b.size), (c.fp, Pubkey.stackBytes), (c.pk, 32)] ?_ ?_ ?_⟩
  rotate_left
  · intro y hy
    rcases hy with (h | h | h) | (h | h)
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
  all_goals handler_facts b pkCtx Pubkey.Ctx.fp Pubkey.stackBytes

theorem sign_interrupted_nonvacuous (b : Build) :
    Sign.Pre b (sgCtx b skM2) (sgSt b skM2) ∧
      TraceSpec.HandlerRoom 256 Sign.stackBytes (sgCtx b skM2).sp0
        (fun y => Sign.ReadRegion b (sgCtx b skM2) y ∨ Sign.WrOk (sgCtx b skM2) y) ∧
      TraceSpec.Handlers 256 (fun y => Sign.ReadRegion b (sgCtx b skM2) y ∨
          Sign.WrOk (sgCtx b skM2) y) (tickBelowSp 256 0x20002000#32) := by
  let c := sgCtx b skM2
  refine ⟨sign_pre b _, interruptWitness_of
    [(c.sk, 64), (c.msg, c.len.toNat), (c.base, b.size), (c.fp, Sign.stackBytes), (c.sig, 64)]
    ?_ ?_ ?_⟩
  rotate_left
  · intro y hy
    rcases hy with (h | h | h | h) | (h | h)
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
  all_goals handler_facts b sgCtx Sign.Ctx.fp Sign.stackBytes

theorem verify_interrupted_nonvacuous (b : Build) :
    Verify.Pre b (vfCtx b []) (vfSt b []) ∧
      TraceSpec.HandlerRoom 256 Verify.stackBytes (vfCtx b []).sp0
        (fun y => Verify.ReadRegion b (vfCtx b []) y ∨ Verify.WrOk (vfCtx b []) y) ∧
      TraceSpec.Handlers 256 (fun y => Verify.ReadRegion b (vfCtx b []) y ∨
          Verify.WrOk (vfCtx b []) y) (tickBelowSp 256 0x20002000#32) := by
  let c := vfCtx b []
  refine ⟨verify_pre b _, interruptWitness_of
    [(c.sig, 64), (c.msg, c.len.toNat), (c.pk, 32), (c.base, b.size), (c.fp, Verify.stackBytes)]
    ?_ ?_ ?_⟩
  rotate_left
  · intro y hy
    rcases hy with (h | h | h | h | h) | h
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
  all_goals handler_facts b vfCtx Verify.Ctx.fp Verify.stackBytes

/-! ## The specification on the witness calls -/

#guard (pkCtx .compact test2.privKey).pkOut == test2.A
#guard (sgCtx .compact skM2).pkB == Spec.Ed25519.publicKey (sgCtx .compact skM2).seedB
#guard (sgCtx .fast skM2).sigOut == test2.sig
#guard Spec.Ed25519.verify (vfCtx .compact []).sigB (vfCtx .compact []).msgB (vfCtx .compact []).pkB

end M0Crypto.Release.Ed25519.NonVacuity
