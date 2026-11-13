import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.Blake2sStatements

/-!
# Non-vacuity of the BLAKE2s entry contracts

The witnesses are an initialized context and, for `final`, an unaligned output; each is
passed to its correctness theorem (`example`s below). `copy` has its own witness,
`Blake2sCopy.copy_correct_nonvacuous`. The composed claims have `c1_nonvacuous` (their
hypotheses `C1Hyp` at a concrete call) and `c4_nonvacuous` (`C4Hyp` for two executions that
differ in their message bytes).
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2sStream (Ctx)

/-! ## BLAKE2s: an initialized context at 0x20000000 -/

def ctxBase : Word := 0x20000000#32

/-- The 112 context bytes after `init`: `h0`, then `count`, `buf` and `used` all zero. -/
def ctxBytes : List (BitVec 8) :=
  (Spec.Blake2s.h0.toList.flatMap Spec.Blake2s.bytesOfWord) ++ List.replicate 80 0

def bMem : Mem := memOf [(ctxBase.toNat, ctxBytes)]

def bState (pc r0 r1 r2 : Nat) : State := stOf bMem (regsOf pc r0 r1 r2 0)

theorem ctx_init : Ctx bMem ctxBase Spec.Blake2s.State.init := by
  refine ⟨⟨by decide, ?_, by decide +kernel, by decide +kernel, by decide, by decide, rfl⟩,
    by decide +kernel⟩
  decide +kernel

/-- `h` and `block` word aligned, `f0 = 0` at the stack top. -/
theorem compress_correct_nonvacuous :
    Blake2sCompress.Entry 0 (bState Blake2sCode.fnStart 0x20000000 0x20000100 0) := by
  refine ⟨by decide, by decide, codeAt _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, Blake2sCompress.fpOf, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

theorem init_correct_nonvacuous :
    Blake2sInit.InitEntry 0 (bState Blake2sStreamCode.iStart 0x20000000 0 0) := by
  refine ⟨by decide, by decide, codeAt _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | (simp only [Disj, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

/-- 100 input bytes into a fresh context. -/
theorem update_correct_nonvacuous :
    Blake2sUpdate.UpdateEntry 0 (bState Blake2sStreamCode.uStart 0x20000000 0x20000200 100)
      Spec.Blake2s.State.init := by
  refine ⟨by decide, by decide, codeAt _, ?_, ?_, ?_, ?_, ctx_init, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | (simp only [Disj, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

/-- Digest of a fresh context to an odd address. -/
theorem final_correct_nonvacuous :
    Blake2sFinal.FinalEntry 0 (bState Blake2sStreamCode.fStart 0x20000000 0x20000203 0)
      Spec.Blake2s.State.init := by
  refine ⟨by decide, by decide, codeAt _, ?_, ?_, ?_, ?_, ctx_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | (simp only [Disj, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

/-! ## Each witness fits its theorem -/

example := Blake2sCompress.compress_correct compress_correct_nonvacuous ret_out
example := Blake2sHash.init_correct init_correct_nonvacuous ret_out
example := Blake2sHash.update_correct update_correct_nonvacuous ret_out
example := Blake2sHash.final_correct final_correct_nonvacuous ret_out

/-- The hypotheses of the composed `C1` hold for a concrete call: the `init` witness and one
`update` call of 100 bytes. (The premises inside `CallsTotal` are per-call obligations;
`update_correct_nonvacuous` and `final_correct_nonvacuous` show them satisfiable for a fresh
context.) -/
theorem c1_nonvacuous :
    Blake2sStatements.C1Hyp 0 ctxBase (bState Blake2sStreamCode.iStart 0x20000000 0 0)
      [bState Blake2sStreamCode.uStart 0x20000000 0x20000200 100] :=
  ⟨init_correct_nonvacuous, rfl, ret_out, by decide⟩

/-! ## C4: two executions with different message bytes

Both executions run the `init` witness, then one `update` of three bytes at `msgBase`, then
`final` to an odd address. They differ only in the message bytes (`msgA`, `msgB`), the
secret input of an unkeyed hash. Between calls the caller's memory is arbitrary except for
the 112 context bytes, so the `update` entry memory is the memory `init` returned with plus the
message, and the `final` entry memory is the memory `update` returned with. -/

def msgBase : Word := 0x20000200#32
def msgA : List (BitVec 8) := [1, 2, 3]
def msgB : List (BitVec 8) := [4, 5, 6]

/-- `m` with `msg` stored at `msgBase`. -/
def withMsg (m : Mem) (msg : List (BitVec 8)) : Mem := fun a =>
  if (a - msgBase).toNat < msg.length then msg.getD (a - msgBase).toNat 0 else m a

/-- The `update` entry: context at 0x20000000, `msg` at `msgBase`, on the memory `m`. -/
def uState (m : Mem) (msg : List (BitVec 8)) : State :=
  { bState Blake2sStreamCode.uStart 0x20000000 0x20000200 msg.length with mem := withMsg m msg }

/-- The `final` entry on the memory `m`: context at 0x20000000, output at the odd 0x20000203. -/
def fState (m : Mem) : State := { bState Blake2sStreamCode.fStart 0x20000000 0x20000203 0 with mem := m }

/-- Addresses below `msgBase` keep their byte in `withMsg` for a three-byte message. -/
theorem withMsg_low (m : Mem) (msg : List (BitVec 8)) (hl : msg.length = 3) (a : Word)
    (ha : a.toNat < 0x20000200) : withMsg m msg a = m a := by
  have h : ¬ (a - msgBase).toNat < msg.length := by
    rw [hl, BitVec.toNat_sub]
    simp only [msgBase, BitVec.toNat_ofNat]
    omega
  simp only [withMsg, h, ↓reduceIte]

theorem withMsg_bytes (m : Mem) (msg : List (BitVec 8)) (hl : msg.length = 3) :
    Blake2sUpdate.LL (uState m msg) = msg := by
  apply List.ext_getElem
  · simp [Blake2sUpdate.LL, Blake2sUpdate.nn, Blake2sStream.bytesAt_length, uState, bState, stOf,
      regsOf, hl]
  · intro i h1 h2
    have hi : i < 3 := hl ▸ h2
    simp only [Blake2sUpdate.LL, Blake2sStream.bytesAt, List.getElem_map, List.getElem_range]
    show withMsg m msg (0x20000200#32 + BitVec.ofNat 32 i) = _
    unfold withMsg
    have e : (0x20000200#32 + BitVec.ofNat 32 i - msgBase).toNat = i := by
      simp only [msgBase, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [e, h2, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- Code bytes carry over to any memory that agrees on the code range. -/
theorem codeAt_of_agree {m m' : Mem} (h : Thumb.CodeAt m 0 B)
    (hm : ∀ a : Word, a.toNat < Artifacts.Release.size → m' a = m a) : Thumb.CodeAt m' 0 B := by
  intro i hi
  have hi' : i < Artifacts.Release.size := by rw [B_len] at hi; exact hi
  have e : (0 + BitVec.ofNat 32 i : Word).toNat = i := by
    have h0 : (0 : Word).toNat = 0 := rfl
    have : i < 2 ^ 32 := by unfold Artifacts.Release.size at hi'; omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
  rw [hm _ (by rw [e]; exact hi')]
  exact h i hi

theorem uState_entry {m : Mem} {msg : List (BitVec 8)} (hl : msg.length = 3)
    (hcode : Thumb.CodeAt m 0 B) (st : Blake2sUpdate.SState)
    (hst : Ctx (uState m msg).mem ((uState m msg).regs 0) st)
    (htot : Blake2sHash.total st + Blake2sUpdate.nn (uState m msg) < 2 ^ 64) :
    Blake2sUpdate.UpdateEntry 0 (uState m msg) st := by
  have hcode' : Thumb.CodeAt (uState m msg).mem 0 B := codeAt_of_agree hcode fun a ha =>
    withMsg_low m msg hl a (by unfold Artifacts.Release.size at ha; omega)
  refine ⟨by decide, ?_, hcode', ?_, ?_, ?_, ?_, hst, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | exact htot
    | (simp only [uState, Disj, bState, stOf, regsOf, hl, Artifacts.Release.size]; decide +kernel)

theorem fState_entry {m : Mem} (hcode : Thumb.CodeAt m 0 B) (st : Spec.Blake2s.State)
    (hst : Ctx (fState m).mem ((fState m).regs 0) st) (htot : Blake2sHash.total st < 2 ^ 64) :
    Blake2sFinal.FinalEntry 0 (fState m) st := by
  refine ⟨by decide, ?_, hcode, ?_, ?_, ?_, ?_, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | exact htot
    | (simp only [fState, Disj, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

/-- One execution after `init` returned with `t0`: the `update` call on `msg` runs, and the
`final` entry on its returned memory meets `final`'s obligations. -/
theorem update_then_final {t0 : State} (msg : List (BitVec 8)) (hl : msg.length = 3)
    (hcode : Thumb.CodeAt t0.mem 0 B) (hctx : Ctx t0.mem ctxBase Spec.Blake2s.State.init) :
    ∃ w, Blake2sHash.Calls 0 ctxBase t0.mem [(uState t0.mem msg, w)] ∧
      (∀ st, Ctx (fState w.mem).mem ((fState w.mem).regs 0) st → Blake2sHash.total st < 2 ^ 64 →
        Blake2sFinal.FinalEntry 0 (fState w.mem) st) := by
  have hagree : ∀ o < 112, (uState t0.mem msg).mem (ctxBase + BitVec.ofNat 32 o) =
      t0.mem (ctxBase + BitVec.ofNat 32 o) := by
    intro o ho
    apply withMsg_low _ _ hl
    simp only [ctxBase, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc : Ctx (uState t0.mem msg).mem ((uState t0.mem msg).regs 0) Spec.Blake2s.State.init :=
    Blake2sHash.ctx_congr hctx hagree
  have he := uState_entry hl hcode _ hc (by
    simp [Blake2sHash.total, Blake2sUpdate.nn, uState, bState, stOf, regsOf, hl,
      Spec.Blake2s.State.init])
  obtain ⟨n, h⟩ := Blake2sHash.update_correct he ret_out
  obtain ⟨w, tr, hrun, hpost, -⟩ := h n (Nat.le_refl n)
  have hcodew : Thumb.CodeAt w.mem 0 B := by
    have hu : Thumb.CodeAt (uState t0.mem msg).mem 0 B := codeAt_of_agree hcode fun a ha =>
      withMsg_low _ msg hl a (by unfold Artifacts.Release.size at ha; omega)
    refine codeAt_of_agree hu fun a ha => hpost.mem a ?_
    unfold Artifacts.Release.size at ha
    rintro (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩) <;>
      simp [uState, bState, stOf, regsOf, sp0, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
        at ha ho ⊢ <;> omega
  refine ⟨w, ⟨rfl, hagree, uState_entry hl hcode, ret_out, ⟨n, tr, hrun⟩, trivial⟩, ?_⟩
  exact fState_entry hcodew

/-- The hypotheses of the composed `C4` hold for two executions that differ in their secret
input: the same `init`, then one `update` on `msgA` in the first and on `msgB` in the second
(same address and length), then `final`. -/
theorem c4_nonvacuous :
    ∃ t0 w w' : State,
      Blake2sStatements.C4Hyp 0 ctxBase (bState Blake2sStreamCode.iStart 0x20000000 0 0) t0
        (bState Blake2sStreamCode.iStart 0x20000000 0 0) t0 (fState w.mem) (fState w'.mem)
        [(uState t0.mem msgA, w)] [(uState t0.mem msgB, w')] ∧
      Blake2sHash.inputs [(uState t0.mem msgA, w)] = [msgA] ∧
      Blake2sHash.inputs [(uState t0.mem msgB, w')] = [msgB] ∧ msgA ≠ msgB := by
  obtain ⟨n, h⟩ := Blake2sHash.init_correct init_correct_nonvacuous ret_out
  obtain ⟨t0, tr, hrun, hpost, -⟩ := h n (Nat.le_refl n)
  have hcode : Thumb.CodeAt t0.mem 0 B := by
    refine codeAt_of_agree (codeAt [(ctxBase.toNat, ctxBytes)]) fun a ha => hpost.mem a ?_ ?_
    all_goals
      intro o ho heq
      have := congrArg BitVec.toNat heq
      simp [bState, stOf, regsOf, sp0, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      unfold Artifacts.Release.size at ha
      omega
  have hctx : Ctx t0.mem ctxBase Spec.Blake2s.State.init := hpost.ctx
  obtain ⟨w, hcw, hfw⟩ := update_then_final msgA rfl hcode hctx
  obtain ⟨w', hcw', hfw'⟩ := update_then_final msgB rfl hcode hctx
  have hinA : Blake2sHash.inputs [(uState t0.mem msgA, w)] = [msgA] := by
    simp only [Blake2sHash.inputs, List.map_cons, List.map_nil, withMsg_bytes _ msgA rfl]
  have hinB : Blake2sHash.inputs [(uState t0.mem msgB, w')] = [msgB] := by
    simp only [Blake2sHash.inputs, List.map_cons, List.map_nil, withMsg_bytes _ msgB rfl]
  refine ⟨t0, w, w', ⟨init_correct_nonvacuous, init_correct_nonvacuous, rfl, ret_out,
    ⟨n, tr, hrun⟩, rfl, ⟨n, tr, hrun⟩, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩, hcw, hcw',
    .cons ⟨rfl, rfl, rfl, fun _ _ => rfl⟩ .nil, ?_, ?_, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    hfw, hfw', ret_out, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩, hinA, hinB, by decide⟩
  · rw [hinA]; decide
  · rw [hinB]; decide

end M0Crypto.Release.NonVacuity
