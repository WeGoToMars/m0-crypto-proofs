import M0Crypto.Release.ChaCha20Xor
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.Blake2sStatements

/-!
# Non-vacuity of the entry contracts

A theorem whose hypotheses no real call can satisfy is true and useless. For each
function this file gives one concrete call (registers, memory with the release code at address
0, buffers and stack arguments) and proves that it meets the hypothesis shared by all of the
function's headline theorems (`ChaCha20Xor.Pre`, `Aead.APre`). Each witness is then passed to
its correctness theorem (`example`s at the end).

The calls are chosen to exercise the cases where an over-strong precondition would hide:
in-place operation, unaligned buffers and a non-empty message.
For BLAKE2s the witnesses are an initialized context and, for `final`, an unaligned output.
`copy` has its own witness, `Blake2sCopy.copy_correct_nonvacuous`.

All witnesses are checked by kernel evaluation (`decide +kernel`) of the concrete facts.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj Ctx Valid)
open M0Crypto.Release.Aead (ACall AValid ABuf AEntry)
open M0Crypto.Release.Blake2sStream (Ctx)

/-! ## Concrete memory and registers -/

/-- Little-endian bytes of a 32-bit value. -/
def le32 (w : Nat) : List (BitVec 8) := (List.range 4).map fun i => BitVec.ofNat 8 (w / 256 ^ i)

/-- The release code at address 0, the given regions `(start, bytes)` above it, zeros
elsewhere. -/
def memOf (regions : List (Nat × List (BitVec 8))) : Mem := fun a =>
  if a.toNat < Artifacts.Release.size then B.getD a.toNat 0
  else match regions.find? (fun r => decide (r.1 ≤ a.toNat ∧ a.toNat < r.1 + r.2.length)) with
    | some r => r.2.getD (a.toNat - r.1) 0
    | none => 0

theorem codeAt (rs : List (Nat × List (BitVec 8))) : Thumb.CodeAt (memOf rs) 0 B := by
  intro i hi
  have hi' : i < Artifacts.Release.size := by rw [B_len] at hi; exact hi
  have e : (0 + BitVec.ofNat 32 i).toNat = i := by
    have : i < 2 ^ 32 := by unfold Artifacts.Release.size at hi'; omega
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
  show (if _ then _ else _) = _
  simp only [e, hi', ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- Entry SP of every witness call. -/
def sp0 : Nat := 0x20001000

/-- Registers of a call: PC, r0-r3, SP = `sp0`, LR = 0x00010001 (Thumb, outside the code). -/
def regsOf (pc r0 r1 r2 r3 : Nat) : Reg → Word := fun r =>
  if r = 0 then BitVec.ofNat 32 r0 else if r = 1 then BitVec.ofNat 32 r1
  else if r = 2 then BitVec.ofNat 32 r2 else if r = 3 then BitVec.ofNat 32 r3
  else if r = 13 then BitVec.ofNat 32 sp0 else if r = 14 then 0x00010001#32
  else if r = 15 then BitVec.ofNat 32 pc else 0#32

def stOf (m : Mem) (rg : Reg → Word) : State := ⟨rg, false, false, false, false, m⟩

/-- The return address lies outside the code. -/
theorem ret_out :
    ∀ i < Artifacts.Release.size, (0x00010001#32 : Word) &&& ~~~1#32 ≠ 0 + BitVec.ofNat 32 i := by
  intro i hi heq
  have := congrArg BitVec.toNat heq
  simp at this
  unfold Artifacts.Release.size at hi
  omega

/-! ## ChaCha20: in place, 100 bytes at an odd address, counter 1 -/

def chMem : Mem := memOf [(sp0, le32 0x20000340 ++ le32 1)]

def chCtx : Frame.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000401#32, 100#32, 0x20000300#32, 0x20000340#32,
   1#32, chMem, regsOf 0 0x20000401 0x20000401 100 0x20000300⟩

theorem xor_correct_nonvacuous : ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, Frame.Ctx.fp, chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, Artifacts.Release.size]; decide +kernel)

/-! ## AEAD: in place, 100 bytes at an odd address, 13-byte AAD, unaligned tag -/

def aMem : Mem :=
  memOf [(sp0, le32 0x20000500 ++ le32 13 ++ le32 0x20000300 ++ le32 0x20000340)]

def aCall (off : Nat) : ACall :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000483#32, 0x20000401#32, 100#32, 0x20000500#32,
   13#32, 0x20000300#32, 0x20000340#32, aMem, regsOf off 0x20000401 0x20000483 0x20000401 100⟩

local macro "aead_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide +kernel, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, aCall, Artifacts.Release.size]; decide +kernel)))

theorem encrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) := by
  aead_witness

theorem decrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.decOff) Aead.decOff (stOf aMem (aCall Aead.decOff).regs0) := by
  aead_witness

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

example := ChaCha20Xor.xor_correct _ _ xor_correct_nonvacuous
example := Aead.encrypt_correct _ _ encrypt_correct_nonvacuous
example := Aead.decrypt_correct _ _ decrypt_correct_nonvacuous
example := Blake2sCompress.compress_correct compress_correct_nonvacuous ret_out
example := Blake2sHash.init_correct init_correct_nonvacuous ret_out
example := Blake2sHash.update_correct update_correct_nonvacuous ret_out
example := Blake2sHash.final_correct final_correct_nonvacuous ret_out

/-- The hypotheses of the composed `C1` are satisfiable: the `init` witness, one `update` call
on the same context, and a total length below 2^64. (The premises inside `CallsTotal` are
per-call obligations; `update_correct_nonvacuous` and `final_correct_nonvacuous` show them
satisfiable for a fresh context.) -/
example := Blake2sStatements.c1 (base := 0) (c := ctxBase) init_correct_nonvacuous rfl ret_out
  [bState Blake2sStreamCode.uStart 0x20000000 0x20000200 100] (by decide)

/-- The hypotheses of the composed `C4` are satisfiable too: the `init` witness run twice
(the run comes from `init_correct`), no `update` calls, and `final` on the resulting context. -/
theorem c4_nonvacuous : True := by
  obtain ⟨n, h⟩ := Blake2sHash.init_correct init_correct_nonvacuous ret_out
  obtain ⟨t, tr, hrun, hpost, -⟩ := h n (Nat.le_refl n)
  let S := bState Blake2sStreamCode.iStart 0x20000000 0 0
  let sf : State := { bState Blake2sStreamCode.fStart 0x20000000 0x20000203 0 with mem := t.mem }
  have hc : ∀ st, Ctx sf.mem (sf.regs 0) st → Blake2sHash.total st < 2 ^ 64 →
      Blake2sFinal.FinalEntry 0 sf st := by
    intro st hst htot
    have hcode : Thumb.CodeAt t.mem 0 B := by
      intro i hi
      have hi' : i < Artifacts.Release.size := by rw [B_len] at hi; exact hi
      have hlt : i < 2 ^ 32 := by unfold Artifacts.Release.size at hi'; omega
      have e : (0 + BitVec.ofNat 32 i : Word).toNat = i := by
        have h0 : (0 : Word).toNat = 0 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
      have hs := hpost.mem (0 + BitVec.ofNat 32 i)
        (by
          intro o ho heq
          have := congrArg BitVec.toNat heq
          simp [bState, stOf, regsOf, sp0, BitVec.toNat_add, BitVec.toNat_ofNat] at this
          unfold Artifacts.Release.size at hi'
          omega)
        (by
          intro o ho heq
          have := congrArg BitVec.toNat heq
          simp [bState, stOf, regsOf, BitVec.toNat_add, BitVec.toNat_ofNat] at this
          unfold Artifacts.Release.size at hi'
          omega)
      rw [hs]
      exact codeAt [(ctxBase.toNat, ctxBytes)] i hi
    refine ⟨by decide, ?_, hcode, ?_, ?_, ?_, ?_, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | rfl
      | (simp only [sf, Disj, bState, stOf, regsOf, Artifacts.Release.size]; decide +kernel)
      | exact htot
  have key := Blake2sHash.hash_constant_time (base := 0) (c := ctxBase) (s0 := S) (t0 := t)
    (s0' := S) (t0' := t) (sf := sf) (sf' := sf) (calls := []) (calls' := [])
    init_correct_nonvacuous init_correct_nonvacuous rfl ret_out ⟨n, tr, hrun⟩ rfl ⟨n, tr, hrun⟩
    ⟨rfl, rfl, rfl, fun _ _ => rfl⟩ trivial trivial Blake2sHash.All2.nil (by simp [Blake2sHash.inputs])
    (by simp [Blake2sHash.inputs]) rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) hc hc ret_out
    ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  trivial

end M0Crypto.Release.NonVacuity
