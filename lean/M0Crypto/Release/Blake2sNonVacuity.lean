import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.Blake2sComposed
import M0Crypto.Release.Blake2sCompress

set_option linter.unusedSimpArgs false

/-!
# Non-vacuity of the BLAKE2s contracts

Each function's witness proves its `Pre` at a concrete call on a context that holds a buffered
stream (`bufStream`: three bytes absorbed, so `used = 3`), and is passed to the function's
correctness theorem (`example`s below):

* `init_pre_nonvacuous`: `init` re-initializes that context.
* `update_pre_nonvacuous`: 100 input bytes at an odd address; the call completes the buffered
  block, compresses it and buffers the rest.
* `final_pre_nonvacuous`: the digest of the buffered stream to an odd address.

The `*_constant_time_nonvacuous` witnesses pair each call with a second valid call with equal
public inputs and different secret memory (section "Constant time" below).

The composed claims have `hash_correct_nonvacuous` (`HashCorrectHyp` at a concrete call) and
`hash_constant_time_nonvacuous` (`HashConstantTimeHyp` for two executions that differ in their message bytes).
The internal compression has its own entry witness (`compress_entry_nonvacuous`), as does
`copy` (`Blake2sCopy.copy_correct_nonvacuous`).
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Blake2s (ContextHolds)

/-! ## A context holding a buffered stream, at 0x20000000 -/

def ctxBase : Word := 0x20000000#32

/-- The stream after absorbing three bytes into the empty stream. -/
def bufStream : Spec.Blake2s.State := Spec.Blake2s.absorb Spec.Blake2s.State.init [1, 2, 3]

/-- The 112 context bytes of the empty stream with three bytes `b` absorbed: `h0`,
`count = 0`, `buf` = `b` then zeros, `used = 3`, padding. -/
def ctxBytes3 (b : List (BitVec 8)) : List (BitVec 8) :=
  (Spec.Blake2s.h0.toList.flatMap Spec.Blake2s.bytesOfWord) ++ List.replicate 8 0 ++ b ++
    List.replicate 61 0 ++ le32 3 ++ List.replicate 4 0

/-- Its 112 context bytes: `h0`, `count = 0`, `buf` = 1 2 3 then zeros, `used = 3`, padding. -/
def bufCtxBytes : List (BitVec 8) := ctxBytes3 [1, 2, 3]

def bufMem : Mem := memOf [(ctxBase.toNat, bufCtxBytes)]

local macro "holds_witness" : tactic => `(tactic| (
  refine ⟨⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩, by decide +kernel⟩
  decide +kernel))

theorem buf_holds : ContextHolds bufMem ctxBase bufStream := by
  holds_witness

/-! ## Per-function witnesses -/

/-- `init` on the buffered context. -/
def iCtx : Blake2s.Init.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, ctxBase, bufMem,
   regsOf Artifacts.Release.blake2s_init 0x20000000 0 0 0⟩

/-- 100 input bytes at an odd address into the buffered stream. -/
def uCtx : Blake2s.Update.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, ctxBase, 0x20000201#32, 100#32, bufStream, bufMem,
   regsOf Artifacts.Release.blake2s_update 0x20000000 0x20000201 100 0⟩

/-- The digest of the buffered stream to an odd address. -/
def fCtx : Blake2s.Final.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, ctxBase, 0x20000203#32, bufStream, bufMem,
   regsOf Artifacts.Release.blake2s_final 0x20000000 0x20000203 0 0⟩

local macro "init_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩, ⟨rfl, rfl, ?_, ?_, ?_⟩, by decide,
    Region.not ret_out⟩
  all_goals first
    | decide +kernel
    | (simp only [Disj, Blake2s.Init.Ctx.fp, iCtx, Blake2s.initStackBytes, Blake2s.contextBytes,
        sp0, Artifacts.Release.size]; decide +kernel)
    | (simp only [Disj]; decide +kernel)))

/-- `h` proves that the call's context holds its stream. -/
local macro "update_witness " h:term : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, $h, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first
    | decide +kernel
    | (simp only [Disj, Blake2s.Update.Ctx.fp, uCtx, Blake2s.streamStackBytes,
        Blake2s.streamSavedBytes, Blake2s.streamPadBytes, Blake2s.compressFrameBytes,
        Blake2s.compressLocalsBytes, Blake2s.compressSavedBytes, Blake2s.contextBytes, sp0,
        Artifacts.Release.size]; decide +kernel)
    | (simp only [Disj]; decide +kernel)))

/-- `h` proves that the call's context holds its stream. -/
local macro "final_witness " h:term : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, $h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first
    | decide +kernel
    | (simp only [Disj, Blake2s.Final.Ctx.fp, fCtx, Blake2s.streamStackBytes,
        Blake2s.streamSavedBytes, Blake2s.streamPadBytes, Blake2s.compressFrameBytes,
        Blake2s.compressLocalsBytes, Blake2s.compressSavedBytes, Blake2s.contextBytes,
        Blake2s.digestBytes, sp0, Artifacts.Release.size]; decide +kernel)
    | (simp only [Disj]; decide +kernel)))

theorem init_pre_nonvacuous : Blake2s.Init.Pre iCtx (stOf bufMem iCtx.regs0) := by
  init_witness

theorem update_pre_nonvacuous : Blake2s.Update.Pre uCtx (stOf bufMem uCtx.regs0) := by
  update_witness buf_holds

theorem final_pre_nonvacuous : Blake2s.Final.Pre fCtx (stOf bufMem fCtx.regs0) := by
  final_witness buf_holds

example := Blake2s.Init.init_correct _ _ init_pre_nonvacuous
example := Blake2s.Update.update_correct.choose_spec _ _ update_pre_nonvacuous
example := Blake2s.Final.final_correct.choose_spec _ _ final_pre_nonvacuous

/-! ## Constant time: two valid calls with equal public inputs and different secrets

Each per-function constant-time theorem assumes two valid calls with equal `pub`. Each witness
below pairs the call above with a second one that differs only in secret memory:

* `init` has no secret argument and reads only the code and its stack: the second call runs
  on a context of zero bytes instead of the buffered stream.
* `update`: the second call's 100 input bytes are 0, 1, ..., 99 instead of zeros.
* `final`: the second context holds the stream with the bytes 4 5 6 absorbed instead of 1 2 3
  (the same number of pending bytes, which `pub` lists). -/

def zeroCtxMem : Mem := memOf [(ctxBase.toNat, List.replicate 112 0)]

/-- `iCtx` on a context of 112 zero bytes. -/
def iCtx2 : Blake2s.Init.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, ctxBase, zeroCtxMem,
   regsOf Artifacts.Release.blake2s_init 0x20000000 0 0 0⟩

theorem init_constant_time_nonvacuous :
    Blake2s.Init.Pre iCtx (stOf bufMem iCtx.regs0) ∧
      Blake2s.Init.Pre iCtx2 (stOf zeroCtxMem iCtx2.regs0) ∧ iCtx.pub = iCtx2.pub ∧
      Blake2s.bytesAt iCtx.m0 iCtx.context Blake2s.contextBytes ≠
        Blake2s.bytesAt iCtx2.m0 iCtx2.context Blake2s.contextBytes :=
  ⟨init_pre_nonvacuous, by init_witness, by simp only [Blake2s.Init.Ctx.pub, iCtx, iCtx2],
    by decide +kernel⟩

/-- `bufMem` with the input bytes 0, 1, ..., 99 at the input address of `uCtx`. -/
def uMem2 : Mem :=
  memOf [(ctxBase.toNat, bufCtxBytes), (0x20000201, (List.range 100).map (BitVec.ofNat 8 ·))]

def uCtx2 : Blake2s.Update.Ctx := { uCtx with m0 := uMem2 }

theorem update_constant_time_nonvacuous :
    Blake2s.Update.Pre uCtx (stOf bufMem uCtx.regs0) ∧
      Blake2s.Update.Pre uCtx2 (stOf uMem2 uCtx2.regs0) ∧ uCtx.pub = uCtx2.pub ∧
      uCtx.inputB ≠ uCtx2.inputB :=
  ⟨update_pre_nonvacuous, by update_witness Blake2s.holds_congr buf_holds (by decide +kernel),
    by simp only [Blake2s.Update.Ctx.pub, uCtx2], by decide +kernel⟩

/-- The stream after absorbing 4 5 6 into the empty stream. -/
def bufStream2 : Spec.Blake2s.State := Spec.Blake2s.absorb Spec.Blake2s.State.init [4, 5, 6]

def bufMem2 : Mem := memOf [(ctxBase.toNat, ctxBytes3 [4, 5, 6])]

theorem buf_holds2 : ContextHolds bufMem2 ctxBase bufStream2 := by
  holds_witness

def fCtx2 : Blake2s.Final.Ctx := { fCtx with stream := bufStream2, m0 := bufMem2 }

theorem pending_length2 : bufStream.pending.length = bufStream2.pending.length := by
  decide +kernel

theorem final_constant_time_nonvacuous :
    Blake2s.Final.Pre fCtx (stOf bufMem fCtx.regs0) ∧
      Blake2s.Final.Pre fCtx2 (stOf bufMem2 fCtx2.regs0) ∧ fCtx.pub = fCtx2.pub ∧
      fCtx.stream ≠ fCtx2.stream :=
  ⟨final_pre_nonvacuous, by final_witness buf_holds2,
    by simp only [Blake2s.Final.Ctx.pub, fCtx2, fCtx, pending_length2],
    fun h => absurd (congrArg Spec.Blake2s.State.pending h) (by decide +kernel)⟩

/-- The internal compression: `h` and `block` word aligned, `f0 = 0` at the stack top. -/
theorem compress_entry_nonvacuous :
    Blake2sCompress.Entry 0 (stOf bufMem (regsOf Blake2sCode.fnStart 0x20000000 0x20000100 0 0)) := by
  refine ⟨by decide, by decide, codeAt _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | decide +kernel
    | (left; decide +kernel)
    | (simp only [Disj, Blake2sCompress.fpOf, stOf, regsOf, Artifacts.Release.size]; decide +kernel)

example := Blake2sCompress.compress_correct compress_entry_nonvacuous ret_out

/-! ## `hash_correct` -/

/-- The hypotheses of the composed `HashCorrect` hold for a concrete call: the `init` witness
and the `update` call of `update_pre_nonvacuous`. (The premises inside `UpdatesReturn` are
per-call obligations; `update_pre_nonvacuous` and `final_pre_nonvacuous` show them
satisfiable.) -/
theorem hash_correct_nonvacuous :
    Blake2s.HashCorrectHyp iCtx (stOf bufMem iCtx.regs0) [stOf bufMem uCtx.regs0] :=
  ⟨init_pre_nonvacuous, by decide +kernel⟩

example := Blake2s.hash_correct _ _ _ hash_correct_nonvacuous

/-! ## `hash_constant_time`: two executions with different message bytes

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
  stOf (withMsg m msg) (regsOf Artifacts.Release.blake2s_update 0x20000000 0x20000200 msg.length 0)

/-- The `final` entry on the memory `m`: context at 0x20000000, output at the odd 0x20000203. -/
def fState (m : Mem) : State :=
  stOf m (regsOf Artifacts.Release.blake2s_final 0x20000000 0x20000203 0 0)

/-- Addresses below `msgBase` keep their byte in `withMsg` for a three-byte message. -/
theorem withMsg_low (m : Mem) (msg : List (BitVec 8)) (hl : msg.length = 3) (a : Word)
    (ha : a.toNat < 0x20000200) : withMsg m msg a = m a := by
  have h : ¬ (a - msgBase).toNat < msg.length := by
    rw [hl, BitVec.toNat_sub]
    simp only [msgBase, BitVec.toNat_ofNat]
    omega
  simp only [withMsg, h, ↓reduceIte]

theorem withMsg_bytes (m : Mem) (msg : List (BitVec 8)) (hl : msg.length = 3) :
    Blake2s.inputAt (uState m msg) = msg := by
  apply List.ext_getElem
  · simp [Blake2s.inputAt, Blake2s.bytesAt, uState, stOf, regsOf, hl]
  · intro i h1 h2
    have hi : i < 3 := hl ▸ h2
    simp only [Blake2s.inputAt, Blake2s.bytesAt, List.getElem_map, List.getElem_range]
    show withMsg m msg (0x20000200#32 + BitVec.ofNat 32 i) = _
    unfold withMsg
    have e : (0x20000200#32 + BitVec.ofNat 32 i - msgBase).toNat = i := by
      simp only [msgBase, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [e, h2, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

/-- A code address is in no region that starts at or above 0x20000000 and stays below 2^32. -/
theorem code_not_region {a r : Word} {n : Nat} (ha : a.toNat < Artifacts.Release.size)
    (hr : 0x20000000 ≤ r.toNat) (hn : r.toNat + n ≤ 2 ^ 32) : ¬ Region r n a := by
  intro h
  obtain ⟨o, ho, rfl⟩ := Region.exists h
  unfold Artifacts.Release.size at ha
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at ha
  omega

theorem uState_pre {m : Mem} {msg : List (BitVec 8)} (hl : msg.length = 3)
    (hcode : Thumb.CodeAt m 0 B) (st : Spec.Blake2s.State)
    (hst : ContextHolds (uState m msg).mem ctxBase st)
    (htot : st.count + st.pending.length + ((uState m msg).regs 2).toNat < 2 ^ 64) :
    Blake2s.Update.Pre (Blake2s.Update.callAt 0 st (uState m msg)) (uState m msg) := by
  have hcode' : Thumb.CodeAt (uState m msg).mem 0 B := codeAt_of_agree hcode fun a ha =>
    withMsg_low m msg hl a (by unfold Artifacts.Release.size at ha; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, hst, htot, ?_, ?_, ?_, ?_, ?_, hcode'⟩,
    ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩, (by decide : (0x00010001#32 : Word).getLsbD 0 = true), Region.not ret_out⟩
  all_goals first
    | decide +kernel
    | (simp only [uState, Disj, Blake2s.Update.Ctx.fp, Blake2s.Update.callAt, stOf, regsOf, hl,
        Blake2s.streamStackBytes, Blake2s.streamSavedBytes, Blake2s.streamPadBytes,
        Blake2s.compressFrameBytes, Blake2s.compressLocalsBytes, Blake2s.compressSavedBytes,
        Blake2s.contextBytes, sp0, Artifacts.Release.size]; decide +kernel)

theorem fState_pre {m : Mem} (hcode : Thumb.CodeAt m 0 B) (st : Spec.Blake2s.State)
    (hst : ContextHolds (fState m).mem ctxBase st) (htot : st.count + st.pending.length < 2 ^ 64) :
    Blake2s.Final.Pre (Blake2s.Final.callAt 0 st (fState m)) (fState m) := by
  refine ⟨⟨?_, ?_, ?_, ?_, hst, htot, ?_, ?_, ?_, ?_, ?_, ?_, hcode⟩,
    ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩, (by decide : (0x00010001#32 : Word).getLsbD 0 = true), Region.not ret_out⟩
  all_goals first
    | decide +kernel
    | (simp only [fState, Disj, Blake2s.Final.Ctx.fp, Blake2s.Final.callAt, stOf, regsOf,
        Blake2s.streamStackBytes, Blake2s.streamSavedBytes, Blake2s.streamPadBytes,
        Blake2s.compressFrameBytes, Blake2s.compressLocalsBytes, Blake2s.compressSavedBytes,
        Blake2s.contextBytes, Blake2s.digestBytes, sp0, Artifacts.Release.size]; decide +kernel)

/-- One execution after `init` returned with `t0`: the `update` call on `msg` runs, and the
`final` entry on its returned memory meets `final`'s obligations. -/
theorem update_then_final {t0 : State} (msg : List (BitVec 8)) (hl : msg.length = 3)
    (hcode : Thumb.CodeAt t0.mem 0 B) (hctx : ContextHolds t0.mem ctxBase Spec.Blake2s.State.init) :
    ∃ w, Blake2s.UpdatesRan 0 ctxBase t0.mem [(uState t0.mem msg, w)] ∧
      Blake2s.Final.EntryOn 0 ctxBase (fState w.mem) := by
  have hagree : Blake2s.ContextKept ctxBase t0.mem (uState t0.mem msg) := by
    intro o ho
    have ho' : o < 112 := ho
    apply withMsg_low _ _ hl
    simp only [ctxBase, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hentry : Blake2s.Update.EntryOn 0 ctxBase (uState t0.mem msg) :=
    ⟨rfl, fun st hst htot => uState_pre hl hcode st hst htot⟩
  have hP := hentry.2 _ (Blake2s.holds_congr hctx hagree) (by
    simp [uState, stOf, regsOf, hl, Spec.Blake2s.State.init])
  obtain ⟨_, hU⟩ := Blake2s.Update.update_correct
  obtain ⟨n, h⟩ := hU _ _ hP
  obtain ⟨w, tr, hrun, R, -⟩ := h n (Nat.le_refl n)
  have hcodew : Thumb.CodeAt w.mem 0 B := by
    have hu : Thumb.CodeAt (uState t0.mem msg).mem 0 B := codeAt_of_agree hcode fun a ha =>
      withMsg_low _ msg hl a (by unfold Artifacts.Release.size at ha; omega)
    refine codeAt_of_agree hu fun a ha => R.mem a ?_
    have hfp : (Blake2s.Update.callAt 0 Spec.Blake2s.State.init (uState t0.mem msg)).fp =
        BitVec.ofNat 32 sp0 - BitVec.ofNat 32 Blake2s.streamStackBytes := rfl
    have hcx : (Blake2s.Update.callAt 0 Spec.Blake2s.State.init (uState t0.mem msg)).context =
        ctxBase := rfl
    rintro (h | h)
    · rw [hfp] at h; exact code_not_region ha (by decide +kernel) (by decide +kernel) h
    · rw [hcx] at h; exact code_not_region ha (by decide +kernel) (by decide +kernel) h
  exact ⟨w, ⟨hagree, hentry, ⟨n, tr, hrun⟩, trivial⟩,
    ⟨rfl, fun st hst htot => fState_pre hcodew st hst htot⟩⟩

/-- The hypotheses of the composed `HashConstantTime` hold for two executions that differ in
their secret input: the same `init`, then one `update` on `msgA` in the first and on `msgB` in
the second (same address and length), then `final`. -/
theorem hash_constant_time_nonvacuous :
    ∃ t0 w w' : State,
      Blake2s.HashConstantTimeHyp iCtx iCtx (stOf bufMem iCtx.regs0) (stOf bufMem iCtx.regs0)
        t0 t0 (fState w.mem) (fState w'.mem) [(uState t0.mem msgA, w)] [(uState t0.mem msgB, w')] ∧
      [(uState t0.mem msgA, w)].map (fun p => Blake2s.inputAt p.1) = [msgA] ∧
      [(uState t0.mem msgB, w')].map (fun p => Blake2s.inputAt p.1) = [msgB] ∧ msgA ≠ msgB := by
  obtain ⟨n, h⟩ := Blake2s.Init.init_correct _ _ init_pre_nonvacuous
  obtain ⟨t0, tr, hrun, R, -⟩ := h n (Nat.le_refl n)
  have hcode : Thumb.CodeAt t0.mem 0 B := by
    refine codeAt_of_agree (codeAt [(ctxBase.toNat, bufCtxBytes)]) fun a ha => R.mem a ?_
    rintro (h | h)
    · exact code_not_region ha (by decide +kernel) (by decide +kernel) h
    · exact code_not_region ha (by decide +kernel) (by decide +kernel) h
  have hctx : ContextHolds t0.mem ctxBase Spec.Blake2s.State.init := R.holds
  obtain ⟨w, hcw, hfw⟩ := update_then_final msgA rfl hcode hctx
  obtain ⟨w', hcw', hfw'⟩ := update_then_final msgB rfl hcode hctx
  refine ⟨t0, w, w', ⟨init_pre_nonvacuous, init_pre_nonvacuous, rfl, ⟨n, tr, hrun⟩,
    ⟨n, tr, hrun⟩, hcw, hcw', rfl, by simp [uState, stOf, regsOf, msgA], fun _ _ => rfl, fun _ _ => rfl, hfw, hfw',
    rfl⟩, ?_, ?_, by decide⟩
  · simp only [List.map_cons, List.map_nil, withMsg_bytes _ msgA rfl]
  · simp only [List.map_cons, List.map_nil, withMsg_bytes _ msgB rfl]

end M0Crypto.Release.NonVacuity
