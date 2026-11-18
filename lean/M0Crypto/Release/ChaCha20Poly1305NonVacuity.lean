import M0Crypto.Release.NonVacuityBase
import M0Crypto.Release.AeadEncrypt
import M0Crypto.Release.AeadDecrypt
import M0Crypto.Release.ChaCha20TraceSpec
import M0Crypto.Release.ChaCha20XorDiscipline
import M0Crypto.Release.AeadDiscipline

/-!
# Non-vacuity of the ChaCha20 and ChaCha20-Poly1305 entry contracts

For each function, one concrete call that meets the hypothesis shared by all of the
function's top-level theorems (`ChaCha20Xor.Pre`, `Aead.APre`), passed to its correctness
theorem (`example`s). The calls exercise the cases where an over-strong
precondition would hide: in-place operation, unaligned buffers and a non-empty message.
For each function, `*_constant_time_nonvacuous` gives two valid calls with equal public inputs
and different keys, the hypothesis of its constant-time theorem.
The `*_interrupted_nonvacuous` witnesses give the first call 256 bytes of handler room and a
handler that also writes one byte outside the call's regions, the hypotheses of the function's
interrupted-call theorem.
-/

namespace M0Crypto.Release.NonVacuity

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Release.Frame (Disj Ctx Valid)
open M0Crypto.Release.Aead (ACall AValid ABuf AEntry)

/-! ## ChaCha20: in place, 100 bytes at an odd address, counter 1 -/

def chMem : Mem := memOf [(sp0, le32 0x20000340 ++ le32 1)]

def chCtx : Frame.Ctx :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000401#32, 100#32, 0x20000300#32, 0x20000340#32,
   1#32, chMem, regsOf 0 0x20000401 0x20000401 100 0x20000300⟩

local macro "xor_witness" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, codeAt _⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, Frame.Ctx.fp, chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, Artifacts.Release.size]; decide +kernel) | (simp only [Disj]; decide +kernel)))

theorem xor_correct_nonvacuous : ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) := by
  xor_witness

/-! ## AEAD: in place, 100 bytes at an odd address, 13-byte AAD, unaligned tag -/

def aMem : Mem :=
  memOf [(sp0, le32 0x20000500 ++ le32 13 ++ le32 0x20000300 ++ le32 0x20000340)]

def aCall (off : Nat) : ACall :=
  ⟨0, BitVec.ofNat 32 sp0, 0x20000401#32, 0x20000483#32, 0x20000401#32, 100#32, 0x20000500#32,
   13#32, 0x20000300#32, 0x20000340#32, aMem, regsOf off 0x20000401 0x20000483 0x20000401 100⟩

/-- `code` proves `CodeAt` of the call's memory. -/
local macro "aead_witness " code:term : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, $code⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by decide +kernel, Region.not ret_out⟩
  all_goals first | decide +kernel | (left; decide +kernel) | (simp only [Disj, aCall, Artifacts.Release.size]; decide +kernel) | (simp only [Disj]; decide +kernel)))

theorem encrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) := by
  aead_witness codeAt _

theorem decrypt_correct_nonvacuous :
    Aead.APre (aCall Aead.decOff) Aead.decOff (stOf aMem (aCall Aead.decOff).regs0) := by
  aead_witness codeAt _

/-! ## Each witness fits its theorem -/

example := ChaCha20Xor.xor_correct _ _ xor_correct_nonvacuous
example := Aead.encrypt_correct.choose_spec _ _ encrypt_correct_nonvacuous
example := Aead.decrypt_correct.choose_spec _ _ decrypt_correct_nonvacuous

/-! ## Constant time: two valid calls with equal public inputs and different keys

Each constant-time theorem assumes two valid calls with equal `pub`. The witnesses below give
two such calls that differ in the key bytes, the secret of every function. The first calls
above use the all-zero key at 0x20000300; the second calls put `key2` there. -/

/-- The second key: bytes 0, 1, ..., 31. -/
def key2 : List (BitVec 8) := (List.range 32).map (BitVec.ofNat 8 ·)

def chMem2 : Mem := memOf [(sp0, le32 0x20000340 ++ le32 1), (0x20000300, key2)]

/-- `chCtx` with `key2`. -/
def chCtx2 : Frame.Ctx := { chCtx with m0 := chMem2 }

theorem xor_constant_time_nonvacuous :
    ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) ∧
      ChaCha20Xor.Pre chCtx2 (stOf chMem2 chCtx2.regs0) ∧
      chCtx.pub = chCtx2.pub ∧ chCtx.keyB ≠ chCtx2.keyB :=
  ⟨xor_correct_nonvacuous, by xor_witness, rfl, by decide +kernel⟩

/-- The stack arguments of `aCall` and the key `k` at its key address. -/
def aRegions (k : List (BitVec 8)) : List (Nat × List (BitVec 8)) :=
  [(sp0, le32 0x20000500 ++ le32 13 ++ le32 0x20000300 ++ le32 0x20000340), (0x20000300, k)]

def aMem2 : Mem := memOf (aRegions key2)

/-- `aCall off` with `key2`. -/
def aCall2 (off : Nat) : ACall := { aCall off with m0 := aMem2 }

theorem encrypt_constant_time_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) ∧
      Aead.APre (aCall2 Aead.encOff) Aead.encOff (stOf aMem2 (aCall2 Aead.encOff).regs0) ∧
      (aCall Aead.encOff).pub = (aCall2 Aead.encOff).pub ∧
      (aCall Aead.encOff).keyB ≠ (aCall2 Aead.encOff).keyB :=
  ⟨encrypt_correct_nonvacuous, by aead_witness codeAt _, rfl, by decide +kernel⟩

/-! Decryption also needs equal verdicts. Each call below carries, at `tag`, the tag that its
key gives the all-zero nonce, AAD and ciphertext of `aCall`, so both calls accept. -/

def zeros (n : Nat) : List (BitVec 8) := List.replicate n 0#8

/-- The tag of the all-zero nonce, 13-byte AAD and 100-byte ciphertext under `k`. -/
def tagOf (k : List (BitVec 8)) : List (BitVec 8) :=
  Spec.Aead.poly1305 (Spec.Aead.polyKey k (zeros 12)) (Spec.Aead.macData (zeros 13) (zeros 100))

/-- The tag address of `aCall`. -/
def tagAt : Word := 0x20000483#32

/-- The decryption memory for key `k`: the stack arguments, `k`, and `tagOf k` at `tagAt`. -/
def dMem (k : List (BitVec 8)) : Mem := fun a =>
  if (a - tagAt).toNat < 16 then (tagOf k).getD (a - tagAt).toNat 0
  else memOf (aRegions k) a

def dCall (k : List (BitVec 8)) : ACall := { aCall Aead.decOff with m0 := dMem k }

theorem dMem_code (k : List (BitVec 8)) : Thumb.CodeAt (dMem k) 0 B :=
  codeAt_of_agree (codeAt (aRegions k)) fun a ha => by
    have : ¬ (a - tagAt).toNat < 16 := by
      simp only [tagAt, BitVec.toNat_sub, BitVec.toNat_ofNat]
      unfold Artifacts.Release.size at ha; omega
    simp only [dMem, this, ↓reduceIte]

theorem dCall_tagB (k : List (BitVec 8)) : (dCall k).tagB = tagOf k := by
  have hl : (tagOf k).length = 16 := Poly1305Spec.leBytes_length _ _
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 16
  · show (Frame.Ctx.bytesAt (dMem k) tagAt 16)[i]? = _
    rw [Frame.bytesAt_get _ _ _ _ hi]
    have e : (tagAt + BitVec.ofNat 32 i - tagAt).toNat = i := by
      simp only [tagAt, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [dMem, e, hi, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (hl ▸ hi : i < (tagOf k).length), Option.getD_some]
  · show (Frame.Ctx.bytesAt (dMem k) tagAt 16)[i]? = _
    rw [List.getElem?_eq_none (by rw [Frame.bytesAt_length]; omega),
      List.getElem?_eq_none (by omega)]

theorem dCall_pub (k k' : List (BitVec 8)) : (dCall k).pub = (dCall k').pub := by
  simp only [ACall.pub, dCall]

theorem dCall_verdict (k : List (BitVec 8)) (hk : (dCall k).keyB = k)
    (hn : (dCall k).nonceB = zeros 12) (ha : (dCall k).aadB = zeros 13)
    (hp : (dCall k).ptB = zeros 100) : (dCall k).verdict := by
  show Spec.Aead.poly1305 (Spec.Aead.polyKey (dCall k).keyB (dCall k).nonceB)
    (Spec.Aead.macData (dCall k).aadB (dCall k).ptB) = (dCall k).tagB
  rw [hk, hn, ha, hp, dCall_tagB]; rfl

theorem decrypt_constant_time_nonvacuous :
    Aead.APre (dCall (zeros 32)) Aead.decOff (stOf (dMem (zeros 32)) (dCall (zeros 32)).regs0) ∧
      Aead.APre (dCall key2) Aead.decOff (stOf (dMem key2) (dCall key2).regs0) ∧
      (dCall (zeros 32)).pub = (dCall key2).pub ∧
      (dCall (zeros 32)).verdict = (dCall key2).verdict ∧
      (dCall (zeros 32)).keyB ≠ (dCall key2).keyB := by
  have v1 := dCall_verdict (zeros 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have v2 := dCall_verdict key2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  exact ⟨by aead_witness dMem_code _, by aead_witness dMem_code _, dCall_pub _ _,
    propext ⟨fun _ => v2, fun _ => v1⟩, by decide +kernel⟩

/-! ## Interrupts: 256 bytes of handler room below the stack window -/

/-- The call of `xor_correct_nonvacuous` with 256 bytes of handler room, and a handler that
zeroes the 256 bytes below SP and increments the byte at 0x20002000, as `xor_interrupted`
assumes them. -/
theorem xor_interrupted_nonvacuous :
    ChaCha20Xor.Pre chCtx (stOf chMem chCtx.regs0) ∧
      TraceSpec.HandlerRoom 256 ChaCha20Layout.chStackBytes chCtx.sp0
        (fun y => TraceSpec.ChaCha20XorReadRegion chCtx y ∨ ChaCha20Xor.WrOk chCtx y ∨
          Region chCtx.out chCtx.len.toNat y) ∧
      TraceSpec.Handlers 256
        (fun y => TraceSpec.ChaCha20XorReadRegion chCtx y ∨ ChaCha20Xor.WrOk chCtx y ∨
          Region chCtx.out chCtx.len.toNat y)
        (tickBelowSp 256 0x20002000#32) := by
  refine ⟨xor_correct_nonvacuous, interruptWitness_of [(chCtx.inp, 100), (chCtx.key, 32),
    (chCtx.nonce, 12), (chCtx.base, Artifacts.Release.size),
    (chCtx.fp, ChaCha20Layout.chStackBytes + 8)] ?_ ?_ ?_⟩
  · simp only [chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, sp0]
    decide
  · intro y hy
    rcases hy with (h | h | h | h | h) | (h | ⟨-, h⟩) | h
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))),
        show (y - chCtx.fp).toNat < ChaCha20Layout.chStackBytes + 8 by unfold Region at h; omega⟩
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .head _, h⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      Disj, Frame.Ctx.fp, chCtx, ChaCha20Layout.chStackBytes, ChaCha20Layout.chStackWords, sp0,
      Artifacts.Release.size]
    decide +kernel

example := ChaCha20Xor.xor_interrupted 256 _ _ xor_interrupted_nonvacuous.1
  xor_interrupted_nonvacuous.2.1 _ xor_interrupted_nonvacuous.2.2

/-- The call of `encrypt_correct_nonvacuous` with 256 bytes of handler room, and a handler that
zeroes the 256 bytes below SP and increments the byte at 0x20002000, as `encrypt_interrupted`
assumes them. -/
theorem encrypt_interrupted_nonvacuous :
    Aead.APre (aCall Aead.encOff) Aead.encOff (stOf aMem (aCall Aead.encOff).regs0) ∧
      TraceSpec.HandlerRoom 256 TraceSpec.aeadStackBytes (aCall Aead.encOff).sp0
        (fun y => TraceSpec.AeadEncryptReadRegion (aCall Aead.encOff) y ∨ Aead.AWr (aCall Aead.encOff) y) ∧
      TraceSpec.Handlers 256
        (fun y => TraceSpec.AeadEncryptReadRegion (aCall Aead.encOff) y ∨ Aead.AWr (aCall Aead.encOff) y)
        (tickBelowSp 256 0x20002000#32) := by
  have e : (aCall Aead.encOff).A - 176#32 =
      (aCall Aead.encOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes := by decide
  refine ⟨encrypt_correct_nonvacuous, interruptWitness_of [((aCall Aead.encOff).inp, 100), ((aCall Aead.encOff).aad, 13), ((aCall Aead.encOff).key, 32), ((aCall Aead.encOff).nonce, 12), ((aCall Aead.encOff).out, 100), ((aCall Aead.encOff).base, Artifacts.Release.size), ((aCall Aead.encOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes, TraceSpec.aeadStackBytes + 16), ((aCall Aead.encOff).tag, 16)] ?_ ?_ ?_⟩
  · simp only [aCall, TraceSpec.aeadStackBytes, sp0]
    decide
  · intro y hy
    rcases hy with (h | h | h | h | h | h | h) | (h | h | h)
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), show Region ((aCall Aead.encOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes) (TraceSpec.aeadStackBytes + 16) y by
        unfold Aead.SWr at h; rw [e] at h; unfold Region at h ⊢; rw [TraceSpec.aeadStackBytes_eq] at h ⊢; omega⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), h⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      Disj, aCall, TraceSpec.aeadStackBytes, sp0, Artifacts.Release.size]
    decide +kernel

example := Aead.encrypt_interrupted 256 _ _ encrypt_interrupted_nonvacuous.1
  encrypt_interrupted_nonvacuous.2.1 _ encrypt_interrupted_nonvacuous.2.2

/-- The call of `decrypt_correct_nonvacuous` with 256 bytes of handler room, and a handler that
zeroes the 256 bytes below SP and increments the byte at 0x20002000, as `decrypt_interrupted`
assumes them. -/
theorem decrypt_interrupted_nonvacuous :
    Aead.APre (aCall Aead.decOff) Aead.decOff (stOf aMem (aCall Aead.decOff).regs0) ∧
      TraceSpec.HandlerRoom 256 TraceSpec.aeadStackBytes (aCall Aead.decOff).sp0
        (fun y => TraceSpec.AeadDecryptReadRegion (aCall Aead.decOff) y ∨ Aead.DWr (aCall Aead.decOff) y) ∧
      TraceSpec.Handlers 256
        (fun y => TraceSpec.AeadDecryptReadRegion (aCall Aead.decOff) y ∨ Aead.DWr (aCall Aead.decOff) y)
        (tickBelowSp 256 0x20002000#32) := by
  have e : (aCall Aead.decOff).A - 176#32 =
      (aCall Aead.decOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes := by decide
  refine ⟨decrypt_correct_nonvacuous, interruptWitness_of [((aCall Aead.decOff).inp, 100), ((aCall Aead.decOff).aad, 13), ((aCall Aead.decOff).key, 32), ((aCall Aead.decOff).nonce, 12), ((aCall Aead.decOff).tag, 16), ((aCall Aead.decOff).base, Artifacts.Release.size), ((aCall Aead.decOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes, TraceSpec.aeadStackBytes + 16), ((aCall Aead.decOff).out, 100)] ?_ ?_ ?_⟩
  · simp only [aCall, TraceSpec.aeadStackBytes, sp0]
    decide
  · intro y hy
    rcases hy with (h | h | h | h | h | h | h) | (h | h)
    · exact ⟨_, .head _, h⟩
    · exact ⟨_, .tail _ (.head _), h⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), h⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), show Region ((aCall Aead.decOff).sp0 - BitVec.ofNat 32 TraceSpec.aeadStackBytes) (TraceSpec.aeadStackBytes + 16) y by
        unfold Aead.SWr at h; rw [e] at h; unfold Region at h ⊢; rw [TraceSpec.aeadStackBytes_eq] at h ⊢; omega⟩
    · exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), h⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      Disj, aCall, TraceSpec.aeadStackBytes, sp0, Artifacts.Release.size]
    decide +kernel

example := Aead.decrypt_interrupted 256 _ _ decrypt_interrupted_nonvacuous.1
  decrypt_interrupted_nonvacuous.2.1 _ decrypt_interrupted_nonvacuous.2.2

end M0Crypto.Release.NonVacuity
