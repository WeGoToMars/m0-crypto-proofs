import M0Crypto.Release.ConstantTime.ExactStoreSites
import M0Crypto.Release.ConstantTime.AeadEncryptEntry
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Untracked stores of the AEAD certificates

Every store the certificate does not track as a stack store is, in the decrypt certificate, at an
output-store instruction of ChaCha with the counter slot known to be `1`. In the encrypt
certificate the same holds except for the sixteen tag-emit stores of the finish routine.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Aead

/-- Stack slot, relative to the entry SP, of the ChaCha counter word `A + 4`. -/
def counterSlot : Int := 4 - aeadFrame

/-- First tag-emit store of the finish routine: the emit sequence starts with `mov r1, r12`,
which stores nothing. -/
def emitStoresAt : Nat := Poly1305Finish.emitAt + seqSize [.movHi 1 12]

/-- Offsets of the tag-emit stores of the finish routine, in the context of the encrypt call of
finish (its return address). -/
def emitSite (off : Nat) (ctx : Option Nat) : Bool :=
  ctx == some (encFinishAt + blSize) && decide (emitStoresAt ≤ off ∧ off < Poly1305Finish.clearAt)

def walkCounter (env : Env) (allow : Nat → Option Nat → Bool) (ctx : Option Nat) :
    Nat → AbsState → List Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    (!untrackedStore st i ||
      (outputStoreOffset off && stkGet st.stk counterSlot == AbsVal.num 1 1) || allow off ctx) &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out => match out.succs with
      | [(_, next)] => walkCounter env allow ctx (off + i.size) next is
      | _ => walkCounter env allow ctx (off + i.size) st is

def certCounter (env : Env) (allow : Nat → Option Nat → Bool) (cert : Cert) : Bool :=
  cert.all fun b => walkCounter env allow b.ctx b.off b.st b.code

theorem blockPoint_counter {env : Env} {allow} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Instr} (hc : walkCounter env allow b.ctx b.off b.st b.code = true)
    (hp : BlockPoint env b off st code) : walkCounter env allow b.ctx off st code = true := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkCounter, Bool.and_eq_true, hx, hs] at ih
    exact ih.2

theorem decrypt_counter : certCounter decryptEnv (fun _ _ => false) decryptCert = true := by
  decide +kernel

theorem encrypt_counter : certCounter encryptEnv emitSite encryptCert = true := by
  decide +kernel

/-- The counter slot value, from the certificate state. -/
theorem counter_of_stack {p : Params} {st : AbsState} {x y : State} {mem : M0Crypto.Armv6M.Mem}
    {m2 : M0Crypto.Armv6M.Mem} (hst : StkSem p st.stk mem m2)
    (h : stkGet st.stk counterSlot == AbsVal.num 1 1) :
    M0Crypto.Armv6M.read32 mem (p.sp0 + BitVec.ofInt 32 counterSlot) = 1#32 := by
  have h' : stkGet st.stk counterSlot = AbsVal.num 1 1 := by simpa using h
  have := hst counterSlot
  rw [h'] at this
  obtain ⟨-, h1, h2⟩ := this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- At an untracked store of a certified point, either the site is an output-store instruction
with counter word `1`, or the `allow` exception applies. -/
theorem untracked_cases {env : Env} {allow} {cert : Cert} (hcert : certCounter env allow cert = true)
    {b : Blk} {off : Nat} {st : AbsState} {i : Instr} {is : List Instr} (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (hu : untrackedStore st i = true) :
    (outputStoreOffset off = true ∧ stkGet st.stk counterSlot == AbsVal.num 1 1) ∨ allow off b.ctx = true := by
  have hw := blockPoint_counter (List.all_eq_true.mp hcert b hm) hp
  simp only [walkCounter, Bool.and_eq_true, hu, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hw
  rcases hw.1 with h | h
  · left; simpa [Bool.and_eq_true] using h
  · right; exact h

end M0Crypto.Release.ConstantTime
