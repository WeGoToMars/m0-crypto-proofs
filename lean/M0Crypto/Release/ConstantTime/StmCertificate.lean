import M0Crypto.Release.ConstantTime.InstructionCases
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-! Checking the abstract bases of multiple-register stores. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- Check the base at every multiple-store instruction in a block. -/
def walkStmStack (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    (match i with | .stm n _ => (st.get n.val).isSp | _ => true) &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out =>
      match out.succs with
      | [(_, next)] => walkStmStack env ctx (off + i.size) next is
      | _ => walkStmStack env ctx (off + i.size) st is

def certStmStack (env : Env) (cert : Cert) : Bool :=
  cert.all fun b => walkStmStack env b.ctx b.off b.st b.code

theorem blockPoint_stmStack {env : Env} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Instr} (hc : walkStmStack env b.ctx b.off b.st b.code = true)
    (hp : BlockPoint env b off st code) : walkStmStack env b.ctx off st code = true := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkStmStack, Bool.and_eq_true, hx, hs] at ih
    exact ih.2

theorem certPoint_stmStack {env : Env} {cert : Cert} {b : Blk} {off : Nat}
    {st : AbsState} {n : M0Crypto.Armv6M.LowReg} {l : BitVec 8} {is : List Instr}
    (hc : certStmStack env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.stm n l :: is)) :
    ∃ lo hi, st.get n.val = .sp lo hi := by
  have hw := blockPoint_stmStack (List.all_eq_true.mp hc b hm) hp
  simp only [walkStmStack, Bool.and_eq_true] at hw
  have hs : (st.get n.val).isSp = true := hw.1
  cases h : st.get n.val <;> simp [h, AbsVal.isSp] at hs ⊢

theorem decrypt_stmStack : certStmStack decryptEnv decryptCert = true := by
  decide +kernel

/-- Multiple-store sites in the checked decryption certificate require no
untracked-buffer separation premise. -/
theorem decrypt_stm_bufferStoreOk {p : Params} {bytes : List (BitVec 8)} {s : M0Crypto.Armv6M.State}
    {b : Blk} {off : Nat} {st : AbsState} {n : M0Crypto.Armv6M.LowReg} {l : BitVec 8}
    {is : List Instr} (hm : b ∈ decryptCert)
    (hp : BlockPoint decryptEnv b off st (.stm n l :: is)) :
    BufferStoreOk decryptEnv p bytes st s (.stm n l) := by
  obtain ⟨lo, hi, hs⟩ := certPoint_stmStack decrypt_stmStack hm hp
  intro h
  exact False.elim (h lo hi hs)

end M0Crypto.Release.ConstantTime

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- Untracked single-register stores use the output pointer register. -/
def outputStoreBaseCheck (st : AbsState) : Instr → Bool
  | .memImm op _ n imm =>
    op.isLoad || ((st.get n.val).addK (imm.toNat * op.width)).isSp || (n.val == 3)
  | .memReg op _ n m =>
    op.isLoad || ((st.get n.val).add (st.get m.val)).isSp || (n.val == 3)
  | _ => true

def walkOutputStoreBase (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Bool
  | _, _, [] => true
  | off, st, i :: is =>
    outputStoreBaseCheck st i &&
    match xfer env off ctx i st with
    | .error _ => false
    | .ok out =>
      match out.succs with
      | [(_, next)] => walkOutputStoreBase env ctx (off + i.size) next is
      | _ => walkOutputStoreBase env ctx (off + i.size) st is

end M0Crypto.Release.ConstantTime
