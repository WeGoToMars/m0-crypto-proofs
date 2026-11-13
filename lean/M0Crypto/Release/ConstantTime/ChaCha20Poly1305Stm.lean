import M0Crypto.Release.ConstantTime.StmCertificate
import M0Crypto.Release.ConstantTime.AeadDecryptEntry

/-!
The `stm` stack certificate of AEAD decryption.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

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
