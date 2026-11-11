import M0Crypto.Release.ConstantTime.SubImm8

/-! Address-event agreement for checked multiple-register accesses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (LowReg)
open M0Crypto.Thumb

/-- A successful multiple-store transfer uses a public base address. -/
theorem stm_base_public {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : LowReg) (l : BitVec 8)
    (hx : xfer env off ctx (.stm n l) st = .ok out) : (st.get n.val).pub = true := by
  cases ha : st.get n.val <;> simp_all [xfer, xferCore, AbsVal.pub]
  split at hx <;> contradiction

/-- A successful multiple-load transfer uses a public base address. -/
theorem ldm_base_public {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : LowReg) (l : BitVec 8)
    (hx : xfer env off ctx (.ldm n l) st = .ok out) : (st.get n.val).pub = true := by
  cases ha : st.get n.val <;> simp_all [xfer, xferCore, AbsVal.pub]
  split at hx <;> contradiction

/-- Accepted multiple-register accesses emit identical address lists in both runs. -/
theorem stm_accesses_eq {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {out : Out}
    (n : LowReg) (l : BitVec 8) (hx : xfer env off ctx (.stm n l) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂) :
    (Instr.stm n l).accesses s₁ = (Instr.stm n l).accesses s₂ := by
  have he := AbsVal.sem_public (lowReg_sem n h) (stm_base_public n l hx)
  simp [Instr.accesses, he]

theorem ldm_accesses_eq {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {out : Out}
    (n : LowReg) (l : BitVec 8) (hx : xfer env off ctx (.ldm n l) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂) :
    (Instr.ldm n l).accesses s₁ = (Instr.ldm n l).accesses s₂ := by
  have he := AbsVal.sem_public (lowReg_sem n h) (ldm_base_public n l hx)
  simp [Instr.accesses, he]

end M0Crypto.Release.ConstantTime
