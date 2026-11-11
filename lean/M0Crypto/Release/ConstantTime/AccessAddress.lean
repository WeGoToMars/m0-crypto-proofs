import M0Crypto.Release.ConstantTime.SemArithmetic
import M0Crypto.Release.ConstantTime.MovSound

/-! Address equality for checked memory accesses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)

/-- A successful transfer cannot use a secret address. -/
theorem access_public {env : Env} {st : AbsState} {a : AbsVal} {w : Nat}
    {isLoad : Bool} {t : Nat} {out : AbsState × List SiteK}
    (h : access env st a w isLoad t = .ok out) : a.pub = true := by
  cases a <;> simp_all [access, AbsVal.pub]

/-- Checked addresses denote the same concrete address in both executions. -/
theorem access_address_eq {env : Env} {st : AbsState} {a : AbsVal} {w : Nat}
    {isLoad : Bool} {t : Nat} {out : AbsState × List SiteK} {p : Params} {x y : Word}
    (h : access env st a w isLoad t = .ok out) (hs : AbsVal.Sem p a x y) : x = y :=
  AbsVal.sem_public hs (access_public h)

/-- An immediate-offset access has the same address in both runs. -/
theorem access_addK_address_eq {env : Env} {st : AbsState} {a : AbsVal} {w k : Nat}
    {isLoad : Bool} {t : Nat} {out : AbsState × List SiteK} {p : Params} {x y : Word}
    (h : access env st (a.addK k) w isLoad t = .ok out) (hs : AbsVal.Sem p a x y) :
    x + BitVec.ofNat 32 k = y + BitVec.ofNat 32 k :=
  access_address_eq h (AbsVal.addK_sound k hs)

/-- A register-offset access has the same address in both runs. -/
theorem access_add_address_eq {env : Env} {st : AbsState} {a b : AbsVal} {w : Nat}
    {isLoad : Bool} {t : Nat} {out : AbsState × List SiteK} {p : Params} {x₁ x₂ y₁ y₂ : Word}
    (h : access env st (a.add b) w isLoad t = .ok out)
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) : x₁ + y₁ = x₂ + y₂ :=
  access_address_eq h (AbsVal.add_sound ha hb)

/-- Low-register values have the interpretation recorded in the abstract state. -/
theorem lowReg_sem {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (r : M0Crypto.Armv6M.LowReg)
    (h : LowEq p bytes off st s₁ s₂) :
    AbsVal.Sem p (st.get r.val) (s₁.reg r) (s₂.reg r) := by
  have hr : regIndexOk r.val := by
    constructor <;> have := r.isLt <;> simp [numRegs] <;> omega
  have hr16 : r.val < 16 := by have := r.isLt; omega
  have hv := h.regs r.val hr.1 hr.2
  rw [regAt_eq_regs s₁ r.val hr16, regAt_eq_regs s₂ r.val hr16] at hv
  simpa [M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.LowReg.toReg] using hv

/-- Immediate-address instructions accepted by the transfer have matching access events. -/
theorem memImm_accesses_eq {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {out : Out}
    (op : M0Crypto.Thumb.MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hx : xfer env off ctx (.memImm op t n imm) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂) :
    (M0Crypto.Thumb.Instr.memImm op t n imm).accesses s₁ =
      (M0Crypto.Thumb.Instr.memImm op t n imm).accesses s₂ := by
  have ha : ∃ result, access env st ((st.get n.val).addK (imm.toNat * op.width))
      op.width op.isLoad t.val = .ok result := by
    simp only [xfer] at hx
    split at hx <;> simp_all [xferCore]
    split at hx <;> simp_all
  obtain ⟨result, hr⟩ := ha
  have he := access_addK_address_eq hr (lowReg_sem n h)
  simp [M0Crypto.Thumb.Instr.accesses, he]

/-- Register-address instructions accepted by the transfer have matching access events. -/
theorem memReg_accesses_eq {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {out : Out}
    (op : M0Crypto.Thumb.MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hx : xfer env off ctx (.memReg op t n m) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂) :
    (M0Crypto.Thumb.Instr.memReg op t n m).accesses s₁ =
      (M0Crypto.Thumb.Instr.memReg op t n m).accesses s₂ := by
  have ha : ∃ result, access env st ((st.get n.val).add (st.get m.val))
      op.width op.isLoad t.val = .ok result := by
    simp only [xfer] at hx
    split at hx <;> simp_all [xferCore]
    split at hx <;> simp_all
    split at hx <;> simp_all
  obtain ⟨result, hr⟩ := ha
  have he := access_add_address_eq hr (lowReg_sem n h) (lowReg_sem m h)
  simp [M0Crypto.Thumb.Instr.accesses, he]

end M0Crypto.Release.ConstantTime
