import M0Crypto.Release.ConstantTime.AccessBufferLoad

/-! Paired certificate steps for single-register memory instructions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg)
open M0Crypto.Thumb

/-- Immediate-offset accesses preserve paired certificate execution when
buffer stores satisfy their concrete separation obligations. -/
theorem certPoint_memImm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n : LowReg) (imm : BitVec 5)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memImm op t n imm :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : ((st.get n.val).addK (imm.toNat * op.width)).isSp = false →
      op.isLoad = false →
      M0Crypto.Release.Frame.Disj p.base bytes.length
        (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s₁.reg n + BitVec.ofNat 32 (imm.toNat * op.width)) op.width)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  cases ha : (st.get n.val).addK (imm.toNat * op.width) with
  | sp x y =>
    cases hop : op.isLoad with
    | false => exact certPoint_memImm_stack_store_paired op t n imm hop ha hc hi hslots hm hp hrel hwidth hdisj heven
    | true => exact certPoint_memImm_stack_load_paired op t n imm hop ha hc hi hm hp hrel heven
  | hi | lo | num | ret | lr0 =>
    have hn : ((st.get n.val).addK (imm.toNat * op.width)).isSp = false := by simp [ha, AbsVal.isSp]
    cases hop : op.isLoad with
    | false =>
      have ⟨hcode, hstack⟩ := hbuffer hn hop
      exact certPoint_memImm_buffer_store_paired op t n imm hop hn hc hi hslots hm hp hrel hcode hstack heven
    | true => exact certPoint_memImm_buffer_load_paired op t n imm hop hn hc hi hm hp hrel heven

/-- Register-offset accesses preserve paired certificate execution when
buffer stores satisfy their concrete separation obligations. -/
theorem certPoint_memReg_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (op : MemOp) (t n m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.memReg op t n m :: is))
    (hrel : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : ((st.get n.val).add (st.get m.val)).isSp = false →
      op.isLoad = false →
      M0Crypto.Release.Frame.Disj p.base bytes.length
        (s₁.reg n + s₁.reg m) op.width ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s₁.reg n + s₁.reg m) op.width)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  cases ha : (st.get n.val).add (st.get m.val) with
  | sp x y =>
    cases hop : op.isLoad with
    | false => exact certPoint_memReg_stack_store_paired op t n m hop ha hc hi hslots hm hp hrel hwidth hdisj heven
    | true => exact certPoint_memReg_stack_load_paired op t n m hop ha hc hi hm hp hrel heven
  | hi | lo | num | ret | lr0 =>
    have hn : ((st.get n.val).add (st.get m.val)).isSp = false := by simp [ha, AbsVal.isSp]
    cases hop : op.isLoad with
    | false =>
      have ⟨hcode, hstack⟩ := hbuffer hn hop
      exact certPoint_memReg_buffer_store_paired op t n m hop hn hc hi hslots hm hp hrel hcode hstack heven
    | true => exact certPoint_memReg_buffer_load_paired op t n m hop hn hc hi hm hp hrel heven

end M0Crypto.Release.ConstantTime
