import M0Crypto.Release.ConstantTime.BufferSeparation

/-! Relating functional write bounds to concrete store accesses. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg)
open M0Crypto.Thumb
open M0Crypto.Release (WritesTo)

/-- A recorded immediate-offset store inherits the functional trace's per-byte
write predicate. -/
theorem memImm_trace_write_bounds {Wr : Word → Prop} {tr : List Event} {e : Event}
    (op : MemOp) (t n : LowReg) (imm : BitVec 5) (s : State)
    (hop : op.isLoad = false) (hw : WritesTo Wr tr) (he : e ∈ tr)
    (ha : e.accesses = (Instr.memImm op t n imm).accesses s) :
    ∀ k, k < op.width → Wr (s.reg n + BitVec.ofNat 32 (imm.toNat * op.width) + BitVec.ofNat 32 k) := by
  intro k hk
  apply hw e he _
  rw [ha]
  refine ⟨⟨.write, s.reg n + BitVec.ofNat 32 (imm.toNat * op.width), op.width⟩, ?_, rfl, k, hk, rfl⟩
  simp [Instr.accesses, hop]

/-- A recorded register-offset store inherits the functional trace's per-byte
write predicate. -/
theorem memReg_trace_write_bounds {Wr : Word → Prop} {tr : List Event} {e : Event}
    (op : MemOp) (t n m : LowReg) (s : State)
    (hop : op.isLoad = false) (hw : WritesTo Wr tr) (he : e ∈ tr)
    (ha : e.accesses = (Instr.memReg op t n m).accesses s) :
    ∀ k, k < op.width → Wr (s.reg n + s.reg m + BitVec.ofNat 32 k) := by
  intro k hk
  apply hw e he _
  rw [ha]
  refine ⟨⟨.write, s.reg n + s.reg m, op.width⟩, ?_, rfl, k, hk, rfl⟩
  simp [Instr.accesses, hop]

end M0Crypto.Release.ConstantTime
