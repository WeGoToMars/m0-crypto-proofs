import SafegcdRow.Blocks
import SafegcdRow.FoldArtifact

namespace SafegcdRow.FoldCode
open M0Crypto.Armv6M (State Reg Mem LowReg read32 write32 slot)
open M0Crypto.Thumb

def head : List Instr :=
  [.memImm .ldr 1 0 16, .lslImm 1 1 1, .memImm .ldr 2 0 15, .lsrImm 3 2 15,
   .addReg 1 1 3, .lslImm 2 2 17, .lsrImm 2 2 17, .memImm .str 2 0 15, .movImm 2 19,
   .dp .muls 1 2]

def column (i : BitVec 5) : List Instr :=
  [.memImm .ldr 2 0 i, .addReg 1 1 2, .uxth 2 1, .memImm .str 2 0 i, .asrImm 1 1 16]

def tail : List Instr := [.memImm .str 1 0 16]

def body : List Instr := head ++ (List.range 16).flatMap (fun i => column (BitVec.ofNat 5 i)) ++ tail

theorem bytes_match : seqAt FoldArtifact.bytes 0 (body ++ [.bx 14]) = true := by
  decide +kernel

def truncate (w : Word) : Word := (w <<< 17) >>> 17

def spill (m : Mem) (a : Word) : Word := (read32 m (slot a 16) <<< 1) + (read32 m (slot a 15) >>> 15)

theorem head_effect (s : State) :
    let t := execAll head s
    t.mem = write32 s.mem (slot (s.regs 0) 15) (truncate (read32 s.mem (slot (s.regs 0) 15))) ∧
    t.regs 1 = 19#32 * spill s.mem (s.regs 0) := by
  unfold head spill truncate
  row_simps
  <;> rfl

theorem column_effect (s : State) (i : BitVec 5) :
    let t := execAll (column i) s
    let z := s.regs 1 + read32 s.mem (slot (s.regs 0) i.toNat)
    t.mem = write32 s.mem (slot (s.regs 0) i.toNat) (low z) ∧
    t.regs 1 = carry z := by
  unfold column
  row_simps
  rw [Nat.mul_comm]
  exact ⟨rfl, rfl⟩

theorem tail_effect (s : State) :
    (execAll tail s).mem = write32 s.mem (slot (s.regs 0) 16) (s.regs 1) := by
  unfold tail
  row_simps

theorem column_keeps (s : State) (i : BitVec 5) (r : Reg)
    (hr : r.val ≠ 1 ∧ r.val ≠ 2 ∧ r.val ≠ 15) :
    (execAll (column i) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ hr.2.2
  simp [column, Instr.dsts, MemOp.isLoad, List.contains_eq_mem]
  exact ⟨hr.2.1, hr.1, hr.2.1, hr.1⟩

end SafegcdRow.FoldCode
