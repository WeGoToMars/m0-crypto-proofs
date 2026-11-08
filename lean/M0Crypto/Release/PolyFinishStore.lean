import M0Crypto.Release.PolyFinishArith
import M0Crypto.Release.ChaChaOut
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace M0Crypto.Release.PolyFinish
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
attribute [local simp] M0Crypto.Proofs.toReg_0 M0Crypto.Proofs.toReg_1 M0Crypto.Proofs.toReg_2
  M0Crypto.Proofs.toReg_3 M0Crypto.Proofs.toReg_4 M0Crypto.Proofs.toReg_5
  M0Crypto.Proofs.toReg_6 M0Crypto.Proofs.toReg_7
attribute [local simp] M0Crypto.Armv6M.State.setNZC M0Crypto.Armv6M.State.setNZCV

theorem extract_shift (v : Word) (n k : Nat) :
    (v >>> n).extractLsb' k 8 = v.extractLsb' (n+k) 8 := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]
  congr 1
  omega

/-- The four byte stores used for arbitrary tag alignment encode one LE word. -/
theorem four_bytes (m : Mem) (a v : Word) :
    write8 (write8 (write8 (write8 m a v) (a+1#32) (v>>>8)) (a+2#32) ((v>>>8)>>>8))
      (a+3#32) (((v>>>8)>>>8)>>>8) = write32 m a v := by
  funext x
  have h01 : a ≠ a+1#32 := by bv_omega
  have h02 : a ≠ a+2#32 := by bv_omega
  have h03 : a ≠ a+3#32 := by bv_omega
  have h12 : a+1#32 ≠ a+2#32 := by bv_omega
  have h13 : a+1#32 ≠ a+3#32 := by bv_omega
  have h23 : a+2#32 ≠ a+3#32 := by bv_omega
  by_cases h0 : x = a
  · subst x; simp [write8, write32, h01, h02, h03]
  by_cases h1 : x = a+1#32
  · subst x; simp [write8, write32, h01.symm, h12, h13, extract_shift]
  by_cases h2 : x = a+2#32
  · subst x; simp [write8, write32, h02.symm, h12.symm, h23, extract_shift]
  by_cases h3 : x = a+3#32
  · subst x; simp [write8, write32, h03.symm, h13.symm, h23.symm, extract_shift]
  simp [write8, write32, h0, h1, h2, h3]

theorem stle_mem (s : State) (v : LowReg) (off : Nat) (hoff : off+3 < 32) (hv : v.val ≠ 1) :
    (execAll (stle v off) s).mem = write32 s.mem (s.regs 1 + BitVec.ofNat 32 off) (s.regs v.toReg) := by
  have h1 : v.toReg ≠ (1 : Reg) := by intro h; apply hv; exact congrArg Fin.val h
  have h1' := h1.symm
  have h15 : v.toReg ≠ (15 : Reg) := by intro h; have := congrArg Fin.val h; simp [LowReg.toReg] at this; omega
  have h15' := h15.symm
  simp (config := { decide := true }) only [stle, execAll, Instr.next, Instr.exec, Instr.exec.memOp,
    MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
    M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_1,
    lsrC, h1, h1', h15, h15', ite_false, ite_true]
  have eo : ∀ k, k ≤ 3 → (BitVec.ofNat 5 (off+k)).toNat = off+k := by intro k hk; simp; omega
  rw [show (BitVec.ofNat 5 off).toNat = off from by simp; omega, eo 1 (by decide), eo 2 (by decide), eo 3 (by decide)]
  simp only [show (8 : BitVec 5).toNat = 8 from rfl, Nat.mul_one]
  rw [show s.regs 1 + BitVec.ofNat 32 (off+1) = s.regs 1 + BitVec.ofNat 32 off + 1#32 from by bv_omega,
    show s.regs 1 + BitVec.ofNat 32 (off+2) = s.regs 1 + BitVec.ofNat 32 off + 2#32 from by bv_omega,
    show s.regs 1 + BitVec.ofNat 32 (off+3) = s.regs 1 + BitVec.ofNat 32 off + 3#32 from by bv_omega]
  exact four_bytes _ _ _

theorem stle_regs (s : State) (v : LowReg) (off : Nat) (r : Reg) (h15 : r.val ≠ 15) (hv : r.val ≠ v.val) :
    (execAll (stle v off) s).regs r = s.regs r := by
  apply execAll_regs_other _ _ _ h15
  simp [stle, Instr.dsts, hv]

/-- Four output words before their registers are shifted for byte stores. -/
def tagMem (s : State) : Mem := storeWords s.mem (s.regs 12) [s.regs 2, s.regs 3, s.regs 4, s.regs 5]

theorem emit_mem (s : State) : (execAll emit s).mem = tagMem s := by
  simp only [emit, execAll_append]
  rw [stle_mem _ 5 12 (by decide) (by decide), stle_mem _ 4 8 (by decide) (by decide),
    stle_mem _ 3 4 (by decide) (by decide), stle_mem _ 2 0 (by decide) (by decide)]
  simp only [M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5]
  simp only [stle_regs _ 2 _ 1 (by decide) (by decide), stle_regs _ 3 _ 1 (by decide) (by decide),
    stle_regs _ 4 _ 1 (by decide) (by decide), stle_regs _ 2 _ 3 (by decide) (by decide),
    stle_regs _ 2 _ 4 (by decide) (by decide), stle_regs _ 3 _ 4 (by decide) (by decide),
    stle_regs _ 2 _ 5 (by decide) (by decide), stle_regs _ 3 _ 5 (by decide) (by decide),
    stle_regs _ 4 _ 5 (by decide) (by decide)]
  simp (config := { decide := true }) [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
    tagMem, storeWords, BitVec.add_assoc]
theorem stle_aligned (s : State) (v : LowReg) (off : Nat) : alignedAll (stle v off) s = true := by
  simp [alignedAll, stle, Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one]

theorem stle_writes (s : State) (v : LowReg) (off : Nat) (hoff : off+3 < 16) (hv : v.val ≠ 1) :
    WritesIn (traceAll (stle v off) s) (s.regs 1) 16 := by
  have h1 : (1 : Reg) ≠ v.toReg := by intro h; apply hv; exact (congrArg Fin.val h).symm
  intro e he y ⟨a, ha, hw, k, hk, hy⟩
  simp only [traceAll, stle, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { decide := true }) only [Instr.accesses, M0Crypto.Armv6M.State.reg,
      M0Crypto.Proofs.toReg_1, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC, h1, ite_false, ite_true,
      List.mem_singleton, List.not_mem_nil] at ha
  all_goals try contradiction
  all_goals
    subst a
    have hk0 : k = 0 := by simpa [MemOp.width] using (show k < 1 from hk)
    subst k
    simp only [BitVec.add_zero, MemOp.width, Nat.mul_one] at hy
    rw [hy]
    refine ⟨_, ?_, rfl⟩
    simp only [BitVec.toNat_ofNat]
    omega

theorem emit_aligned (s : State) : alignedAll emit s = true := by
  simp only [emit, alignedAll_append, Bool.and_eq_true, stle_aligned]
  simp [alignedAll, Instr.accesses]

theorem emit_writes (s : State) : WritesIn (traceAll emit s) (s.regs 12) 16 := by
  simp only [emit, traceAll_append]
  have a := stle_writes (execAll [.movHi 1 12] s) 2 0 (by decide) (by decide)
  have b := stle_writes (execAll (stle 2 0) (execAll [.movHi 1 12] s)) 3 4 (by decide) (by decide)
  have c := stle_writes (execAll (stle 3 4) (execAll (stle 2 0) (execAll [.movHi 1 12] s))) 4 8 (by decide) (by decide)
  have d := stle_writes (execAll (stle 4 8) (execAll (stle 3 4) (execAll (stle 2 0) (execAll [.movHi 1 12] s)))) 5 12 (by decide) (by decide)
  simp only [stle_regs _ 2 _ 1 (by decide) (by decide), stle_regs _ 3 _ 1 (by decide) (by decide),
    stle_regs _ 4 _ 1 (by decide) (by decide)] at b c d
  have ptr : (execAll [.movHi 1 12] s).regs 1 = s.regs 12 := by
    simp [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg]
  rw [ptr] at a b c d
  intro e he y hy
  simp only [execAll_append] at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · have hn := ChaChaBlock.noWrites [.movHi 1 12] s (by decide) (fun _ => False) e he y hy
          exact hn.elim
        · exact a e he y hy
      · exact b e he y hy
    · exact c e he y hy
  · exact d e he y hy

theorem word_byte_nat (v : Word) (k : Nat) (hk : k < 4) :
    v.extractLsb' (8*k) 8 = BitVec.ofNat 8 (v.toNat / 256^k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- Byte-level interpretation of the four emitted words. -/
theorem tagMem_bytes (s : State) :
    Ctx.bytesAt (tagMem s) (s.regs 12) 16 = M0Crypto.Spec.AEAD.leBytes 16 (low s) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 16
  · rw [ChaChaOut.bytesAt_get _ _ _ _ hi, PolySpec.leBytes_get _ _ _ hi]
    have hj : i / 4 < 4 := by omega
    have hk : i % 4 < 4 := by omega
    have hw : read32 (tagMem s) (slot (s.regs 12) (i/4)) =
        (if i/4 = 0 then s.regs 2 else if i/4 = 1 then s.regs 3 else if i/4 = 2 then s.regs 4 else s.regs 5) := by
      unfold tagMem
      rw [show slot (s.regs 12) (i/4) = s.regs 12 + BitVec.ofNat 32 (4*(i/4)) from rfl,
        ChaChaRet.read32_storeWords_same _ _ _ (i/4) (by simp; omega) (by simp)]
      rcases (by omega : i/4 = 0 ∨ i/4 = 1 ∨ i/4 = 2 ∨ i/4 = 3) with h | h | h | h <;> simp [h]
    have hb := byte_of_read32 (tagMem s) (slot (s.regs 12) (i/4)) (i%4) hk
    rw [hw] at hb
    rw [slot, ofNat_add_assoc, show 4*(i/4)+i%4 = i by omega] at hb
    rw [hb, word_byte_nat _ _ hk]
    congr 1
    have ht := PolySpec.tag_byte (s.regs 2).toNat (s.regs 3).toNat (s.regs 4).toNat (s.regs 5).toNat 0
      (i/4) (i%4) (s.regs 2).isLt (s.regs 3).isLt (s.regs 4).isLt hj hk
    simp only [Nat.mul_zero, Nat.add_zero, show 4*(i/4)+i%4 = i by omega] at ht
    rw [low, ht]
    rcases (by omega : i/4 = 0 ∨ i/4 = 1 ∨ i/4 = 2 ∨ i/4 = 3) with h | h | h | h <;> simp [h]
  · rw [List.getElem?_eq_none (by rw [bytesAt_length]; omega),
      List.getElem?_eq_none (by rw [PolySpec.leBytes_length]; omega)]
end M0Crypto.Release.PolyFinish
