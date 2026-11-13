import M0Crypto.Release.ConstantTime.ChaCha20Sites
import M0Crypto.Release.AccessReach
import M0Crypto.Release.ChaCha20TraceSpec

/-! Access bounds of the ChaCha20 output macros, with the instruction address of each store. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout

/-- A write in an aligned output macro is the final store instruction. -/
theorem aligned_chunk_write_pc (t : State) (i : Nat) (e : Event)
    (he : e ∈ traceAll (ach i) t) (y : Word) (hy : Writes e.accesses y) :
    e.pc = t.pc + BitVec.ofNat 32 (seqSize (ach i).dropLast) := by
  rcases hy with ⟨a, ha, hw, q, hq, hy⟩
  simp only [traceAll, ach, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hw)
  change (execAll ((ach i).dropLast) t).pc = _
  rw [execAll_pc _ _ (by simp [ach, Instr.falls])]

/-- The aligned word macro reads two stack words and one input word. -/
theorem aligned_chunk_read_addresses (t : State) (i : Nat) (hi : i < 16)
    (e : Event) (he : e ∈ traceAll (ach i) t) (y : Word) (hy : Reads e.accesses y) :
    ∃ q < 4, y = t.regs 13 + BitVec.ofNat 32 (4 * (slotX + i)) + BitVec.ofNat 32 q ∨
      y = t.regs 13 + BitVec.ofNat 32 (4 * (slotJ + i)) + BitVec.ofNat 32 q ∨
      y = t.regs 2 + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q := by
  have hreg : (execAll [.ldrSp 0 (BitVec.ofNat 8 (slotX + i)),
      .ldrSp 1 (BitVec.ofNat 8 (slotJ + i)), .addReg 0 0 1] t).regs 2 = t.regs 2 :=
    execAll_regs_other _ _ _ (by decide) (by simp [Instr.dsts])
  have hreg' : ((Instr.addReg 0 0 1).next ((Instr.ldrSp 1 (BitVec.ofNat 8 (slotJ + i))).next
      ((Instr.ldrSp 0 (BitVec.ofNat 8 (slotX + i))).next t))).regs 2 = t.regs 2 := by
    simpa [execAll] using hreg
  have hsp : ((Instr.ldrSp 0 (BitVec.ofNat 8 (slotX + i))).next t).regs 13 = t.regs 13 :=
    next_regs_other _ _ (by decide) (by simp [Instr.dsts])
  rcases hy with ⟨a, ha, hk, q, hq, hy⟩
  simp only [traceAll, ach, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hk)
  all_goals try subst ha
  all_goals refine ⟨q, by simpa [MemOp.width] using hq, ?_⟩
  all_goals simp only [M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg,
    M0Crypto.Proofs.toReg_2, hsp, hreg', BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simp [slotX, slotJ]; omega : slotX + i < 256),
    Nat.mod_eq_of_lt (by simp [slotX, slotJ]; omega : slotJ + i < 256),
    Nat.mod_eq_of_lt (by omega : i < 32), MemOp.width, Nat.mul_comm] at hy
  · left; simpa [Nat.mul_comm] using hy
  · right; left; simpa [Nat.mul_comm] using hy
  · right; right; simpa [Nat.mul_comm] using hy

/-- Instruction addresses of ChaCha's caller-buffer output stores. -/
def OutputStorePC (base pc : Word) : Prop :=
  (∃ i < 16, pc = base + BitVec.ofNat 32
    (achOff + achSize * i + seqSize (ach i).dropLast)) ∨
  pc = base + BitVec.ofNat 32 (blOff + seqSize (bl.take 3))

/-- Read bounds and instruction-specific output-store bounds. -/
def OutputAccess (c : Ctx) (pc : Word) (kind : Kind) (y : Word) : Prop :=
  match kind with
  | .read => TraceSpec.ChaCha20XorReadRegion c y
  | .write => c.Wr y ∧ (OutputStorePC c.base pc → c.oidx y < c.len.toNat)

/-- A preparation macro's store is its final instruction. -/
theorem byte_prepare_write_pc (t : State) (i : Nat) (e : Event)
    (he : e ∈ traceAll (bch i) t) (y : Word) (hy : Writes e.accesses y) :
    e.pc = t.pc + BitVec.ofNat 32 (seqSize (bch i).dropLast) := by
  rcases hy with ⟨a, ha, hw, q, hq, hy⟩
  simp only [traceAll, bch, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hw)
  change (execAll ((bch i).dropLast) t).pc = _
  rw [execAll_pc _ _ (by simp [bch, Instr.falls])]

/-- Preparation stores and caller-buffer stores have distinct instruction offsets. -/
theorem byte_prepare_store_offsets :
    (List.range 16).all (fun i =>
      (List.range 16).all (fun j =>
        BitVec.ofNat 32 (bchOff + bchSize * i + seqSize (bch i).dropLast) !=
          BitVec.ofNat 32 (achOff + achSize * j + seqSize (ach j).dropLast)) &&
      (BitVec.ofNat 32 (bchOff + bchSize * i + seqSize (bch i).dropLast) !=
        BitVec.ofNat 32 (blOff + seqSize (bl.take 3)))) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem byte_prepare_store_not_output (base : Word) (i : Nat) (hi : i < 16) :
    ¬ OutputStorePC base (base + BitVec.ofNat 32
      (bchOff + bchSize * i + seqSize (bch i).dropLast)) := by
  have ht := List.all_eq_true.mp byte_prepare_store_offsets i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, bne_iff_ne] at ht
  rintro (⟨j, hj, heq⟩ | heq)
  · have hj' := List.all_eq_true.mp ht.1 j (List.mem_range.mpr hj)
    simp only [bne_iff_ne] at hj'
    exact hj' ((BitVec.add_right_inj base).mp heq)
  · exact ht.2 ((BitVec.add_right_inj base).mp heq)

/-- The byte-output preparation macro reads two words from its stack frame. -/
theorem byte_prepare_read_addresses (t : State) (i : Nat) (hi : i < 16)
    (e : Event) (he : e ∈ traceAll (bch i) t) (y : Word) (hy : Reads e.accesses y) :
    ∃ q < 4, y = t.regs 13 + BitVec.ofNat 32 (4 * (slotX + i)) + BitVec.ofNat 32 q ∨
      y = t.regs 13 + BitVec.ofNat 32 (4 * (slotJ + i)) + BitVec.ofNat 32 q := by
  have hsp : ((Instr.ldrSp 0 (BitVec.ofNat 8 (slotX + i))).next t).regs 13 = t.regs 13 :=
    next_regs_other _ _ (by decide) (by simp [Instr.dsts])
  rcases hy with ⟨a, ha, hk, q, hq, hy⟩
  simp only [traceAll, bch, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hk)
  all_goals try subst ha
  all_goals refine ⟨q, by simpa [MemOp.width] using hq, ?_⟩
  all_goals simp only [M0Crypto.Armv6M.State.sp, hsp, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simp [slotX, slotJ]; omega : slotX + i < 256),
    Nat.mod_eq_of_lt (by simp [slotX, slotJ]; omega : slotJ + i < 256),
    MemOp.width, Nat.mul_comm] at hy
  · left; simpa [Nat.mul_comm] using hy
  · right; simpa [Nat.mul_comm] using hy

/-- Every access in the byte-output preparation macro stays in the frame. -/
theorem byte_prepare_contract_policy (c : Ctx) (t : State) (i : Nat) (hi : i < 16)
    (hsp : t.regs 13 = c.fp)
    (hpc : t.pc = c.base + BitVec.ofNat 32 (bchOff + bchSize * i)) :
    EventAccessesTo (OutputAccess c) (traceAll (bch i) t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read =>
    obtain ⟨j, hj, haddr | haddr⟩ := byte_prepare_read_addresses t i hi e he _ ⟨a, ha, hk, q, hq, rfl⟩
    · right; right; right; right
      refine Region.mk (o := 4 * (slotX + i) + j) ?_ ?_
      · have hs := chStackBytes_eq; simp [slotX] at *; omega
      · rw [haddr, hsp, Ctx.fp, ofNat_add_assoc]
    · right; right; right; right
      refine Region.mk (o := 4 * (slotJ + i) + j) ?_ ?_
      · have hs := chStackBytes_eq; simp [slotJ] at *; omega
      · rw [haddr, hsp, Ctx.fp, ofNat_add_assoc]
  | write =>
    have hw := bch_writes t i hi e he _ ⟨a, ha, hk, q, hq, rfl⟩
    rw [hsp] at hw
    refine ⟨ChaCha20Setup.wr_frame hw (by have := chFrameWords_eq; have := chStackWords_eq; omega), ?_⟩
    intro hout
    exfalso
    apply byte_prepare_store_not_output c.base i hi
    have hp := byte_prepare_write_pc t i e he _ ⟨a, ha, hk, q, hq, rfl⟩
    rw [hp, hpc, ofNat_add_assoc] at hout
    exact hout

/-- The byte-tail body reads only its input byte and keystream byte. -/
theorem byte_tail_read_addresses (t : State) (e : Event)
    (he : e ∈ traceAll bl t) (y : Word) (hy : Reads e.accesses y) :
    y = t.regs 2 + t.regs 0 ∨ y = t.regs 5 + t.regs 0 := by
  have h5 : ((Instr.memReg .ldrb 1 2 0).next t).regs 5 = t.regs 5 :=
    next_regs_other _ _ (by decide) (by decide)
  have h0 : ((Instr.memReg .ldrb 1 2 0).next t).regs 0 = t.regs 0 :=
    next_regs_other _ _ (by decide) (by decide)
  rcases hy with ⟨a, ha, hk, q, hq, hy⟩
  simp only [traceAll, bl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Instr.accesses, MemOp.isLoad] at ha
  all_goals try (subst ha; cases hk)
  all_goals try subst ha
  all_goals have hq0 : q = 0 := by simpa [MemOp.width] using hq
  all_goals subst q
  · left; simpa [M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_0] using hy
  · right; simpa [M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_5,
      M0Crypto.Proofs.toReg_0, h5, h0] using hy

/-- A byte-tail iteration reads only the permitted input and stack windows. -/
theorem byte_tail_reads_contract (c : Ctx) (k : Nat) (t : State)
    (hin : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k))
    (hstack : t.regs 5 = c.fp) (hindex : (t.regs 0).toNat < 64)
    (hbound : 64 * k + (t.regs 0).toNat < c.len.toNat) :
    ReadsFrom (TraceSpec.ChaCha20XorReadRegion c) (traceAll bl t) := by
  intro e he y hy
  have hword : BitVec.ofNat 32 (t.regs 0).toNat = t.regs 0 := by simp
  rcases byte_tail_read_addresses t e he y hy with ha | ha
  · left
    refine Region.mk (o := 64 * k + (t.regs 0).toNat) hbound ?_
    calc
      y = (c.inp + BitVec.ofNat 32 (64 * k)) + t.regs 0 := by rw [ha, hin]
      _ = c.inp + BitVec.ofNat 32 (64 * k + (t.regs 0).toNat) := by
        rw [← ofNat_add_assoc, hword]
  · right; right; right; right
    refine Region.mk (o := (t.regs 0).toNat) ?_ ?_
    · have hs := chStackBytes_eq
      omega
    · rw [ha, hstack, Ctx.fp, hword]

/-- A byte-tail iteration obeys the ChaCha read and write bounds. -/
theorem byte_tail_contract_policy (c : Ctx) (hv : Valid c) (block : Nat) (t : State)
    (hin : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * block)) (hstack : t.regs 5 = c.fp)
    (hout : t.regs 3 = c.out + BitVec.ofNat 32 (64 * block))
    (hindex : (t.regs 0).toNat < 64)
    (hbound : 64 * block + (t.regs 0).toNat < c.len.toNat) :
    EventAccessesTo (OutputAccess c) (traceAll bl t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read =>
    exact byte_tail_reads_contract c block t hin hstack hindex hbound e he _
      ⟨a, ha, hk, q, hq, rfl⟩
  | write =>
    have hw := chacha20_tail_writes_output c hv block t hout hbound e he _
      ⟨a, ha, hk, q, hq, rfl⟩
    exact ⟨Or.inr hw, fun _ => hw⟩

/-- The aligned output macro reads only the ChaCha contract's permitted
input and stack regions. -/
theorem aligned_chunk_reads_contract (c : Ctx) (k i : Nat) (t : State)
    (hi : i < 16) (hsp : t.regs 13 = c.fp)
    (hin : t.regs 2 = c.inp + BitVec.ofNat 32 (64 * k))
    (hbound : 64 * k + 4 * i + 4 ≤ c.len.toNat) :
    ReadsFrom (TraceSpec.ChaCha20XorReadRegion c) (traceAll (ach i) t) := by
  intro e he y hy
  obtain ⟨q, hq, ha | ha | ha⟩ := aligned_chunk_read_addresses t i hi e he y hy
  · right; right; right; right
    refine Region.mk (o := 4 * (slotX + i) + q) ?_ ?_
    · have hs := chStackBytes_eq
      simp [slotX] at *
      omega
    · rw [ha, hsp, Ctx.fp, ofNat_add_assoc]
  · right; right; right; right
    refine Region.mk (o := 4 * (slotJ + i) + q) ?_ ?_
    · have hs := chStackBytes_eq
      simp [slotJ] at *
      omega
    · rw [ha, hsp, Ctx.fp, ofNat_add_assoc]
  · left
    refine Region.mk (o := 64 * k + 4 * i + q) (by omega) ?_
    rw [ha, hin, ofNat_add_assoc, ofNat_add_assoc, Nat.add_assoc]

/-- The aligned macro satisfies a PC-aware policy when that policy permits
its two stack words, input word, and bounded output writes. -/
theorem aligned_chunk_policy (c : Ctx) (hv : Valid c) (k i : Nat) (t : State)
    (hi : i < 16) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (hbound : 64 * k + 4 * i + 4 ≤ c.len.toNat)
    (allowed : Word → Kind → Word → Prop)
    (hw : ∀ y, c.oidx y < c.len.toNat →
      allowed (t.pc + BitVec.ofNat 32 (seqSize (ach i).dropLast)) .write y)
    (hr : ∀ pc q, q < 4 →
      allowed pc .read (t.regs 13 + BitVec.ofNat 32 (4 * (slotX + i)) + BitVec.ofNat 32 q) ∧
      allowed pc .read (t.regs 13 + BitVec.ofNat 32 (4 * (slotJ + i)) + BitVec.ofNat 32 q) ∧
      allowed pc .read (t.regs 2 + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    EventAccessesTo allowed (traceAll (ach i) t) := by
  intro e he a ha q hq
  cases hk : a.kind with
  | read =>
    obtain ⟨j, hj, haddr⟩ := aligned_chunk_read_addresses t i hi e he _ ⟨a, ha, hk, q, hq, rfl⟩
    rcases haddr with haddr | haddr | haddr
    · rw [haddr]; exact (hr e.pc j hj).1
    · rw [haddr]; exact (hr e.pc j hj).2.1
    · rw [haddr]; exact (hr e.pc j hj).2.2
  | write =>
    rw [aligned_chunk_write_pc t i e he _ ⟨a, ha, hk, q, hq, rfl⟩]
    apply hw
    exact chacha20_chunk_writes_output c hv k i t hi h3 hbound e he _
      ⟨a, ha, hk, q, hq, rfl⟩

end M0Crypto.Release.ConstantTime
