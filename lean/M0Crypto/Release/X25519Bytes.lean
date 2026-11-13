import M0Crypto.Release.ReachSteps

set_option linter.unusedSimpArgs false

/-!
# Byte loads and byte stores of `m0c_x25519`

The entry reads `scalar` and `point` with the generator's `load_le32` and writes `out` with a
four-byte store sequence (`tools/gen_x25519.py` in the library):

* `load_le32 rd, rt, rb, k`: `ldrb rd, [rb, #k]`, then for `i = 1, 2, 3`
  `ldrb rt, [rb, #k+i]; lsls rt, rt, #8i; orrs rd, rt`. `rd` ends as the little-endian word of the
  four bytes at `rb + k`, whatever the alignment.
* the store of word `w`: `ldr rv, [rs, #4w]; strb rv, [rd, #k]`, then for `j = 1, 2, 3`
  `lsrs rv, rv, #8; strb rv, [rd, #k+j]`. Byte `k + j` at `rd` ends as byte `j` of the word, and
  nothing else is written.

One run lemma per sequence (`loadLe32_run_w`, `storeLe32_run_w`), each generic in its registers,
its pointers and its offsets, with `Reach` corollaries through `ReachW.toReach`
(`loadLe32_run`, `storeLe32_run`). The instruction lists are built from one group per byte (`loadByte`,
`storeByte`), and each group has one execution lemma generic in the byte index; nothing
enumerates the 32 bytes of a buffer or the call's offsets. The block length is
`seqSize` of the list, never a literal.
-/

namespace M0Crypto.Release.X25519Bytes

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release

/-! ## Instruction lists -/

/-- Byte `i ≥ 1` of `load_le32`: `ldrb rt, [rb, #k+i]; lsls rt, rt, #8i; orrs rd, rt`. -/
def loadByte (rd rt rb : LowReg) (k i : Nat) : List Instr :=
  [.memImm .ldrb rt rb (BitVec.ofNat 5 (k + i)), .lslImm rt rt (BitVec.ofNat 5 (8 * i)),
    .dp .orrs rd rt]

/-- `load_le32 rd, rt, rb, k`: the little-endian word at `rb + k` into `rd`. -/
def loadLe32 (rd rt rb : LowReg) (k : Nat) : List Instr :=
  .memImm .ldrb rd rb (BitVec.ofNat 5 k) ::
    (loadByte rd rt rb k 1 ++ loadByte rd rt rb k 2 ++ loadByte rd rt rb k 3)

/-- Byte `j ≥ 1` of a word store: `lsrs rv, rv, #8; strb rv, [rd, #k+j]`. -/
def storeByte (rv rd : LowReg) (k j : Nat) : List Instr :=
  [.lsrImm rv rv (BitVec.ofNat 5 8), .memImm .strb rv rd (BitVec.ofNat 5 (k + j))]

/-- Store word `w` at `rs` as four bytes at `rd + k`: `ldr rv, [rs, #4w]; strb rv, [rd, #k]`,
then three `storeByte` groups. -/
def storeLe32 (rv rs rd : LowReg) (w k : Nat) : List Instr :=
  .memImm .ldr rv rs (BitVec.ofNat 5 w) :: .memImm .strb rv rd (BitVec.ofNat 5 k) ::
    (storeByte rv rd k 1 ++ storeByte rv rd k 2 ++ storeByte rv rd k 3)

/-! ## Static facts -/

theorem loadLe32_falls (rd rt rb : LowReg) (k : Nat) : (loadLe32 rd rt rb k).all Instr.falls = true := by
  simp [loadLe32, loadByte, Instr.falls]

theorem loadLe32_noW (rd rt rb : LowReg) (k : Nat) :
    (loadLe32 rd rt rb k).all (!·.writesMem) = true := by
  simp [loadLe32, loadByte, Instr.writesMem, MemOp.isLoad]

theorem storeLe32_falls (rv rs rd : LowReg) (w k : Nat) :
    (storeLe32 rv rs rd w k).all Instr.falls = true := by
  simp [storeLe32, storeByte, Instr.falls]

/-! ## Arithmetic -/

theorem toReg_ne {a b : LowReg} (h : a ≠ b) : a.toReg ≠ b.toReg := by
  intro e; apply h; have := congrArg Fin.val e; simp [LowReg.toReg] at this; exact Fin.ext this

/-- `x ||| b << n` with `x < 2^n` and a byte `b` adds `2^n b`. -/
theorem or_shl_toNat (x : Word) (b : BitVec 8) (n : Nat) (hn : n + 8 ≤ 32) (hx : x.toNat < 2 ^ n) :
    (x ||| b.setWidth 32 <<< n).toNat = x.toNat + 2 ^ n * b.toNat := by
  have hb := b.isLt
  have hp : 2 ^ n * 2 ^ 8 ≤ 2 ^ 32 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hn
  have hlt : b.toNat * 2 ^ n < 2 ^ 32 := by
    calc b.toNat * 2 ^ n < 2 ^ 8 * 2 ^ n := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos n)
      _ = 2 ^ n * 2 ^ 8 := Nat.mul_comm _ _
      _ ≤ 2 ^ 32 := hp
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (by decide : 2 ^ 8 ≤ 2 ^ 32)), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hlt, Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx,
    Nat.shiftLeft_eq]
  rw [Nat.mul_comm]; omega

/-- The low byte after `j` shifts right by 8 is byte `j` of the word. -/
theorem byte_of_shr (v : Word) (j : Nat) :
    (v >>> (8 * j)).extractLsb' 0 8 = BitVec.ofNat 8 (v.toNat / 2 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shr8_shr (v : Word) (j : Nat) : v >>> (8 * j) >>> 8 = v >>> (8 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show 8 * j + 8 = 8 * (j + 1) by omega]

/-! ## Registers and addresses -/

/-- A register different from `d.toReg` has a different index. -/
theorem val_ne {r : Reg} {d : LowReg} (h : r ≠ d.toReg) : r.val ≠ d.val := fun e => h (Fin.ext e)

/-- Distinct offsets below 32 from one base are distinct addresses. -/
theorem addr_ne (d : Word) {a b : Nat} (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    d + BitVec.ofNat 32 a ≠ d + BitVec.ofNat 32 b := by
  intro h
  bv_omega

theorem regs_other_of {is : List Instr} {s : State} {r : Reg} (h15 : r.val ≠ 15)
    (h : is.all (fun i => !(i.dsts.contains r.val)) = true) : (execAll is s).regs r = s.regs r :=
  execAll_regs_other is s r h15 h

/-! ## Execution of one group -/

section Exec

variable (s : State) {rd rt rb : LowReg} (k i : Nat)

/-- One `loadByte` group, as values: `rd += 2^(8i) * byte (rb + k + i)` while `rd < 2^(8i)`;
memory and `rb` unchanged. -/
theorem loadByte_step (hdt : rd ≠ rt) (hdb : rd ≠ rb) (htb : rt ≠ rb) (hi : 0 < i) (hi3 : i < 4)
    (hk : k + i < 32) (hx : (s.regs rd.toReg).toNat < 2 ^ (8 * i)) :
    ((execAll (loadByte rd rt rb k i) s).regs rd.toReg).toNat =
        (s.regs rd.toReg).toNat + 2 ^ (8 * i) * (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + i))).toNat ∧
      (execAll (loadByte rd rt rb k i) s).mem = s.mem ∧
      (execAll (loadByte rd rt rb k i) s).regs rb.toReg = s.regs rb.toReg := by
  have h1 := toReg_ne hdt
  have h2 := toReg_ne_15 rd
  have h3 := toReg_ne_15 rt
  have e1 : (k + i) % 32 = k + i := Nat.mod_eq_of_lt hk
  have e2 : 8 * i % 32 = 8 * i := Nat.mod_eq_of_lt (by omega)
  have e3 : ¬ 8 * i = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have hv : (execAll (loadByte rd rt rb k i) s).regs rd.toReg =
        s.regs rd.toReg ||| (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + i))).setWidth 32 <<< (8 * i) := by
      simp [execAll, loadByte, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
        M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
        M0Crypto.Armv6M.State.reg, lslC, read8, h1, h2, h3, e1, e2, e3]
    rw [hv, or_shl_toNat _ _ _ (by omega) hx]
  · exact execAll_mem _ s (by simp [loadByte, Instr.writesMem, MemOp.isLoad])
  · apply regs_other_of (by have := toReg_ne_15 rb; exact fun e => this (Fin.ext e))
    simp [loadByte, Instr.dsts, MemOp.isLoad, LowReg.toReg]
    exact ⟨fun e => htb (Fin.ext e.symm), fun e => hdb (Fin.ext e.symm)⟩

variable {rv rs : LowReg} (j : Nat) (v : Word)

/-- One `storeByte` group: with `rv` holding `v >> 8(j-1)`, it shifts `rv` to `v >> 8j` and
writes its low byte at `rd + k + j`; `rd` unchanged. -/
theorem storeByte_step (hvd : rv ≠ rd) (hj : 0 < j) (hk : k + j < 32)
    (hv : s.regs rv.toReg = v >>> (8 * (j - 1))) :
    (execAll (storeByte rv rd k j) s).regs rv.toReg = v >>> (8 * j) ∧
      (execAll (storeByte rv rd k j) s).regs rd.toReg = s.regs rd.toReg ∧
      (execAll (storeByte rv rd k j) s).mem =
        write8 s.mem (s.regs rd.toReg + BitVec.ofNat 32 (k + j)) (v >>> (8 * j)) := by
  have h1 := toReg_ne hvd
  have h2 := toReg_ne_15 rv
  have h3 := toReg_ne_15 rd
  have e1 : (k + j) % 32 = k + j := Nat.mod_eq_of_lt hk
  have e8 : v >>> (8 * (j - 1)) >>> 8 = v >>> (8 * j) := by
    rw [shr8_shr]; congr 2; omega
  simp [execAll, storeByte, Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.setNZC,
    M0Crypto.Armv6M.State.reg, lsrC, h1, h2, h3, Ne.symm h1, e1, hv, e8]

/-- The writes of one `storeByte` group: the byte at `rd + k + j`. -/
theorem storeByte_writes {Wr : Word → Prop} (hvd : rv ≠ rd) (hk : k + j < 32)
    (hw : Wr (s.regs rd.toReg + BitVec.ofNat 32 (k + j))) :
    WritesTo Wr (traceAll (storeByte rv rd k j) s) := by
  have h1 := toReg_ne hvd
  have h2 := toReg_ne_15 rv
  have e1 : (k + j) % 32 = k + j := Nat.mod_eq_of_lt hk
  intro e he y hy
  simp [storeByte, traceAll, Instr.next, Instr.exec, Instr.size, Instr.accesses, MemOp.isLoad,
    MemOp.width, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZC,
    M0Crypto.Armv6M.State.reg, h1, h2, Ne.symm h1, e1] at he
  rcases he with rfl | rfl
  · obtain ⟨a, ha, -⟩ := hy
    simp at ha
  · obtain ⟨a, ha, -, n, hn, rfl⟩ := hy
    simp at ha; subst ha
    simp at hn; subst hn
    simpa [toReg_ne_15 rd] using hw

end Exec

/-! ## The whole sequences -/

/-- `load_le32` leaves in `rd` the little-endian value of the four bytes at `rb + k`. -/
theorem loadLe32_exec (s : State) {rd rt rb : LowReg} {k : Nat} (hdt : rd ≠ rt) (hdb : rd ≠ rb)
    (htb : rt ≠ rb) (hk : k + 3 < 32) :
    ((execAll (loadLe32 rd rt rb k) s).regs rd.toReg).toNat =
      (s.mem (s.regs rb.toReg + BitVec.ofNat 32 k)).toNat +
      2 ^ 8 * (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 1))).toNat +
      2 ^ 16 * (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 2))).toNat +
      2 ^ 24 * (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 3))).toNat := by
  have h1 := toReg_ne hdb
  have h2 := toReg_ne_15 rd
  have ek : k % 32 = k := Nat.mod_eq_of_lt (by omega)
  rw [loadLe32, execAll, execAll_append, execAll_append]
  generalize hs1 : (Instr.memImm .ldrb rd rb (BitVec.ofNat 5 k)).next s = s1
  have r0 : s1.regs rd.toReg = (s.mem (s.regs rb.toReg + BitVec.ofNat 32 k)).setWidth 32 := by
    subst hs1
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, read8, h2, ek]
  have m0 : s1.mem = s.mem := by subst hs1; exact next_mem (by simp [Instr.writesMem, MemOp.isLoad]) s
  have b0 : s1.regs rb.toReg = s.regs rb.toReg := by
    subst hs1
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, Ne.symm h1, toReg_ne_15 rb]
  have x0 : (s1.regs rd.toReg).toNat < 2 ^ (8 * 1) := by
    rw [r0, BitVec.toNat_setWidth]; have := (s.mem (s.regs rb.toReg + BitVec.ofNat 32 k)).isLt; omega
  obtain ⟨r1, m1, b1⟩ := loadByte_step s1 k 1 hdt hdb htb (by omega) (by omega) (by omega) x0
  generalize execAll (loadByte rd rt rb k 1) s1 = s2 at r1 m1 b1
  have hb0 := (s.mem (s.regs rb.toReg + BitVec.ofNat 32 k)).isLt
  have hb1 := (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 1))).isLt
  have hb2 := (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 2))).isLt
  have hb3 := (s.mem (s.regs rb.toReg + BitVec.ofNat 32 (k + 3))).isLt
  have v0 : (s1.regs rd.toReg).toNat = (s.mem (s.regs rb.toReg + BitVec.ofNat 32 k)).toNat := by
    rw [r0, BitVec.toNat_setWidth]; omega
  rw [m0, b0] at r1
  rw [m0] at m1; rw [b0] at b1
  have x1 : (s2.regs rd.toReg).toNat < 2 ^ (8 * 2) := by rw [r1, v0]; omega
  obtain ⟨r2, m2, b2⟩ := loadByte_step s2 k 2 hdt hdb htb (by omega) (by omega) (by omega) x1
  generalize execAll (loadByte rd rt rb k 2) s2 = s3 at r2 m2 b2
  rw [m1, b1] at r2
  rw [m1] at m2; rw [b1] at b2
  have x2 : (s3.regs rd.toReg).toNat < 2 ^ (8 * 3) := by rw [r2, r1, v0]; omega
  obtain ⟨r3, -, -⟩ := loadByte_step s3 k 3 hdt hdb htb (by omega) (by omega) (by omega) x2
  rw [r3, m2, b2, r2, r1, v0]

theorem loadLe32_aligned (s : State) (rd rt rb : LowReg) (k : Nat) :
    alignedAll (loadLe32 rd rt rb k) s = true := by
  simp [loadLe32, loadByte, alignedAll, Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one]

theorem loadLe32_regs_other (s : State) {rd rt rb : LowReg} (k : Nat) {r : Reg}
    (hd : r ≠ rd.toReg) (ht : r ≠ rt.toReg) (h15 : r.val ≠ 15) :
    (execAll (loadLe32 rd rt rb k) s).regs r = s.regs r := by
  have a := val_ne hd
  have b := val_ne ht
  apply regs_other_of h15
  simp [loadLe32, loadByte, Instr.dsts, MemOp.isLoad, a, b]

/-- The word store writes byte `j` of the word at `rs + 4w` to `rd + k + j`, for `j < 4`. -/
theorem storeLe32_mem (s : State) {rv rs rd : LowReg} {w k : Nat} (hvs : rv ≠ rs) (hvd : rv ≠ rd)
    (hw : w < 32) (hk : k + 3 < 32) :
    (execAll (storeLe32 rv rs rd w k) s).mem =
      write8 (write8 (write8 (write8 s.mem (s.regs rd.toReg + BitVec.ofNat 32 (k + 0))
        (read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) >>> (8 * 0)))
        (s.regs rd.toReg + BitVec.ofNat 32 (k + 1))
        (read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) >>> (8 * 1)))
        (s.regs rd.toReg + BitVec.ofNat 32 (k + 2))
        (read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) >>> (8 * 2)))
        (s.regs rd.toReg + BitVec.ofNat 32 (k + 3))
        (read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) >>> (8 * 3)) := by
  have h1 := toReg_ne hvd
  have h2 := toReg_ne_15 rv
  have hs := toReg_ne hvs
  have ew : w % 32 = w := Nat.mod_eq_of_lt hw
  have ek : k % 32 = k := Nat.mod_eq_of_lt (by omega)
  generalize hv : read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) = v
  rw [storeLe32, execAll, execAll, execAll_append, execAll_append]
  generalize hs1 : (Instr.memImm .strb rv rd (BitVec.ofNat 5 k)).next
    ((Instr.memImm .ldr rv rs (BitVec.ofNat 5 w)).next s) = s1
  have r1 : s1.regs rv.toReg = v >>> (8 * (1 - 1)) := by
    subst hs1; rw [← hv]
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, h2, ew, Nat.mul_comm]
  have d1 : s1.regs rd.toReg = s.regs rd.toReg := by
    subst hs1
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, Ne.symm h1, toReg_ne_15 rd]
  have m1 : s1.mem = write8 s.mem (s.regs rd.toReg + BitVec.ofNat 32 (k + 0)) (v >>> (8 * 0)) := by
    subst hs1; rw [← hv]
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, h2, Ne.symm h1, toReg_ne_15 rd, ew, ek,
      Nat.mul_comm]
  obtain ⟨r2, d2, m2⟩ := storeByte_step s1 k 1 v hvd (by omega) (by omega) r1
  generalize execAll (storeByte rv rd k 1) s1 = s2 at r2 d2 m2
  rw [d1, m1] at m2; rw [d1] at d2
  obtain ⟨r3, d3, m3⟩ := storeByte_step s2 k 2 v hvd (by omega) (by omega) r2
  generalize execAll (storeByte rv rd k 2) s2 = s3 at r3 d3 m3
  rw [d2, m2] at m3; rw [d2] at d3
  obtain ⟨-, -, m4⟩ := storeByte_step s3 k 3 v hvd (by omega) (by omega) r3
  rw [m4, d3, m3]

/-- The register written by a `storeByte` group is `rv` only. -/
theorem storeByte_regs_other (s : State) {rv rd : LowReg} (k j : Nat) {r : Reg} (hv : r ≠ rv.toReg)
    (h15 : r.val ≠ 15) : (execAll (storeByte rv rd k j) s).regs r = s.regs r := by
  have a := val_ne hv
  apply regs_other_of h15
  simp [storeByte, Instr.dsts, MemOp.isLoad, a]

theorem storeLe32_regs_other (s : State) {rv rs rd : LowReg} (w k : Nat) {r : Reg}
    (hv : r ≠ rv.toReg) (h15 : r.val ≠ 15) :
    (execAll (storeLe32 rv rs rd w k) s).regs r = s.regs r := by
  have a := val_ne hv
  apply regs_other_of h15
  simp [storeLe32, storeByte, Instr.dsts, MemOp.isLoad, a]

/-- Byte `j < 4` of the stored word is at `rd + k + j`. -/
theorem storeLe32_bytes (s : State) {rv rs rd : LowReg} {w k : Nat} (hvs : rv ≠ rs) (hvd : rv ≠ rd)
    (hw : w < 32) (hk : k + 3 < 32) {j : Nat} (hj : j < 4) :
    (execAll (storeLe32 rv rs rd w k) s).mem (s.regs rd.toReg + BitVec.ofNat 32 (k + j)) =
      BitVec.ofNat 8 ((read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w))).toNat / 2 ^ (8 * j)) := by
  rw [storeLe32_mem s hvs hvd hw hk]
  generalize s.regs rd.toReg = d
  generalize read32 s.mem (s.regs rs.toReg + BitVec.ofNat 32 (4 * w)) = v
  have n01 := addr_ne d (a := k + 0) (b := k + 1) (by omega) (by omega) (by omega)
  have n02 := addr_ne d (a := k + 0) (b := k + 2) (by omega) (by omega) (by omega)
  have n03 := addr_ne d (a := k + 0) (b := k + 3) (by omega) (by omega) (by omega)
  have n12 := addr_ne d (a := k + 1) (b := k + 2) (by omega) (by omega) (by omega)
  have n13 := addr_ne d (a := k + 1) (b := k + 3) (by omega) (by omega) (by omega)
  have n23 := addr_ne d (a := k + 2) (b := k + 3) (by omega) (by omega) (by omega)
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [write8, n01, n02, n03, n12, n13, n23, Ne.symm n01, Ne.symm n02, Ne.symm n03,
      Ne.symm n12, Ne.symm n13, Ne.symm n23, ite_true, ite_false, byte_of_shr]

/-- The word store writes no other byte. -/
theorem storeLe32_other (s : State) {rv rs rd : LowReg} {w k : Nat} (hvs : rv ≠ rs) (hvd : rv ≠ rd)
    (hw : w < 32) (hk : k + 3 < 32) {y : Word}
    (hy : ∀ j < 4, y ≠ s.regs rd.toReg + BitVec.ofNat 32 (k + j)) :
    (execAll (storeLe32 rv rs rd w k) s).mem y = s.mem y := by
  rw [storeLe32_mem s hvs hvd hw hk]
  simp only [write8, hy 0 (by omega), hy 1 (by omega), hy 2 (by omega), hy 3 (by omega), ite_false]

theorem storeLe32_aligned (s : State) (rv rs rd : LowReg) {w : Nat} (k : Nat) (hw : w < 32)
    (hal : (s.regs rs.toReg).toNat % 4 = 0) : alignedAll (storeLe32 rv rs rd w k) s = true := by
  have ew : w % 32 = w := Nat.mod_eq_of_lt hw
  simp [storeLe32, storeByte, alignedAll, Instr.accesses, Access.aligned, MemOp.width, Nat.mod_one,
    M0Crypto.Armv6M.State.reg, ew, BitVec.toNat_add]
  omega

/-- The word store writes only the four bytes at `rd + k`. -/
theorem storeLe32_writes (s : State) {rv rs rd : LowReg} {w k : Nat} {Wr : Word → Prop}
    (hvd : rv ≠ rd) (hk : k + 3 < 32)
    (hwr : ∀ j < 4, Wr (s.regs rd.toReg + BitVec.ofNat 32 (k + j))) :
    WritesTo Wr (traceAll (storeLe32 rv rs rd w k) s) := by
  have h1 := toReg_ne hvd
  have h2 := toReg_ne_15 rv
  have h3 := toReg_ne_15 rd
  have ek : k % 32 = k := Nat.mod_eq_of_lt (by omega)
  have hd : ∀ r : Reg, r ≠ rv.toReg → r = rd.toReg → r.val ≠ 15 := fun r _ e => by
    subst e; exact fun e => h3 (Fin.ext e)
  rw [storeLe32, traceAll, traceAll, traceAll_append, traceAll_append, execAll_append]
  generalize hs0 : (Instr.memImm .ldr rv rs (BitVec.ofNat 5 w)).next s = s0
  have d0 : s0.regs rd.toReg = s.regs rd.toReg := by
    subst hs0
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, Ne.symm h1, h3]
  have d1 : ((Instr.memImm .strb rv rd (BitVec.ofNat 5 k)).next s0).regs rd.toReg = s.regs rd.toReg := by
    rw [← d0]
    simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, Instr.size,
      M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg, h3]
  generalize (Instr.memImm .strb rv rd (BitVec.ofNat 5 k)).next s0 = s1 at d1
  have d2 := storeByte_regs_other s1 (rd := rd) k 1 (Ne.symm h1) (hd _ (Ne.symm h1) rfl)
  generalize execAll (storeByte rv rd k 1) s1 = s2 at d2
  have d3 := storeByte_regs_other s2 (rd := rd) k 2 (Ne.symm h1) (hd _ (Ne.symm h1) rfl)
  refine WritesTo.cons ?_ (WritesTo.cons ?_ (WritesTo.append (WritesTo.append ?_ ?_) ?_))
  · intro y hy
    obtain ⟨a, ha, hk', -⟩ := hy
    simp [Instr.accesses, MemOp.isLoad] at ha; subst ha; simp at hk'
  · intro y hy
    obtain ⟨a, ha, -, n, hn, rfl⟩ := hy
    simp [Instr.accesses, MemOp.isLoad, MemOp.width] at ha; subst ha
    simp at hn; subst hn
    have := hwr 0 (by omega)
    simpa [M0Crypto.Armv6M.State.reg, ek, d0] using this
  · exact storeByte_writes s1 k 1 hvd (by omega) (by rw [d1]; exact hwr 1 (by omega))
  · exact storeByte_writes s2 k 2 hvd (by omega) (by rw [d2, d1]; exact hwr 2 (by omega))
  · exact storeByte_writes _ k 3 hvd (by omega) (by rw [d3, d2, d1]; exact hwr 3 (by omega))

/-! ## Run lemmas -/

/-- **`load_le32`**: from `pc = base + off`, the sequence leaves in `rd` the little-endian value
of the four bytes at `p + k` (`p` in `rb`), changes no memory and no register other than `rd`,
`rt` and the flags, and continues at the end of the sequence. -/
theorem loadLe32_run_w {base p : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {t : State}
    {off k : Nat} {rd rt rb : LowReg} (hdt : rd ≠ rt) (hdb : rd ≠ rb) (htb : rt ≠ rb)
    (hk : k + 3 < 32) (hseq : seqAt B off (loadLe32 rd rt rb k) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hp : t.regs rb.toReg = p)
    (hr : InRegion Pc base off (seqSize (loadLe32 rd rt rb k))) {Q : State → Prop}
    (cont : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (loadLe32 rd rt rb k)) →
      t'.mem = t.mem →
      (∀ r : Reg, r ≠ rd.toReg → r ≠ rt.toReg → r.val ≠ 15 → t'.regs r = t.regs r) →
      (t'.regs rd.toReg).toNat = (t.mem (p + BitVec.ofNat 32 k)).toNat +
        2 ^ 8 * (t.mem (p + BitVec.ofNat 32 (k + 1))).toNat +
        2 ^ 16 * (t.mem (p + BitVec.ofNat 32 (k + 2))).toNat +
        2 ^ 24 * (t.mem (p + BitVec.ofNat 32 (k + 3))).toNat →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  apply ReachW.block hb (loadLe32 rd rt rb k) off hpc ho hseq (loadLe32_falls rd rt rb k)
    (loadLe32_aligned t rd rt rb k)
    (WritesTo.of_noWritesMem _ _ (loadLe32_noW rd rt rb k) Wr) hr
  apply cont
  · rw [execAll_pc _ _ (loadLe32_falls rd rt rb k), hpc, ofNat_add_assoc]
  · exact execAll_mem _ _ (loadLe32_noW rd rt rb k)
  · intro r h1 h2 h15
    exact loadLe32_regs_other t k h1 h2 h15
  · rw [← hp]; exact loadLe32_exec t hdt hdb htb hk

theorem loadLe32_run {base p : Word} (hb : base.toNat % 2 = 0) {Wr : Word → Prop} {t : State}
    {off k : Nat} {rd rt rb : LowReg} (hdt : rd ≠ rt) (hdb : rd ≠ rb) (htb : rt ≠ rb)
    (hk : k + 3 < 32) (hseq : seqAt B off (loadLe32 rd rt rb k) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hp : t.regs rb.toReg = p) {Q : State → Prop}
    (cont : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (loadLe32 rd rt rb k)) →
      t'.mem = t.mem →
      (∀ r : Reg, r ≠ rd.toReg → r ≠ rt.toReg → r.val ≠ 15 → t'.regs r = t.regs r) →
      (t'.regs rd.toReg).toNat = (t.mem (p + BitVec.ofNat 32 k)).toNat +
        2 ^ 8 * (t.mem (p + BitVec.ofNat 32 (k + 1))).toNat +
        2 ^ 16 * (t.mem (p + BitVec.ofNat 32 (k + 2))).toNat +
        2 ^ 24 * (t.mem (p + BitVec.ofNat 32 (k + 3))).toNat →
      Reach base Wr t' Q) :
    Reach base Wr t Q :=
  (loadLe32_run_w (Pc := fun _ => True) hb hdt hdb htb hk hseq ho hpc hp (fun _ _ => trivial)
    (fun t' a b c d => (cont t' a b c d).toReachW)).toReach

/-- **Word store**: from `pc = base + off`, the sequence writes byte `j` of the word at
`src + 4w` (`src` in `rs`) to `dst + k + j` (`dst` in `rd`) for `j < 4`, writes nothing else,
changes no register other than `rv` and the flags, and continues at the end of the sequence. -/
theorem storeLe32_run_w {base src dst : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {t : State} {off w k : Nat} {rv rs rd : LowReg} (hvs : rv ≠ rs) (hvd : rv ≠ rd) (hw : w < 32)
    (hk : k + 3 < 32) (hseq : seqAt B off (storeLe32 rv rs rd w k) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hs : t.regs rs.toReg = src)
    (hd : t.regs rd.toReg = dst) (hal : src.toNat % 4 = 0)
    (hwr : ∀ j < 4, Wr (dst + BitVec.ofNat 32 (k + j)))
    (hr : InRegion Pc base off (seqSize (storeLe32 rv rs rd w k))) {Q : State → Prop}
    (cont : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (storeLe32 rv rs rd w k)) →
      (∀ r : Reg, r ≠ rv.toReg → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < 4, t'.mem (dst + BitVec.ofNat 32 (k + j)) =
        BitVec.ofNat 8 ((read32 t.mem (src + BitVec.ofNat 32 (4 * w))).toNat / 2 ^ (8 * j))) →
      (∀ y, (∀ j < 4, y ≠ dst + BitVec.ofNat 32 (k + j)) → t'.mem y = t.mem y) →
      ReachW base Pc Wr t' Q) :
    ReachW base Pc Wr t Q := by
  subst hs hd
  apply ReachW.block hb (storeLe32 rv rs rd w k) off hpc ho hseq (storeLe32_falls rv rs rd w k)
    (storeLe32_aligned t rv rs rd k hw hal) (storeLe32_writes t hvd hk hwr) hr
  apply cont
  · rw [execAll_pc _ _ (storeLe32_falls rv rs rd w k), hpc, ofNat_add_assoc]
  · intro r h1 h15
    exact storeLe32_regs_other t w k h1 h15
  · intro j hj
    exact storeLe32_bytes t hvs hvd hw hk hj
  · intro y hy
    exact storeLe32_other t hvs hvd hw hk hy

theorem storeLe32_run {base src dst : Word} (hb : base.toNat % 2 = 0) {Wr : Word → Prop}
    {t : State} {off w k : Nat} {rv rs rd : LowReg} (hvs : rv ≠ rs) (hvd : rv ≠ rd) (hw : w < 32)
    (hk : k + 3 < 32) (hseq : seqAt B off (storeLe32 rv rs rd w k) = true) (ho : off % 2 = 0)
    (hpc : t.pc = base + BitVec.ofNat 32 off) (hs : t.regs rs.toReg = src)
    (hd : t.regs rd.toReg = dst) (hal : src.toNat % 4 = 0)
    (hwr : ∀ j < 4, Wr (dst + BitVec.ofNat 32 (k + j))) {Q : State → Prop}
    (cont : ∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize (storeLe32 rv rs rd w k)) →
      (∀ r : Reg, r ≠ rv.toReg → r.val ≠ 15 → t'.regs r = t.regs r) →
      (∀ j < 4, t'.mem (dst + BitVec.ofNat 32 (k + j)) =
        BitVec.ofNat 8 ((read32 t.mem (src + BitVec.ofNat 32 (4 * w))).toNat / 2 ^ (8 * j))) →
      (∀ y, (∀ j < 4, y ≠ dst + BitVec.ofNat 32 (k + j)) → t'.mem y = t.mem y) →
      Reach base Wr t' Q) :
    Reach base Wr t Q :=
  (storeLe32_run_w (Pc := fun _ => True) hb hvs hvd hw hk hseq ho hpc hs hd hal hwr
    (fun _ _ => trivial) (fun t' a b c d => (cont t' a b c d).toReachW)).toReach

end M0Crypto.Release.X25519Bytes
