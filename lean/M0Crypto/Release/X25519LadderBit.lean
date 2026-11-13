import M0Crypto.Release.X25519OpRun
import M0Crypto.Release.X25519InlBase
import M0Crypto.Thumb.SpBlock

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
The scalar-bit block of the ladder step (`X25519EntryCode.bitL`, plan phase 9, step 3).

From the counter `t` in `LV_T`, the block loads word `t / 32` of the clamped scalar (index
`(t >>> 3) &&& 28`, `X25519Decode.word_index`), extracts bit `t mod 32` (`rors`, `ands #1`,
`X25519Decode.ror_bit`), sets `r7 = -(swap ^ bit)` and stores the bit to `LV_SWAP`.
`bit_w` runs it in `ReachW`: SP and every frame byte outside `LV_SWAP` are unchanged.
-/

namespace M0Crypto.Release.X25519LadderBit
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 rorC addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region InRegion WritesTo B)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode (bitL)
open M0Crypto.Release.X25519Mem (toReg0 toReg1 toReg2 toReg7)

/-! ## Single instructions -/

theorem regs_lsrImm (s : State) (d m : LowReg) (i : BitVec 5) (r : Reg) (hr : r ≠ 15) :
    ((Instr.lsrImm d m i).next s).regs r =
      if r = d.toReg then s.reg m >>> (if i.toNat = 0 then 32 else i.toNat) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, lsrC, hr]

theorem regs_movImm (s : State) (d : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.movImm d i).next s).regs r = if r = d.toReg then i.setWidth 32 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_ldrReg (s : State) (t n m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.memReg .ldr t n m).next s).regs r =
      if r = t.toReg then read32 s.mem (s.reg n + s.reg m) else s.regs r := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg, hr]

theorem regs_rors (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .rors d m).next s).regs r =
      if r = d.toReg then (rorC (s.reg d) ((s.reg m).toNat % 256) s.c).1 else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, hr]

theorem regs_eors (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .eors d m).next s).regs r = if r = d.toReg then s.reg d ^^^ s.reg m else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, hr]

theorem regs_rsbs (s : State) (d m : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.dp .rsbs d m).next s).regs r =
      if r = d.toReg then (addWithCarry (~~~(s.reg m)) 0#32 true).1 else s.regs r := by
  simp [Instr.next, Instr.exec, addFlags, State.setReg, State.setNZCV, hr]

theorem regs_strSp (s : State) (t : LowReg) (i : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.strSp t i).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, hr]

theorem mem_strSp (s : State) (t : LowReg) (i : BitVec 8) :
    ((Instr.strSp t i).next s).mem = write32 s.mem (s.sp + BitVec.ofNat 32 (i.toNat * 4)) (s.reg t) := by
  simp [Instr.next, Instr.exec, State.setReg]

theorem rsbs_val (x : Word) : (addWithCarry (~~~x) 0#32 true).1 = 0#32 - x := by
  simp only [addWithCarry]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_not, BitVec.toNat_sub]
  omega

theorem c_lsrImm (s : State) (d m : LowReg) (i : BitVec 5) :
    ((Instr.lsrImm d m i).next s).c =
      (s.reg m).getLsbD ((if i.toNat = 0 then 32 else i.toNat) - 1) := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC, lsrC]

theorem c_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).c = s.c := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ]

theorem c_ldrReg (s : State) (t n m : LowReg) : ((Instr.memReg .ldr t n m).next s).c = s.c := by
  simp [Instr.next, Instr.exec, Instr.exec.memOp, State.setReg]

theorem mem_lsrImm (s : State) (d m : LowReg) (i : BitVec 5) : ((Instr.lsrImm d m i).next s).mem = s.mem :=
  next_mem (i := .lsrImm d m i) rfl s
theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem :=
  next_mem (i := .movImm d i) rfl s
theorem mem_dp (s : State) (op : DpOp) (d m : LowReg) : ((Instr.dp op d m).next s).mem = s.mem :=
  next_mem (i := .dp op d m) (by cases op <;> rfl) s
theorem mem_ldrReg (s : State) (t n m : LowReg) : ((Instr.memReg .ldr t n m).next s).mem = s.mem :=
  next_mem (i := .memReg .ldr t n m) rfl s

/-! ## The block -/

/-- The bit block's effect: `r7 = -(swap ^ bit)`, `LV_SWAP = bit`, SP unchanged. -/
theorem bit_exec (s : State) :
    let sp := s.regs 13
    let tW := read32 s.mem (sp + BitVec.ofNat 32 lvT)
    let w := read32 s.mem (sp + BitVec.ofNat 32 sK + ((tW >>> 3) &&& 28#32))
    let b := (rorC w (tW.toNat % 256) (tW.getLsbD 2)).1 &&& 1#32
    let u := execAll bitL s
    u.regs 13 = sp ∧ u.regs 7 = 0#32 - (read32 s.mem (sp + BitVec.ofNat 32 lvSwap) ^^^ b) ∧
      u.mem = write32 s.mem (sp + BitVec.ofNat 32 lvSwap) b := by
  intro sp tW w b u
  refine ⟨?_, ?_, ?_⟩
  · simp [u, sp, bitL, execAll, regs_lsrImm, regs_movImm, regs_ldrReg, regs_rors, regs_eors, regs_rsbs,
      regs_strSp, X25519Mem.regs_ldrSp, X25519Mem.regs_addRdSp, X25519Inl.regs_ands, State.reg, toReg0, toReg1, toReg2, toReg7]
  · simp [u, sp, tW, w, b, bitL, execAll, regs_lsrImm, regs_movImm, regs_ldrReg, regs_rors, regs_eors,
      regs_rsbs, regs_strSp, X25519Mem.regs_ldrSp, X25519Mem.regs_addRdSp, X25519Inl.regs_ands, rsbs_val,
      mem_lsrImm, mem_movImm, mem_dp, mem_ldrReg, X25519Mem.mem_ldrSp, X25519Mem.mem_addRdSp,
      c_lsrImm, c_movImm, c_ldrReg, X25519Inl.c_ands, X25519Mem.c_ldrSp, X25519Mem.c_addRdSp,
      State.reg, State.sp, lvT, lvSwap, sK, toReg0, toReg1, toReg2, toReg7]
  · simp [u, sp, tW, w, b, bitL, execAll, regs_lsrImm, regs_movImm, regs_ldrReg, regs_rors, regs_eors,
      regs_rsbs, regs_strSp, X25519Mem.regs_ldrSp, X25519Mem.regs_addRdSp, X25519Inl.regs_ands,
      mem_lsrImm, mem_movImm, mem_dp, mem_ldrReg, X25519Mem.mem_ldrSp, X25519Mem.mem_addRdSp, mem_strSp,
      c_lsrImm, c_movImm, c_ldrReg, X25519Inl.c_ands, X25519Mem.c_ldrSp, X25519Mem.c_addRdSp,
      State.reg, State.sp, lvT, lvSwap, sK, toReg0, toReg1, toReg2, toReg7]

theorem and28_mod (n : Nat) : (n &&& 28) % 4 = 0 := by
  have h := Nat.and_mod_two_pow (a := n) (b := 28) (n := 2)
  simp only [show (2 : Nat) ^ 2 = 4 from rfl] at h
  rw [h]; simp

/-- The block's accesses: aligned, and the only write is `LV_SWAP`. -/
theorem bit_acc {Wr : Word → Prop} (s : State) (hsp : (s.regs 13).toNat % 4 = 0)
    (hW : ∀ k < 4, Wr (s.regs 13 + BitVec.ofNat 32 lvSwap + BitVec.ofNat 32 k)) :
    X25519Block.AccAll (X25519Block.AccOk Wr) bitL s := by
  simp [X25519Block.AccAll, X25519Block.AccOk, bitL, traceAll, Instr.accesses, Access.aligned,
    regs_lsrImm, regs_movImm, regs_ldrReg, regs_rors, regs_eors, regs_rsbs, regs_strSp,
    X25519Mem.regs_ldrSp, X25519Mem.regs_addRdSp, X25519Inl.regs_ands, State.reg, State.sp,
    mem_lsrImm, mem_movImm, mem_dp, mem_ldrReg, X25519Mem.mem_ldrSp, X25519Mem.mem_addRdSp,
    toReg0, toReg1, toReg2, toReg7, lvT, lvSwap, sK, MemOp.width, MemOp.isLoad]
  simp only [lvSwap] at hW
  have := and28_mod (BitVec.toNat (read32 s.mem (s.regs 13 + 320#32)) >>> 3)
  refine ⟨by omega, by omega, by omega, fun k hk => hW k hk⟩

theorem write32_out {m : Mem} {a v y : Word} (h : ¬ Region a 4 y) : write32 m a v y = m y := by
  apply M0Crypto.Armv6M.write32_other
  intro k hk e
  apply h; subst e
  show (a + BitVec.ofNat 32 k - a).toNat < 4
  rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact hk

/-- The bit block in the entry: `r7 = -(swap ^ bit)` and `LV_SWAP = bit`, `Body` kept. -/
theorem bit_w {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} {Wr : Word → Prop}
    (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
    {s : State} {Q : State → Prop} {o : Nat}
    (hseq : seqAt B o bitL = true) (ho : o % 2 = 0) (hlo : lo ≤ o) (hend : o + seqSize bitL ≤ hi)
    (hpc : s.pc = c.base + BitVec.ofNat 32 o) (hs : X25519Op.Body c m1 s)
    (k : ∀ u, u.pc = c.base + BitVec.ofNat 32 (o + seqSize bitL) → X25519Op.Body c m1 u →
      let tW := read32 s.mem (E c + BitVec.ofNat 32 lvT)
      let w := read32 s.mem (E c + BitVec.ofNat 32 sK + ((tW >>> 3) &&& 28#32))
      let b := (rorC w (tW.toNat % 256) (tW.getLsbD 2)).1 &&& 1#32
      u.regs 7 = 0#32 - (read32 s.mem (E c + BitVec.ofNat 32 lvSwap) ^^^ b) →
      u.mem = write32 s.mem (E c + BitVec.ofNat 32 lvSwap) b →
      ReachW c.base Pc Wr u Q) :
    ReachW c.base Pc Wr s Q := by
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have := hPO.hile
  have hE := X25519Op.E_toNat hv
  have hF := X25519Op.fp_toNat hv
  have hsp := hv.spLo
  have hs4 := hv.sp4
  have hR := hv.codeS
  simp only [X25519.stackBytes, SAVED, LFRAME, Frame.Disj] at hE hF hsp hR
  have hsz : seqSize bitL = 26 := by decide
  have h13 := hs.sp
  have hsw : ∀ y, Region (E c + BitVec.ofNat 32 lvSwap) 4 y → Region c.fp X25519.wipeBytes y := by
    intro y h
    have e := X25519Op.E_add hv (d := lvSwap) (by decide)
    exact X25519Op.region_sub (by simp only [X25519.wipeBytes]; omega)
      (by rw [e]; simp only [lvSwap]; omega) (by rw [e]; simp only [lvSwap, X25519.wipeBytes]; omega) h
  have hacc : X25519Block.AccAll (X25519Block.AccOk Wr) bitL s := by
    refine bit_acc s (by rw [h13]; omega) fun j hj => hWr _ ?_
    rw [h13]
    refine X25519Op.region_sub (a := E c + BitVec.ofNat 32 lvSwap) (n := 4) (by simp only [X25519.stackBytes]; omega) ?_ ?_ ?_
    · rw [X25519Op.E_add hv (by decide)]; simp only [lvSwap, X25519.stackBytes]; omega
    · rw [X25519Op.E_add hv (by decide)]; simp only [lvSwap, X25519.stackBytes]; omega
    · show (_ - _ : Word).toNat < 4
      rw [Frame.sub_ofNat_toNat _ _ (by omega)]; exact hj
  refine X25519Block.ReachW.blockAcc hb0 bitL o hpc ho hseq (by decide) hacc
    (hPO.inE hlo hend) ?_
  obtain ⟨u13, u7, um⟩ := bit_exec s
  rw [h13] at u13 u7 um
  refine k _ (by rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]) ⟨u13, fun y hy => ?_⟩ u7 um
  rw [um, write32_out (fun h => hy (hsw y h))]
  exact hs.keep y hy

end M0Crypto.Release.X25519LadderBit
