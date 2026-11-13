import M0Crypto.Release.X25519OpRun

set_option linter.unusedSimpArgs false

/-!
The epilogue of `m0c_x25519`.

`epilogue` is `add sp, #(CALLEE + LFRAME); movs r0, #0; mov r12, r0; pop {r4-r7};
mov r8-r11, r4-r7; pop {r4-r7, pc}` (`X25519EntryCode.epilogue`). The prologue saved, from
`F = sp0 - SAVED` up, `r8`-`r11`, then `r4`-`r7`, then `lr` (`push {r4-r7, lr}` first, at
`sp0 - 20`; then `push {r4-r7}` of the copies of `r8`-`r11`, at `sp0 - 36`): word `i` of the
save area holds `savedReg i`.

`epilogue_run_w` runs the segment, generic in its SP: the eight registers come back from the
save area, SP ends at `F + SAVED`, `r0` and `r12` are zero, `r1`-`r3` are unchanged, memory is
unchanged, and the PC is the saved `lr` with bit 0 cleared (the return; the `pop {pc}` is the
last instruction executed in the region, as in `X25519MulcEnds.pop_run_w`).
-/

namespace M0Crypto.Release.X25519OutEpi
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region B)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode

/-- The register saved in word `i` of the save area (`i < 9`): `r8`-`r11`, `r4`-`r7`, `lr`. -/
def savedReg (i : Nat) : Reg :=
  ⟨(if i < 4 then 8 + i else if i < 8 then i else 14) % 16, Nat.mod_lt _ (by decide)⟩

theorem savedReg_cover (r : Reg) (h4 : 4 ≤ r.val) (h12 : r.val < 12) :
    ∃ i < 8, savedReg i = r := by
  rcases r with ⟨v, hv⟩
  simp only at h4 h12
  by_cases h : v < 8
  · refine ⟨v, by omega, Fin.ext ?_⟩
    show (if v < 4 then 8 + v else if v < 8 then v else 14) % 16 = v
    simp only [show ¬ v < 4 by omega, h, ite_true, ite_false]; omega
  · refine ⟨v - 8, by omega, Fin.ext ?_⟩
    show (if v - 8 < 4 then 8 + (v - 8) else if v - 8 < 8 then v - 8 else 14) % 16 = v
    simp only [show v - 8 < 4 by omega, ite_true]; omega

/-- The first eight instructions; the last `pop {r4-r7, pc}` returns. -/
def epiA : List Instr :=
  [.addSp (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)), .movImm 0 0, .movHi 12 0, .pop 0xf0 false,
    .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7]

theorem epilogue_eq : epilogue = epiA ++ [.pop 0xf0 true] := rfl

theorem frame_off : (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)).toNat * 4 = CALLEE + LFRAME := by decide
theorem frame_off' : (CALLEE + LFRAME) / 4 % 128 * 4 = CALLEE + LFRAME := by decide

theorem listRegs_240 : listRegs 240#8 = [4, 5, 6, 7] := by decide
theorem bitCount_240 : bitCount 240#8 = 4 := by decide

/-! ## One instruction at a time -/

open M0Crypto.Release.InstrNext (regs_movHi regs_movImm)

theorem regs_addSp (s : State) (i : BitVec 7) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addSp i).next s).regs r =
      if r = 13 then s.regs 13 + BitVec.ofNat 32 (i.toNat * 4) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, hr]

theorem mem_addSp (s : State) (i : BitVec 7) : ((Instr.addSp i).next s).mem = s.mem := next_mem rfl s
theorem mem_movHi (s : State) (d m : Reg) : ((Instr.movHi d m).next s).mem = s.mem := next_mem rfl s
theorem mem_movImm (s : State) (d : LowReg) (i : BitVec 8) : ((Instr.movImm d i).next s).mem = s.mem :=
  next_mem rfl s

/-- `pop {r4-r7}`: word `j` from SP into `r(4 + j)`, SP up by 16. -/
theorem regs_pop4 (s : State) (r : Reg) (hr : r ≠ 15) :
    ((Instr.pop 0xf0 false).next s).regs r =
      if r = 4 then read32 s.mem (s.regs 13) else if r = 5 then read32 s.mem (s.regs 13 + 4#32)
      else if r = 6 then read32 s.mem (s.regs 13 + 4#32 + 4#32)
      else if r = 7 then read32 s.mem (s.regs 13 + 4#32 + 4#32 + 4#32)
      else if r = 13 then s.regs 13 + 16#32 else s.regs r := by
  have h4 : (4 : Reg) ≠ 15 := by decide
  simp only [Instr.next, Instr.exec, State.sp, Bool.false_eq_true, ite_false]
  rw [Frame.listRegs_f0]
  simp only [List.map, loadRegs, State.setReg, Frame.bitCount_f0]
  by_cases a4 : r = 4 <;> by_cases a5 : r = 5 <;> by_cases a6 : r = 6 <;> by_cases a7 : r = 7 <;>
    by_cases a13 : r = 13 <;> subst_vars <;> simp_all (config := { decide := true }) [LowReg.toReg, Fin.ext_iff] <;>
    simp only [show ((4 : LowReg) : Nat) = 4 from rfl, show ((5 : LowReg) : Nat) = 5 from rfl,
      show ((6 : LowReg) : Nat) = 6 from rfl, show ((7 : LowReg) : Nat) = 7 from rfl,
      show ((4 : Reg) : Nat) = 4 from rfl, show ((5 : Reg) : Nat) = 5 from rfl,
      show ((6 : Reg) : Nat) = 6 from rfl, show ((7 : Reg) : Nat) = 7 from rfl] at * <;> simp_all

theorem mem_pop4 (s : State) : ((Instr.pop 0xf0 false).next s).mem = s.mem := next_mem rfl s

section
variable (s : State) {F : Word} (hF : s.regs 13 + BitVec.ofNat 32 (CALLEE + LFRAME) = F)
include hF

/-- Register values after `epiA`, one fact per register the contract names. -/
theorem epiA_regs :
    let u := execAll epiA s
    u.regs 0 = 0#32 ∧ u.regs 12 = 0#32 ∧ u.regs 13 = F + 16#32 ∧
    u.regs 1 = s.regs 1 ∧ u.regs 2 = s.regs 2 ∧ u.regs 3 = s.regs 3 ∧
    u.regs 8 = read32 s.mem F ∧ u.regs 9 = read32 s.mem (F + 4#32) ∧
    u.regs 10 = read32 s.mem (F + 4#32 + 4#32) ∧ u.regs 11 = read32 s.mem (F + 4#32 + 4#32 + 4#32) := by
  intro u
  subst hF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) only [u, epiA, execAll, regs_movHi, regs_movImm, regs_addSp,
      regs_pop4, mem_pop4, mem_movHi, mem_movImm, mem_addSp, frame_off, LowReg.toReg, ite_true, ite_false,
      ne_eq, not_false_eq_true] <;> rfl

omit hF in
theorem epiA_mem : (execAll epiA s).mem = s.mem := execAll_mem _ _ rfl

end

/-- State after `pop {r4-r7, pc}` from `s`, when the loaded PC is odd. -/
def popPC (s : State) : State :=
  ((loadRegs (s.setReg 15 (s.pc + 2#32)) (s.regs 13) ((listRegs 0xf0).map LowReg.toReg)).setReg 13
    (s.regs 13 + 20#32)).setReg 15 (read32 s.mem (s.regs 13 + 16#32) &&& ~~~1#32)

theorem popPC_exec (s : State) (hlr : (read32 s.mem (s.regs 13 + 16#32)).getLsbD 0 = true) :
    (Instr.pop 0xf0 true).exec s = .ok (popPC s) := by
  have e1 : s.regs 13 + BitVec.ofNat 32 (4 * bitCount 0xf0) = s.regs 13 + 16#32 := by
    rw [Frame.bitCount_f0]
  have e2 : s.regs 13 + BitVec.ofNat 32 (4 * (bitCount 0xf0 + true.toNat)) = s.regs 13 + 20#32 := by
    rw [Frame.bitCount_f0]; rfl
  simp only [Instr.exec, State.sp, e1, e2, hlr, ite_true, popPC]
  rfl

theorem popPC_regs (s : State) (r : Reg) (hr : r ≠ 15) :
    (popPC s).regs r =
      if r = 4 then read32 s.mem (s.regs 13) else if r = 5 then read32 s.mem (s.regs 13 + 4#32)
      else if r = 6 then read32 s.mem (s.regs 13 + 4#32 + 4#32)
      else if r = 7 then read32 s.mem (s.regs 13 + 4#32 + 4#32 + 4#32)
      else if r = 13 then s.regs 13 + 20#32 else s.regs r := by
  simp only [popPC]
  rw [Frame.listRegs_f0]
  simp only [List.map, loadRegs, State.setReg]
  by_cases a4 : r = 4 <;> by_cases a5 : r = 5 <;> by_cases a6 : r = 6 <;> by_cases a7 : r = 7 <;>
    by_cases a13 : r = 13 <;> subst_vars <;> simp_all (config := { decide := true }) [LowReg.toReg, Fin.ext_iff] <;>
    simp only [show ((4 : LowReg) : Nat) = 4 from rfl, show ((5 : LowReg) : Nat) = 5 from rfl,
      show ((6 : LowReg) : Nat) = 6 from rfl, show ((7 : LowReg) : Nat) = 7 from rfl,
      show ((4 : Reg) : Nat) = 4 from rfl, show ((5 : Reg) : Nat) = 5 from rfl,
      show ((6 : Reg) : Nat) = 6 from rfl, show ((7 : Reg) : Nat) = 7 from rfl] at * <;> simp_all

theorem popPC_pc (s : State) : (popPC s).pc = read32 s.mem (s.regs 13 + 16#32) &&& ~~~1#32 := by
  simp [popPC, State.pc, State.setReg]

theorem popPC_mem (s : State) : (popPC s).mem = s.mem := by
  simp only [popPC, setReg_mem, loadRegs_mem]

theorem epiA_falls : epiA.all Instr.falls = true := by decide

/-- **`epilogue`**: from `pc = base + off` with `F = SP + CALLEE + LFRAME` aligned and an odd
saved `lr` (word 8), the segment returns to that `lr` with bit 0 cleared, with SP at
`F + SAVED`, the eight saved registers restored from words 0..7, `r0 = r12 = 0`, `r1`-`r3`
and memory unchanged. -/
theorem epilogue_run_w {base F : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {s : State}
    {off : Nat} (hseq : seqAt B off epilogue = true) (ho : off % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (hF : s.regs 13 + BitVec.ofNat 32 (CALLEE + LFRAME) = F)
    (hF4 : F.toNat % 4 = 0) (hlr : (read32 s.mem (F + BitVec.ofNat 32 (4 * 8))).getLsbD 0 = true)
    (hr : InRegion Pc base off (seqSize epilogue)) {Q : State → Prop}
    (hq : ∀ t, t.pc = read32 s.mem (F + BitVec.ofNat 32 (4 * 8)) &&& ~~~1#32 →
      t.regs 13 = F + BitVec.ofNat 32 SAVED → t.mem = s.mem → t.regs 0 = 0#32 → t.regs 12 = 0#32 →
      (∀ r : Reg, 1 ≤ r.val → r.val ≤ 3 → t.regs r = s.regs r) →
      (∀ i < 8, t.regs (savedReg i) = read32 s.mem (F + BitVec.ofNat 32 (4 * i))) → Q t) :
    ReachW base Pc Wr s Q := by
  rw [epilogue_eq, seqAt_append, Bool.and_eq_true] at hseq
  rw [epilogue_eq, seqSize_append] at hr
  have hA : seqSize epiA = 16 := rfl
  rw [hA] at hseq hr
  -- the eight fall-through instructions: one read access, the `pop {r4-r7}` at `F`
  refine ReachW.block hb epiA off hpc ho hseq.1 epiA_falls ?_ (WritesTo.of_noWritesMem _ _ rfl Wr)
    (hr.prefix (by omega)) ?_
  · have e3 : (execAll [.addSp (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)), .movImm 0 0, .movHi 12 0] s).regs 13
        = F := by
      subst hF
      simp (config := { decide := true }) [execAll, Instr.next, Instr.exec, State.setReg, State.setNZ,
        State.sp, LowReg.toReg, frame_off']
    have hsplit : epiA = [.addSp (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)), .movImm 0 0, .movHi 12 0] ++
        [.pop 0xf0 false] ++ [.movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7] := rfl
    rw [hsplit, alignedAll_append, alignedAll_append,
      X25519Mul.alignedAll_regOnly [.addSp (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)), .movImm 0 0, .movHi 12 0] _ rfl,
      X25519Mul.alignedAll_regOnly [.movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7] _ rfl]
    simp only [Bool.true_and, Bool.and_true, alignedAll, Instr.accesses, State.sp, e3]
    exact X25519Block.wordAccesses_aligned hF4
  · obtain ⟨u0, u12, u13, u1, u2, u3, u8, u9, u10, u11⟩ := epiA_regs s hF
    have um := epiA_mem s
    have upc : (execAll epiA s).pc = base + BitVec.ofNat 32 (off + 16) := by
      rw [execAll_pc _ _ epiA_falls, hpc, ofNat_add_assoc]; rfl
    generalize execAll epiA s = u at u0 u12 u13 u1 u2 u3 u8 u9 u10 u11 um upc
    have a16 : F + 16#32 + 16#32 = F + BitVec.ofNat 32 (4 * 8) := by bv_omega
    have hlr' : (read32 u.mem (u.regs 13 + 16#32)).getLsbD 0 = true := by rw [u13, um, a16]; exact hlr
    have hs2 := hseq.2
    simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs2
    have hu4 : (u.regs 13).toNat % 4 = 0 := by
      rw [u13, BitVec.toNat_add]; have := F.isLt
      simp only [BitVec.toNat_ofNat]; omega
    refine ReachW.step hb (off + 16) (.pop 0xf0 true) upc (by omega) hs2.1 hs2.2
      (by simpa [Instr.accesses, State.sp, bitCount_240] using X25519Block.wordAccesses_aligned (k := .read) (n := 5) hu4)
      (popPC_exec u hlr')
      (fun y ⟨a, ha, hw, _⟩ => by
        simp [Instr.accesses, wordAccesses] at ha; obtain ⟨_, _, rfl⟩ := ha; cases hw)
      (by have := hr.at (a := 16) (by simp [seqSize, Instr.size]); simpa using this)
      (ReachS.done (hq _ ?_ ?_ ?_ ?_ ?_ ?_ ?_))
    · rw [popPC_pc, u13, um, a16]
    · rw [popPC_regs u 13 (by decide)]; simp (config := { decide := true }) only [ite_false, ite_true, u13]
      simp only [SAVED]; bv_omega
    · rw [popPC_mem, um]
    · rw [popPC_regs u 0 (by decide)]; simp (config := { decide := true }) only [ite_false, u0]
    · rw [popPC_regs u 12 (by decide)]; simp (config := { decide := true }) only [ite_false, u12]
    · intro r h1 h3
      have hr' : r = 1 ∨ r = 2 ∨ r = 3 := by
        rcases r with ⟨v, hv⟩
        simp only at h1 h3
        rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3) with rfl | rfl | rfl <;> simp [Fin.ext_iff]
      rcases hr' with rfl | rfl | rfl <;> rw [popPC_regs u _ (by decide)] <;>
        simp (config := { decide := true }) only [ite_false, u1, u2, u3]
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show savedReg 0 = 8 from rfl, popPC_regs u 8 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 1 = 9 from rfl, popPC_regs u 9 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 2 = 10 from rfl, popPC_regs u 10 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 3 = 11 from rfl, popPC_regs u 11 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 4 = 4 from rfl, popPC_regs u 4 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 5 = 5 from rfl, popPC_regs u 5 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 6 = 6 from rfl, popPC_regs u 6 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp
      · rw [show savedReg 7 = 7 from rfl, popPC_regs u 7 (by decide)]
        simp (config := { decide := true }) only [ite_false, ite_true, u8, u9, u10, u11, u13, um]
        all_goals first | (simp only [BitVec.add_assoc]; rfl) | simp

end M0Crypto.Release.X25519OutEpi
