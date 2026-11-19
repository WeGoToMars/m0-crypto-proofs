import SafegcdTermination.FinalCode
import SafegcdTermination.RowCalls
import SafegcdTermination.PublicTrace
import M0Crypto.Release.Routine

namespace SafegcdTermination.Leaf

open SafegcdRow
open SafegcdTermination.Bank
open SafegcdRow.BatchCode
open SafegcdTermination.RowCalls (entered_lr entered_regs entered_pc entered_mem entered_sp linkedRet_odd linkedRet_clear)
open M0Crypto.Armv6M (State Reg)
open M0Crypto.Thumb
open M0Crypto.Release.Routine (execAll_mem_other)
open M0Crypto.Sym
open SafegcdTermination.PublicTrace (traceChk trace_chk_sound)

structure Checked (is : List Instr) (al : List (Reg × Nat)) (r : Reg) (n : Nat) : Prop where
  falls : is.all Instr.falls = true
  noSp : is.all (fun i => !i.dsts.contains 13) = true
  noRet : is.all (fun i => !i.dsts.contains 14) = true
  align : alignChk al is = true
  writes : writeChk [(r,0,n)] is = true

theorem checked_canon : Checked InitCode.canonBody [(0,4),(1,4)] 0 32 := by
  constructor <;> decide +kernel

theorem checked_sub : Checked FinalCode.subBody [(0,4),(1,4),(2,4)] 0 32 := by
  constructor <;> decide +kernel

theorem checked_select : Checked FinalCode.selectBody [(0,4),(1,4),(2,4)] 0 32 := by
  constructor <;> decide +kernel

theorem memory_frame {is : List Instr} {al : List (Reg × Nat)} {r : Reg} {n : Nat}
    (h : Checked is al r n) (s : State) :
    WritesOnly s.mem (execAll is s).mem (s.regs r) n := by
  intro x hx
  apply execAll_mem_other
  intro e he hw
  obtain ⟨p,hP,o,ho,hx'⟩ := writeChk_sound _ _ (sound_all h.falls) s h.writes e he x hw
  simp only [List.mem_singleton] at hP
  subst p
  have hEq : x = s.regs r + 0#32 + BitVec.ofNat 32 o := hx'
  rw [show (s.regs r + 0#32) = s.regs r by simp] at hEq
  exact hx o ho hEq

def leafTrace (is : List Instr) (pc : Word) (s : State) : List Event :=
  traceAll is s ++ [⟨nextPC pc is,.bx 14,[]⟩]

def callTrace (is : List Instr) (base : Word) (off dest : Nat) (entry : State) : List Event :=
  ⟨base + BitVec.ofNat 32 off,callTo off dest,[]⟩ :: leafTrace is (base + BitVec.ofNat 32 dest) entry

theorem call_trace_congr {is : List Instr} {base : Word} {off dest : Nat} {u v : State} {regs : List Reg}
    (hf : is.all Instr.falls = true) (h : traceChk regs is = true) (hr : ∀ r ∈ regs, u.regs r = v.regs r) :
    callTrace is base off dest u = callTrace is base off dest v := by
  simp only [callTrace,leafTrace,trace_chk_sound hf h hr]

theorem run_leaf {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    {is : List Instr} {al : List (Reg × Nat)} {r : Reg} {n : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt code off (is ++ [.bx 14]) = true)
    (hRet : (s.regs 14).getLsbD 0 = true)
    (h : Checked is al r n) (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0) :
    ∃ t, runH code base (is.length+1) s = .ok (t,leafTrace is s.pc s) ∧
      t.pc = s.regs 14 &&& ~~~1#32 ∧ t.sp = s.sp ∧
      t.mem = (execAll is s).mem ∧ WritesOnly s.mem t.mem (s.regs r) n := by
  let u := execAll is s
  have he : (off + seqSize is) % 2 = 0 := by
    have := seqSize_mod_two is
    omega
  have hr : u.regs 14 = s.regs 14 := execAll_regs_other _ _ _ (by decide) h.noRet
  have hs : u.sp = s.sp := execAll_regs_other _ _ _ (by decide) h.noSp
  have hR : (u.regs 14).getLsbD 0 = true := by rw [hr]; exact hRet
  have hAligned := alignChk_sound al is (sound_all h.falls) s hal h.align
  have hexe := runH_leaf hb hlen hpc ho hat h.falls hAligned he hR
  let t := u.setReg 15 (u.regs 14 &&& ~~~1#32)
  have pc : t.pc = s.regs 14 &&& ~~~1#32 := by simp [t, State.pc, State.setReg, hr]
  have sp : t.sp = u.sp := by simp [t, State.sp, State.setReg]
  have hTr : u.pc = nextPC s.pc is := execAll_pc _ _ h.falls
  dsimp only at hexe

  rw [hTr] at hexe
  exact ⟨t, hexe, pc, sp.trans hs, rfl, memory_frame h s⟩

theorem run_leaf_call {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State}
    {is : List Instr} {al : List (Reg × Nat)} {r : Reg} {n : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (hat : seqAt code off [callTo off dest] = true) (hleaf : seqAt code dest (is ++ [.bx 14]) = true)
    (h : Checked is al r n) (hal : ∀ p ∈ al, p.1 ≠ 14 ∧ p.1 ≠ 15 ∧ (s.regs p.1).toNat % p.2 = 0)
    (hR : r ≠ 14 ∧ r ≠ 15) :
    let entry := entered base off dest s
    ∃ t, runH code base (is.length+1+1) s = .ok (t,callTrace is base off dest entry) ∧
      t.pc = base + BitVec.ofNat 32 (off+4) ∧ t.sp = s.sp ∧
      t.mem = (execAll is entry).mem ∧ WritesOnly s.mem t.mem (s.regs r) n := by
  have hlen' : code.length < 2^32 := by omega
  have hCall := (seqAt_size _ _ _ hat).resolve_right (by simp)
  change off + 4 ≤ code.length at hCall
  have hDest : dest + seqSize (is ++ [.bx 14]) ≤ code.length := (seqAt_size _ _ _ hleaf).resolve_right (by simp)
  let u := entered base off dest s
  have hAlg : ∀ p ∈ al, (u.regs p.1).toNat % p.2 = 0 := fun p hp => by
    obtain ⟨h1,h2,h3⟩ := hal p hp
    rw [entered_regs _ _ _ _ _ h1 h2]
    exact h3
  have hReturn : (u.regs 14).getLsbD 0 = true := by rw [entered_lr]; exact linkedRet_odd _ _
  obtain ⟨t,hRun,hPc,hSp,hMem,hFrames⟩ :=
    run_leaf hb hlen' (entered_pc _ _ _ _) hd hleaf hReturn h hAlg
  have hCombined := run_call hb hlen' hpc ho (by omega) (by omega) hat hRun
  have hp : t.pc = base + BitVec.ofNat 32 (off+4) := by
    rw [hPc, entered_lr]
    exact linkedRet_clear hb ho
  rw [entered_mem,entered_regs _ _ _ _ _ hR.1 hR.2] at hFrames
  rw [hpc, entered_pc] at hCombined
  exact ⟨t,hCombined,hp,hSp.trans (entered_sp _ _ _ _),hMem,hFrames⟩

end SafegcdTermination.Leaf
