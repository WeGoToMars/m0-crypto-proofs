import M0Crypto.Release.ConstantTime.TraceFragment
import M0Crypto.Release.ConstantTime.HolesAccess
import M0Crypto.Release.ConstantTime.PopSound
import M0Crypto.Release.ConstantTime.ReturnSound
import M0Crypto.Release.ConstantTime.BranchDirect
import M0Crypto.Release.ConstantTime.BranchConditional
import M0Crypto.Release.ConstantTime.Alignment

set_option linter.unusedSimpArgs false

/-!
# The next PC of a certified step

From a certificate position, a step goes to one of the offsets `succOffs` lists (`Holes.lean`)
or returns to the caller.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State Reg LowReg)
open M0Crypto.Thumb

/-- A step from a decoded instruction is its execution, with its event. -/
theorem step_exec_of {s t : State} {e : Event} {base : Word} {bytes : List (BitVec 8)}
    (hcode : M0Crypto.Thumb.CodeAt s.mem base bytes) (off : Nat) (i : Instr)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (hi : instrAt bytes off = some i)
    (hlen : off + i.size ≤ bytes.length) (h : step s = .ok (t, e)) :
    i.exec s = .ok t ∧ e = ⟨s.pc, i, i.accesses s⟩ := by
  have hd := decode_at hcode off i hi hlen
  rw [← hpc] at hd
  unfold step at h
  simp only [hd] at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i s' hex
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hex, rfl⟩
      · cases h
    · cases h

/-- Instructions that continue at the next instruction. -/
def fallInstr : Instr → Bool
  | .bcond .. | .b .. | .bl .. | .pop _ true | .bx .. => false
  | _ => true

theorem succOffs_fall {off : Nat} {i : Instr} {out : Out} (h : fallInstr i = true) :
    succOffs off i out = [off + i.size] := by
  cases i <;> simp_all [fallInstr, succOffs]
  case pop l pc => cases pc <;> simp_all

theorem lowReg_ne_pc (r : LowReg) : (15 : Reg) ≠ r.toReg := by
  intro h
  have := congrArg Fin.val h
  simp [LowReg.toReg] at this
  omega

theorem setReg_low_pc (s : State) (r : LowReg) (x : Word) : (s.setReg r.toReg x).pc = s.pc := by
  simp [State.pc, State.setReg, lowReg_ne_pc r]

theorem loadRegs_pc (s : State) (a : Word) (rs : List LowReg) :
    (loadRegs s a (rs.map LowReg.toReg)).pc = s.pc := by
  induction rs generalizing s a with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, loadRegs]; rw [ih, setReg_low_pc]

theorem addFlags_pc (s : State) (d : LowReg) (a b : Word) (c w : Bool) :
    (addFlags s d.toReg a b c w).pc = s.pc := by
  unfold addFlags
  cases w <;> simp [State.setNZCV, State.setNZ, State.pc, State.setReg, lowReg_ne_pc d]

theorem addFlags0_pc (s : State) (a b : Word) (c : Bool) :
    (addFlags s 0 a b c false).pc = s.pc := by
  simp [addFlags, State.setNZCV, State.setNZ, State.pc]

theorem setNZ_pc (s : State) (x : Word) : (s.setNZ x).pc = s.pc := rfl
theorem setNZC_pc (s : State) (x : Word) (c : Bool) : (s.setNZC x c).pc = s.pc := rfl
theorem withMem_pc (s : State) (m : M0Crypto.Armv6M.Mem) : ({ s with mem := m } : State).pc = s.pc := rfl
theorem setSp_pc (s : State) (x : Word) : (s.setReg 13 x).pc = s.pc := by
  simp [State.pc, State.setReg]
theorem setPc_pc (s : State) (x : Word) : (s.setReg 15 x).pc = x := by
  simp [State.pc, State.setReg]
theorem memOp_pc (s : State) (op : MemOp) (t : LowReg) (a : Word) :
    (Instr.exec.memOp s op t a).pc = s.pc := by
  cases op <;> simp only [Instr.exec.memOp, withMem_pc, setReg_low_pc]

/-- An instruction that continues at the next instruction sets the PC to it. -/
theorem exec_pc_fall {s t : State} (i : Instr) (hf : fallInstr i = true) (hs : pcSafe i = true)
    (h : i.exec s = .ok t) : t.pc = s.pc + BitVec.ofNat 32 i.size := by
  cases i with
  | bcond => simp [fallInstr] at hf
  | b => simp [fallInstr] at hf
  | bl => simp [fallInstr] at hf
  | bx => simp [fallInstr] at hf
  | pop l pc =>
    cases pc
    · simp only [Instr.exec, Bool.false_eq_true, ite_false, Except.ok.injEq] at h
      subst h
      rw [setSp_pc, loadRegs_pc, setPc_pc]
    · simp [fallInstr] at hf
  | movHi d m =>
    simp only [Instr.exec, Except.ok.injEq] at h
    subst h
    simp only [pcSafe, bne_iff_ne, ne_eq] at hs
    have hd : (15 : Reg) ≠ d := by intro e; apply hs; rw [← e]; rfl
    simp [State.pc, State.setReg, hd]
  | ldm n l =>
    simp only [Instr.exec] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rw [loadRegs_pc, setPc_pc]
    · simp only [Except.ok.injEq] at h; subst h; rw [setReg_low_pc, loadRegs_pc, setPc_pc]
  | dp op d m =>
    cases op <;> simp only [Instr.exec, Except.ok.injEq] at h <;> (try split at h) <;>
      (try simp only [Except.ok.injEq] at h) <;> subst h <;>
      simp only [setNZ_pc, setNZC_pc, setReg_low_pc, addFlags_pc, addFlags0_pc, setPc_pc]
  | _ =>
    simp only [Instr.exec] at h
    (try split at h) <;> (simp only [Except.ok.injEq] at h; subst h
                          simp only [setNZ_pc, setNZC_pc, setReg_low_pc, addFlags_pc, addFlags0_pc,
                            setPc_pc, memOp_pc, withMem_pc, setSp_pc])

theorem mem_succOffs_pt {off target : Nat} {i : Instr} {out : Out} {ctx : Option Nat}
    {st : AbsState} (hi : fallInstr i = false) (hm : (Tgt.pt target ctx, st) ∈ out.succs) :
    target ∈ succOffs off i out := by
  have : succOffs off i out = ptOffs out := by
    cases i <;> simp_all [fallInstr, succOffs]
    case pop l pc => cases pc <;> simp_all
  rw [this]
  exact List.mem_filterMap.2 ⟨_, hm, rfl⟩

/-- **The next PC of a certified step**: the caller's return address, or the artifact address of
an offset listed by `succOffs`. -/
theorem certPoint_next_pc {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {i : Instr}
    {is : List Instr} {p : Params} {s t : State} {e : Event} {out : Out}
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is)) (h : LowEq p bytes off st s s)
    (hx : xfer env off b.ctx i st = .ok out) (hsafe : pcSafe i = true)
    (hst : step s = .ok (t, e)) (hplain : env.frameCallAt off = none) :
    t.pc = p.lr0 &&& ~~~1#32 ∨ ∃ tgt ∈ succOffs off i out, t.pc = p.base + BitVec.ofNat 32 tgt := by
  have heven := certPoint_pc_even p.base hbase ha hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  obtain ⟨hex, -⟩ := step_exec_of h.code₁ off i h.pc hdecode hlen hst
  by_cases hf : fallInstr i = true
  · right
    refine ⟨off + i.size, by simp [succOffs_fall hf], ?_⟩
    rw [exec_pc_fall i hf hsafe hex, h.pc, BitVec.add_assoc, ← BitVec.ofNat_add]
  · have hf' : fallInstr i = false := by simpa using hf
    cases i with
    | b imm =>
      obtain ⟨target, t₁, t₂, e', hs₁, -, -, hmem, hnext⟩ :=
        branch_checked_step imm hx hidx h heven hdecode hlen
      have he := hst.symm.trans hs₁
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨target, mem_succOffs_pt hf' hmem, hnext.pc⟩
    | bcond cond imm =>
      obtain ⟨target, nextSt, t₁, t₂, e', hs₁, -, hmem, hnext⟩ :=
        bcond_checked_step cond imm hx hidx h (fun _ => rfl)
          (fun _ _ hs => certPoint_successor_indices hi hm hp hx hs) heven hdecode hlen
      have he := hst.symm.trans hs₁
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨target, mem_succOffs_pt hf' hmem, hnext.pc⟩
    | bl imm =>
      have hb := xfer_sp_bounds hx
      have hw : env.win.covers st.spOff st.spOff = true := by
        simp [StackWindow.covers, hb.1, hb.2.2]
      have hx' := hx
      simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx'
      cases hctx : b.ctx with
      | some r => simp [hctx] at hx'
      | none =>
        simp only [hctx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hx'
        cases ht : relTarget off (blDisp imm) with
        | none => simp [ht] at hx'
        | some target =>
          simp only [ht, hplain, Except.ok.injEq] at hx'
          subst out
          have htarget := relTarget_address p.base off target (blDisp imm) ht
          have hdisp : BitVec.ofInt 32 (blDisp imm) = imm.signExtend 32 := by simp [blDisp]
          rw [hdisp] at htarget
          right
          refine ⟨target, by simp [succOffs, ptOffs], ?_⟩
          simp only [Instr.exec, Except.ok.injEq] at hex
          subst hex
          rw [setPc_pc, h.pc, htarget]
    | pop l pc =>
      cases pc with
      | false => simp [fallInstr] at hf
      | true =>
        have hnil := certPoint_return_final l hc hm hp
        subst hnil
        have hsf := certPoint_final_successors hc hm hp hx
        simp only [Instr.exec, ite_true] at hex
        split at hex
        · simp only [Except.ok.injEq] at hex
          subst hex
          rw [setPc_pc]
          have hsp : s.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
          cases hctx : b.ctx with
          | none =>
            have hx' : xfer env off none (.pop l true) st = .ok out := by simpa [hctx] using hx
            left
            rw [(return_slot_value l h (pop_exit_slot l hx')).1]
          | some c =>
            have hx' : xfer env off (some c) (.pop l true) st = .ok out := by simpa [hctx] using hx
            obtain ⟨rs, hslot, hout⟩ := pop_internal_transfer l hx'
            have hv0 := h.stack (st.spOff + (4 * bitCount l : Nat))
            rw [hslot] at hv0
            simp only [AbsVal.Sem] at hv0
            obtain ⟨⟨ret, hret, hr₁⟩, -⟩ := hv0
            have hmember : (Tgt.pt ret none, { loadStackRegs st.stk st.spOff (listRegs l) st with
                spOff := st.spOff + (4 * (bitCount l + 1) : Nat) }) ∈ out.succs := by
              rw [hout]
              exact List.mem_map.2 ⟨ret, hret, rfl⟩
            obtain ⟨blk, hfind, -, -⟩ := succFailure_target hsf hmember
            have hev := pc_even p.base ret hbase (findBlk_aligned ha hfind)
            right
            refine ⟨ret, mem_succOffs_pt hf' hmember, ?_⟩
            have ha' : s.sp + BitVec.ofNat 32 (4 * bitCount l) =
                p.sp0 + BitVec.ofInt 32 (st.spOff + (4 * bitCount l : Nat)) := by
              rw [hsp, sp_add_ofInt]
            rw [ha', hr₁, clear_thumb_bit _ hev]
        · cases hex
    | bx =>
      unfold xfer at hx
      split at hx <;> simp [xferCore] at hx
    | _ => simp [fallInstr] at hf

end M0Crypto.Release.ConstantTime
