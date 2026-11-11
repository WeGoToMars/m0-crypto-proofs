import M0Crypto.Release.ConstantTime.SpSound

/-! Relational stack stores for register-save instructions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb

set_option maxHeartbeats 2000000 in
/-- A successful push transfer identifies its stored registers, stack range,
and fall-through abstract state. -/
theorem push_transfer {env : Env} {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out}
    (l : BitVec 8) (lr : Bool) (hx : xfer env off ctx (.push l lr) st = .ok out) :
    let rs := regsOf l ++ (if lr then [14] else [])
    let base := st.spOff - (4 * rs.length : Nat)
    env.win.covers base st.spOff = true ∧
    out = ⟨[(.pt (off + (Instr.push l lr).size) ctx,
      { st with spOff := base, stk := storeStackWords base (rs.map st.get) st.stk })], []⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, Bool.true_and, decide_eq_true hb.2.1, xferCore] at hx
  dsimp only
  by_cases hwin : env.win.covers
      (st.spOff - (4 * (regsOf l ++ if lr then [14] else []).length : Nat)) st.spOff = true
  · simp only [hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx
    constructor
    · exact hwin
    · have hf : ((regsOf l ++ if lr then [14] else []).zip
          (List.range (regsOf l ++ if lr then [14] else []).length)).foldl
          (fun s (r, k) => stkSet s
            (st.spOff - (4 * (regsOf l ++ if lr then [14] else []).length : Nat) + (4 * k : Nat))
            (st.get r)) st.stk =
          storeStackWords (st.spOff - (4 * (regsOf l ++ if lr then [14] else []).length : Nat))
            ((regsOf l ++ if lr then [14] else []).map st.get) st.stk := by
        simpa only [List.range_eq_range', Nat.mul_zero, Int.natCast_zero, Int.add_zero] using storeStackWords_fold st.get
          (st.spOff - (4 * (regsOf l ++ if lr then [14] else []).length : Nat))
          (regsOf l ++ if lr then [14] else []) 0 st.stk
      rw [hf] at hx
      simpa [fall] using hx.symm
  · have hf : env.win.covers
        (st.spOff - (4 * (regsOf l ++ if lr then [14] else []).length : Nat)) st.spOff = false := by
      cases h : env.win.covers _ _ <;> simp_all
    simp only [hf, Bool.not_false, ↓reduceIte, reduceCtorEq] at hx

/-- Every word in a covered stack interval lies in that interval. -/
theorem covered_stack_words (w : StackWindow) (base : Int) (n : Nat)
    (hwin : w.covers base (base + (4 * n : Nat)) = true) :
    ∀ k, k < n →
      w.covers (base + (4 * k : Nat)) (base + (4 * k : Nat) + 4) = true := by
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  intro k hk
  constructor <;> omega

/-- Every register in a push list is a tracked architectural register. -/
theorem push_reg_index (l : BitVec 8) (lr : Bool) (r : Nat)
    (hr : r ∈ regsOf l ++ (if lr then [14] else [])) : regIndexOk r := by
  simp only [List.mem_append, regsOf, List.mem_map] at hr
  rcases hr with ⟨x, _, rfl⟩ | hr
  · constructor <;> have := x.isLt <;> simp [numRegs] <;> omega
  · cases lr <;> simp_all [regIndexOk, numRegs]

/-- The analyzer's register numbering agrees with the machine's saved values. -/
theorem push_reg_values (l : BitVec 8) (lr : Bool) (s : State) :
    (regsOf l ++ (if lr then [14] else [])).map (regAt s) =
      (listRegs l).map (s.reg ·) ++ (if lr then [s.regs 14] else []) := by
  have hlow : ∀ r : M0Crypto.Armv6M.LowReg, regAt s r.val = s.reg r := by
    intro r
    rw [regAt_eq_regs s r.val (by have := r.isLt; omega)]
    simp [State.reg, M0Crypto.Armv6M.LowReg.toReg]
  have hlr : regAt s 14 = s.regs 14 := by
    simpa using regAt_eq_regs s 14 (by decide)
  cases lr <;> simp [regsOf, List.map_map, Function.comp_def, hlow, hlr]

/-- The words saved by a checked push preserve the tracked stack relation and
the code bytes in both executions. -/
theorem push_stack_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out} {s₁ s₂ : State}
    (l : BitVec 8) (lr : Bool) (hx : xfer env off ctx (.push l lr) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hslots : st.stk.slotsOk env.win) (halign : st.spOff % 4 = 0)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above)) :
    let rs := regsOf l ++ (if lr then [14] else [])
    let base := st.spOff - (4 * rs.length : Nat)
    let m₁ := storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 base) (rs.map (regAt s₁))
    let m₂ := storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 base) (rs.map (regAt s₂))
    StkSem p (storeStackWords base (rs.map st.get) st.stk) m₁ m₂ ∧
      CodeAt m₁ p.base bytes ∧ CodeAt m₂ p.base bytes := by
  let rs := regsOf l ++ (if lr then [14] else [])
  let base : Int := st.spOff - (4 * rs.length : Nat)
  let values := rs.map fun r => (st.get r, regAt s₁ r, regAt s₂ r)
  have hwin := (push_transfer l lr hx).1
  change env.win.covers base st.spOff = true at hwin
  have hwinbase : env.win.covers base (base + (4 * rs.length : Nat)) = true := by
    simpa [base] using hwin
  have hall := covered_stack_words env.win base rs.length hwinbase
  have halign' : base % 4 = 0 := by simp only [base]; omega
  have hvals : ∀ v ∈ values, AbsVal.Sem p v.1 v.2.1 v.2.2 := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    have hr' := push_reg_index l lr r hr
    exact h.regs r hr'.1 hr'.2
  have hwinvals : ∀ k, k < values.length →
      env.win.covers (base + (4 * k : Nat)) (base + (4 * k : Nat) + 4) = true := by
    simpa [values] using hall
  have hs := storeStackWords_sound env.win base values st.stk s₁.mem s₂.mem
    hwidth hslots halign' hwinvals hvals h.stack
  have hc₁ := codeAt_stack_storeWords env.win base (rs.map (regAt s₁)) h.code₁ hdisj
    (by simpa using hall)
  have hc₂ := codeAt_stack_storeWords env.win base (rs.map (regAt s₂)) h.code₂ hdisj
    (by simpa using hall)
  simpa [rs, base, values, List.map_map, Function.comp_def] using And.intro hs (And.intro hc₁ hc₂)

/-- Executing a checked push preserves the paired abstract state. -/
theorem push_exec_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out} {s₁ s₂ : State}
    (l : BitVec 8) (lr : Bool) (hx : xfer env off ctx (.push l lr) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hslots : st.stk.slotsOk env.win) (halign : st.spOff % 4 = 0)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above)) :
    let rs := regsOf l ++ (if lr then [14] else [])
    let base := st.spOff - (4 * rs.length : Nat)
    ∃ u₁ u₂, (Instr.push l lr).exec s₁ = .ok u₁ ∧
      (Instr.push l lr).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.push l lr).size)
        { st with spOff := base, stk := storeStackWords base (rs.map st.get) st.stk } u₁ u₂ := by
  let rs := regsOf l ++ (if lr then [14] else [])
  let base : Int := st.spOff - (4 * rs.length : Nat)
  let stk := storeStackWords base (rs.map st.get) st.stk
  let m₁ := storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 base) (rs.map (regAt s₁))
  let m₂ := storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 base) (rs.map (regAt s₂))
  have ⟨hs, hc₁, hc₂⟩ := push_stack_sound l lr hx h hwidth hslots halign hdisj
  change StkSem p stk m₁ m₂ at hs
  change CodeAt m₁ p.base bytes at hc₁
  change CodeAt m₂ p.base bytes at hc₂
  have hm : LowEq p bytes off {st with stk := stk} {s₁ with mem := m₁} {s₂ with mem := m₂} := by
    rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, _, hrel,
      hlnk, hsize, _, _⟩
    exact ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, hs, hrel,
      hlnk, hsize, hc₁, hc₂⟩
  have hidx' : ({st with stk := stk} : AbsState).indicesOk := by simpa [AbsState.indicesOk] using hidx
  have hn := (hm.withPC hidx' (next := off + (Instr.push l lr).size)).withSP hidx' base
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have hlen : rs.length = bitCount l + lr.toNat := by cases lr <;> simp [rs, regsOf, bitCount]
  have haddr : p.sp0 + BitVec.ofInt 32 base =
      (p.sp0 + BitVec.ofInt 32 st.spOff) - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat)) := by
    simp only [base, hlen, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.ofInt_natCast, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have hm₁ : m₁ = storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 base)
      ((listRegs l).map (s₁.reg ·) ++ (if lr then [s₁.regs 14] else [])) := by
    dsimp only [m₁, rs]
    rw [push_reg_values]
  have hm₂ : m₂ = storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 base)
      ((listRegs l).map (s₂.reg ·) ++ (if lr then [s₂.regs 14] else [])) := by
    dsimp only [m₂, rs]
    rw [push_reg_values]
  let u₁ := ({s₁ with mem := m₁}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.push l lr).size))).setReg 13 (p.sp0 + BitVec.ofInt 32 base)
  let u₂ := ({s₂ with mem := m₂}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.push l lr).size))).setReg 13 (p.sp0 + BitVec.ofInt 32 base)
  refine ⟨u₁, u₂, ?_, ?_, ?_⟩
  · simp [Instr.exec, h.pc, hsp₁, ← haddr, u₁, hm₁, State.setReg, BitVec.ofNat_add, BitVec.add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, hsp₂, ← haddr, u₂, hm₂, State.setReg, BitVec.ofNat_add, BitVec.add_assoc]
  · simpa [u₁, u₂, rs, base, stk] using hn

/-- A checked push advances related executions together, or they encounter
the same alignment fault. -/
theorem certPoint_push_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (l : BitVec 8) (lr : Bool)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.push l lr :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨halign, htracked⟩ := (AbsState.stackCheck_iff env.win st).mp (certPoint_stackCheck hslots hm hp)
  have ⟨_, hout⟩ := push_transfer l lr hx
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have ⟨u₁, u₂, he₁, he₂, hnext⟩ := push_exec_sound l lr hx hidx h hwidth htracked halign hdisj
  have hsp₁ : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  have hsp₂ : s₂.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by
    simpa [State.sp, h.sp_eq] using h.sp
  have hacc : (Instr.push l lr).accesses s₁ = (Instr.push l lr).accesses s₂ := by
    simp [Instr.accesses, hsp₁, hsp₂]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.push l lr).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.push l lr).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.push l lr) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.push l lr) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.push l lr) hdecode hlen
    have hd₂ := decode_at hc₂ off (.push l lr) hdecode hlen
    have hal₂ : ((Instr.push l lr).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]

end M0Crypto.Release.ConstantTime
