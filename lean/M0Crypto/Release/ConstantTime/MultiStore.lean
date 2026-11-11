import M0Crypto.Release.ConstantTime.MultiLoad
import M0Crypto.Release.ConstantTime.PushSound
import M0Crypto.Release.ConstantTime.StackForgetFrame
import M0Crypto.Release.ConstantTime.AccessBuffer

/-! Relational execution of multiple-register stores. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word Mem)
open M0Crypto.Thumb

/-- A sequence of word stores changes only bytes in its contiguous footprint. -/
theorem storeWords_frame (m : Mem) (a : Word) (vs : List Word) (q : Word)
    (h : ∀ j, j < 4 * vs.length → q ≠ a + BitVec.ofNat 32 j) :
    storeWords m a vs q = m q := by
  apply storeWords_other
  intro i k hi hk
  have hh := h (4 * i + k) (by omega)
  simpa [ofNat_add_assoc] using hh

/-- A multiword store disjoint from the artifact preserves the artifact. -/
theorem buffer_storeWords_code {m : Mem} {base a : Word} {bytes : List (BitVec 8)}
    (vs : List Word) (hc : CodeAt m base bytes)
    (hd : M0Crypto.Release.Frame.Disj base bytes.length a (4 * vs.length)) :
    CodeAt (storeWords m a vs) base bytes := by
  intro i hi
  rw [storeWords_frame m a vs _ (by
    intro j hj
    exact M0Crypto.Release.Frame.ne_of_disj hd.1 hd.2.1 hd.2.2 hi hj)]
  exact hc i hi

/-- A multiword buffer store disjoint from the stack preserves every tracked
stack word, even when the two executions store different values. -/
theorem buffer_storeWords_stack {p : Params} {s : Stk} {m₁ m₂ : Mem} {a : Word}
    (w : StackWindow) (vs₁ vs₂ : List Word) (hlen : vs₁.length = vs₂.length)
    (hslots : s.slotsOk w) (hs : StkSem p s m₁ m₂)
    (hd : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 w.below)
      (w.below + w.above) a (4 * vs₁.length)) :
    StkSem p s (storeWords m₁ a vs₁) (storeWords m₂ a vs₂) := by
  intro o
  cases hp : (stkGet s o).pub with
  | false =>
    have hv : stkGet s o = .hi := by cases hv : stkGet s o <;> simp_all [AbsVal.pub]
    simp [hv, AbsVal.Sem]
  | true =>
    obtain ⟨v, hv⟩ := stkGet_public_mem s o hp
    have ⟨_, ho⟩ := hslots (o, v) hv
    have ho' := ho
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at ho'
    have ha := stack_offset_rebase p.sp0 w.below o ho'.1
    have hb (i : Nat) (hi : i < 4) : ∀ j, j < 4 * vs₁.length →
        p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 j := by
      intro j hj
      rw [ha, ofNat_add_assoc]
      apply M0Crypto.Release.Frame.ne_of_disj hd.1 hd.2.1 hd.2.2 _ hj
      have hcast : (((o + (w.below : Int)).toNat : Nat) : Int) = o + (w.below : Int) :=
        Int.toNat_of_nonneg (by omega)
      omega
    have hread (m : Mem) (vs : List Word) (hlen' : vs.length = vs₁.length) :
        M0Crypto.Armv6M.read32 (storeWords m a vs) (p.sp0 + BitVec.ofInt 32 o) =
          M0Crypto.Armv6M.read32 m (p.sp0 + BitVec.ofInt 32 o) := by
      apply M0Crypto.Release.Frame.read32_congr
      intro i hi
      apply storeWords_frame
      simpa [hlen'] using hb i hi
    rw [hread m₁ vs₁ rfl, hread m₂ vs₂ hlen.symm]
    exact hs o

/-- Storing a sequence at any offset in the checked interval preserves all
stack facts outside that interval after the abstract stack forgets it. -/
theorem stkForget_storeWords_sem {p : Params} {s : Stk} {lo hi t : Int}
    {m₁ m₂ : Mem} (w : StackWindow) (vs₁ vs₂ : List Word)
    (hlen : vs₁.length = vs₂.length)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : s.slotsOk w)
    (hwin : w.covers t (t + (4 * vs₁.length : Nat)) = true)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (hs : StkSem p s m₁ m₂) :
    StkSem p (stkForget s lo (hi + (4 * vs₁.length : Nat)))
      (storeWords m₁ (p.sp0 + BitVec.ofInt 32 t) vs₁)
      (storeWords m₂ (p.sp0 + BitVec.ofInt 32 t) vs₂) := by
  apply stkForget_write_frame (width := 4 * vs₁.length) w hwidth hslots hwin hlo hhi hs
  intro a ha
  constructor
  · exact storeWords_frame m₁ _ vs₁ a ha
  · apply storeWords_frame m₂ _ vs₂ a
    simpa [hlen] using ha

/-- A multiple store at a stack-relative address preserves tracked stack
semantics: exact aligned addresses retain values; other intervals are forgotten. -/
theorem stm_stack_memory_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State}
    (w : StackWindow) (l : BitVec 8) (lo hi t : Int)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : st.stk.slotsOk w)
    (hcover : w.covers lo (hi + (4 * (regsOf l).length : Nat)) = true)
    (hlo : lo ≤ t) (hhi : t ≤ hi) (h : LowEq p bytes off st s₁ s₂) :
    let rs := regsOf l
    let stk := if lo == hi && lo % 4 == 0 then
      storeStackWords lo (rs.map st.get) st.stk else
      stkForget st.stk lo (hi + (4 * rs.length : Nat))
    StkSem p stk
      (storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 t) (rs.map (regAt s₁)))
      (storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 t) (rs.map (regAt s₂))) := by
  let rs := regsOf l
  let values := rs.map fun r => (st.get r, regAt s₁ r, regAt s₂ r)
  change w.covers lo (hi + (4 * rs.length : Nat)) = true at hcover
  have hcov : w.covers t (t + (4 * rs.length : Nat)) = true := by
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hcover ⊢
    omega
  dsimp only
  split
  · rename_i hprecise
    simp only [Bool.and_eq_true, beq_iff_eq] at hprecise
    obtain ⟨heq, halign⟩ := hprecise
    have ht : t = lo := by omega
    subst t
    have hwords := covered_stack_words w lo rs.length (by simpa [heq] using hcover)
    have hvals : ∀ v ∈ values, AbsVal.Sem p v.1 v.2.1 v.2.2 := by
      intro v hv
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
      have hr' := push_reg_index l false r (by simpa using hr)
      exact h.regs r hr'.1 hr'.2
    have hs := storeStackWords_sound w lo values st.stk s₁.mem s₂.mem hwidth hslots halign
      (by simpa [values] using hwords) hvals h.stack
    simpa [rs, values, List.map_map, Function.comp_def] using hs
  · have hs := stkForget_storeWords_sem w (rs.map (regAt s₁)) (rs.map (regAt s₂))
      (by simp) hwidth hslots (by simpa [rs] using hcov) hlo hhi h.stack
    simpa [rs] using hs

/-- Abstract stack contents after a checked multiple store. -/
def stmStack (st : AbsState) (l : BitVec 8) (lo hi : Int) : Stk :=
  if lo == hi && lo % 4 == 0 then
    storeStackWords lo ((regsOf l).map st.get) st.stk
  else stkForget st.stk lo (hi + (4 * (regsOf l).length : Nat))

/-- A successful stack multiple-store transfer exposes its window check and
its precise abstract successor. -/
theorem stm_stack_transfer {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8) (lo hi : Int)
    (hx : xfer env off ctx (.stm n l) st = .ok out)
    (hbase : st.get n.val = .sp lo hi) :
    env.win.covers lo (hi + (4 * (regsOf l).length : Nat)) = true ∧
    out = ⟨[(.pt (off + (Instr.stm n l).size) ctx,
      { st with stk := stmStack st l lo hi } |>.set n.val
        ((st.get n.val).addK (4 * bitCount l)))], []⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
    xferCore, hbase] at hx
  split at hx
  · contradiction
  · rename_i hwin
    have hwin' : env.win.covers lo (hi + (4 * (regsOf l).length : Nat)) = true := by
      cases hc : env.win.covers lo (hi + (4 * (regsOf l).length : Nat)) <;> simp_all
    refine ⟨hwin', ?_⟩
    have hf := storeStackWords_fold st.get lo (regsOf l) 0 st.stk
    simp only [Nat.mul_zero, Int.natCast_zero, Int.add_zero] at hf
    rw [List.range_eq_range', hf] at hx
    simpa [fall, stmStack, hbase, regsOf, bitCount, Instr.size] using hx.symm

/-- A successful non-stack multiple store records a buffer write and the base
register's writeback. -/
theorem stm_buffer_transfer {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8)
    (hx : xfer env off ctx (.stm n l) st = .ok out)
    (hnotsp : ∀ lo hi, st.get n.val ≠ .sp lo hi) :
    out = ⟨[(.pt (off + (Instr.stm n l).size) ctx,
      st.set n.val ((st.get n.val).addK (4 * bitCount l)))], [.store]⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
  cases ha : st.get n.val <;> simp only [ha] at hx
  all_goals try contradiction
  all_goals try { exfalso; exact hnotsp _ _ ha }
  all_goals simpa [bitCount, regsOf, Instr.size] using hx.symm

/-- Public-buffer multiple stores preserve the paired state when their full
write footprint is disjoint from the code and tracked stack. -/
theorem stm_buffer_exec_sound {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {st : AbsState} {s₁ s₂ : State}
    (w : StackWindow) (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hpub : (st.get n.val).pub = true) (hslots : st.stk.slotsOk w)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length (s₁.reg n) (4 * bitCount l))
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 w.below)
      (w.below + w.above) (s₁.reg n) (4 * bitCount l)) :
    ∃ u₁ u₂, (Instr.stm n l).exec s₁ = .ok u₁ ∧
      (Instr.stm n l).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.stm n l).size)
        (st.set n.val ((st.get n.val).addK (4 * bitCount l))) u₁ u₂ := by
  have hd : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hv := lowReg_sem n h
  have heq := AbsVal.sem_public hv hpub
  let vs₁ := (listRegs l).map (s₁.reg ·)
  let vs₂ := (listRegs l).map (s₂.reg ·)
  let m₁ := storeWords s₁.mem (s₁.reg n) vs₁
  let m₂ := storeWords s₂.mem (s₁.reg n) vs₂
  have hlen : vs₁.length = vs₂.length := by simp [vs₁, vs₂]
  have hs : StkSem p st.stk m₁ m₂ := by
    apply buffer_storeWords_stack w vs₁ vs₂ hlen hslots h.stack
    simpa [vs₁, bitCount] using hstack
  have hc₁ : CodeAt m₁ p.base bytes := by
    apply buffer_storeWords_code vs₁ h.code₁
    simpa [vs₁, bitCount] using hcode
  have hc₂ : CodeAt m₂ p.base bytes := by
    apply buffer_storeWords_code vs₂ h.code₂
    simpa [vs₂, bitCount] using hcode
  have hm : LowEq p bytes off st {s₁ with mem := m₁} {s₂ with mem := m₂} := by
    rcases h with ⟨a,b,c,d,e,f,g,_,i,j,k,_,_⟩
    exact ⟨a,b,c,d,e,f,g,hs,i,j,k,hc₁,hc₂⟩
  have hadd := AbsVal.addK_sound (4 * bitCount l) hv
  have hn := paired_setReg_sound hd hidx (hm.withPC hidx (next := off + (Instr.stm n l).size)) hadd
  have hreg : (⟨n.val, by have := hd.1; simp [numRegs] at this; omega⟩ :
      M0Crypto.Armv6M.Reg) = n.toReg := by apply Fin.ext; rfl
  rw [hreg] at hn
  refine ⟨({s₁ with mem := m₁}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.stm n l).size))).setReg
      n.toReg (s₁.reg n + BitVec.ofNat 32 (4 * bitCount l)),
    ({s₂ with mem := m₂}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.stm n l).size))).setReg
      n.toReg (s₂.reg n + BitVec.ofNat 32 (4 * bitCount l)), ?_, ?_, hn⟩
  · simp [Instr.exec, h.pc, m₁, vs₁, State.setReg, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, m₂, vs₂, heq, State.setReg, ofNat_add_assoc]

/-- Executing a stack-relative multiple store preserves the paired state when
the tracked stack window is narrow and disjoint from the code. -/
theorem stm_stack_exec_sound {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out} {s₁ s₂ : State}
    (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8) (lo hi : Int)
    (hx : xfer env off ctx (.stm n l) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hbase : st.get n.val = .sp lo hi)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hslots : st.stk.slotsOk env.win)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above)) :
    ∃ u₁ u₂, (Instr.stm n l).exec s₁ = .ok u₁ ∧
      (Instr.stm n l).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.stm n l).size)
        ({ st with stk := stmStack st l lo hi } |>.set n.val
          ((st.get n.val).addK (4 * bitCount l))) u₁ u₂ := by
  have hd : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hv := lowReg_sem n h
  have hv' := hv
  rw [hbase] at hv'
  obtain ⟨t, hlo, hhi, haddr₁, haddr₂⟩ := hv'
  have haddr₂' : s₂.reg n = p.sp0 + BitVec.ofInt 32 t := haddr₂.trans haddr₁
  have hcov := (stm_stack_transfer n l lo hi hx hbase).1
  let rs := regsOf l
  let m₁ := storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 t) (rs.map (regAt s₁))
  let m₂ := storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 t) (rs.map (regAt s₂))
  have hs : StkSem p (stmStack st l lo hi) m₁ m₂ := by
    simpa [stmStack, rs, m₁, m₂] using stm_stack_memory_sound env.win l lo hi t
      hwidth hslots hcov hlo hhi h
  have hwin : env.win.covers t (t + (4 * rs.length : Nat)) = true := by
    change env.win.covers lo (hi + (4 * rs.length : Nat)) = true at hcov
    simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hcov ⊢
    omega
  have hall := covered_stack_words env.win t rs.length hwin
  have hc₁ : CodeAt m₁ p.base bytes := by
    apply codeAt_stack_storeWords env.win t _ h.code₁ hdisj
    simpa [rs] using hall
  have hc₂ : CodeAt m₂ p.base bytes := by
    apply codeAt_stack_storeWords env.win t _ h.code₂ hdisj
    simpa [rs] using hall
  have hm : LowEq p bytes off { st with stk := stmStack st l lo hi }
      {s₁ with mem := m₁} {s₂ with mem := m₂} := by
    rcases h with ⟨a,b,c,d,e,f,g,_,i,j,k,_,_⟩
    exact ⟨a,b,c,d,e,f,g,hs,i,j,k,hc₁,hc₂⟩
  have hidx' : ({ st with stk := stmStack st l lo hi } : AbsState).indicesOk := by
    simpa [AbsState.indicesOk] using hidx
  have hadd := AbsVal.addK_sound (4 * bitCount l) hv
  have hn := paired_setReg_sound hd hidx' (hm.withPC hidx' (next := off + (Instr.stm n l).size)) hadd
  have hreg : (⟨n.val, by have := hd.1; simp [numRegs] at this; omega⟩ :
      M0Crypto.Armv6M.Reg) = n.toReg := by apply Fin.ext; rfl
  rw [hreg] at hn
  have hm₁ : m₁ = storeWords s₁.mem (p.sp0 + BitVec.ofInt 32 t) ((listRegs l).map (s₁.reg ·)) := by
    dsimp [m₁, rs]
    have hv : (regsOf l).map (regAt s₁) = (listRegs l).map (s₁.reg ·) := by
      simpa using push_reg_values l false s₁
    rw [hv]
  have hm₂ : m₂ = storeWords s₂.mem (p.sp0 + BitVec.ofInt 32 t) ((listRegs l).map (s₂.reg ·)) := by
    dsimp [m₂, rs]
    have hv : (regsOf l).map (regAt s₂) = (listRegs l).map (s₂.reg ·) := by
      simpa using push_reg_values l false s₂
    rw [hv]
  refine ⟨({s₁ with mem := m₁}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.stm n l).size))).setReg
      n.toReg (s₁.reg n + BitVec.ofNat 32 (4 * bitCount l)),
    ({s₂ with mem := m₂}.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.stm n l).size))).setReg
      n.toReg (s₂.reg n + BitVec.ofNat 32 (4 * bitCount l)), ?_, ?_, hn⟩
  · simp [Instr.exec, h.pc, haddr₁, hm₁, State.setReg, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, haddr₂', hm₂, State.setReg, ofNat_add_assoc]

/-- A checked stack multiple store advances paired executions or faults equally. -/
theorem certPoint_stm_stack_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8) (lo upper : Int)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.stm n l :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hbase : st.get n.val = .sp lo upper)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have htracked := ((AbsState.stackCheck_iff env.win st).mp (certPoint_stackCheck hslots hm hp)).2
  have ⟨_, hout⟩ := stm_stack_transfer n l lo upper hx hbase
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
    stm_stack_exec_sound n l lo upper hx hidx h hbase hwidth htracked hdisj
  have hacc := stm_accesses_eq n l hx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.stm n l).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.stm n l).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.stm n l) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.stm n l) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.stm n l) hdecode hlen
    have hd₂ := decode_at hc₂ off (.stm n l) hdecode hlen
    have hal₂ : ((Instr.stm n l).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]

/-- A checked non-stack multiple store advances paired executions when its
concrete footprint is separated from code and the stack window. -/
theorem certPoint_stm_buffer_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.stm n l :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hnotsp : ∀ lo upper, st.get n.val ≠ .sp lo upper)
    (hcode : M0Crypto.Release.Frame.Disj p.base bytes.length (s₁.reg n) (4 * bitCount l))
    (hstack : M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
      (env.win.below + env.win.above) (s₁.reg n) (4 * bitCount l))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have htracked := ((AbsState.stackCheck_iff env.win st).mp (certPoint_stackCheck hslots hm hp)).2
  have hout := stm_buffer_transfer n l hx hnotsp
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hpub := stm_base_public n l hx
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ :=
    stm_buffer_exec_sound env.win n l hidx h hpub htracked hcode hstack
  have hacc := stm_accesses_eq n l hx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.stm n l).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.stm n l).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.stm n l) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.stm n l) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.stm n l) hdecode hlen
    have hd₂ := decode_at hc₂ off (.stm n l) hdecode hlen
    have hal₂ : ((Instr.stm n l).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]

/-- Checked multiple stores preserve paired execution under stack separation
and, for a non-stack base, separation of the concrete output footprint. -/
theorem certPoint_stm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : M0Crypto.Armv6M.LowReg) (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hslots : certSlotsCheck env cert = true) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (.stm n l :: is)) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above))
    (hbuffer : (∀ lo upper, st.get n.val ≠ .sp lo upper) →
      M0Crypto.Release.Frame.Disj p.base bytes.length (s₁.reg n) (4 * bitCount l) ∧
      M0Crypto.Release.Frame.Disj (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (s₁.reg n) (4 * bitCount l))
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  by_cases hs : ∃ lo upper, st.get n.val = .sp lo upper
  · obtain ⟨lo, upper, hbase⟩ := hs
    exact certPoint_stm_stack_paired n l lo upper hc hi hslots hm hp h hbase hwidth hdisj heven
  · have hn : ∀ lo upper, st.get n.val ≠ .sp lo upper := by
      intro lo upper hbase
      exact hs ⟨lo, upper, hbase⟩
    obtain ⟨hcode, hstack⟩ := hbuffer hn
    exact certPoint_stm_buffer_paired n l hc hi hslots hm hp h hn hcode hstack heven

end M0Crypto.Release.ConstantTime
