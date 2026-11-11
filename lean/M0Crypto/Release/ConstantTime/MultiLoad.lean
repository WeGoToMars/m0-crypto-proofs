import M0Crypto.Release.ConstantTime.MultiAccess
import M0Crypto.Release.ConstantTime.LoadRegsSound

/-! Relational execution of multiple-register loads. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word LowReg)
open M0Crypto.Thumb

/-- Abstract loads whose contents are not known to be public. -/
def loadSecretRegs : List LowReg → AbsState → AbsState
  | [], st => st
  | r :: rs, st => loadSecretRegs rs (st.set r.val .hi)

/-- A sequence of loads at the same addresses in both runs preserves the
paired state when each loaded register receives the secret label. -/
theorem loadSecretRegs_sound {p : Params} {bytes : List (BitVec 8)} {pc : Nat}
    (a : Word) (rs : List LowReg) (st : AbsState) (s₁ s₂ : State)
    (hidx : st.indicesOk) (h : LowEq p bytes pc st s₁ s₂) :
    LowEq p bytes pc (loadSecretRegs rs st)
      (loadRegs s₁ a (rs.map LowReg.toReg))
      (loadRegs s₂ a (rs.map LowReg.toReg)) := by
  induction rs generalizing a st s₁ s₂ with
  | nil => exact h
  | cons r rs ih =>
    have hr : regIndexOk r.val := by
      constructor <;> have := r.isLt <;> simp [numRegs] <;> omega
    have hv : AbsVal.Sem p .hi (M0Crypto.Armv6M.read32 s₁.mem a)
        (M0Crypto.Armv6M.read32 s₂.mem a) := by trivial
    have hw := paired_setReg_sound hr hidx h hv
    have hreg : (⟨r.val, by have := hr.1; simp [numRegs] at this; omega⟩ :
        M0Crypto.Armv6M.Reg) = r.toReg := by apply Fin.ext; rfl
    rw [hreg] at hw
    simpa [loadSecretRegs, loadRegs] using
      ih (a + 4#32) (st.set r.val .hi) _ _ (AbsState.indicesOk_set hidx) hw

/-- The executable analyzer fold agrees with the sequential definition. -/
theorem loadSecretRegs_fold (rs : List LowReg) (st : AbsState) :
    (rs.map (fun r => r.val)).foldl (fun s r => s.set r .hi) st = loadSecretRegs rs st := by
  induction rs generalizing st with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, List.foldl_cons, loadSecretRegs, ih]

/-- The same fold remains valid when the analyzer pairs each register with an
unused word index. -/
theorem loadSecretRegs_zip_fold (rs : List LowReg) (k : Nat) (st : AbsState) :
    ((rs.map (fun r => r.val)).zip (List.range' k rs.length)).foldl
      (fun s (r, _) => s.set r .hi) st = loadSecretRegs rs st := by
  induction rs generalizing k st with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.zip_cons_cons,
      List.foldl_cons, loadSecretRegs, ih]

theorem loadSecretRegs_indices (rs : List LowReg) (st : AbsState) (h : st.indicesOk) :
    (loadSecretRegs rs st).indicesOk := by
  induction rs generalizing st with
  | nil => exact h
  | cons r rs ih => exact ih _ (AbsState.indicesOk_set h)

/-- The register-list membership test used by the analyzer matches the encoded
bit used by the instruction semantics. -/
theorem regsOf_contains (l : BitVec 8) (n : LowReg) :
    (regsOf l).contains n.val = l.getLsbD n.val := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  simp only [regsOf, List.mem_map, listRegs, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, ha, he⟩
    have : a = n := Fin.ext he
    subst a
    exact ha
  · intro h
    exact ⟨n, h, rfl⟩

/-- Loading unknown words and performing architectural writeback preserves the
paired state whenever the original base is public. -/
theorem ldm_secret_exec_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hpub : (st.get n.val).pub = true) :
    ∃ u₁ u₂, (Instr.ldm n l).exec s₁ = .ok u₁ ∧
      (Instr.ldm n l).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.ldm n l).size)
        (if l.getLsbD n.val then loadSecretRegs (listRegs l) st else
          (loadSecretRegs (listRegs l) st).set n.val ((st.get n.val).addK (4 * bitCount l))) u₁ u₂ := by
  have hd : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hv := lowReg_sem n h
  have heq := AbsVal.sem_public hv hpub
  have hpc := h.withPC hidx (next := off + (Instr.ldm n l).size)
  have hloads := loadSecretRegs_sound (s₁.reg n) (listRegs l) st _ _ hidx hpc
  have hloadidx := loadSecretRegs_indices (listRegs l) st hidx
  have hadd := AbsVal.addK_sound (4 * bitCount l) hv
  have hw := paired_setReg_sound hd hloadidx hloads hadd
  have hreg : (⟨n.val, by have := hd.1; simp [numRegs] at this; omega⟩ :
      M0Crypto.Armv6M.Reg) = n.toReg := by apply Fin.ext; rfl
  rw [hreg] at hw
  cases hbit : l.getLsbD n.val with
  | false =>
    have hbit' : l[n.val] = false := by simpa using hbit
    refine ⟨(loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
      (s₁.reg n) ((listRegs l).map LowReg.toReg)).setReg n.toReg
        (s₁.reg n + BitVec.ofNat 32 (4 * bitCount l)),
      (loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
        (s₁.reg n) ((listRegs l).map LowReg.toReg)).setReg n.toReg
        (s₂.reg n + BitVec.ofNat 32 (4 * bitCount l)), ?_, ?_, ?_⟩
    · simp [Instr.exec, h.pc, hbit', ofNat_add_assoc]
    · simp [Instr.exec, h.pc_eq.trans h.pc, hbit', heq, ofNat_add_assoc]
    · simpa [hbit, heq] using hw
  | true =>
    refine ⟨loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
      (s₁.reg n) ((listRegs l).map LowReg.toReg),
      loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
        (s₁.reg n) ((listRegs l).map LowReg.toReg), ?_, ?_, ?_⟩
    · simp [Instr.exec, h.pc, hbit, ofNat_add_assoc]
    · simp [Instr.exec, h.pc_eq.trans h.pc, hbit, heq, ofNat_add_assoc]
    · simpa [hbit, heq] using hloads

/-- For a non-stack base, the successful abstract multiple-load transfer marks
all loaded words secret and uses the instruction's writeback rule. -/
theorem ldm_secret_transfer {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : LowReg) (l : BitVec 8)
    (hx : xfer env off ctx (.ldm n l) st = .ok out)
    (hnotsp : ∀ a b, st.get n.val ≠ .sp a b) :
    out = ⟨[(.pt (off + (Instr.ldm n l).size) ctx,
      if l.getLsbD n.val then loadSecretRegs (listRegs l) st else
        (loadSecretRegs (listRegs l) st).set n.val ((st.get n.val).addK (4 * bitCount l)))], [.load]⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
  have hf : (regsOf l).foldl (fun s r => s.set r .hi) st = loadSecretRegs (listRegs l) st := by
    simpa [regsOf] using loadSecretRegs_fold (listRegs l) st
  cases ha : st.get n.val <;> simp only [ha] at hx
  all_goals try contradiction
  all_goals try { exfalso; exact hnotsp _ _ ha }
  all_goals rw [regsOf_contains, hf] at hx
  all_goals cases hbit : l.getLsbD n.val <;>
    simp_all [Instr.size, bitCount, regsOf]

/-- Multiple loads from an exact abstract stack offset preserve the tracked
values loaded from each slot, including architectural writeback. -/
theorem ldm_exact_stack_exec_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8) (base : Int)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hbase : st.get n.val = .sp base base) :
    ∃ u₁ u₂, (Instr.ldm n l).exec s₁ = .ok u₁ ∧
      (Instr.ldm n l).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.ldm n l).size)
        (if l.getLsbD n.val then loadStackRegs st.stk base (listRegs l) st else
          (loadStackRegs st.stk base (listRegs l) st).set n.val
            ((st.get n.val).addK (4 * bitCount l))) u₁ u₂ := by
  have hd : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hv := lowReg_sem n h
  have hv' := hv
  rw [hbase] at hv'
  obtain ⟨q, hqlo, hqhi, haddr₁, haddr₂⟩ := hv'
  have hq : q = base := by omega
  subst q
  have haddr₂' : s₂.reg n = p.sp0 + BitVec.ofInt 32 base := haddr₂.trans haddr₁
  have hpc := h.withPC hidx (next := off + (Instr.ldm n l).size)
  have hloads := loadStackRegs_sound st.stk base (listRegs l) st _ _ hidx rfl hpc
  have hloadidx := loadStackRegs_indices st.stk base (listRegs l) st hidx
  have hadd := AbsVal.addK_sound (4 * bitCount l) hv
  have hw := paired_setReg_sound hd hloadidx hloads hadd
  have hreg : (⟨n.val, by have := hd.1; simp [numRegs] at this; omega⟩ :
      M0Crypto.Armv6M.Reg) = n.toReg := by apply Fin.ext; rfl
  rw [hreg] at hw
  cases hbit : l.getLsbD n.val with
  | false =>
    have hbit' : l[n.val] = false := by simpa using hbit
    refine ⟨(loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
      (p.sp0 + BitVec.ofInt 32 base) ((listRegs l).map LowReg.toReg)).setReg n.toReg
        (s₁.reg n + BitVec.ofNat 32 (4 * bitCount l)),
      (loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
        (p.sp0 + BitVec.ofInt 32 base) ((listRegs l).map LowReg.toReg)).setReg n.toReg
        (s₂.reg n + BitVec.ofNat 32 (4 * bitCount l)), ?_, ?_, ?_⟩
    · simp [Instr.exec, h.pc, hbit', haddr₁, ofNat_add_assoc]
    · simp [Instr.exec, h.pc_eq.trans h.pc, hbit', haddr₂', ofNat_add_assoc]
    · simpa [hbit] using hw
  | true =>
    refine ⟨loadRegs (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
      (p.sp0 + BitVec.ofInt 32 base) ((listRegs l).map LowReg.toReg),
      loadRegs (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.ldm n l).size)))
        (p.sp0 + BitVec.ofInt 32 base) ((listRegs l).map LowReg.toReg), ?_, ?_, ?_⟩
    · simp [Instr.exec, h.pc, hbit, haddr₁, ofNat_add_assoc]
    · simp [Instr.exec, h.pc_eq.trans h.pc, hbit, haddr₂', ofNat_add_assoc]
    · simpa [hbit] using hloads

/-- A checked exact, word-aligned stack base uses the tracked stack slots. -/
theorem ldm_exact_stack_transfer {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : LowReg) (l : BitVec 8) (base : Int)
    (hx : xfer env off ctx (.ldm n l) st = .ok out)
    (hbase : st.get n.val = .sp base base) (halign : base % 4 = 0) :
    out = ⟨[(.pt (off + (Instr.ldm n l).size) ctx,
      if l.getLsbD n.val then loadStackRegs st.stk base (listRegs l) st else
        (loadStackRegs st.stk base (listRegs l) st).set n.val
          ((st.get n.val).addK (4 * bitCount l)))], []⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
    xferCore, hbase] at hx
  split at hx
  · contradiction
  · simp only [beq_self_eq_true, halign, Bool.and_self, ↓reduceIte] at hx
    rw [pop_load_fold, regsOf_contains] at hx
    cases hbit : l.getLsbD n.val <;>
      simp_all [fall, Instr.size, bitCount, regsOf]

/-- Non-exact stack bases conservatively label all loaded registers secret. -/
theorem ldm_imprecise_stack_transfer {env : Env} {off : Nat} {ctx : Option Nat}
    {st : AbsState} {out : Out} (n : LowReg) (l : BitVec 8) (lo hi : Int)
    (hx : xfer env off ctx (.ldm n l) st = .ok out)
    (hbase : st.get n.val = .sp lo hi)
    (himprecise : (lo == hi && lo % 4 == 0) = false) :
    out = ⟨[(.pt (off + (Instr.ldm n l).size) ctx,
      if l.getLsbD n.val then loadSecretRegs (listRegs l) st else
        (loadSecretRegs (listRegs l) st).set n.val
          ((st.get n.val).addK (4 * bitCount l)))], []⟩ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
    xferCore, hbase] at hx
  split at hx
  · contradiction
  · simp only [himprecise, Bool.false_eq_true, ↓reduceIte] at hx
    have hf : ((regsOf l).zip (List.range (regsOf l).length)).foldl
        (fun s (r, _) => s.set r .hi) st = loadSecretRegs (listRegs l) st := by
      simpa [regsOf, List.length_map, List.range_eq_range'] using
        loadSecretRegs_zip_fold (listRegs l) 0 st
    rw [hf, regsOf_contains] at hx
    cases hbit : l.getLsbD n.val <;>
      simp_all [fall, Instr.size, bitCount, regsOf]

/-- A checked multiple load with a non-stack base advances paired executions,
or faults identically on an unaligned access. -/
theorem certPoint_ldm_nonstack_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldm n l :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (hnotsp : ∀ a b, st.get n.val ≠ .sp a b)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hout := ldm_secret_transfer n l hx hnotsp
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hpub := ldm_base_public n l hx
  have ⟨u₁, u₂, he₁, he₂, hnext⟩ := ldm_secret_exec_sound n l hidx h hpub
  have hacc := ldm_accesses_eq n l hx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.ldm n l).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.ldm n l) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.ldm n l) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.ldm n l) hdecode hlen
    have hd₂ := decode_at hc₂ off (.ldm n l) hdecode hlen
    have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]


/-- A checked multiple load with an exact aligned stack base advances paired executions,
or faults identically on an unaligned access. -/
theorem certPoint_ldm_exact_stack_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8) (base : Int)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldm n l :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (hbase : st.get n.val = .sp base base) (halign : base % 4 = 0)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hout := ldm_exact_stack_transfer n l base hx hbase halign
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have ⟨u₁, u₂, he₁, he₂, hnext⟩ := ldm_exact_stack_exec_sound n l base hidx h hbase
  have hacc := ldm_accesses_eq n l hx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.ldm n l).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.ldm n l) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.ldm n l) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.ldm n l) hdecode hlen
    have hd₂ := decode_at hc₂ off (.ldm n l) hdecode hlen
    have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]


/-- A checked multiple load with an imprecise stack base advances paired executions,
or faults identically on an unaligned access. -/
theorem certPoint_ldm_imprecise_stack_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8) (lo upper : Int)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldm n l :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (hbase : st.get n.val = .sp lo upper)
    (himprecise : (lo == upper && lo % 4 == 0) = false)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hout := ldm_imprecise_stack_transfer n l lo upper hx hbase himprecise
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  have hpub := ldm_base_public n l hx
  have ⟨u₁, u₂, he₁, he₂, hnext⟩ := ldm_secret_exec_sound n l hidx h hpub
  have hacc := ldm_accesses_eq n l hx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.ldm n l).accesses s₁).all Access.aligned = true
  · have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    have hs₁ := step_of_instrAt hc₁ off (.ldm n l) hpc₁ heven hdecode hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.ldm n l) hpc₂ heven hdecode hlen hal₂ he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [h.pc_eq, hacc] using hs₂
  · have hd₁ := decode_at hc₁ off (.ldm n l) hdecode hlen
    have hd₂ := decode_at hc₂ off (.ldm n l) hdecode hlen
    have hal₂ : ((Instr.ldm n l).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    unfold PairedStep
    simp [step, hpc₁, hpc₂, heven', hd₁, hd₂, hal, hal₂]


/-- Every checked multiple load preserves paired execution, including stack,
non-stack, and identical alignment-fault cases. -/
theorem certPoint_ldm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : LowReg) (l : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.ldm n l :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  by_cases hs : ∃ lo upper, st.get n.val = .sp lo upper
  · obtain ⟨lo, upper, hbase⟩ := hs
    cases hp' : (lo == upper && lo % 4 == 0) with
    | false =>
      exact certPoint_ldm_imprecise_stack_paired n l lo upper hc hi hm hp h hbase hp' heven
    | true =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hp'
      obtain ⟨heq, halign⟩ := hp'
      subst upper
      exact certPoint_ldm_exact_stack_paired n l lo hc hi hm hp h hbase halign heven
  · apply certPoint_ldm_nonstack_paired n l hc hi hm hp h
    · intro lo upper hbase
      exact hs ⟨lo, upper, hbase⟩
    · exact heven

end M0Crypto.Release.ConstantTime
