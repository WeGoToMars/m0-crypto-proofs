import M0Crypto.Release.ConstantTime.InstructionSound

/-! Relational execution of carry-dependent data processing. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg Word addWithCarry)
open M0Crypto.Thumb

/-- Add-with-carry produces public output and flags exactly when both words
and the input carry are public. -/
theorem adc_values_sound {p : Params} {a b : AbsVal} {cf : AbsFlags}
    {x₁ x₂ y₁ y₂ : Word} {c₁ c₂ : Bool}
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) (hc : AbsFlags.Sem cf c₁ c₂) :
    let q := a.pub && b.pub && cf.pub
    let z₁ := addWithCarry x₁ y₁ c₁
    let z₂ := addWithCarry x₂ y₂ c₂
    AbsVal.Sem p (AbsVal.ofPub q) z₁.1 z₂.1 ∧
    AbsFlags.Sem (AbsFlags.ofPub q) z₁.1.msb z₂.1.msb ∧
    AbsFlags.Sem (AbsFlags.ofPub q) (z₁.1 == 0#32) (z₂.1 == 0#32) ∧
    AbsFlags.Sem (AbsFlags.ofPub q) z₁.2.1 z₂.2.1 ∧
    AbsFlags.Sem (AbsFlags.ofPub q) z₁.2.2 z₂.2.2 := by
  by_cases hq : a.pub && b.pub && cf.pub
  · have hpub := hq
    simp only [Bool.and_eq_true] at hpub
    obtain ⟨⟨hpa, hpb⟩, hpc⟩ := hpub
    have hx := AbsVal.sem_public ha hpa
    have hy := AbsVal.sem_public hb hpb
    have hcarry : c₁ = c₂ := by cases cf <;> simp_all [AbsFlags.Sem, AbsFlags.pub]
    subst x₂; subst y₂; subst c₂
    simp [hq, AbsVal.ofPub, AbsVal.Sem, AbsFlags.ofPub, AbsFlags.Sem]
  · simp [hq, AbsVal.ofPub, AbsVal.Sem, AbsFlags.ofPub, AbsFlags.Sem]

/-- Add-with-carry preserves the paired abstract state and all NZCV flags. -/
theorem adcs_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
    ∃ t₁ t₂, (Instr.dp .adcs d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .adcs d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .adcs d m).size)
        { st.set d.val (AbsVal.ofPub q) with fl := AFl.all (AbsFlags.ofPub q) } t₁ t₂ := by
  let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hca := h.flags.2.2.1
  have hs := adc_values_sound (by simpa [State.reg, LowReg.toReg] using ha)
    (by simpa [State.reg, LowReg.toReg] using hb) hca
  have hnext := h.withPC hidx (next := off + (Instr.dp .adcs d m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .adcs d m).size)))
      d.toReg (s₁.reg d) (s₁.reg m) s₁.c,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .adcs d m).size)))
      d.toReg (s₂.reg d) (s₂.reg m) s₂.c, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, AFl.all, State.setNZCV, State.setNZ, State.reg, LowReg.toReg, AbsVal.pub] using hs.2
    · intro c hc
      simp [AFl.all] at hc

/-- Checked add-with-carry advances paired certificate executions. -/
theorem certPoint_adcs_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .adcs d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .adcs d m).size) b.ctx,
      { st.set d.val (AbsVal.ofPub q) with fl := AFl.all (AbsFlags.ofPub q) })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, q] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := adcs_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .adcs d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .adcs d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

theorem notWord_pub (v : AbsVal) : (notWord v).pub = v.pub := by
  cases v with
  | num a b =>
    by_cases he : a = b
    · subst b
      by_cases hb : a < AbsVal.word <;> simp [notWord, AbsVal.exact?, AbsVal.pub, AbsVal.cst, hb]
    · simp [notWord, AbsVal.exact?, AbsVal.pub, AbsVal.ofPub, he]
  | hi | lo | sp _ _ | ret _ | lr0 => simp [notWord, AbsVal.exact?, AbsVal.pub, AbsVal.ofPub]

/-- Register complement preserves the relation and updates N/Z. -/
theorem mvns_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .mvns d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .mvns d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .mvns d m).size)
        { st.set d.val (notWord (st.get m.val)) with fl := setNZ st.fl (st.get m.val).pub } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hv := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hv
  have hval : AbsVal.Sem p (notWord (st.get m.val)) (~~~(s₁.reg m)) (~~~(s₂.reg m)) := by
    apply notWord_sound
    simpa [State.reg, LowReg.toReg] using hv
  have hnext := h.withPC hidx (next := off + (Instr.dp .mvns d m).size)
  have hw := paired_setReg_sound hd hidx hnext hval
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hval
  rw [notWord_pub] at hn
  simp only [AbsState.set, setNZ_touch] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, State.reg, LowReg.toReg, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, State.reg, LowReg.toReg, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked register complements advance paired certificate executions. -/
theorem certPoint_mvns_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .mvns d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .mvns d m).size) b.ctx,
      { st.set d.val (notWord (st.get m.val)) with fl := setNZ st.fl (st.get m.val).pub })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := mvns_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .mvns d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .mvns d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Reverse subtraction from zero preserves the relation and NZCV labels. -/
theorem rsbs_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .rsbs d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .rsbs d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .rsbs d m).size)
        { st.set d.val (AbsVal.ofPub (st.get m.val).pub) with
          fl := AFl.all (AbsFlags.ofPub (st.get m.val).pub) } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hv := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hv
  have hv' : AbsVal.Sem p (st.get m.val) (s₁.reg m) (s₂.reg m) := by
    simpa [State.reg, LowReg.toReg] using hv
  have hcst : AbsVal.Sem p (.cst 0) (0#32) (0#32) := by simp [AbsVal.Sem, AbsVal.cst]
  have hs := adc_values_sound (notWord_sound hv') hcst (show AbsFlags.Sem (.known true) true true by simp [AbsFlags.Sem])
  dsimp only at hs
  rw [notWord_pub] at hs
  simp only [AbsVal.cst, AbsVal.pub, AbsFlags.pub, Bool.and_true] at hs
  have hnext := h.withPC hidx (next := off + (Instr.dp .rsbs d m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .rsbs d m).size)))
      d.toReg (~~~(s₁.reg m)) 0 true,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .rsbs d m).size)))
      d.toReg (~~~(s₂.reg m)) 0 true, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, AFl.all, State.setNZCV, State.setNZ, State.reg, LowReg.toReg, AbsVal.pub] using hs.2
    · intro c hc
      simp [AFl.all] at hc

/-- Checked reverse subtraction advances paired certificate executions. -/
theorem certPoint_rsbs_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .rsbs d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .rsbs d m).size) b.ctx,
      { st.set d.val (AbsVal.ofPub (st.get m.val).pub) with
        fl := AFl.all (AbsFlags.ofPub (st.get m.val).pub) })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := rsbs_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .rsbs d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .rsbs d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Subtract-with-carry (`Rdn + NOT(Rm) + C`) preserves the paired abstract state and all NZCV flags. -/
theorem sbcs_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
    ∃ t₁ t₂, (Instr.dp .sbcs d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .sbcs d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .sbcs d m).size)
        { st.set d.val (AbsVal.ofPub q) with fl := AFl.all (AbsFlags.ofPub q) } t₁ t₂ := by
  let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hca := h.flags.2.2.1
  have hs := adc_values_sound (by simpa [State.reg, LowReg.toReg] using ha)
    (notWord_sound (by simpa [State.reg, LowReg.toReg] using hb)) hca
  dsimp only at hs
  rw [notWord_pub] at hs
  have hnext := h.withPC hidx (next := off + (Instr.dp .sbcs d m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .sbcs d m).size)))
      d.toReg (s₁.reg d) (~~~(s₁.reg m)) s₁.c,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .sbcs d m).size)))
      d.toReg (s₂.reg d) (~~~(s₂.reg m)) s₂.c, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, AFl.all, State.setNZCV, State.setNZ, State.reg, LowReg.toReg, AbsVal.pub] using hs.2
    · intro c hc
      simp [AFl.all] at hc

/-- Checked subtract-with-carry advances paired certificate executions. -/
theorem certPoint_sbcs_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .sbcs d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let q := (st.get d.val).pub && (st.get m.val).pub && st.fl.c.pub
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .sbcs d m).size) b.ctx,
      { st.set d.val (AbsVal.ofPub q) with fl := AFl.all (AbsFlags.ofPub q) })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, q] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := sbcs_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .sbcs d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .sbcs d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- A rotate result depends on the value and amount, while its carry may
also depend on the incoming carry when the amount is zero. -/
theorem ror_values_sound {p : Params} {a b : AbsVal} {cf : AbsFlags}
    {x₁ x₂ y₁ y₂ : Word} {c₁ c₂ : Bool}
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) (hc : AbsFlags.Sem cf c₁ c₂) :
    let pub := a.pub && b.pub
    let z₁ := M0Crypto.Armv6M.rorC x₁ (y₁.toNat % 256) c₁
    let z₂ := M0Crypto.Armv6M.rorC x₂ (y₂.toNat % 256) c₂
    AbsVal.Sem p (AbsVal.ofPub pub) z₁.1 z₂.1 ∧
      AbsFlags.Sem (AbsFlags.ofPub (pub && cf.pub)) z₁.2 z₂.2 := by
  by_cases hp : a.pub && b.pub
  · have hp' := hp
    simp only [Bool.and_eq_true] at hp'
    have hx := AbsVal.sem_public ha hp'.1
    have hy := AbsVal.sem_public hb hp'.2
    subst x₂; subst y₂
    constructor
    · by_cases hz : y₁.toNat % 256 = 0 <;>
        simp [hp, AbsVal.ofPub, AbsVal.Sem, M0Crypto.Armv6M.rorC, hz]
    · by_cases hcf : cf.pub
      · have hcarry : c₁ = c₂ := by cases cf <;> simp_all [AbsFlags.Sem, AbsFlags.pub]
        subst c₂
        simp [hp, hcf, AbsFlags.ofPub, AbsFlags.Sem]
      · simp [hp, hcf, AbsFlags.ofPub, AbsFlags.Sem]
  · simp [hp, AbsVal.ofPub, AbsVal.Sem, AbsFlags.ofPub, AbsFlags.Sem]

/-- Updating N/Z and C with independently chosen labels preserves the
relational state. -/
theorem LowEq.withNZCLabels {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} {v : AbsVal} {x y : Word} {c₁ c₂ : Bool} (pc : Bool)
    (h : LowEq p bytes off st s₁ s₂) (hv : AbsVal.Sem p v x y)
    (hc : AbsFlags.Sem (AbsFlags.ofPub pc) c₁ c₂) :
    LowEq p bytes off { st with fl := setNZC st.fl v.pub pc }
      (s₁.setNZC x c₁) (s₂.setNZC y c₂) := by
  rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  have hn := setNZ_sound hv hflags
  refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  · simpa [FlagSem, setNZC, setNZ, State.setNZC] using ⟨hn.1, hn.2.1, hc, hn.2.2.2⟩
  · intro c hcmp
    simp [setNZC] at hcmp

/-- Register rotate-right preserves result, flag, and carry labels. -/
theorem rors_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    let pub := (st.get d.val).pub && (st.get m.val).pub
    ∃ t₁ t₂, (Instr.dp .rors d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .rors d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .rors d m).size)
        { st.set d.val (AbsVal.ofPub pub) with fl := setNZC st.fl pub (pub && st.fl.c.pub) } t₁ t₂ := by
  let pub := (st.get d.val).pub && (st.get m.val).pub
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hca := h.flags.2.2.1
  have hs := ror_values_sound (by simpa [State.reg, LowReg.toReg] using ha)
    (by simpa [State.reg, LowReg.toReg] using hb) hca
  have hnext := h.withPC hidx (next := off + (Instr.dp .rors d m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZCLabels (pub && st.fl.c.pub) hs.1 hs.2
  have hpub : (AbsVal.ofPub pub).pub = pub := by cases pub <;> rfl
  rw [hpub] at hn
  simp only [AbsState.set, setNZC_touch] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, State.reg, LowReg.toReg, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, State.reg, LowReg.toReg, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked register rotations advance paired certificate executions. -/
theorem certPoint_rors_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .rors d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let pub := (st.get d.val).pub && (st.get m.val).pub
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .rors d m).size) b.ctx,
      { st.set d.val (AbsVal.ofPub pub) with fl := setNZC st.fl pub (pub && st.fl.c.pub) })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, pub] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := rors_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .rors d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .rors d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- A bit test updates N/Z without writing a register. -/
theorem tst_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    let pub := (st.get d.val).pub && (st.get m.val).pub
    ∃ t₁ t₂, (Instr.dp .tst d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .tst d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .tst d m).size)
        { st with fl := setNZ st.fl pub } t₁ t₂ := by
  let pub := (st.get d.val).pub && (st.get m.val).pub
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hv : AbsVal.Sem p (AbsVal.ofPub pub) (s₁.reg d &&& s₁.reg m) (s₂.reg d &&& s₂.reg m) := by
    apply AbsVal.ofPub_binary (fun x y => x &&& y)
    · simpa [State.reg, LowReg.toReg] using ha
    · simpa [State.reg, LowReg.toReg] using hb
  have hn := (h.withPC hidx (next := off + (Instr.dp .tst d m).size)).withNZ hv
  have hp : (AbsVal.ofPub pub).pub = pub := by cases pub <;> rfl
  rw [hp] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked bit tests advance paired certificate executions. -/
theorem certPoint_tst_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .tst d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let pub := (st.get d.val).pub && (st.get m.val).pub
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .tst d m).size) b.ctx,
      { st with fl := setNZ st.fl pub })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, pub] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := tst_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .tst d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .tst d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
