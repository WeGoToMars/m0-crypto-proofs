import M0Crypto.Release.ConstantTime.InstructionSound

/-! Relational execution of comparisons and their recorded flag meaning. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg Word addWithCarry)
open M0Crypto.Thumb

/-- The comparison flags computed by the abstract transfer. -/
def cmpImmFlags (v : AbsVal) (r : Nat) (k : Nat) : AFl :=
  let f := (addRes v (notWord (.cst k)) (.known true) .lo).2
  if v.pub then { f with cmp := some ⟨r, .imm k, false⟩ } else f

private theorem cmpBase_no_record (a b : AbsVal) :
    (addRes a b (.known true) .lo).2.cmp = none := by
  unfold addRes
  split <;> simp_all [AFl.all]
  split <;> simp_all [AFl.all]

/-- The comparison's NZCV labels describe both concrete computations, even
when the compared register is secret. -/
theorem cmpImm_flags_sound {p : Params} {v : AbsVal} {x y : Word} (k : Nat)
    (hk : k < 2 ^ 32) (hv : AbsVal.Sem p v x y) :
    let f := (addRes v (notWord (.cst k)) (.known true) .lo).2
    let a := addWithCarry x (~~~(BitVec.ofNat 32 k)) true
    let b := addWithCarry y (~~~(BitVec.ofNat 32 k)) true
    AbsFlags.Sem f.n a.1.msb b.1.msb ∧
    AbsFlags.Sem f.z (a.1 == 0#32) (b.1 == 0#32) ∧
    AbsFlags.Sem f.c a.2.1 b.2.1 ∧ AbsFlags.Sem f.v a.2.2 b.2.2 := by
  have hksem : AbsVal.Sem p (.cst k) (BitVec.ofNat 32 k) (BitVec.ofNat 32 k) := by
    simp [AbsVal.Sem, AbsVal.cst, Nat.mod_eq_of_lt hk]
  cases hp : v.pub with
  | false =>
    cases v <;> simp_all [AbsVal.pub, addRes, AbsVal.exact?, AFl.all, AbsFlags.ofPub, AbsFlags.Sem, AbsFlags.pub]
  | true =>
    have hxy := AbsVal.sem_public hv hp
    have hresult : AbsVal.Sem p .lo (addWithCarry x (~~~(BitVec.ofNat 32 k)) true).1
        (addWithCarry y (~~~(BitVec.ofNat 32 k)) true).1 := by
      simp [AbsVal.Sem, hxy]
    exact (addRes_sound hv (notWord_sound hksem) (by simp [AbsFlags.Sem]) hresult).2

set_option maxRecDepth 2048 in
/-- Immediate comparison preserves the paired state and records the actual
comparison when its operand is public. -/
theorem cmpImm_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (n : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.cmpImm n imm).exec s₁ = .ok t₁ ∧
      (Instr.cmpImm n imm).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.cmpImm n imm).size)
        { st with fl := cmpImmFlags (st.get n.val) n.val imm.toNat } t₁ t₂ := by
  have hn : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hn16 : n.val < 16 := by have := n.isLt; omega
  have hn15 : n.val ≠ (15 : Fin 16).val := by
    change n.val ≠ 15
    have := n.isLt
    omega
  have hv := h.regs n.val hn.1 hn.2
  rw [regAt_eq_regs s₁ n.val hn16, regAt_eq_regs s₂ n.val hn16] at hv
  have hv' : AbsVal.Sem p (st.get n.val) (s₁.reg n) (s₂.reg n) := by
    simpa [State.reg, LowReg.toReg] using hv
  have hk : imm.toNat < 2 ^ 32 := by have := imm.isLt; omega
  have hflags := cmpImm_flags_sound imm.toNat hk hv'
  have hconst : imm.setWidth 32 = BitVec.ofNat 32 imm.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk]
  rw [← hconst] at hflags
  have hnext := h.withPC hidx (next := off + (Instr.cmpImm n imm).size)
  rcases hnext with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  let t₁ := addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.cmpImm n imm).size)))
    0 (s₁.reg n) (~~~(imm.setWidth 32)) true false
  let t₂ := addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.cmpImm n imm).size)))
    0 (s₂.reg n) (~~~(imm.setWidth 32)) true false
  refine ⟨t₁, t₂, ?_, ?_, ?_⟩
  · simp [Instr.exec, t₁, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, t₂, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [t₁, t₂, addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · cases hp : (st.get n.val).pub <;>
        simpa [cmpImmFlags, hp, FlagSem, State.setNZCV, State.setNZ] using hflags
    · intro c hc
      cases hp : (st.get n.val).pub with
      | false =>
        have hc' := cmpBase_no_record (st.get n.val) (notWord (.cst imm.toNat))
        simp [cmpImmFlags, hp, hc'] at hc
      | true =>
        have hc' : c = ⟨n.val, .imm imm.toNat, false⟩ := by
          simpa [cmpImmFlags, hp] using hc.symm
        subst c
        constructor <;>
          simp [CmpSem, operand, State.setNZCV, State.setNZ, regAt, State.setReg,
            State.reg, LowReg.toReg, ← hconst, Nat.mod_eq_of_lt hn16,
            Fin.ext_iff, hn15]

/-- Checked immediate comparisons advance paired certificate executions. -/
theorem certPoint_cmpImm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (n : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.cmpImm n imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.cmpImm n imm).size) b.ctx,
      { st with fl := cmpImmFlags (st.get n.val) n.val imm.toNat })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, cmpImmFlags] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := cmpImm_sound n imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.cmpImm n imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.cmpImm n imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Abstract flag record for a comparison between two low registers. -/
def cmpRegFlags (a b : AbsVal) (d m : Nat) : AFl :=
  let pub := a.pub && b.pub
  let f := AFl.all (AbsFlags.ofPub pub)
  if pub then { f with cmp := some ⟨d, .reg m, false⟩ } else f

/-- Register comparison preserves the paired state and its flag record. -/
theorem cmpReg_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .cmp d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .cmp d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .cmp d m).size)
        { st with fl := cmpRegFlags (st.get d.val) (st.get m.val) d.val m.val } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hd15 : d.val ≠ (15 : Fin 16).val := by change d.val ≠ 15; have := d.isLt; omega
  have hm15 : m.val ≠ (15 : Fin 16).val := by change m.val ≠ 15; have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have ha' : AbsVal.Sem p (st.get d.val) (s₁.reg d) (s₂.reg d) := by
    simpa [State.reg, LowReg.toReg] using ha
  have hb' : AbsVal.Sem p (st.get m.val) (s₁.reg m) (s₂.reg m) := by
    simpa [State.reg, LowReg.toReg] using hb
  have hnext := h.withPC hidx (next := off + (Instr.dp .cmp d m).size)
  rcases hnext with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  let t₁ := addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .cmp d m).size)))
    0 (s₁.reg d) (~~~(s₁.reg m)) true false
  let t₂ := addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .cmp d m).size)))
    0 (s₂.reg d) (~~~(s₂.reg m)) true false
  refine ⟨t₁, t₂, ?_, ?_, ?_⟩
  · simp [Instr.exec, t₁, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, t₂, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [t₁, t₂, addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · cases hpa : (st.get d.val).pub <;> cases hpb : (st.get m.val).pub
      all_goals try simp [cmpRegFlags, hpa, hpb, AFl.all, AbsFlags.ofPub, FlagSem, AbsFlags.Sem, State.setNZCV, State.setNZ]
      have hea := AbsVal.sem_public ha' hpa
      have heb := AbsVal.sem_public hb' hpb
      simp [hea, heb]
    · intro c hc
      cases hp : (st.get d.val).pub && (st.get m.val).pub with
      | false => simp [cmpRegFlags, hp, AFl.all] at hc
      | true =>
        have hc' : c = ⟨d.val, .reg m.val, false⟩ := by simpa [cmpRegFlags, hp] using hc.symm
        subst c
        constructor <;>
          simp [CmpSem, operand, State.setNZCV, State.setNZ, regAt, State.setReg,
            State.reg, LowReg.toReg, Nat.mod_eq_of_lt hd16, Nat.mod_eq_of_lt hm16,
            Fin.ext_iff, hd15, hm15]

/-- Checked register comparisons advance paired certificate executions. -/
theorem certPoint_cmpReg_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .cmp d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .cmp d m).size) b.ctx,
      { st with fl := cmpRegFlags (st.get d.val) (st.get m.val) d.val m.val })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1, cmpRegFlags] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := cmpReg_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .cmp d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .cmp d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
