import M0Crypto.Release.ConstantTime.ShiftLinks

/-! Paired semantics for eight-bit immediate addition. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg addWithCarry)
open M0Crypto.Thumb

private theorem addRes_no_cmp (a b v : AbsVal) (c : AbsFlags) : (addRes a b c v).2.cmp = none := by
  unfold addRes
  split <;> simp_all [AFl.all]
  split <;> simp_all

/-- Adding a small immediate preserves the result and flag relations. -/
theorem addImm8_base_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.addImm8 d imm).exec s₁ = .ok u₁ ∧
      (Instr.addImm8 d imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.addImm8 d imm).size)
        { st.set d.val (addRes (st.get d.val) (.cst imm.toNat) (.known false)
          ((st.get d.val).addK imm.toNat)).1 with
          fl := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
            ((st.get d.val).addK imm.toNat)).2 } u₁ u₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have ha := lowReg_sem d h
  have hs := addRes_sound ha
    (show AbsVal.Sem p (.cst imm.toNat) (imm.setWidth 32) (imm.setWidth 32) from by
      have hk : imm.toNat < 2^32 := by have := imm.isLt; omega
      simp [AbsVal.Sem, AbsVal.cst, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hk])
    (show AbsFlags.Sem (.known false) false false from by simp [AbsFlags.Sem])
    (by simpa [addWithCarry, BitVec.add_def, BitVec.setWidth_eq] using AbsVal.addK_sound imm.toNat ha)
  have hw := paired_setReg_sound hd hidx (h.withPC hidx (next := off + (Instr.addImm8 d imm).size)) hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d imm).size)))
      d.toReg (s₁.reg d) (imm.setWidth 32) false,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d imm).size)))
      d.toReg (s₂.reg d) (imm.setWidth 32) false, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, State.setNZCV, State.setNZ, State.reg, LowReg.toReg] using hs.2
    · intro c hc'
      have hn := addRes_no_cmp (st.get d.val) (.cst imm.toNat)
        ((st.get d.val).addK imm.toNat) (.known false)
      simp_all

/-- Immediate addition also preserves the ordering facts inferred by the transfer. -/
theorem addImm8_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.addImm8 d imm).exec s₁ = .ok u₁ ∧
      (Instr.addImm8 d imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.addImm8 d imm).size)
        (incFacts st d.val d.val imm.toNat
          { st.set d.val (addRes (st.get d.val) (.cst imm.toNat) (.known false)
            ((st.get d.val).addK imm.toNat)).1 with
            fl := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
              ((st.get d.val).addK imm.toNat)).2 }) u₁ u₂ := by
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := addImm8_base_sound d imm hidx h
  refine ⟨u₁, u₂, he₁, he₂, ?_⟩
  by_cases hk : imm.toNat = 1
  · have himm : imm = 1#8 := by apply BitVec.eq_of_toNat_eq; simpa using hk
    subst imm
    have hu₁ : u₁ = addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d 1#8).size)))
        d.toReg (s₁.reg d) (1#32) false := by
      simpa [Instr.exec, h.pc, ofNat_add_assoc] using he₁.symm
    have hu₂ : u₂ = addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d 1#8).size)))
        d.toReg (s₂.reg d) (1#32) false := by
      simpa [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc] using he₂.symm
    have hd16 : d.val < 16 := by have := d.isLt; omega
    apply h.withIncFacts hidx hnext
    · rw [hu₁]
      simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, State.reg,
        LowReg.toReg, addWithCarry, BitVec.add_def, Nat.mod_eq_of_lt hd16]
    · rw [hu₂]
      simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, State.reg,
        LowReg.toReg, addWithCarry, BitVec.add_def, Nat.mod_eq_of_lt hd16]
    · intro j hj hjd
      rw [hu₁]
      have hj16 : j < 16 := by have := hj.1; simp [numRegs] at this; omega
      have hj15 : j ≠ 15 := by have := hj.1; simp [numRegs] at this; omega
      simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, LowReg.toReg,
        Nat.mod_eq_of_lt hj16, Fin.ext_iff, hjd] <;> omega
    · intro j hj hjd
      rw [hu₂]
      have hj16 : j < 16 := by have := hj.1; simp [numRegs] at this; omega
      have hj15 : j ≠ 15 := by have := hj.1; simp [numRegs] at this; omega
      simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, LowReg.toReg,
        Nat.mod_eq_of_lt hj16, Fin.ext_iff, hjd] <;> omega
  · simpa [incFacts, hk] using hnext


/-- The full abstract transfer, including affine-link movement and tightening,
preserves the paired concrete state. -/
theorem addImm8_shifted_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (w : StackWindow) (d : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ u₁ u₂, (Instr.addImm8 d imm).exec s₁ = .ok u₁ ∧
      (Instr.addImm8 d imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.addImm8 d imm).size)
        (shiftLinks w st d.val imm.toNat
          (incFacts st d.val d.val imm.toNat
            { st.set d.val (addRes (st.get d.val) (.cst imm.toNat) (.known false)
              ((st.get d.val).addK imm.toNat)).1 with
              fl := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
                ((st.get d.val).addK imm.toNat)).2 })) u₁ u₂ := by
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := addImm8_sound d imm hidx h
  refine ⟨u₁, u₂, he₁, he₂, ?_⟩
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hset := AbsState.indicesOk_set (r := d.val)
    (v := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
      ((st.get d.val).addK imm.toNat)).1) hidx
  have hpostidx : (incFacts st d.val d.val imm.toNat
      { st.set d.val (addRes (st.get d.val) (.cst imm.toNat) (.known false)
          ((st.get d.val).addK imm.toNat)).1 with
        fl := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
          ((st.get d.val).addK imm.toNat)).2 }).indicesOk := by
    apply incFacts_indicesOk hd hidx
    refine ⟨?_, hset.2⟩
    intro c hc
    have hn := addRes_no_cmp (st.get d.val) (.cst imm.toNat)
      ((st.get d.val).addK imm.toNat) (.known false)
    simp_all
  have hu₁ : u₁ = addFlags
      (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d imm).size)))
      d.toReg (s₁.reg d) (imm.setWidth 32) false := by
    simpa [Instr.exec, h.pc, ofNat_add_assoc] using he₁.symm
  have hu₂ : u₂ = addFlags
      (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addImm8 d imm).size)))
      d.toReg (s₂.reg d) (imm.setWidth 32) false := by
    simpa [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc] using he₂.symm
  have hd16 : d.val < 16 := by have := d.isLt; omega
  apply shiftLinks_sound w (imm.toNat : Int) h hnext hidx hpostidx
  · rw [hu₁]
    simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, State.reg,
      LowReg.toReg, addWithCarry, BitVec.add_def, BitVec.ofInt_natCast,
      Nat.mod_eq_of_lt hd16]
  · rw [hu₂]
    simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, State.reg,
      LowReg.toReg, addWithCarry, BitVec.add_def, BitVec.ofInt_natCast,
      Nat.mod_eq_of_lt hd16]
  · intro j hj hjd
    rw [hu₁]
    have hj16 : j < 16 := by have := hj.1; simp [numRegs] at this; omega
    have hj15 : j ≠ 15 := by have := hj.1; simp [numRegs] at this; omega
    simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, LowReg.toReg,
      Nat.mod_eq_of_lt hj16, Fin.ext_iff, hjd] <;> omega
  · intro j hj hjd
    rw [hu₂]
    have hj16 : j < 16 := by have := hj.1; simp [numRegs] at this; omega
    have hj15 : j ≠ 15 := by have := hj.1; simp [numRegs] at this; omega
    simp [addFlags, regAt, State.setNZCV, State.setNZ, State.setReg, LowReg.toReg,
      Nat.mod_eq_of_lt hj16, Fin.ext_iff, hjd] <;> omega

/-- A checked eight-bit immediate addition advances paired certificate executions. -/
theorem certPoint_addImm8_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.addImm8 d imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.addImm8 d imm).size) b.ctx,
      shiftLinks env.win st d.val imm.toNat
        (incFacts st d.val d.val imm.toNat
          { st.set d.val (addRes (st.get d.val) (.cst imm.toNat) (.known false)
              ((st.get d.val).addK imm.toNat)).1 with
            fl := (addRes (st.get d.val) (.cst imm.toNat) (.known false)
              ((st.get d.val).addK imm.toNat)).2 }))], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hpoint := BlockPoint.next hp hx (congrArg Out.succs hout)
  obtain ⟨u₁, u₂, he₁, he₂, hnext⟩ := addImm8_shifted_sound env.win d imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.addImm8 d imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.addImm8 d imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂
end M0Crypto.Release.ConstantTime
