import M0Crypto.Release.ConstantTime.Reach

/-! Relational execution of immediate register operations. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg)
open M0Crypto.Thumb

/-- Moving an eight-bit constant preserves the paired state and establishes
the analyzer's exact result and N/Z flag labels. -/
theorem movImm_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.movImm d imm).exec s₁ = .ok t₁ ∧
      (Instr.movImm d imm).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.movImm d imm).size)
        { st.set d.val (.cst imm.toNat) with
          fl := { st.fl with n := .known false, z := .known (imm.toNat == 0), cmp := none } } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hval : AbsVal.Sem p (.cst imm.toNat) (imm.setWidth 32) (imm.setWidth 32) := by
    have hm : imm.toNat % 4294967296 = imm.toNat := Nat.mod_eq_of_lt (by have := imm.isLt; omega)
    simp [AbsVal.Sem, AbsVal.cst, BitVec.toNat_setWidth, hm]
  have hnat : (imm.setWidth 32).toNat = imm.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show imm.toNat < 2 ^ 32 by have := imm.isLt; omega)]
  have hmsb : (imm.setWidth 32).msb = false := by
    rw [BitVec.msb_eq_decide, hnat]
    have := imm.isLt
    simp only [decide_eq_false_iff_not]
    omega
  have hzero : (imm.setWidth 32 == 0) = (imm.toNat == 0) := by
    have heq : imm.setWidth 32 = 0 ↔ imm.toNat = 0 := by
      constructor
      · intro he
        have hn := congrArg BitVec.toNat he
        simpa [hnat] using hn
      · intro he
        apply BitVec.eq_of_toNat_eq
        simpa [hnat] using he
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using heq
  have hnext := h.withPC hidx (next := off + (Instr.movImm d imm).size)
  have hw := paired_setReg_sound hd hidx hnext hval
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨((s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.movImm d imm).size))).setReg
      d.toReg (imm.setWidth 32)).setNZ (imm.setWidth 32),
    ((s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.movImm d imm).size))).setReg
      d.toReg (imm.setWidth 32)).setNZ (imm.setWidth 32), ?_, ?_, ?_⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simp only [FlagSem, AbsFlags.Sem, State.setNZ]
      have hc := h.flags.2.2.1
      have hv := h.flags.2.2.2
      simp [hmsb, hzero, State.setReg] at *
      exact ⟨hc, hv⟩
    · intro c hc
      simp at hc

/-- A checked immediate move advances both executions and the certificate
position with identical observations. -/
theorem certPoint_movImm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d : LowReg) (imm : BitVec 8)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.movImm d imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.movImm d imm).size) b.ctx,
      { st.set d.val (.cst imm.toNat) with
        fl := { st.fl with n := .known false, z := .known (imm.toNat == 0), cmp := none } })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := movImm_sound d imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.movImm d imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.movImm d imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- A zero-distance logical shift copies a register, sets N/Z, and preserves
the carry flag in both executions. -/
theorem lslZero_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.lslImm d m 0).exec s₁ = .ok t₁ ∧
      (Instr.lslImm d m 0).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.lslImm d m 0).size)
        { st.set d.val (st.get m.val) with fl := setNZ st.fl (st.get m.val).pub } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hval := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hval
  have hval' : AbsVal.Sem p (st.get m.val) (s₁.reg m) (s₂.reg m) := by
    simpa [State.reg, LowReg.toReg] using hval
  have hnext := h.withPC hidx (next := off + (Instr.lslImm d m 0).size)
  have hw := paired_setReg_sound hd hidx hnext hval'
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hval'
  simp only [AbsState.set, setNZ_touch] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, lslC, State.setNZC, State.setNZ, State.setReg, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, lslC, State.setNZC, State.setNZ, State.setReg, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- A checked zero-distance shift advances the certificate position with
matching observations. -/
theorem certPoint_lslZero_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.lslImm d m 0 :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.lslImm d m 0).size) b.ctx,
      { st.set d.val (st.get m.val) with fl := setNZ st.fl (st.get m.val).pub })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := lslZero_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.lslImm d m 0) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.lslImm d m 0) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Updating N, Z and C preserves the relational state when their abstract
labels describe the two concrete results and carries. -/
theorem LowEq.withNZC {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} {v : AbsVal} {x y : M0Crypto.Armv6M.Word} {c₁ c₂ : Bool}
    (h : LowEq p bytes off st s₁ s₂) (hv : AbsVal.Sem p v x y)
    (hc : AbsFlags.Sem (AbsFlags.ofPub v.pub) c₁ c₂) :
    LowEq p bytes off { st with fl := setNZC st.fl v.pub v.pub }
      (s₁.setNZC x c₁) (s₂.setNZC y c₂) := by
  rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  have hn := setNZ_sound hv hflags
  refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  · simpa [FlagSem, setNZC, setNZ, State.setNZC] using ⟨hn.1, hn.2.1, hc, hn.2.2.2⟩
  · intro c hcmp
    simp [setNZC] at hcmp

/-- Abstract result of a nonzero immediate left shift. -/
def lslResult (v : AbsVal) (n : Nat) : AbsVal :=
  match v.exact? with
  | some a => .cst ((a <<< n) % AbsVal.word)
  | none => AbsVal.ofPub v.pub

theorem lslResult_pub (v : AbsVal) (n : Nat) : (lslResult v n).pub = v.pub := by
  cases hv : v.exact? with
  | none =>
    simp only [lslResult, hv]
    cases hp : v.pub <;> simp only [AbsVal.ofPub, AbsVal.pub, Bool.false_eq_true, ↓reduceIte]
  | some a =>
    have hp : v.pub = true := by cases v <;> simp_all [AbsVal.exact?, AbsVal.pub]
    simp only [lslResult, hv, AbsVal.cst, AbsVal.pub]
    exact hp.symm

/-- The abstract left-shift result describes both concrete words. -/
theorem lslResult_sound {p : Params} {v : AbsVal} {x y : M0Crypto.Armv6M.Word}
    (n : Nat) (hv : AbsVal.Sem p v x y) :
    AbsVal.Sem p (lslResult v n) (x <<< n) (y <<< n) := by
  cases he : v.exact? with
  | none =>
    cases hp : v.pub with
    | false => simp [lslResult, he, hp, AbsVal.ofPub, AbsVal.Sem]
    | true =>
      have hxy := AbsVal.sem_public hv hp
      simp [lslResult, he, hp, AbsVal.ofPub, AbsVal.Sem, hxy]
  | some a =>
    obtain ⟨ha, rfl, rfl⟩ := AbsVal.exact_sem he hv
    simp [lslResult, he, AbsVal.Sem, AbsVal.cst, AbsVal.word, BitVec.toNat_shiftLeft,
      Nat.mod_eq_of_lt (show a < 2 ^ 32 by simpa [AbsVal.word] using ha)]

theorem setNZC_touch (f : AFl) (r : Nat) (p pc : Bool) :
    setNZC (f.touch r) p pc = setNZC f p pc := by
  cases h : f.cmp with
  | none => simp [AFl.touch, h, setNZC]
  | some c => cases hu : c.uses r <;> simp [AFl.touch, h, hu, setNZC]

/-- A nonzero immediate left shift preserves the abstract result, flags and
paired execution relation. -/
theorem lslNonzero_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg) (imm : BitVec 5)
    (himm : imm.toNat ≠ 0) (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.lslImm d m imm).exec s₁ = .ok t₁ ∧
      (Instr.lslImm d m imm).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.lslImm d m imm).size)
        { st.set d.val (lslResult (st.get m.val) imm.toNat) with
          fl := setNZC st.fl (st.get m.val).pub (st.get m.val).pub } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hval := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hval
  have hval' : AbsVal.Sem p (st.get m.val) (s₁.reg m) (s₂.reg m) := by
    simpa [State.reg, LowReg.toReg] using hval
  have hresult := lslResult_sound imm.toNat hval'
  have hcarry : AbsFlags.Sem (AbsFlags.ofPub (lslResult (st.get m.val) imm.toNat).pub)
      ((s₁.reg m).getLsbD (32 - imm.toNat)) ((s₂.reg m).getLsbD (32 - imm.toNat)) := by
    rw [lslResult_pub]
    cases hp : (st.get m.val).pub with
    | false => simp [AbsFlags.ofPub, AbsFlags.Sem]
    | true =>
      have heq := AbsVal.sem_public hval' hp
      simp [AbsFlags.ofPub, AbsFlags.Sem, heq]
  have hnext := h.withPC hidx (next := off + (Instr.lslImm d m imm).size)
  have hw := paired_setReg_sound hd hidx hnext hresult
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZC hresult hcarry
  rw [lslResult_pub] at hn
  simp only [AbsState.set, setNZC_touch] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, lslC, himm, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, lslC, himm, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Every checked immediate left shift advances paired executions with the
same observation. -/
theorem certPoint_lslImm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg) (imm : BitVec 5)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.lslImm d m imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  by_cases hz : imm.toNat = 0
  · have hi0 : imm = 0 := by apply BitVec.eq_of_toNat_eq; simpa using hz
    subst imm
    exact certPoint_lslZero_paired d m hc hi hm hp h heven
  · obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
    have hidx := certPoint_state_indices hi hm hp
    have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
    have hb := xfer_sp_bounds hx
    have hw : env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers, hb.1, hb.2.2]
    have hout : out = ⟨[(.pt (off + (Instr.lslImm d m imm).size) b.ctx,
        { st.set d.val (lslResult (st.get m.val) imm.toNat) with
          fl := setNZC st.fl (st.get m.val).pub (st.get m.val).pub })], []⟩ := by
      cases he : (st.get m.val).exact? <;>
        simpa [xfer, xferCore, fall, hw, hb.2.1, hz, lslResult, he] using hx.symm
    have hsucc := congrArg Out.succs hout
    have hpoint := BlockPoint.next hp hx hsucc
    obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := lslNonzero_sound d m imm hz hidx h
    have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
    have hs₁ := step_of_instrAt hc₁ off (.lslImm d m imm) h.pc heven hdecode hlen
      (by simp [Instr.accesses]) he₁
    have hs₂ := step_of_instrAt hc₂ off (.lslImm d m imm) (h.pc_eq.trans h.pc) heven hdecode hlen
      (by simp [Instr.accesses]) he₂
    apply certAt_paired_step hc hi hm hpoint hnext hs₁
    simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Abstract result of an immediate logical right shift. -/
def lsrResult (v : AbsVal) (n : Nat) : AbsVal :=
  match v with
  | .num a b => .num (a >>> n) (b >>> n)
  | _ => AbsVal.ofPub v.pub

theorem lsrResult_pub (v : AbsVal) (n : Nat) : (lsrResult v n).pub = v.pub := by
  cases v <;> simp [lsrResult, AbsVal.ofPub, AbsVal.pub]

/-- Shifting the interval endpoints bounds every shifted concrete value. -/
theorem lsrResult_sound {p : Params} {v : AbsVal} {x y : M0Crypto.Armv6M.Word}
    (n : Nat) (hv : AbsVal.Sem p v x y) :
    AbsVal.Sem p (lsrResult v n) (x >>> n) (y >>> n) := by
  cases v with
  | hi => simp [lsrResult, AbsVal.ofPub, AbsVal.pub, AbsVal.Sem]
  | lo =>
    change x = y at hv
    simpa [lsrResult, AbsVal.ofPub, AbsVal.pub, AbsVal.Sem] using
      congrArg (fun z : M0Crypto.Armv6M.Word => z >>> n) hv
  | num a b =>
    change x = y ∧ a ≤ x.toNat ∧ x.toNat ≤ b at hv
    obtain ⟨hxy, hlo, hhi⟩ := hv
    simp only [lsrResult, AbsVal.Sem, BitVec.toNat_ushiftRight]
    refine ⟨congrArg (fun z : M0Crypto.Armv6M.Word => z >>> n) hxy, ?_, ?_⟩
    · simpa only [Nat.shiftRight_eq_div_pow] using (Nat.div_le_div_right (c := 2 ^ n) hlo)
    · simpa only [Nat.shiftRight_eq_div_pow] using (Nat.div_le_div_right (c := 2 ^ n) hhi)
  | sp a b =>
    have heq := AbsVal.sem_public hv (by simp [AbsVal.pub])
    simp [lsrResult, AbsVal.ofPub, AbsVal.pub, AbsVal.Sem, heq]
  | ret r =>
    have heq := AbsVal.sem_public hv (by simp [AbsVal.pub])
    simp [lsrResult, AbsVal.ofPub, AbsVal.pub, AbsVal.Sem, heq]
  | lr0 =>
    have heq := AbsVal.sem_public hv (by simp [AbsVal.pub])
    simp [lsrResult, AbsVal.ofPub, AbsVal.pub, AbsVal.Sem, heq]

/-- An immediate right shift preserves the analyzer's interval and flag
labels, including the encoding where zero denotes a shift by 32. -/
theorem lsrImm_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg) (imm : BitVec 5)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    let n := if imm.toNat = 0 then 32 else imm.toNat
    ∃ t₁ t₂, (Instr.lsrImm d m imm).exec s₁ = .ok t₁ ∧
      (Instr.lsrImm d m imm).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.lsrImm d m imm).size)
        { st.set d.val (lsrResult (st.get m.val) n) with
          fl := setNZC st.fl (st.get m.val).pub (st.get m.val).pub } t₁ t₂ := by
  let n := if imm.toNat = 0 then 32 else imm.toNat
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have hval := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hval
  have hval' : AbsVal.Sem p (st.get m.val) (s₁.reg m) (s₂.reg m) := by
    simpa [State.reg, LowReg.toReg] using hval
  have hresult := lsrResult_sound n hval'
  have hcarry : AbsFlags.Sem (AbsFlags.ofPub (lsrResult (st.get m.val) n).pub)
      ((s₁.reg m).getLsbD (n - 1)) ((s₂.reg m).getLsbD (n - 1)) := by
    rw [lsrResult_pub]
    cases hp : (st.get m.val).pub with
    | false => simp [AbsFlags.ofPub, AbsFlags.Sem]
    | true =>
      have heq := AbsVal.sem_public hval' hp
      simp [AbsFlags.ofPub, AbsFlags.Sem, heq]
  have hnext := h.withPC hidx (next := off + (Instr.lsrImm d m imm).size)
  have hw := paired_setReg_sound hd hidx hnext hresult
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZC hresult hcarry
  rw [lsrResult_pub] at hn
  simp only [AbsState.set, setNZC_touch] at hn
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, lsrC, n, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, lsrC, n, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked immediate right shifts advance paired certificate executions. -/
theorem certPoint_lsrImm_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg) (imm : BitVec 5)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.lsrImm d m imm :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  let n := if imm.toNat = 0 then 32 else imm.toNat
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.lsrImm d m imm).size) b.ctx,
      { st.set d.val (lsrResult (st.get m.val) n) with
        fl := setNZC st.fl (st.get m.val).pub (st.get m.val).pub })], []⟩ := by
    cases hv : st.get m.val <;>
      simpa [xfer, xferCore, fall, hw, hb.2.1, lsrResult, n, hv] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := lsrImm_sound d m imm hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.lsrImm d m imm) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.lsrImm d m imm) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

/-- Checked register subtraction advances paired certificate executions. -/
theorem certPoint_subReg_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d n m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.subReg d n m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.subReg d n m).size) b.ctx,
      { st.set d.val (addRes (st.get n.val) (notWord (st.get m.val)) (.known true)
        ((st.get n.val).sub (st.get m.val))).1 with
        fl := (addRes (st.get n.val) (notWord (st.get m.val)) (.known true)
          ((st.get n.val).sub (st.get m.val))).2 })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := subReg_sound d n m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.subReg d n m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.subReg d n m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
