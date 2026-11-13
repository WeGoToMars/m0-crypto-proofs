import M0Crypto.Release.ConstantTime.MovSound
import M0Crypto.Release.ConstantTime.AddResSound
import M0Crypto.Release.Reach

/-! Paired execution of arithmetic instructions. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg addWithCarry)
open M0Crypto.Thumb

/-- Abstract complement preserves exact constants and publicness. -/
theorem notWord_sound {p : Params} {v : AbsVal} {x y : M0Crypto.Armv6M.Word}
    (hv : AbsVal.Sem p v x y) : AbsVal.Sem p (notWord v) (~~~x) (~~~y) := by
  cases he : v.exact? with
  | none =>
    cases hp : v.pub with
    | false => simp [notWord, he, hp, AbsVal.ofPub, AbsVal.Sem]
    | true =>
      have hxy := AbsVal.sem_public hv hp
      simp [notWord, he, hp, AbsVal.ofPub, AbsVal.Sem, hxy]
  | some a =>
    obtain ⟨ha, rfl, rfl⟩ := AbsVal.exact_sem he hv
    have ha' : a < 2 ^ 32 := by simpa [AbsVal.word] using ha
    have ha'' : a < 4294967296 := by omega
    simp [notWord, he, ha'', AbsVal.Sem, AbsVal.cst, AbsVal.word, BitVec.toNat_not,
      Nat.mod_eq_of_lt ha']

/-- Subtraction supplies the complemented operand and result premises of
the analyzer's add-with-carry flag computation. -/
theorem addRes_sub_sound {p : Params} {a b : AbsVal}
    {x₁ x₂ y₁ y₂ : M0Crypto.Armv6M.Word}
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) :
    let res := addRes a (notWord b) (.known true) (a.sub b)
    let v₁ := addWithCarry x₁ (~~~y₁) true
    let v₂ := addWithCarry x₂ (~~~y₂) true
    AbsVal.Sem p res.1 v₁.1 v₂.1 ∧
    AbsFlags.Sem res.2.n v₁.1.msb v₂.1.msb ∧
    AbsFlags.Sem res.2.z (v₁.1 == 0#32) (v₂.1 == 0#32) ∧
    AbsFlags.Sem res.2.c v₁.2.1 v₂.2.1 ∧ AbsFlags.Sem res.2.v v₁.2.2 v₂.2.2 := by
  apply addRes_sound ha (notWord_sound hb) (by simp [AbsFlags.Sem])
  simpa [M0Crypto.Release.sub_flags] using AbsVal.sub_sound ha hb

private theorem addRes_cmp_none (a b v : AbsVal) (c : AbsFlags) :
    (addRes a b c v).2.cmp = none := by
  unfold addRes
  split <;> simp_all [AFl.all]
  split <;> simp_all [AFl.all]

/-- Register addition preserves the relational state, including all NZCV flags. -/
theorem addReg_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d n m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.addReg d n m).exec s₁ = .ok t₁ ∧
      (Instr.addReg d n m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.addReg d n m).size)
        { st.set d.val (addRes (st.get n.val) (st.get m.val) (.known false)
          ((st.get n.val).add (st.get m.val))).1 with
          fl := (addRes (st.get n.val) (st.get m.val) (.known false)
            ((st.get n.val).add (st.get m.val))).2 } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hn : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hn16 : n.val < 16 := by have := n.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs n.val hn.1 hn.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ n.val hn16, regAt_eq_regs s₂ n.val hn16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hs := addRes_add_sound (by simpa [State.reg, LowReg.toReg] using ha)
    (by simpa [State.reg, LowReg.toReg] using hb)
  have hnext := h.withPC hidx (next := off + (Instr.addReg d n m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  have hpc₁' := h.pc
  have hpc₂' := h.pc_eq.trans hpc₁'
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addReg d n m).size)))
      d.toReg (s₁.reg n) (s₁.reg m) false,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.addReg d n m).size)))
      d.toReg (s₂.reg n) (s₂.reg m) false, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, hpc₁', ofNat_add_assoc]
  · simp [Instr.exec, addFlags, hpc₂', ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, State.setNZCV, State.setNZ, State.reg, LowReg.toReg] using hs.2
    · intro c hc
      have hc' := addRes_cmp_none (st.get n.val) (st.get m.val)
        ((st.get n.val).add (st.get m.val)) (.known false)
      simp_all

/-- Register subtraction preserves the relation and all four condition flags. -/
theorem subReg_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d n m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.subReg d n m).exec s₁ = .ok t₁ ∧
      (Instr.subReg d n m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.subReg d n m).size)
        { st.set d.val (addRes (st.get n.val) (notWord (st.get m.val)) (.known true)
          ((st.get n.val).sub (st.get m.val))).1 with
          fl := (addRes (st.get n.val) (notWord (st.get m.val)) (.known true)
            ((st.get n.val).sub (st.get m.val))).2 } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hn : regIndexOk n.val := by
    constructor <;> have := n.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hn16 : n.val < 16 := by have := n.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs n.val hn.1 hn.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ n.val hn16, regAt_eq_regs s₂ n.val hn16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hs := addRes_sub_sound (by simpa [State.reg, LowReg.toReg] using ha)
    (by simpa [State.reg, LowReg.toReg] using hb)
  have hnext := h.withPC hidx (next := off + (Instr.subReg d n m).size)
  have hw := paired_setReg_sound hd hidx hnext hs.1
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  rcases hw with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, _, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨addFlags (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.subReg d n m).size)))
      d.toReg (s₁.reg n) (~~~(s₁.reg m)) true,
    addFlags (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.subReg d n m).size)))
      d.toReg (s₂.reg n) (~~~(s₂.reg m)) true, ?_, ?_, ?_⟩
  · simp [Instr.exec, addFlags, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, addFlags, h.pc_eq.trans h.pc, ofNat_add_assoc]
  · simp only [addFlags]
    refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, ?_, ?_, hstk, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    · simpa [FlagSem, State.setNZCV, State.setNZ, State.reg, LowReg.toReg] using hs.2
    · intro c hc
      have hc' := addRes_cmp_none (st.get n.val) (notWord (st.get m.val))
        ((st.get n.val).sub (st.get m.val)) (.known true)
      simp_all

/-- A checked register-add transfer agrees with paired machine steps. -/
theorem addReg_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (d n m : LowReg)
    (hx : xfer env off ctx (.addReg d n m) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.addReg d n m))
    (hlen : off + (Instr.addReg d n m).size ≤ bytes.length) :
    ∃ t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      out.sites = [] ∧
      ((.pt (off + (Instr.addReg d n m).size) ctx,
        { st.set d.val (addRes (st.get n.val) (st.get m.val) (.known false)
          ((st.get n.val).add (st.get m.val))).1 with
          fl := (addRes (st.get n.val) (st.get m.val) (.known false)
            ((st.get n.val).add (st.get m.val))).2 }) ∈ out.succs) ∧
      LowEq p bytes (off + (Instr.addReg d n m).size)
        { st.set d.val (addRes (st.get n.val) (st.get m.val) (.known false)
          ((st.get n.val).add (st.get m.val))).1 with
          fl := (addRes (st.get n.val) (st.get m.val) (.known false)
            ((st.get n.val).add (st.get m.val))).2 } t₁ t₂ := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.addReg d n m).size) ctx,
      { st.set d.val (addRes (st.get n.val) (st.get m.val) (.known false)
        ((st.get n.val).add (st.get m.val))).1 with
        fl := (addRes (st.get n.val) (st.get m.val) (.known false)
          ((st.get n.val).add (st.get m.val))).2 })], []⟩ := by
    simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  subst out
  obtain ⟨t₁, t₂, he₁, he₂, hrel⟩ := addReg_sound d n m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hs₁ := step_of_instrAt hc₁ off (.addReg d n m) hpc₁ heven hi hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.addReg d n m) hpc₂ heven hi hlen
    (by simp [Instr.accesses]) he₂
  refine ⟨t₁, t₂, ⟨s₁.pc, .addReg d n m, []⟩, ?_, ?_, rfl, by simp, hrel⟩
  · simpa [Instr.accesses] using hs₁
  · simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
