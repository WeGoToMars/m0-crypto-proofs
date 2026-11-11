import M0Crypto.Release.ConstantTime.MovSound
import M0Crypto.Release.ConstantTime.FlagSound
import M0Crypto.Release.ConstantTime.SemArithmetic

/-! Relational semantics for logical operations. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg)
open M0Crypto.Thumb

/-- Register XOR preserves the state relation with the analyzer's result and flag
labels. Execution only; the certificate step is composed in `ConstantTime.InstructionCases`. -/
theorem eors_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .eors d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .eors d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .eors d m).size)
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) } t₁ t₂ := by
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
  have hval : AbsVal.Sem p (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub))
      (s₁.reg d ^^^ s₁.reg m) (s₂.reg d ^^^ s₂.reg m) := by
    apply AbsVal.ofPub_binary (fun x y => x ^^^ y)
    · simpa [State.reg, LowReg.toReg] using ha
    · simpa [State.reg, LowReg.toReg] using hb
  have hnext := h.withPC hidx (next := off + (Instr.dp .eors d m).size)
  have hw := paired_setReg_sound hd hidx hnext hval
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hval
  have hp : (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)).pub =
      ((st.get d.val).pub && (st.get m.val).pub) := by
    cases hp : ((st.get d.val).pub && (st.get m.val).pub) <;> simp [AbsVal.ofPub, AbsVal.pub, hp]
  rw [hp] at hn
  simp only [AbsState.set, setNZ_touch] at hn
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, hpc₁, ofNat_add_assoc]
  · simp [Instr.exec, hpc₂, ofNat_add_assoc]

/-- Register OR preserves the state relation with the analyzer's result and flag
labels. Execution only; the certificate step is composed in `ConstantTime.InstructionCases`. -/
theorem orrs_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .orrs d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .orrs d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .orrs d m).size)
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) } t₁ t₂ := by
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
  have hval : AbsVal.Sem p (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub))
      (s₁.reg d ||| s₁.reg m) (s₂.reg d ||| s₂.reg m) := by
    apply AbsVal.ofPub_binary (fun x y => x ||| y)
    · simpa [State.reg, LowReg.toReg] using ha
    · simpa [State.reg, LowReg.toReg] using hb
  have hnext := h.withPC hidx (next := off + (Instr.dp .orrs d m).size)
  have hw := paired_setReg_sound hd hidx hnext hval
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hval
  have hp : (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)).pub =
      ((st.get d.val).pub && (st.get m.val).pub) := by
    cases hp : ((st.get d.val).pub && (st.get m.val).pub) <;> simp [AbsVal.ofPub, AbsVal.pub, hp]
  rw [hp] at hn
  simp only [AbsState.set, setNZ_touch] at hn
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, hpc₁, ofNat_add_assoc]
  · simp [Instr.exec, hpc₂, ofNat_add_assoc]

/-- Register multiply preserves the state relation with the analyzer's result and flag
labels. Execution only; the certificate step is composed in `ConstantTime.InstructionCases`. -/
theorem muls_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .muls d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .muls d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .muls d m).size)
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) } t₁ t₂ := by
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
  have hval : AbsVal.Sem p (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub))
      (s₁.reg d * s₁.reg m) (s₂.reg d * s₂.reg m) := by
    apply AbsVal.ofPub_binary (fun x y => x * y)
    · simpa [State.reg, LowReg.toReg] using ha
    · simpa [State.reg, LowReg.toReg] using hb
  have hnext := h.withPC hidx (next := off + (Instr.dp .muls d m).size)
  have hw := paired_setReg_sound hd hidx hnext hval
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hval
  have hp : (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)).pub =
      ((st.get d.val).pub && (st.get m.val).pub) := by
    cases hp : ((st.get d.val).pub && (st.get m.val).pub) <;> simp [AbsVal.ofPub, AbsVal.pub, hp]
  rw [hp] at hn
  simp only [AbsState.set, setNZ_touch] at hn
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  refine ⟨_, _, ?_, ?_, hn⟩
  · simp [Instr.exec, hpc₁, ofNat_add_assoc, BitVec.mul_comm]
  · simp [Instr.exec, hpc₂, ofNat_add_assoc, BitVec.mul_comm]

/-- Checked XOR, OR, and multiply transfers match paired concrete steps. -/
theorem logical_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (op : DpOp) (d m : LowReg) (hop : op = .eors ∨ op = .orrs ∨ op = .muls)
    (hx : xfer env off ctx (.dp op d m) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.dp op d m))
    (hlen : off + (Instr.dp op d m).size ≤ bytes.length) :
    ∃ t₁ t₂ e, step s₁ = .ok (t₁, e) ∧ step s₂ = .ok (t₂, e) ∧
      out.sites = [] ∧
      ((.pt (off + (Instr.dp op d m).size) ctx,
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) }) ∈ out.succs) ∧
      LowEq p bytes (off + (Instr.dp op d m).size)
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) } t₁ t₂ := by
  have hex : ∃ t₁ t₂, (Instr.dp op d m).exec s₁ = .ok t₁ ∧
      (Instr.dp op d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp op d m).size)
        { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
          fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) } t₁ t₂ := by
    rcases hop with rfl | rfl | rfl
    · exact eors_sound d m hidx h
    · exact orrs_sound d m hidx h
    · exact muls_sound d m hidx h
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp op d m).size) ctx,
      { st.set d.val (AbsVal.ofPub ((st.get d.val).pub && (st.get m.val).pub)) with
        fl := setNZ st.fl ((st.get d.val).pub && (st.get m.val).pub) })], []⟩ := by
    rcases hop with rfl | rfl | rfl <;>
      simpa [xfer, xferCore, fall, hw, hb.2.1] using hx.symm
  subst out
  obtain ⟨t₁, t₂, he₁, he₂, hrel⟩ := hex
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  have hs₁ := step_of_instrAt hc₁ off (.dp op d m) hpc₁ heven hi hlen (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp op d m) hpc₂ heven hi hlen (by simp [Instr.accesses]) he₂
  refine ⟨t₁, t₂, ⟨s₁.pc, .dp op d m, []⟩, ?_, ?_, rfl, by simp, hrel⟩
  · simpa [Instr.accesses] using hs₁
  · simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
