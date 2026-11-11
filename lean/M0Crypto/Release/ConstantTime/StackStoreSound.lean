import M0Crypto.Release.ConstantTime.StackLoadSound
import M0Crypto.Release.ConstantTime.StackFrame
import M0Crypto.Release.ConstantTime.EntriesDefs

/-! Paired execution of SP-relative word stores. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg write32)
open M0Crypto.Thumb

/-- The ChaCha entry contract separates the artifact and analysis stack window. -/
theorem chacha20_code_stack_disj (c : M0Crypto.Release.Frame.Ctx)
    (hv : M0Crypto.Release.Frame.Valid c) :
    M0Crypto.Release.Frame.Disj c.base M0Crypto.Artifacts.Release.size
      (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) := by
  simpa [chacha20Env, chacha20ArgWords, TraceSpec.chacha20StackBytes,
    M0Crypto.Release.Frame.Ctx.fp, M0Crypto.Release.ChaCha20Layout.chStackBytes_eq] using hv.codeF

/-- The AEAD entry contract separates the artifact and analysis stack window. -/
theorem aead_code_stack_disj (c : M0Crypto.Release.Aead.ACall)
    (hv : M0Crypto.Release.Aead.AValid c) :
    M0Crypto.Release.Frame.Disj c.base M0Crypto.Artifacts.Release.size
      (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) := by
  simpa [encryptEnv, aeadArgWords, TraceSpec.aeadStackBytes] using hv.codeS

/-- Rebase an integer stack offset at the beginning of the stack window. -/
theorem stack_offset_rebase (sp : M0Crypto.Armv6M.Word) (below : Nat) (o : Int)
    (hlo : -(below : Int) ≤ o) :
    sp + BitVec.ofInt 32 o =
      (sp - BitVec.ofNat 32 below) + BitVec.ofNat 32 (o + (below : Int)).toNat := by
  have hk : (((o + (below : Int)).toNat : Nat) : Int) = o + (below : Int) := by
    exact Int.toNat_of_nonneg (by omega)
  have ho : o = (((o + (below : Int)).toNat : Nat) : Int) - (below : Int) := by omega
  calc
    sp + BitVec.ofInt 32 o =
        sp + BitVec.ofInt 32 ((((o + (below : Int)).toNat : Nat) : Int) - (below : Int)) :=
          congrArg (fun x => sp + BitVec.ofInt 32 x) ho
    _ = (sp - BitVec.ofNat 32 below) + BitVec.ofNat 32 (o + (below : Int)).toNat := by
      rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
        BitVec.ofInt_natCast, BitVec.ofInt_natCast]
      rw [BitVec.sub_eq_add_neg, ← BitVec.add_assoc,
        BitVec.add_assoc sp,
        BitVec.add_comm (BitVec.ofNat 32 (o + (below : Int)).toNat) (-BitVec.ofNat 32 below),
        ← BitVec.add_assoc]

/-- A word write inside a region disjoint from the artifact preserves code bytes. -/
theorem codeAt_write32_of_disj {m : M0Crypto.Armv6M.Mem} {base region addr value : M0Crypto.Armv6M.Word}
    {bytes : List (BitVec 8)} {regionSize offset : Nat}
    (hcode : CodeAt m base bytes)
    (hdisj : M0Crypto.Release.Frame.Disj base bytes.length region regionSize)
    (haddr : addr = region + BitVec.ofNat 32 offset)
    (hwithin : offset + 4 ≤ regionSize) :
    CodeAt (write32 m addr value) base bytes := by
  intro i hi
  rw [M0Crypto.Armv6M.write32_other]
  · exact hcode i hi
  · intro k hk
    rw [haddr, ofNat_add_assoc]
    exact M0Crypto.Release.Frame.ne_of_disj hdisj.1 hdisj.2.1 hdisj.2.2 hi (by omega)

/-- A word store in a stack window disjoint from code preserves the artifact. -/
theorem codeAt_stack_write {m : M0Crypto.Armv6M.Mem} {base sp value : M0Crypto.Armv6M.Word}
    {bytes : List (BitVec 8)} (w : StackWindow) (o : Int)
    (hcode : CodeAt m base bytes)
    (hdisj : M0Crypto.Release.Frame.Disj base bytes.length
      (sp - BitVec.ofNat 32 w.below) (w.below + w.above))
    (hwin : w.covers o (o + 4) = true) :
    CodeAt (write32 m (sp + BitVec.ofInt 32 o) value) base bytes := by
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hwin
  apply codeAt_write32_of_disj hcode hdisj (stack_offset_rebase sp w.below o hwin.1)
  have hk : (((o + (w.below : Int)).toNat : Nat) : Int) = o + (w.below : Int) := by
    exact Int.toNat_of_nonneg (by omega)
  omega

/-- Consecutive stores inside a stack window disjoint from code preserve the
artifact after the entire sequence. -/
theorem codeAt_stack_storeWords {m : M0Crypto.Armv6M.Mem}
    {base sp : M0Crypto.Armv6M.Word} {bytes : List (BitVec 8)}
    (w : StackWindow) (off : Int) (vs : List M0Crypto.Armv6M.Word)
    (hcode : CodeAt m base bytes)
    (hdisj : M0Crypto.Release.Frame.Disj base bytes.length
      (sp - BitVec.ofNat 32 w.below) (w.below + w.above))
    (hwin : ∀ k, k < vs.length →
      w.covers (off + (4 * k : Nat)) (off + (4 * k : Nat) + 4) = true) :
    CodeAt (storeWords m (sp + BitVec.ofInt 32 off) vs) base bytes := by
  induction vs generalizing off m with
  | nil => exact hcode
  | cons v vs ih =>
    have ht : w.covers off (off + 4) = true := by simpa using hwin 0 (by simp)
    have hcode' := codeAt_stack_write (value := v) w off hcode hdisj ht
    have hwin' : ∀ k, k < vs.length →
        w.covers (off + 4 + (4 * k : Nat)) (off + 4 + (4 * k : Nat) + 4) = true := by
      intro k hk
      have h := hwin (k + 1) (by simp; omega)
      have heq : off + 4 + (4 * k : Nat) = off + (4 * (k + 1) : Nat) := by omega
      simpa only [heq] using h
    have hnext := ih (off + 4) hcode' hwin'
    have haddr : sp + BitVec.ofInt 32 (off + 4) =
        (sp + BitVec.ofInt 32 off) + 4#32 := by
      rw [BitVec.ofInt_add, BitVec.add_assoc]
      rfl
    simpa only [storeWords, haddr] using hnext

/-- A checked SP-relative store preserves the code in both related memories
when the entry's stack window is disjoint from the artifact. -/
theorem strSp_code_preserved {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (t : LowReg) (imm : BitVec 8)
    (hx : xfer env off ctx (.strSp t imm) st = .ok out)
    (h : LowEq p bytes off st s₁ s₂)
    (hdisj : M0Crypto.Release.Frame.Disj p.base bytes.length
      (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above)) :
    CodeAt (write32 s₁.mem (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4)) (s₁.reg t)) p.base bytes ∧
    CodeAt (write32 s₂.mem (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4)) (s₂.reg t)) p.base bytes := by
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hwin : env.win.covers (st.spOff + (imm.toNat * 4 : Nat))
      (st.spOff + (imm.toNat * 4 : Nat) + 4) = true := by
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    split at hx <;> simp_all
  have ⟨ha₁, ha₂⟩ := stack_load_address imm h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  constructor
  · rw [ha₁]
    exact codeAt_stack_write env.win _ hc₁ hdisj hwin
  · rw [ha₂]
    exact codeAt_stack_write env.win _ hc₂ hdisj hwin

/-- A word store preserves the relational state when the checked stack slots are
well formed and the write preserves the code bytes in both memories. -/
theorem strSp_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (w : StackWindow) (t : LowReg) (imm : BitVec 8)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : w.below + w.above < 2 ^ 32) (hslots : st.stk.slotsOk w)
    (hspalign : st.spOff % 4 = 0)
    (hwin : w.covers (st.spOff + (imm.toNat * 4 : Nat))
      (st.spOff + (imm.toNat * 4 : Nat) + 4) = true)
    (hcode₁ : CodeAt (write32 s₁.mem (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4))
      (s₁.reg t)) p.base bytes)
    (hcode₂ : CodeAt (write32 s₂.mem (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4))
      (s₂.reg t)) p.base bytes) :
    ∃ u₁ u₂, (Instr.strSp t imm).exec s₁ = .ok u₁ ∧
      (Instr.strSp t imm).exec s₂ = .ok u₂ ∧
      LowEq p bytes (off + (Instr.strSp t imm).size)
        { st with stk := stkSet st.stk (st.spOff + (imm.toNat * 4 : Nat)) (st.get t.val) }
        u₁ u₂ := by
  have ht : regIndexOk t.val := by
    constructor <;> have := t.isLt <;> simp [numRegs] <;> omega
  have ht16 : t.val < 16 := by have := t.isLt; omega
  have hval := h.regs t.val ht.1 ht.2
  rw [regAt_eq_regs s₁ t.val ht16, regAt_eq_regs s₂ t.val ht16] at hval
  have hval' : AbsVal.Sem p (st.get t.val) (s₁.reg t) (s₂.reg t) := by
    simpa [State.reg, LowReg.toReg] using hval
  have ⟨ha₁, ha₂⟩ := stack_load_address imm h
  have halign : (st.spOff + (imm.toNat * 4 : Nat)) % 4 = 0 := by omega
  have hstack := stkSet_word_write_sem w hwidth hslots hwin halign h.stack hval'
  have hnext := h.withPC hidx (next := off + (Instr.strSp t imm).size)
  rcases hnext with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, _, hrel,
    hlnk, hsize, _, _⟩
  have hpc₁' := h.pc
  have hpc₂' := h.pc_eq.trans hpc₁'
  refine ⟨{ (s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.strSp t imm).size))) with
      mem := write32 s₁.mem (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4)) (s₁.reg t) },
    { (s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.strSp t imm).size))) with
      mem := write32 s₂.mem (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4)) (s₂.reg t) }, ?_, ?_, ?_⟩
  · simp [Instr.exec, hpc₁', ofNat_add_assoc]
  · simp [Instr.exec, hpc₂', ofNat_add_assoc]
  · refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, hcmp, ?_, hrel,
      hlnk, hsize, hcode₁, hcode₂⟩
    simpa only [ha₁, ha₂] using hstack

/-- Checked SP stores either emit equal events and preserve the relation, or
both executions fault on alignment. Code preservation is a site obligation. -/
theorem strSp_checked_step {env : Env} {p : Params} {bytes : List (BitVec 8)}
    {off : Nat} {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out}
    (t : LowReg) (imm : BitVec 8)
    (hx : xfer env off ctx (.strSp t imm) st = .ok out)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (hwidth : env.win.below + env.win.above < 2 ^ 32)
    (hstack : st.stackCheck env.win = true)
    (hcode₁ : CodeAt (write32 s₁.mem (s₁.sp + BitVec.ofNat 32 (imm.toNat * 4))
      (s₁.reg t)) p.base bytes)
    (hcode₂ : CodeAt (write32 s₂.mem (s₂.sp + BitVec.ofNat 32 (imm.toNat * 4))
      (s₂.reg t)) p.base bytes)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false)
    (hi : instrAt bytes off = some (.strSp t imm))
    (hlen : off + (Instr.strSp t imm).size ≤ bytes.length) :
    (∃ fault, step s₁ = .error fault ∧ step s₂ = .error fault) ∨
    ∃ u₁ u₂ e, step s₁ = .ok (u₁, e) ∧ step s₂ = .ok (u₂, e) ∧
      out.sites = [] ∧
      ((.pt (off + (Instr.strSp t imm).size) ctx,
        { st with stk := stkSet st.stk (st.spOff + (imm.toNat * 4 : Nat)) (st.get t.val) }) ∈ out.succs) ∧
      LowEq p bytes (off + (Instr.strSp t imm).size)
        { st with stk := stkSet st.stk (st.spOff + (imm.toNat * 4 : Nat)) (st.get t.val) } u₁ u₂ := by
  obtain ⟨hspalign, hslots⟩ := (AbsState.stackCheck_iff env.win st).mp hstack
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hwin : env.win.covers (st.spOff + (imm.toNat * 4 : Nat))
      (st.spOff + (imm.toNat * 4 : Nat) + 4) = true := by
    simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte, xferCore] at hx
    split at hx <;> simp_all
  have hsps : s₁.sp = s₂.sp := by simpa [State.sp] using h.sp_eq.symm
  have hacc : (Instr.strSp t imm).accesses s₁ = (Instr.strSp t imm).accesses s₂ := by
    simp [Instr.accesses, hsps]
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hpc₁ := h.pc
  have hpc₂ := h.pc_eq.trans hpc₁
  by_cases hal : ((Instr.strSp t imm).accesses s₁).all Access.aligned = true
  · right
    have hal₂ : ((Instr.strSp t imm).accesses s₂).all Access.aligned = true := by
      simpa [hacc] using hal
    obtain ⟨u₁, u₂, he₁, he₂, hrel⟩ := strSp_sound env.win t imm hidx h hwidth hslots
      hspalign hwin hcode₁ hcode₂
    have hs₁ := step_of_instrAt hc₁ off (.strSp t imm) hpc₁ heven hi hlen hal he₁
    have hs₂ := step_of_instrAt hc₂ off (.strSp t imm) hpc₂ heven hi hlen hal₂ he₂
    have hout : out = ⟨[(.pt (off + (Instr.strSp t imm).size) ctx,
        { st with stk := stkSet st.stk (st.spOff + (imm.toNat * 4 : Nat)) (st.get t.val) })], []⟩ := by
      simp only [xfer, hw, hb.2.1, decide_true, Bool.and_self, ↓reduceIte,
        xferCore, hwin, fall, Except.ok.injEq] at hx
      exact hx.symm
    subst out
    refine ⟨u₁, u₂, ⟨s₁.pc, .strSp t imm, (Instr.strSp t imm).accesses s₁⟩,
      hs₁, ?_, rfl, by simp, hrel⟩
    simpa [h.pc_eq, hacc] using hs₂
  · left
    have hd₁ := decode_at hc₁ off (.strSp t imm) hi hlen
    have hd₂ := decode_at hc₂ off (.strSp t imm) hi hlen
    have hal₂ : ((Instr.strSp t imm).accesses s₂).all Access.aligned ≠ true := by
      simpa [hacc] using hal
    have heven' : (p.base + BitVec.ofNat 32 off)[0] = false := by
      rw [← BitVec.getLsbD_eq_getElem (show 0 < 32 by decide)]
      exact heven
    refine ⟨.unaligned s₁.pc, ?_, ?_⟩
    · simp [step, hpc₁, heven', hd₁, hal]
    · simp [step, hpc₁, hpc₂, heven', hd₂, hal₂]

end M0Crypto.Release.ConstantTime
