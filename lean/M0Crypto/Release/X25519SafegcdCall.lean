import M0Crypto.Release.X25519SafegcdEntry
import M0Crypto.Release.X25519Bridge
import M0Crypto.Release.ConstantTime.FrameCallSound
import M0Crypto.Release.ConstantTime.TraceFragment
import M0Crypto.Release.Interrupt

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (State Word Reg)
open M0Crypto.Release
open M0Crypto.Release.TraceSpec (X25519ReadRegion)
open M0Crypto.Release.X25519Layout M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519SafegcdCode M0Crypto.Release.X25519SafegcdFrame
open M0Crypto.Release.X25519SafegcdEntry (space work_region work_disj)
open M0Crypto.Release.X25519SafegcdLink (layout checked)
open M0Crypto.Thumb
open SafegcdRow.BatchCode (entered callTo call_at frameBytes)
open SafegcdTermination
open SafegcdTermination.Bank (addr WritesOnly)
open SafegcdTermination.RowCalls (entered_sp entered_mem entered_regs entered_lr linkedRet_clear)

set_option maxRecDepth 40000
set_option maxHeartbeats 1600000

abbrev x25519CallSite : Nat := callSite oChain
abbrev x25519CallRet : Nat := afterSite oChain

def x25519CallTrace (base sp : Word) : List Event :=
  ⟨base+BitVec.ofNat 32 x25519CallSite,callTo x25519CallSite (layout.first+layout.start),[]⟩ ::
    layout.trace base (workSp sp) (addr sp sZ2) (addr sp sZ2)

/-- Every instruction of the summary, including the entering BL, uses the
same stack pointer. Reads lie within the bounds of the entry call. -/
structure X25519SummaryStep (c : X25519.Ctx) (s : State) (ev : Event) : Prop where
  sp : s.sp = workSp (E c)
  reads : ∀ y, Reads ev.accesses y → X25519ReadRegion c y
  code : Interrupt.CodePos c.base B s
  footprint : ∀ y, Reads ev.accesses y ∨ Writes ev.accesses y →
    Region (workSp (E c)) frameBytes y ∨ Region c.base Artifacts.Release.size y

private theorem code_at_step {base : Word} {s t : State} {ev : Event}
    (hCode : CodeAt s.mem base B) (h : stepH B base s = .ok (t,ev)) :
    Interrupt.CodePos base B s := by
  obtain ⟨_,_,hi,hl⟩ := CodeStack.step_instruction h
  exact ⟨_,ev.instr,(base_add_sub s.pc).symm,hi,hl,hCode⟩

private theorem callBytes : Linked B oChain (layout.first+layout.start) :=
  linked_of_body X25519EntrySeg.inversion_seg

private theorem frame_stack {c : X25519.Ctx} (hv : X25519.Valid c) {y : Word}
    (h : Region (workSp (E c)) frameBytes y) : Region c.fp X25519.stackBytes y :=
  Nat.lt_of_lt_of_le (work_region hv (Nat.lt_of_lt_of_le h (by decide))) (by decide)

private theorem pc_not_ret {c : X25519.Ctx} {s : State} (hp : X25519.Pre c s) {y : Word}
    (h : Region c.base Artifacts.Release.size y) : y ≠ c.ret := by
  obtain ⟨i,hi,rfl⟩ := h.exists
  exact (x25519_ret_not_code hp i hi).symm

theorem x25519_call_trace {c : X25519.Ctx} {entry s : State} (hp : X25519.Pre c entry)
    (hCode : CodeAt s.mem c.base B) (hPc : s.pc = c.base+BitVec.ofNat 32 x25519CallSite)
    (hSp : s.sp = workSp (E c)) (h0 : s.regs 0 = addr (E c) sZ2) (h1 : s.regs 1 = addr (E c) sZ2) :
    ∃ t, TraceFragment c.ret (X25519SummaryStep c) s (x25519CallTrace c.base (E c)) t ∧
      t.pc = c.base+BitVec.ofNat 32 x25519CallRet ∧ t.sp = s.sp ∧ CodeAt t.mem c.base B ∧
      WritesOnly s.mem t.mem s.sp frameBytes ∧
      ∀ ev ∈ (x25519CallTrace c.base (E c)).tail, X25519Ev.InvPc c.base ev.pc := by
  let root := entered c.base x25519CallSite (layout.first+layout.start) s
  have pre : LinkedInversion.Pre root c.base B layout :=
    X25519SafegcdRun.call_pre hp.valid.base4 (space hp.valid) (work_disj hp.valid) hCode hSp h0 h1
  obtain ⟨t,hRun,hInv,hCode',hWrites,hPcs⟩ := LinkedInversion.run checked pre
  obtain ⟨hReads,_,hStable⟩ := LinkedInversion.trace_io checked pre
  have hrSp : root.sp = s.sp := entered_sp _ _ _ _
  have hrM : root.mem = s.mem := entered_mem _ _ _ _
  have hr0 : root.regs 0 = addr (E c) sZ2 :=
    (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h0
  have hr1 : root.regs 1 = addr (E c) sZ2 :=
    (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h1
  have hWlen : (layout.window B).length = layout.length := by decide +kernel
  have hFits : layout.first + layout.length ≤ Artifacts.Release.size := by decide +kernel
  have hFr (y : Word) (hy : Region root.sp frameBytes y) : Region c.fp X25519.stackBytes y :=
    frame_stack hp.valid ((hrSp.trans hSp) ▸ hy)
  have hVec {r : Reg} (h : root.regs r = addr (E c) sZ2) {y : Word}
      (hy : Region (root.regs r) 32 y) : Region root.sp frameBytes y := by
    rw [h,rebase] at hy
    rw [hrSp,hSp]
    exact TraceWrites.subregion (by decide : borrowed+sZ2+32 ≤ frameBytes) hy
  have hPCs (ev : Event) (he : ev ∈ layout.trace c.base root.sp (root.regs 0) (root.regs 1)) :
      Region c.base Artifacts.Release.size ev.pc := by
    have h := hPcs ev he
    rw [hWlen] at h
    exact X25519Ev.band_code hFits h
  have hRd (ev : Event) (he : ev ∈ layout.trace c.base root.sp (root.regs 0) (root.regs 1))
      (y : Word) (hy : Reads ev.accesses y) : Region root.sp frameBytes y ∨
        Region c.base Artifacts.Release.size y := by
    rcases hReads ev he y hy with h | h | h
    · exact .inl h
    · exact .inl (hVec hr1 h)
    · exact .inr (X25519Ev.band_code (by decide +kernel) h)
  have hWrite (ev : Event) (he : ev ∈ layout.trace c.base root.sp (root.regs 0) (root.regs 1))
      (y : Word) (hy : Writes ev.accesses y) : Region root.sp frameBytes y :=
    (hWrites ev he y hy).elim id (hVec hr0)
  have hChecks := CodeStack.steps_of_run hRun
    (P := fun ev => Region c.base Artifacts.Release.size ev.pc ∧
      (∀ y, Reads ev.accesses y → Region root.sp frameBytes y ∨ Region c.base Artifacts.Release.size y) ∧
      (∀ y, Writes ev.accesses y → Region root.sp frameBytes y))
    (fun ev he => ⟨hPCs ev he,hRd ev he,hWrite ev he⟩) hStable
  let obs := fun (u : State) (e : Event) => u.sp = workSp (E c) ∧
    ∀ y, Reads e.accesses y ∨ Writes e.accesses y →
      Region (workSp (E c)) frameBytes y ∨ Region c.base Artifacts.Release.size y
  have hChecks' : StepsOk c.base (fun u e => e.pc ≠ c.ret ∧ obs u e ∧ MissesCode B c.base e.accesses)
      (layout.trace c.base root.sp (root.regs 0) (root.regs 1)).length root := by
    apply StepsOk.mono _ hChecks
    intro u e ⟨⟨hpc,hr,hw⟩,hs⟩
    refine ⟨pc_not_ret hp hpc,⟨hs.trans (hrSp.trans hSp),?_⟩,?_⟩
    · intro y hy
      rw [← hSp,← hrSp]
      exact hy.elim (hr y) (fun h => .inl (hw y h))
    · intro i hi hwr
      exact Field25519Facts.region_ne hp.valid.codeS (hFr _ (hw _ hwr)) i (B_len ▸ hi) rfl
  have hFrag := TraceFragment.of_runH hRun pre.bytes hChecks'
    (Q := X25519SummaryStep c) fun _ _ _ hc hs h =>
      ⟨h.1,fun y hy => (h.2 y (.inl hy)).elim
        (fun f => .inr (.inr (.inr (frame_stack hp.valid f)))) (fun f => .inr (.inr (.inl f))),
        code_at_step hc hs,h.2⟩
  have hBefore : stepH B c.base s = .ok (root,⟨s.pc,callTo x25519CallSite (layout.first+layout.start),[]⟩) :=
    call_at (x25519_base2 hp.valid) checked.length hPc (by decide) (by decide) (by decide) callBytes.call
  have hFirst := step_of_stepH hCode hBefore
  have hSZ : x25519CallSite < Artifacts.Release.size := by decide
  have hNonstop : s.pc ≠ c.ret := by rw [hPc]; exact (x25519_ret_not_code hp _ hSZ).symm
  have hLocal : X25519SummaryStep c s ⟨s.pc,callTo x25519CallSite (layout.first+layout.start),[]⟩ :=
    ⟨hSp,fun y h => absurd h (reads_nil y),code_at_step hCode hBefore,
      fun y h => h.elim (fun h => absurd h (reads_nil y)) (fun h => absurd h (writes_nil y))⟩
  have hAll := TraceFragment.cons hNonstop hFirst hLocal hFrag
  rw [hPc,hrSp,hSp,hr0,hr1] at hAll
  refine ⟨t,hAll,?_,hInv.sp.trans hrSp,hCode',?_,?_⟩
  · rw [hInv.pc,show root.regs 14 = _ from entered_lr _ _ _ _,linkedRet_clear (base := c.base) (off := x25519CallSite) (x25519_base2 hp.valid) (by decide)]
    rfl
  · intro y hy
    have hy' : ¬ Region root.sp frameBytes y := by
      rw [hrSp]
      intro h
      obtain ⟨i,hi,he⟩ := h.exists
      exact hy i hi he
    have hsOut := hInv.outside
    rw [hrM] at hsOut
    exact hsOut y (fun i hi h => hy' (Region.mk hi h))
      (fun i hi h => hy' (hVec hr0 (Region.mk hi h)))
  · rw [hWlen,hrSp,hSp,hr0,hr1] at hPcs
    intro ev he
    have hb := hPcs ev he
    exact Nat.lt_of_lt_of_le hb (by decide +kernel)


private theorem call_instr :
    instrAt B x25519CallSite = some (callTo x25519CallSite (layout.first+layout.start)) := by
  have h := callBytes.call
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem summary_sp (c : X25519.Ctx) :
    (x25519Params c).sp0 + BitVec.ofInt 32 x25519InversionCall.spOff = workSp (E c) := by
  unfold workSp E
  rw [BitVec.sub_eq_add_neg,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  congr 1

theorem summary_arg (c : X25519.Ctx) :
    (x25519Params c).sp0 + BitVec.ofInt 32 x25519InversionCall.srcOff = addr (E c) sZ2 := by
  unfold addr E
  rw [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  congr 1

private theorem exact_stack_value {p : Params} {o : Int} {x y : Word}
    (h : AbsVal.Sem p (.sp o o) x y) : x = p.sp0+BitVec.ofInt 32 o ∧ y = p.sp0+BitVec.ofInt 32 o := by
  obtain ⟨k,ha,hb,hx,hy⟩ := h
  have hk : k = o := by omega
  cases hk
  exact ⟨hx,hy.trans hx⟩

/-- At the call's certificate point the checked register offsets establish
the shared preconditions, and the exact trace reaches the checked successor. -/
theorem x25519_enter_summary {c : X25519.Ctx} {entry s₁ s₂ : State} (hp : X25519.Pre c entry)
    (h : CertAt x25519Env x25519Cert (x25519Params c) B s₁ s₂)
    (hpc : s₁.pc = c.base+BitVec.ofNat 32 x25519CallSite) :
    let tr := x25519CallTrace c.base (E c)
    ∃ t₁ t₂, TraceFragment c.ret (X25519SummaryStep c) s₁ tr t₁ ∧
      TraceFragment c.ret (X25519SummaryStep c) s₂ tr t₂ ∧
      CertAt x25519Env x25519Cert (x25519Params c) B t₁ t₂ ∧
      t₁.sp = workSp (E c) ∧ t₁.pc = c.base+BitVec.ofNat 32 x25519CallRet ∧
      ∀ ev ∈ tr.tail, X25519Ev.InvPc c.base ev.pc := by
  obtain ⟨b,off,st,is,hm,hpt,hne,hlow⟩ := h
  cases is with
  | nil => exact absurd rfl hne
  | cons i is =>
    obtain ⟨hi,hb⟩ := certPoint_instrAt x25519_certOk hm hpt
    have hl : Artifacts.Release.bytes.length < 2^32 := checked.length
    have hOff : off = x25519CallSite := by
      have he : c.base+BitVec.ofNat 32 off = c.base+BitVec.ofNat 32 x25519CallSite := hlow.pc.symm.trans hpc
      have hCall : x25519CallSite < 2^32 := by decide
      have hBound : off < 2^32 := by omega
      have hEq := congrArg (fun w : Word => (w-c.base).toNat) he
      rwa [Frame.sub_ofNat_toNat _ _ hBound,Frame.sub_ofNat_toNat _ _ hCall] at hEq
    subst off
    have hInstr := Option.some.inj (hi.symm.trans call_instr)
    subst i
    obtain ⟨out,hx⟩ := certPoint_xfer x25519_certOk hm hpt
    have hSlots := (AbsState.stackCheck_iff x25519Env.win st).mp
      (certPoint_stackCheck x25519_slotsCheck hm hpt)
    obtain ⟨xlo,xhi0,xhi⟩ := xfer_sp_bounds hx
    have hW : x25519Env.win.covers st.spOff st.spOff = true := by
      simp [StackWindow.covers,xlo,xhi]
    have hTarget : relTarget x25519CallSite (blDisp
        (BitVec.ofInt 25 ((layout.first+layout.start : Nat) - (x25519CallSite+4) : Int))) =
        some x25519InversionCall.target := by decide +kernel
    have hAt : x25519Env.frameCallAt x25519CallSite = some x25519InversionCall := by decide +kernel
    have hx' := hx
    simp only [xfer,hW,xhi0,decide_true,Bool.and_self,ite_true,callTo,xferCore] at hx'
    cases hctx : b.ctx with
    | some q => simp [hctx] at hx'
    | none =>
      simp only [hctx,Option.isSome_none,Bool.false_eq_true,ite_false,hTarget,hAt] at hx'
      split at hx'
      · rename_i hOk
        have hu := FrameCall.ok_fields hOk
        obtain ⟨_,hS,h0,h1,hWin⟩ := hu
        have hs₁ : s₁.sp = workSp (E c) := by
          change s₁.regs 13 = _
          rw [hlow.sp,hS,summary_sp]
        have hs₂ : s₂.sp = workSp (E c) := hlow.sp_eq.trans hs₁
        have r0 := hlow.regs 0 (by decide) (by decide)
        have r1 := hlow.regs 1 (by decide) (by decide)
        rw [h0] at r0
        rw [h1] at r1
        obtain ⟨r₀₁,r₀₂⟩ := exact_stack_value r0
        obtain ⟨r₁₁,r₁₂⟩ := exact_stack_value r1
        rw [show x25519InversionCall.dstOff = x25519InversionCall.srcOff from rfl,
          summary_arg] at r₀₁ r₀₂
        rw [summary_arg] at r₁₁ r₁₂
        obtain ⟨a,hA,haPc,haSp,haCode,haW,haRegion⟩ :=
          x25519_call_trace hp hlow.code₁ hpc hs₁ r₀₁ r₁₁
        obtain ⟨v,hV,hvPc,hvSp,hvCode,hvW,_⟩ :=
          x25519_call_trace hp hlow.code₂ (hlow.pc_eq.trans hpc) hs₂ r₀₂ r₁₂
        have hSrcSp : (x25519Params c).sp0 + BitVec.ofInt 32 x25519InversionCall.spOff =
            workSp (E c) := summary_sp c
        have hDone := FrameCall.after_sound hlow x25519_win_width hSlots.2 hWin haPc
          (hvPc.trans haPc.symm) haSp hvSp haCode hvCode (fun y hy =>
            ⟨haW y (by rw [hs₁, ← hSrcSp]; exact hy),
              hvW y (by rw [hs₂, ← hSrcSp]; exact hy)⟩)
        have ho := congrArg Out.succs (Except.ok.inj hx').symm
        rw [← hctx] at ho
        refine ⟨a,v,hA,hV,?_,haSp.trans hs₁,haPc,haRegion⟩
        exact certAt_point x25519_certOk x25519_indicesFailure_eq_none hm (.next hpt hx ho) hDone
      · contradiction

end M0Crypto.Release.ConstantTime
