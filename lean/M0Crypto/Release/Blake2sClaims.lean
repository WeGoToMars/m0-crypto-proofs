import M0Crypto.Release.Blake2sTraceSpec
import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sInitConstantTime
import M0Crypto.Release.Blake2sUpdateReads
import M0Crypto.Release.Blake2sFinalReads

/-!
# The BLAKE2s per-function claims, in the standard form

`Blake2sContract.lean` and `Blake2sTraceSpec.lean` state the claims of `init`, `update` and
`final` over one call description (`Ctx`) and one precondition (`Pre`). This file derives them
from the entry-state theorems the proofs establish (`Blake2sHash.*_correct_of_entry`,
`Blake2s{Init,Update,Final}.*_of_entry`): `Pre` gives the proofs' entry structure, and the
proofs' results, write sets and read sets are restated with `Region`.
-/

namespace M0Crypto.Release.Blake2sClaims

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime (Params Env ReadOk)
open M0Crypto.Release.Blake2s (ContextHolds)

/-! ## The context -/

theorem holds_ctx {m : Mem} {c : Word} {st : Spec.Blake2s.State} (h : ContextHolds m c st) :
    Blake2sStream.Ctx m c st :=
  ⟨⟨h.hSize, h.h, h.countLow, h.countHigh, h.countLt, h.pendingLe, h.buf⟩, h.used⟩

theorem ctx_holds {m : Mem} {c : Word} {st : Spec.Blake2s.State} (h : Blake2sStream.Ctx m c st) :
    ContextHolds m c st :=
  ⟨⟨h.hsz, h.h, h.clo, h.chi, h.cnt, h.plen, h.buf⟩, h.used⟩

/-! ## `Region` and the offset form of the proofs -/

theorem region_of {a y : Word} {n : Nat} (h : ∃ o < n, y = a + BitVec.ofNat 32 o) : Region a n y :=
  let ⟨_, ho, e⟩ := h; Region.mk ho e

theorem not_of_region {a y : Word} {n : Nat} (h : ¬ Region a n y) :
    ¬ ∃ o < n, y = a + BitVec.ofNat 32 o :=
  fun ⟨_, ho, e⟩ => h (Region.mk ho e)

/-- A read the constant-time checker allows (`ReadOk`) is in the code or in the stack window
below the entry SP. -/
theorem readOk_region {p : Params} {env : Env} {y : Word} (habove : env.win.above = 0)
    (hsize : env.size = Artifacts.Release.size) (h : ReadOk p env y) :
    Region p.base Artifacts.Release.size y ∨
      Region (p.sp0 - BitVec.ofNat 32 env.win.below) env.win.below y := by
  rcases h with ⟨o, ho, e⟩ | ⟨o, ho, e⟩
  · right; rw [habove] at ho; exact Region.mk (by omega) e
  · left; rw [hsize] at ho; exact Region.mk ho e

/-- Registers `r0`-`r(n-1)` agree, from one equation per register. -/
theorem regs_lt {s₁ s₂ : State} {n : Nat} (hn : n ≤ 3) (h0 : s₂.regs 0 = s₁.regs 0)
    (h1 : 1 < n → s₂.regs 1 = s₁.regs 1) (h2 : 2 < n → s₂.regs 2 = s₁.regs 2) :
    ∀ r : Reg, r.val < n → s₂.regs r = s₁.regs r := by
  intro ⟨v, hv⟩ hr
  simp only at hr
  rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl
  · exact h0
  · exact h1 (by omega)
  · exact h2 (by omega)

/-- Callee-saved registers, from the proofs' split form. -/
theorem callee_of {t s : State}
    (h47 : t.regs 4 = s.regs 4 ∧ t.regs 5 = s.regs 5 ∧ t.regs 6 = s.regs 6 ∧ t.regs 7 = s.regs 7)
    (hi : ∀ r : Reg, 8 ≤ r.val → r.val ≤ 11 → t.regs r = s.regs r) :
    ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = s.regs r := by
  intro r h4 h12
  by_cases h8 : 8 ≤ r.val
  · exact hi r h8 (by omega)
  · obtain ⟨v, hv⟩ := r
    simp only at h4 h8
    have : v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact h47.1
    · exact h47.2.1
    · exact h47.2.2.1
    · exact h47.2.2.2

end M0Crypto.Release.Blake2sClaims

/-! ## `m0c_blake2s_init` -/

namespace M0Crypto.Release.Blake2s.Init

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime (ReadOk b2iEnv)
open M0Crypto.Release.Blake2sClaims

variable {c : Ctx} {s : State}

theorem Pre.regs13 (h : Pre c s) : s.regs 13 = c.sp0 := by rw [h.entry.regs, h.entry.sp]
theorem Pre.regs14 (h : Pre c s) : s.regs 14 = c.regs0 14 := by rw [h.entry.regs]
theorem Pre.regs0 (h : Pre c s) : s.regs 0 = c.context := by rw [h.entry.regs, h.entry.r0]
theorem Pre.ret_eq (h : Pre c s) : s.regs 14 &&& ~~~1#32 = c.ret := by rw [h.regs14]; rfl

theorem Pre.toEntry (h : Pre c s) : Blake2sInit.InitEntry c.base s := by
  have v := h.valid
  refine ⟨v.base4, ?_, by rw [h.entry.mem]; exact v.code, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s.regs 15 = _; rw [h.entry.regs]; exact h.entry.pc
  · rw [h.regs13]; exact v.sp4
  · rw [h.regs13]; exact v.spLo
  · rw [h.regs0]; exact v.context4
  · rw [h.entry.regs]; exact h.thumb
  · rw [h.regs0]; exact v.codeC
  · rw [h.regs13]; exact v.codeS
  · rw [h.regs0, h.regs13]; exact v.contextS

theorem Pre.retNe (h : Pre c s) :
    ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i := by
  rw [h.ret_eq]; exact Region.ne h.retOut

theorem Pre.wrOk (h : Pre c s) {y : Word} (hy : Blake2sInit.WrI s y) : WrOk c y := by
  rcases hy with hy | hy
  · left; rw [h.regs13] at hy; exact region_of hy
  · right; rw [h.regs0] at hy; exact region_of hy

/-- Claims I1-I3: every valid call of `m0c_blake2s_init` returns with the context holding the
empty stream, callee-saved registers and SP restored, and writes only its stack window and the
context. -/
theorem init_correct : Correct := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sHash.init_correct_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, P, hw⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨t, tr, hru, ⟨?_, ?_, ?_, ?_, ?_⟩, fun e he y hy => h.wrOk (hw e he y hy)⟩
  · rw [P.pc, h.ret_eq]
  · rw [P.sp, h.regs13]
  · intro r h4 h12; rw [P.keep r h4 (by omega), h.entry.regs]
  · rw [← h.regs0]; exact ctx_holds P.ctx
  · intro y hy
    rw [P.mem y (fun o ho e => hy (h.wrOk (Or.inl ⟨o, ho, e⟩)))
      (fun o ho e => hy (h.wrOk (Or.inr ⟨o, ho, e⟩))), h.entry.mem]

/-- `init` constant time: two valid calls with equal public inputs (`Ctx.pub`) have equal
event traces. -/
theorem init_constant_time : TraceSpec.Blake2sInitConstantTime := by
  intro c₁ c₂ s₁ s₂ h₁ h₂ hpub fuel
  simp only [Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hc⟩ := hpub
  have e₂ := h₂.toEntry
  rw [← hb] at e₂
  have hret₂ : c₂.ret = c₁.ret := by simp only [Ctx.ret, hlr]
  rw [hret₂, ← h₁.ret_eq]
  refine Blake2sInit.init_constant_time_of_entry h₁.toEntry e₂ h₁.retNe ?_ ?_ ?_ ?_ fuel
  · show s₂.regs 15 = s₁.regs 15
    rw [h₁.entry.regs, h₂.entry.regs, h₁.entry.pc, h₂.entry.pc, hb]
  · rw [h₁.regs13, h₂.regs13, hsp]
  · rw [h₁.regs14, h₂.regs14, hlr]
  · exact regs_lt (by decide) (by rw [h₁.regs0, h₂.regs0, hc])
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

theorem readRegion (h : Pre c s) {y : Word}
    (hy : ReadOk (Blake2sInit.params c.base s) b2iEnv y) : TraceSpec.Blake2sInitReadRegion c y := by
  have hsp : (Blake2sInit.params c.base s).sp0 = c.sp0 := h.regs13
  rcases Blake2sClaims.readOk_region rfl rfl hy with hy | hy
  · exact Or.inl hy
  · rw [hsp] at hy; exact Or.inr hy

/-- `init` read bounds: every read is in the code or the call's stack window. -/
theorem init_reads : TraceSpec.Blake2sInitReads := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sInit.init_reads_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hr⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  exact ⟨t, tr, hru, fun e he y hy => readRegion h (hr e he y hy)⟩

/-- `init` stack bounds: SP stays within `[sp0 - 4, sp0]`. -/
theorem init_stack : TraceSpec.Blake2sInitStack := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sInit.init_stack_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, tr, hru, hs⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨states, tr, hru, fun u hu => ?_⟩
  have := hs u hu
  rw [h.regs13] at this
  exact this

end M0Crypto.Release.Blake2s.Init

/-! ## `m0c_blake2s_update` -/

namespace M0Crypto.Release.Blake2s.Update

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime (ReadOk b2uEnv)
open M0Crypto.Release.Blake2sClaims

variable {c : Ctx} {s : State}

theorem Pre.regs13 (h : Pre c s) : s.regs 13 = c.sp0 := by rw [h.entry.regs, h.entry.sp]
theorem Pre.regs14 (h : Pre c s) : s.regs 14 = c.regs0 14 := by rw [h.entry.regs]
theorem Pre.regs0 (h : Pre c s) : s.regs 0 = c.context := by rw [h.entry.regs, h.entry.r0]
theorem Pre.regs1 (h : Pre c s) : s.regs 1 = c.input := by rw [h.entry.regs, h.entry.r1]
theorem Pre.regs2 (h : Pre c s) : s.regs 2 = c.len := by rw [h.entry.regs, h.entry.r2]
theorem Pre.ret_eq (h : Pre c s) : s.regs 14 &&& ~~~1#32 = c.ret := by rw [h.regs14]; rfl

theorem Pre.toEntry (h : Pre c s) : Blake2sUpdate.UpdateEntry c.base s c.stream := by
  have v := h.valid
  refine ⟨v.base4, ?_, by rw [h.entry.mem]; exact v.code, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · show s.regs 15 = _; rw [h.entry.regs]; exact h.entry.pc
  · rw [h.regs13]; exact v.sp4
  · rw [h.regs13]; exact v.spLo
  · rw [h.regs0]; exact v.context4
  · rw [h.entry.regs]; exact h.thumb
  · rw [h.regs0, h.entry.mem]; exact holds_ctx v.holds
  · rw [h.regs2]; exact v.lengthLt
  · rw [h.regs0]; exact v.codeC
  · rw [h.regs13]; exact v.codeS
  · rw [h.regs0, h.regs13]; exact v.contextS
  · rw [h.regs1, h.regs2, h.regs0]; exact v.inputC
  · rw [h.regs1, h.regs2, h.regs13]; exact v.inputS

theorem Pre.retNe (h : Pre c s) :
    ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i := by
  rw [h.ret_eq]; exact Region.ne h.retOut

theorem Pre.wrOk (h : Pre c s) {y : Word} (hy : Blake2sUpdate.WrU s y) : WrOk c y := by
  rcases hy with hy | hy
  · left; rw [h.regs13] at hy; exact region_of hy
  · right; rw [h.regs0] at hy; exact region_of hy

theorem Pre.input (h : Pre c s) : Blake2sUpdate.LL s = c.inputB := by
  simp only [Blake2sUpdate.LL, Blake2sUpdate.nn, Ctx.inputB, h.regs1, h.regs2, h.entry.mem]
  rfl

/-- Claims U1-U3: every valid call of `m0c_blake2s_update` returns with the context holding the
stream with the input absorbed, callee-saved registers and SP restored, r0-r3 zero, and writes
only its stack window and the context. -/
theorem update_correct : Correct := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sHash.update_correct_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, P, hw⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨t, tr, hru, ⟨?_, ?_, ?_, ?_, ?_, P.scratch⟩, fun e he y hy => h.wrOk (hw e he y hy)⟩
  · rw [P.pc, h.ret_eq]
  · rw [P.sp, h.regs13]
  · intro r h4 h12
    rw [callee_of ⟨P.r4, P.r5, P.r6, P.r7⟩ P.hi r h4 h12, h.entry.regs]
  · rw [← h.regs0, ← h.input]; exact ctx_holds P.ctx
  · intro y hy
    rw [P.mem y (fun hw => hy (h.wrOk hw)), h.entry.mem]

/-- `update` constant time: two valid calls with equal public inputs (`Ctx.pub`) have equal
event traces. -/
theorem update_constant_time : TraceSpec.Blake2sUpdateConstantTime := by
  intro c₁ c₂ s₁ s₂ h₁ h₂ hpub fuel
  simp only [Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hc, hi, hl, hp⟩ := hpub
  have e₂ := h₂.toEntry
  rw [← hb] at e₂
  have hret₂ : c₂.ret = c₁.ret := by simp only [Ctx.ret, hlr]
  rw [hret₂, ← h₁.ret_eq]
  refine Blake2sUpdate.update_constant_time_of_entry h₁.toEntry e₂ h₁.retNe ?_ ?_ ?_ ?_ ?_ fuel
  · show s₂.regs 15 = s₁.regs 15
    rw [h₁.entry.regs, h₂.entry.regs, h₁.entry.pc, h₂.entry.pc, hb]
  · rw [h₁.regs13, h₂.regs13, hsp]
  · rw [h₁.regs14, h₂.regs14, hlr]
  · exact regs_lt (by decide) (by rw [h₁.regs0, h₂.regs0, hc])
      (fun _ => by rw [h₁.regs1, h₂.regs1, hi]) (fun _ => by rw [h₁.regs2, h₂.regs2, hl])
  · rw [h₁.regs0, h₁.entry.mem, h₁.valid.holds.used, hc, h₂.entry.mem, h₂.valid.holds.used, hp]

theorem readRegion (h : Pre c s) {y : Word}
    (hy : ReadOk (Blake2sUpdate.params c.base s) b2uEnv y ∨ Blake2sUpdate.UR s y) :
    TraceSpec.Blake2sUpdateReadRegion c y := by
  have hsp : (Blake2sUpdate.params c.base s).sp0 = c.sp0 := h.regs13
  rcases hy with hy | hy | hy
  · rcases Blake2sClaims.readOk_region rfl rfl hy with hy | hy
    · exact Or.inr (Or.inr (Or.inl hy))
    · rw [hsp] at hy; exact Or.inr (Or.inr (Or.inr hy))
  · left; rw [h.regs0] at hy; exact region_of hy
  · right; left
    simp only [Blake2sUpdate.nn, h.regs1, h.regs2] at hy
    exact region_of hy

/-- `update` read bounds: every read is in the context, the input, the code or the call's stack
window. -/
theorem update_reads : TraceSpec.Blake2sUpdateReads := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sUpdate.update_reads_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hr⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  exact ⟨t, tr, hru, fun e he y hy => readRegion h (hr e he y hy)⟩

/-- `update` stack bounds: SP stays within `[sp0 - 160, sp0]`, callee frames included. -/
theorem update_stack : TraceSpec.Blake2sUpdateStack := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sUpdate.update_stack_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, tr, hru, hs⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨states, tr, hru, fun u hu => ?_⟩
  have := hs u hu
  rw [h.regs13] at this
  exact this

end M0Crypto.Release.Blake2s.Update

/-! ## `m0c_blake2s_final` -/

namespace M0Crypto.Release.Blake2s.Final

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.ConstantTime (ReadOk b2fEnv)
open M0Crypto.Release.Blake2sClaims

variable {c : Ctx} {s : State}

theorem Pre.regs13 (h : Pre c s) : s.regs 13 = c.sp0 := by rw [h.entry.regs, h.entry.sp]
theorem Pre.regs14 (h : Pre c s) : s.regs 14 = c.regs0 14 := by rw [h.entry.regs]
theorem Pre.regs0 (h : Pre c s) : s.regs 0 = c.context := by rw [h.entry.regs, h.entry.r0]
theorem Pre.regs1 (h : Pre c s) : s.regs 1 = c.out := by rw [h.entry.regs, h.entry.r1]
theorem Pre.ret_eq (h : Pre c s) : s.regs 14 &&& ~~~1#32 = c.ret := by rw [h.regs14]; rfl

theorem Pre.toEntry (h : Pre c s) : Blake2sFinal.FinalEntry c.base s c.stream := by
  have v := h.valid
  refine ⟨v.base4, ?_, by rw [h.entry.mem]; exact v.code, ?_, ?_, ?_, ?_, ?_, v.lengthLt, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show s.regs 15 = _; rw [h.entry.regs]; exact h.entry.pc
  · rw [h.regs13]; exact v.sp4
  · rw [h.regs13]; exact v.spLo
  · rw [h.regs0]; exact v.context4
  · rw [h.entry.regs]; exact h.thumb
  · rw [h.regs0, h.entry.mem]; exact holds_ctx v.holds
  · rw [h.regs0]; exact v.codeC
  · rw [h.regs13]; exact v.codeS
  · rw [h.regs1]; exact v.codeO
  · rw [h.regs0, h.regs13]; exact v.contextS
  · rw [h.regs1, h.regs13]; exact v.outS
  · rw [h.regs0, h.regs1]; exact v.contextO

theorem Pre.retNe (h : Pre c s) :
    ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i := by
  rw [h.ret_eq]; exact Region.ne h.retOut

theorem Pre.wrOk (h : Pre c s) {y : Word} (hy : Blake2sFinal.WrF s y) : WrOk c y := by
  rcases hy with hy | hy | hy
  · left; rw [h.regs13] at hy; exact region_of hy
  · right; left; rw [h.regs0] at hy; exact region_of hy
  · right; right; rw [h.regs1] at hy; exact region_of hy

/-- Claims F1-F3: every valid call of `m0c_blake2s_final` returns with the RFC 7693 digest of the
stream in `out`, callee-saved registers and SP restored, r0-r3 zero, and writes only its stack
window, the context and `out`. -/
theorem final_correct : Correct := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sHash.final_correct_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, P, hw⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨t, tr, hru, ⟨?_, ?_, ?_, ?_, ?_, P.scratch⟩, fun e he y hy => h.wrOk (hw e he y hy)⟩
  · rw [P.pc, h.ret_eq]
  · rw [P.sp, h.regs13]
  · intro r h4 h12; rw [P.keep r h4 (by omega), h.entry.regs]
  · rw [← h.regs1]; exact P.out
  · intro y hy
    rw [P.mem y (fun hw => hy (h.wrOk hw)), h.entry.mem]

/-- `final` constant time: two valid calls with equal public inputs (`Ctx.pub`) have equal
event traces. -/
theorem final_constant_time : TraceSpec.Blake2sFinalConstantTime := by
  intro c₁ c₂ s₁ s₂ h₁ h₂ hpub fuel
  simp only [Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨hb, hsp, hlr, hc, ho, hp⟩ := hpub
  have e₂ := h₂.toEntry
  rw [← hb] at e₂
  have hret₂ : c₂.ret = c₁.ret := by simp only [Ctx.ret, hlr]
  rw [hret₂, ← h₁.ret_eq]
  refine Blake2sFinal.final_constant_time_of_entry h₁.toEntry e₂ h₁.retNe ?_ ?_ ?_ ?_ ?_ fuel
  · show s₂.regs 15 = s₁.regs 15
    rw [h₁.entry.regs, h₂.entry.regs, h₁.entry.pc, h₂.entry.pc, hb]
  · rw [h₁.regs13, h₂.regs13, hsp]
  · rw [h₁.regs14, h₂.regs14, hlr]
  · exact regs_lt (by decide) (by rw [h₁.regs0, h₂.regs0, hc])
      (fun _ => by rw [h₁.regs1, h₂.regs1, ho]) (fun h => absurd h (by decide))
  · rw [h₁.regs0, h₁.entry.mem, h₁.valid.holds.used, hc, h₂.entry.mem, h₂.valid.holds.used, hp]

theorem readRegion (h : Pre c s) {y : Word}
    (hy : ReadOk (Blake2sFinal.params c.base s) b2fEnv y ∨ Blake2sFinal.CtxRF s y) :
    TraceSpec.Blake2sFinalReadRegion c y := by
  have hsp : (Blake2sFinal.params c.base s).sp0 = c.sp0 := h.regs13
  rcases hy with hy | hy
  · rcases Blake2sClaims.readOk_region rfl rfl hy with hy | hy
    · exact Or.inr (Or.inl hy)
    · rw [hsp] at hy; exact Or.inr (Or.inr hy)
  · left; unfold Blake2sFinal.CtxRF at hy; rw [h.regs0] at hy; exact region_of hy

/-- `final` read bounds: every read is in the context, the code or the call's stack window. -/
theorem final_reads : TraceSpec.Blake2sFinalReads := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sFinal.final_reads_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hru, hr⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  exact ⟨t, tr, hru, fun e he y hy => readRegion h (hr e he y hy)⟩

/-- `final` stack bounds: SP stays within `[sp0 - 160, sp0]`, the compression's frame
included. -/
theorem final_stack : TraceSpec.Blake2sFinalStack := by
  intro c s h
  obtain ⟨n, hn⟩ := Blake2sFinal.final_stack_of_entry h.toEntry h.retNe
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨states, tr, hru, hs⟩ := hn fuel hf
  rw [h.ret_eq] at hru
  refine ⟨states, tr, hru, fun u hu => ?_⟩
  have := hs u hu
  rw [h.regs13] at this
  exact this

end M0Crypto.Release.Blake2s.Final
