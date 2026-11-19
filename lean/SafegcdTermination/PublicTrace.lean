import M0Crypto.Sym.Block
import M0Crypto.Thumb.Branch

namespace SafegcdTermination.PublicTrace

open M0Crypto.Armv6M (State Reg Word)
open M0Crypto.Thumb M0Crypto.Sym

set_option linter.unusedSimpArgs false

/-- Address and PC expressions are restricted to declared public registers and constants.
    The bitwise cases cover the Thumb literal-pool alignment mask. -/
def publicExpr (regs : List Reg) : SExpr → Bool
  | .reg0 r => regs.contains r
  | .const _ => true
  | .add a b | .sub a b | .and a b => publicExpr regs a && publicExpr regs b
  | .not a => publicExpr regs a
  | .awc a b (.const _) => publicExpr regs a && publicExpr regs b
  | _ => false

theorem public_expr_congr {regs : List Reg} {s t : State} (hs : ∀ r ∈ regs, s.regs r = t.regs r) :
    ∀ e : SExpr, publicExpr regs e = true → e.denote s = e.denote t
  | .reg0 r, h => hs r (List.contains_iff_mem.mp h)
  | .const _, _ => rfl
  | .add a b, h | .sub a b, h | .and a b, h => by
    rw [publicExpr,Bool.and_eq_true] at h
    simp only [SExpr.denote, public_expr_congr hs a h.1, public_expr_congr hs b h.2]
  | .not a, h => by simp only [SExpr.denote, public_expr_congr hs a h]
  | .awc a b c, h => by
    cases c <;> try cases h
    rw [publicExpr,Bool.and_eq_true] at h
    simp only [SExpr.denote, SBool.denote, public_expr_congr hs a h.1, public_expr_congr hs b h.2]
  | .or .., h | .xor .., h | .mul .., h | .uxth .., h | .lsl .., h | .lsr .., h
  | .ror .., h | .lslR .., h | .lsrR .., h | .asr .., h | .rev .., h | .ld32 .., h | .ld16 .., h
  | .ld8 .., h | .rotl .., h => by cases h

def publicAddr (regs : List Reg) (e : SExpr) : Bool := publicExpr regs e || publicExpr regs (norm e)

theorem public_addr_congr {regs : List Reg} {s t : State} (hs : ∀ r ∈ regs, s.regs r = t.regs r)
    (e : SExpr) (h : publicAddr regs e = true) : e.denote s = e.denote t := by
  simp only [publicAddr,Bool.or_eq_true] at h
  rcases h with hc | hc
  · exact public_expr_congr hs e hc
  · simpa only [norm_sound] using public_expr_congr hs (norm e) hc

def publicEvent (regs : List Reg) (e : SExpr × Instr × List SAccess) : Bool :=
  publicAddr regs e.1 && e.2.2.all (fun a => publicAddr regs a.addr)

def traceChk (regs : List Reg) (is : List Instr) : Bool :=
  (symTrace is SState.init).all (publicEvent regs)

/-- First instruction with a PC or access outside the public-register expressions. -/
def traceFailure (regs : List Reg) (is : List Instr) : Option Instr :=
  ((symTrace is SState.init).find? (fun e => !publicEvent regs e)).map (fun e => e.2.1)

theorem trace_chk_sound {is : List Instr} {regs : List Reg}
    (hf : is.all Instr.falls = true) (hc : traceChk regs is = true) {s t : State}
    (h : ∀ r ∈ regs, s.regs r = t.regs r) : traceAll is s = traceAll is t := by
  have hs := symTrace_sound is (sound_all hf) s SState.init
  have ht := symTrace_sound is (sound_all hf) t SState.init
  rw [SState.init_denote] at hs ht
  rw [← hs, ← ht]
  apply List.map_congr_left
  rintro ⟨pc,i,as⟩ he
  have hEvent := List.all_eq_true.mp hc _ he
  simp only [publicEvent,Bool.and_eq_true] at hEvent
  obtain ⟨hp,hA⟩ := hEvent
  have hp' := public_addr_congr h _ hp
  simp only [SEvent.denote,hp',Event.mk.injEq,true_and]
  apply List.map_congr_left
  intro a ha
  have hAddr := public_addr_congr h _ (List.all_eq_true.mp hA _ ha)
  simp only [SAccess.denote,hAddr]

/-- State whose only meaningful registers are the annotated public values. -/
def publicState (bindings : List (Reg × Word)) : State :=
  ⟨fun r => ((bindings.find? (·.1 == r)).map Prod.snd).getD 0,
    false,false,false,false,fun _ => 0⟩

def stackState (pc sp : Word) : State := publicState [(15,pc),(13,sp)]

theorem stack_trace {is : List Instr} (hf : is.all Instr.falls = true)
    (hc : traceChk [15,13] is = true) (s : State) :
    traceAll is s = traceAll is (stackState s.pc s.sp) := by
  apply trace_chk_sound hf hc
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> rfl

end SafegcdTermination.PublicTrace
