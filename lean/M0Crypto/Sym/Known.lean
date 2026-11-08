import M0Crypto.Sym.Norm

/-!
# Approach C: known register values at block entry

`SState.initK k` is `SState.init` with the registers listed in `k` replaced by constants.
Under the hypothesis that the concrete state holds those values, it denotes that state,
so a block's precondition on registers (e.g. rotation counts) enters the checker as data.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- Register `r` from the list `k` (first match) as a constant, else the unknown `reg0 r`. -/
def lookK : List (Reg × Word) → Reg → SExpr
  | [], r => .reg0 r
  | (r', w) :: k, r => if r = r' then .const w else lookK k r

theorem lookK_denote (s : State) : ∀ (k : List (Reg × Word)), (∀ p ∈ k, s.regs p.1 = p.2) →
    ∀ r, (lookK k r).denote s = s.regs r
  | [], _, r => rfl
  | (r', w) :: k, h, r => by
    simp only [lookK]
    split
    · rename_i hr; subst hr; exact (h _ List.mem_cons_self).symm
    · exact lookK_denote s k (fun p hp => h p (List.mem_cons_of_mem _ hp)) r

def SState.initK (k : List (Reg × Word)) : SState := { SState.init with regs := lookK k }

theorem initK_denote (k : List (Reg × Word)) (s : State) (h : ∀ p ∈ k, s.regs p.1 = p.2) :
    (SState.initK k).denote s = s := by
  cases s
  simp only [SState.denote, SState.initK, SState.init, SExpr.denote, SBool.denote, SMem.denote]
  congr 1
  funext r
  exact lookK_denote _ k h r

/-- Register `r` after the straight-line block `is`, from a state whose registers in `k`
hold the listed values. -/
theorem execAll_regs_normK (is : List Instr) (hf : is.all Instr.falls = true)
    (k : List (Reg × Word)) (s : State) (h : ∀ p ∈ k, s.regs p.1 = p.2) (r : Reg) :
    (execAll is s).regs r = (norm ((symExec is (SState.initK k)).regs r)).denote s := by
  rw [norm_sound, ← denote_regs, symExec_sound is (sound_all hf), initK_denote k s h]

end M0Crypto.Sym
