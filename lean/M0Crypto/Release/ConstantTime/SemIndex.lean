import M0Crypto.Release.ConstantTime.Domain

/-! Well-formed register references in the relational analysis domain.

The abstract state has entries for r0–r12 and LR (r14).  r13 is the separately
tracked stack pointer, and r15 is PC; neither is an abstract general register.
Indices are deliberately not reduced modulo 16: accepting an out-of-range index
would let an analysis record survive a write to the register it aliases in the
machine model.
-/

namespace M0Crypto.Release.ConstantTime

/-- The register indices represented by `AbsState.regs` (r0–r12 and LR). -/
def regIndexOk (r : Nat) : Prop := r < numRegs ∧ r ≠ 13

def opndIndexOk : Opnd → Prop
  | .reg r => regIndexOk r
  | .imm _ => True

def cmpIndexOk (c : Cmp) : Prop := regIndexOk c.a ∧ opndIndexOk c.b

def aflIndexOk (f : AFl) : Prop := ∀ c, f.cmp = some c → cmpIndexOk c

def factIndexOk (f : Fact) : Prop := regIndexOk f.1 ∧ regIndexOk f.2.1

def linkIndexOk (l : Lnk) : Prop := regIndexOk l.i ∧ regIndexOk l.j

/-- Every register reference carried by an abstract state names a tracked register. -/
def AbsState.indicesOk (s : AbsState) : Prop :=
  aflIndexOk s.fl ∧ (∀ f ∈ s.rel, factIndexOk f) ∧ (∀ l ∈ s.lnk, linkIndexOk l)

theorem aflIndexOk_touch {f : AFl} {r : Nat} (hf : aflIndexOk f) :
    aflIndexOk (f.touch r) := by
  intro c hc
  cases hcmp : f.cmp with
  | none => simp [AFl.touch, hcmp] at hc
  | some d =>
    by_cases huses : d.uses r
    · simp [AFl.touch, hcmp, huses] at hc
    · have hc' : c = d := by simpa [AFl.touch, hcmp, huses] using hc.symm
      subst c
      exact hf d hcmp

theorem AbsState.indicesOk_set {s : AbsState} {r : Nat} {v : AbsVal}
    (h : s.indicesOk) : (AbsState.set s r v).indicesOk := by
  rcases h with ⟨hfl, hrel, hlnk⟩
  refine ⟨aflIndexOk_touch hfl, ?_, ?_⟩
  · intro f hf
    simp only [AbsState.set] at hf
    have hmem : f ∈ s.rel := (List.mem_filter.mp hf).1
    exact hrel f hmem
  · intro l hl
    simp only [AbsState.set] at hl
    have hmem : l ∈ s.lnk := (List.mem_filter.mp hl).1
    exact hlnk l hmem

end M0Crypto.Release.ConstantTime
