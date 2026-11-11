import M0Crypto.Release.ConstantTime.TightenSound
import M0Crypto.Release.ConstantTime.BranchSound
import M0Crypto.Release.ChaCha20Output
import M0Crypto.Sym.Norm

/-! Soundness of interval refinement for conditional branches. -/
namespace M0Crypto.Release.ConstantTime

def Rel.holds (rel : Rel) (x y : Nat) : Prop :=
  match rel with
  | .lt => x < y
  | .le => x ≤ y
  | .gt => x > y
  | .ge => x ≥ y
  | .eq => x = y
  | .ne => x ≠ y

/-- A concrete comparison records equality in Z and unsigned ordering in C. -/
theorem cmpSem_flags {c : Cmp} {s : M0Crypto.Armv6M.State}
    (hc : CmpSem c s) :
    s.z = (regAt s c.a == operand s c.b) ∧
      (c.zOnly = false → s.c = decide ((operand s c.b).toNat ≤ (regAt s c.a).toNat)) := by
  unfold CmpSem at hc
  cases hz : c.zOnly with
  | true => simp [hz] at hc ⊢; exact hc
  | false =>
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at hc
    refine ⟨?_, fun _ => ?_⟩
    · rw [hc.2.1, M0Crypto.Sym.awc_not_true]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      constructor
      · intro he
        have hh := congrArg (fun z => z + operand s c.b) he
        simpa [BitVec.sub_add_cancel] using hh
      · intro he
        simpa [he] using (BitVec.sub_self (operand s c.b))
    · rw [hc.2.2.1, M0Crypto.Release.ChaCha20Output.sub_carry]

/-- For the unsigned and equality conditions that the analyzer refines, the
recorded comparison and observed branch direction imply the corresponding
relation between the concrete operands. -/
theorem condRel_sound {c : Cmp} {s : M0Crypto.Armv6M.State}
    (cond : BitVec 4) (taken : Bool) (rel : Rel)
    (hc : CmpSem c s) (hr : condRel cond.toNat taken = some rel)
    (ht : M0Crypto.Thumb.condPassed cond s = taken)
    (hz : c.zOnly = true → rel = .eq ∨ rel = .ne) :
    rel.holds (regAt s c.a).toNat (operand s c.b).toNat := by
  have ⟨hzero, hcarry⟩ := cmpSem_flags hc
  have hnum : cond.toNat < 16 := cond.isLt
  have hcases : cond.toNat = 0 ∨ cond.toNat = 1 ∨ cond.toNat = 2 ∨
      cond.toNat = 3 ∨ cond.toNat = 8 ∨ cond.toNat = 9 ∨
      cond.toNat ≠ 0 ∧ cond.toNat ≠ 1 ∧ cond.toNat ≠ 2 ∧ cond.toNat ≠ 3 ∧
        cond.toNat ≠ 8 ∧ cond.toNat ≠ 9 := by omega
  rcases hcases with h | h | h | h | h | h | h <;>
    cases taken <;> cases hzo : c.zOnly <;> cases rel <;>
    simp_all [condRel, M0Crypto.Thumb.condPassed, Rel.holds, beq_iff_eq,
      ← BitVec.toNat_inj] <;> omega

/-- An operand interval returned by the analyzer bounds that operand in both
related executions. Oversized immediates have no integer interval. -/
theorem opndIval_bounds {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {op : Opnd} {lo hi : Nat}
    (h : LowEq p bytes off st s₁ s₂) (hok : opndIndexOk op)
    (hival : opndIval st op = some (lo, hi)) :
    lo ≤ (operand s₁ op).toNat ∧ (operand s₁ op).toNat ≤ hi ∧
      lo ≤ (operand s₂ op).toNat ∧ (operand s₂ op).toNat ≤ hi := by
  cases op with
  | reg r =>
    have hr := h.regs r hok.1 hok.2
    exact interval_bounds hr hival
  | imm n =>
    simp only [opndIval] at hival
    split at hival
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hival
      rcases hival with ⟨rfl, rfl⟩
      simp [operand, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [AbsVal.word] using hn)]
    · contradiction

/-- An interval-valued abstract register is public. -/
theorem ival_public {v : AbsVal} {lo hi : Nat} (h : ival v = some (lo, hi)) :
    v.pub = true := by
  cases v <;> simp_all [ival, AbsVal.pub]

/-- Operands with an interval have equal values in the related executions. -/
theorem opndIval_equal {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {op : Opnd} {lo hi : Nat}
    (h : LowEq p bytes off st s₁ s₂) (hok : opndIndexOk op)
    (hival : opndIval st op = some (lo, hi)) : operand s₁ op = operand s₂ op := by
  cases op with
  | reg r =>
    apply AbsVal.sem_public (h.regs r hok.1 hok.2)
    exact ival_public hival
  | imm n => rfl

/-- Replacing a tracked register's interval with bounds known for the first
execution also preserves the second execution, since interval values are public. -/
theorem LowEq.withInterval {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {r lo hi oldLo oldHi : Nat}
    (h : LowEq p bytes off st s₁ s₂) (hr : regIndexOk r)
    (hival : ival (st.get r) = some (oldLo, oldHi))
    (hlo : lo ≤ (regAt s₁ r).toNat) (hhi : (regAt s₁ r).toNat ≤ hi) :
    LowEq p bytes off { st with regs := regSet st.regs r (.num lo hi) } s₁ s₂ := by
  have hs := h.regs r hr.1 hr.2
  have he := AbsVal.sem_public hs (ival_public hival)
  apply h.withRegSet r (.num lo hi)
  exact ⟨he, hlo, hhi⟩

/-- Narrowing two register labels preserves the relation when each new
interval contains its concrete value. This also covers coincident registers. -/
theorem LowEq.withTwoIntervals {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State}
    {r q lo hi lo' hi' a b c d : Nat}
    (h : LowEq p bytes off st s₁ s₂) (hr : regIndexOk r) (hq : regIndexOk q)
    (hrange : ival (st.get r) = some (a, b)) (qrange : ival (st.get q) = some (c, d))
    (hrlo : lo ≤ (regAt s₁ r).toNat) (hrhi : (regAt s₁ r).toNat ≤ hi)
    (hqlo : lo' ≤ (regAt s₁ q).toNat) (hqhi : (regAt s₁ q).toNat ≤ hi') :
    LowEq p bytes off
      { st with regs := regSet (regSet st.regs r (.num lo hi)) q (.num lo' hi') } s₁ s₂ := by
  have hfirst := h.withInterval hr hrange hrlo hrhi
  have hqsem := h.regs q hq.1 hq.2
  have heq := AbsVal.sem_public hqsem (ival_public qrange)
  have hsecond := hfirst.withRegSet q (.num lo' hi') ⟨heq, hqlo, hqhi⟩
  exact hsecond

/-- Replacing the recorded facts is sound when each new fact holds in both
concrete executions. -/
theorem LowEq.withFacts {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (facts : List Fact)
    (h : LowEq p bytes off st s₁ s₂)
    (hf : ∀ f ∈ facts, FactSem f s₁ ∧ FactSem f s₂) :
    LowEq p bytes off { st with rel := facts } s₁ s₂ := by
  rcases h with ⟨hp₁, hp₂, hs₁, hs₂, hr, hflags, hcmp, hstk, _, hlnk, hlen, hc₁, hc₂⟩
  exact ⟨hp₁, hp₂, hs₁, hs₂, hr, hflags, hcmp, hstk, hf, hlnk, hlen, hc₁, hc₂⟩

/-- A feasible pair of values remains within the refined intervals. In
particular, a feasible branch cannot be discarded as infeasible. -/
theorem refineI_sound (rel : Rel) (a₁ a₂ b₁ b₂ x y : Nat)
    (hx₁ : a₁ ≤ x) (hx₂ : x ≤ a₂) (hy₁ : b₁ ≤ y) (hy₂ : y ≤ b₂)
    (hrel : rel.holds x y) :
    ∃ x₁ x₂ y₁ y₂, refineI rel a₁ a₂ b₁ b₂ = some ((x₁,x₂),(y₁,y₂)) ∧
      x₁ ≤ x ∧ x ≤ x₂ ∧ y₁ ≤ y ∧ y ≤ y₂ := by
  cases rel with
  | lt =>
    simp only [Rel.holds] at hrel
    have hb : b₂ ≠ 0 := by omega
    refine ⟨a₁, min a₂ (b₂-1), max b₁ (a₁+1), b₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refineI, hb, show a₁ ≤ min a₂ (b₂-1) by omega,
        show max b₁ (a₁+1) ≤ b₂ by omega]
    all_goals omega
  | le =>
    simp only [Rel.holds] at hrel
    refine ⟨a₁, min a₂ b₂, max b₁ a₁, b₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refineI, show a₁ ≤ min a₂ b₂ by omega, show max b₁ a₁ ≤ b₂ by omega]
    all_goals omega
  | gt =>
    simp only [Rel.holds] at hrel
    have ha : a₂ ≠ 0 := by omega
    refine ⟨max a₁ (b₁+1), a₂, b₁, min b₂ (a₂-1), ?_, ?_, ?_, ?_, ?_⟩
    · simp [refineI, ha, show max a₁ (b₁+1) ≤ a₂ by omega,
        show b₁ ≤ min b₂ (a₂-1) by omega]
    all_goals omega
  | ge =>
    simp only [Rel.holds] at hrel
    refine ⟨max a₁ b₁, a₂, b₁, min b₂ a₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refineI, show max a₁ b₁ ≤ a₂ by omega, show b₁ ≤ min b₂ a₂ by omega]
    all_goals omega
  | eq =>
    simp only [Rel.holds] at hrel
    refine ⟨max a₁ b₁, min a₂ b₂, max a₁ b₁, min a₂ b₂, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refineI, show max a₁ b₁ ≤ min a₂ b₂ by omega]
    all_goals omega
  | ne =>
    simp only [Rel.holds] at hrel
    by_cases hb : b₁ = b₂
    · let lo := if a₁ = b₁ then a₁ + 1 else a₁
      let hi := if a₂ = b₁ ∧ 0 < a₂ then a₂ - 1 else a₂
      have hlo : lo ≤ x := by dsimp [lo]; split <;> omega
      have hhi : x ≤ hi := by dsimp [hi]; split <;> omega
      refine ⟨lo, hi, b₁, b₂, ?_, hlo, hhi, hy₁, hy₂⟩
      have hlh : lo ≤ hi := by omega
      subst b₂
      simpa [refineI, lo, hi] using hlh
    · refine ⟨a₁, a₂, b₁, b₂, ?_, hx₁, hx₂, hy₁, hy₂⟩
      simp [refineI, hb, show a₁ ≤ a₂ by omega, show b₁ ≤ b₂ by omega]

/-- The actual result of refinement contains every pair satisfying the original
intervals and the branch relation. -/
theorem refineI_result_sound {rel : Rel} {a₁ a₂ b₁ b₂ x y x₁ x₂ y₁ y₂ : Nat}
    (hx₁ : a₁ ≤ x) (hx₂ : x ≤ a₂) (hy₁ : b₁ ≤ y) (hy₂ : y ≤ b₂)
    (hrel : rel.holds x y)
    (hresult : refineI rel a₁ a₂ b₁ b₂ = some ((x₁,x₂),(y₁,y₂))) :
    x₁ ≤ x ∧ x ≤ x₂ ∧ y₁ ≤ y ∧ y ≤ y₂ := by
  obtain ⟨u₁, u₂, v₁, v₂, hu, bounds⟩ := refineI_sound rel a₁ a₂ b₁ b₂ x y
    hx₁ hx₂ hy₁ hy₂ hrel
  rw [hresult] at hu
  cases hu
  exact bounds

/-- The register-label updates selected by interval refinement preserve both
concrete runs when the comparison relation holds in the first run. -/
theorem refine_registers_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {cmp : Cmp} {rel : Rel}
    {a₁ a₂ b₁ b₂ x₁ x₂ y₁ y₂ : Nat}
    (h : LowEq p bytes off st s₁ s₂) (hcmp : cmpIndexOk cmp)
    (ha : ival (st.get cmp.a) = some (a₁, a₂))
    (hb : opndIval st cmp.b = some (b₁, b₂))
    (hrel : rel.holds (regAt s₁ cmp.a).toNat (operand s₁ cmp.b).toNat)
    (hresult : refineI rel a₁ a₂ b₁ b₂ = some ((x₁,x₂),(y₁,y₂))) :
    LowEq p bytes off
      { st with regs :=
        let regs := regSet st.regs cmp.a (.num x₁ x₂)
        match cmp.b with
        | .reg r => if r == cmp.a then regs else regSet regs r (.num y₁ y₂)
        | .imm _ => regs } s₁ s₂ := by
  have ha' := interval_bounds (h.regs cmp.a hcmp.1.1 hcmp.1.2) ha
  have hb' := opndIval_bounds h hcmp.2 hb
  have hbounds := refineI_result_sound ha'.1 ha'.2.1 hb'.1 hb'.2.1 hrel hresult
  have hone := h.withInterval hcmp.1 ha hbounds.1 hbounds.2.1
  cases hop : cmp.b with
  | imm n => simpa [hop] using hone
  | reg r =>
    have hr : regIndexOk r := by simpa [opndIndexOk, hop] using hcmp.2
    have hrange : ival (st.get r) = some (b₁, b₂) := by simpa [opndIval, hop] using hb
    by_cases heq : r = cmp.a
    · simpa [hop, heq] using hone
    · have htwo := h.withTwoIntervals hcmp.1 hr ha hrange hbounds.1 hbounds.2.1
        (by simpa [operand, hop] using hbounds.2.2.1)
        (by simpa [operand, hop] using hbounds.2.2.2)
      simpa [hop, heq] using htwo

/-- Relational facts recorded by a branch for two distinct registers. -/
def branchFacts (st : AbsState) (a r : Nat) (rel : Rel) : List Fact :=
  if r == a then [] else match rel with
  | .lt => [(a, r, true)]
  | .le => [(a, r, false)]
  | .gt => [(r, a, true)]
  | .ge => [(r, a, false)]
  | .ne => (if st.entails (a, r, false) then [(a, r, true)] else []) ++
           (if st.entails (r, a, false) then [(r, a, true)] else [])
  | .eq => []

/-- Every fact introduced by refinement holds in both concrete states. -/
theorem branchFacts_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {a r : Nat} {rel : Rel}
    (h : LowEq p bytes off st s₁ s₂) (ha : regIndexOk a) (hr : regIndexOk r)
    (hrel₁ : rel.holds (regAt s₁ a).toNat (regAt s₁ r).toNat)
    (hrel₂ : rel.holds (regAt s₂ a).toNat (regAt s₂ r).toNat) :
    ∀ f ∈ branchFacts st a r rel, FactSem f s₁ ∧ FactSem f s₂ := by
  intro f hf
  by_cases heq : r = a
  · simp [branchFacts, heq] at hf
  · cases rel with
    | lt | le | gt | ge =>
      simp [branchFacts, heq] at hf
      subst f
      simp [FactSem, Rel.holds] at hrel₁ hrel₂ ⊢ <;> omega
    | eq => simp [branchFacts, heq] at hf
    | ne =>
      have hab : st.entails (a, r, false) = true →
          FactSem (a, r, false) s₁ ∧ FactSem (a, r, false) s₂ :=
        fun he => AbsState.entails_sound h ⟨ha, hr⟩ he
      have hba : st.entails (r, a, false) = true →
          FactSem (r, a, false) s₁ ∧ FactSem (r, a, false) s₂ :=
        fun he => AbsState.entails_sound h ⟨hr, ha⟩ he
      cases habool : st.entails (a, r, false) <;>
        cases hbbool : st.entails (r, a, false) <;>
        simp_all [branchFacts, heq, FactSem, Rel.holds] <;> omega

/-- Branch-derived facts refer only to the checked comparison operands. -/
theorem branchFacts_indices {st : AbsState} {a r : Nat} {rel : Rel}
    (ha : regIndexOk a) (hr : regIndexOk r) :
    ∀ f ∈ branchFacts st a r rel, factIndexOk f := by
  intro f hf
  by_cases heq : r = a
  · simp [branchFacts, heq] at hf
  · cases rel <;> simp_all [branchFacts, factIndexOk]
    rcases hf with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [factIndexOk, ha, hr]

/-- The successful interval-refinement case preserves the full relational
state, including newly recorded facts and the subsequent tightening pass. -/
theorem refine_core_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} {cmp : Cmp} {rel : Rel}
    {a₁ a₂ b₁ b₂ x₁ x₂ y₁ y₂ : Nat} (w : StackWindow)
    (h : LowEq p bytes off st s₁ s₂) (hidx : st.indicesOk) (hcmp : cmpIndexOk cmp)
    (ha : ival (st.get cmp.a) = some (a₁, a₂))
    (hb : opndIval st cmp.b = some (b₁, b₂))
    (hrel : rel.holds (regAt s₁ cmp.a).toNat (operand s₁ cmp.b).toNat)
    (hresult : refineI rel a₁ a₂ b₁ b₂ = some ((x₁,x₂),(y₁,y₂))) :
    let regs := regSet st.regs cmp.a (.num x₁ x₂)
    let regs := match cmp.b with
      | .reg r => if r == cmp.a then regs else regSet regs r (.num y₁ y₂)
      | .imm _ => regs
    let facts := match cmp.b with
      | .reg r => branchFacts st cmp.a r rel
      | .imm _ => []
    LowEq p bytes off (AbsState.tighten w { st with regs := regs, rel := (st.rel ++ facts).eraseDups }) s₁ s₂ := by
  dsimp only
  have hregs := refine_registers_sound h hcmp ha hb hrel hresult
  have heqa := AbsVal.sem_public (h.regs cmp.a hcmp.1.1 hcmp.1.2) (ival_public ha)
  have heqb := opndIval_equal h hcmp.2 hb
  have hrel₂ : rel.holds (regAt s₂ cmp.a).toNat (operand s₂ cmp.b).toNat := by
    simpa only [← heqa, ← heqb] using hrel
  have hnew : ∀ f ∈ (match cmp.b with
      | .reg r => branchFacts st cmp.a r rel
      | .imm _ => []), FactSem f s₁ ∧ FactSem f s₂ := by
    cases hop : cmp.b with
    | imm n => simp [hop]
    | reg r =>
      have hr : regIndexOk r := by simpa [opndIndexOk, hop] using hcmp.2
      apply branchFacts_sound h hcmp.1 hr
      · simpa [operand, hop] using hrel
      · simpa [operand, hop] using hrel₂
  have hnewidx : ∀ f ∈ (match cmp.b with
      | .reg r => branchFacts st cmp.a r rel
      | .imm _ => []), factIndexOk f := by
    cases hop : cmp.b with
    | imm n => simp [hop]
    | reg r =>
      have hr : regIndexOk r := by simpa [opndIndexOk, hop] using hcmp.2
      exact branchFacts_indices hcmp.1 hr
  apply AbsState.tighten_sound w
  · apply hregs.withFacts
    intro f hf
    simp only [List.mem_eraseDups, List.mem_append] at hf
    rcases hf with hf | hf
    · exact h.facts f hf
    · exact hnew f hf
  · refine ⟨hidx.1, ?_, hidx.2.2⟩
    intro f hf
    simp only [List.mem_eraseDups, List.mem_append] at hf
    rcases hf with hf | hf
    · exact hidx.2.1 f hf
    · exact hnewidx f hf

/-- For a concrete state satisfying the relation, branch refinement never
discards the observed branch as infeasible. -/
theorem refine_feasible {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow) (cond : BitVec 4) (taken : Bool)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (ht : M0Crypto.Thumb.condPassed cond s₁ = taken) :
    ∃ st', refine w st cond.toNat taken = some st' := by
  cases hc : st.fl.cmp with
  | none => simp [refine, hc]
  | some c =>
    cases hr : condRel cond.toNat taken with
    | none => simp [refine, hc, hr]
    | some rel =>
      by_cases hz : c.zOnly && !(rel matches .eq | .ne)
      · cases rel <;> simp_all [refine]
      · have hcmp := (h.comparison c hc).1
        have hci := hidx.1 c hc
        have hzr : c.zOnly = true → rel = .eq ∨ rel = .ne := by
          cases rel <;> simp_all
        have hrelation := condRel_sound cond taken rel hcmp hr ht hzr
        cases hleft : ival (st.get c.a) with
        | none => simp [refine, hc, hr, hz, hleft]
        | some left =>
          rcases left with ⟨a₁, a₂⟩
          cases hright : opndIval st c.b with
          | none => simp [refine, hc, hr, hz, hleft, hright]
          | some right =>
            rcases right with ⟨b₁, b₂⟩
            have ha := interval_bounds (h.regs c.a hci.1.1 hci.1.2) hleft
            have hb := opndIval_bounds h hci.2 hright
            obtain ⟨x₁, x₂, y₁, y₂, hresult, _⟩ :=
              refineI_sound rel a₁ a₂ b₁ b₂ _ _ ha.1 ha.2.1 hb.1 hb.2.1 hrelation
            cases rel <;> simp_all [refine]

/-- If the observed branch is taken, its computed refinement preserves the
relational state. Feasibility is established separately by `refine_feasible`. -/
theorem refine_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st st' : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow) (cond : BitVec 4) (taken : Bool)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (ht : M0Crypto.Thumb.condPassed cond s₁ = taken)
    (href : refine w st cond.toNat taken = some st') :
    LowEq p bytes off st' s₁ s₂ := by
  cases hc : st.fl.cmp with
  | none =>
    have heq : st = st' := by simpa [refine, hc] using href
    simpa [← heq] using h
  | some c =>
    cases hr : condRel cond.toNat taken with
    | none =>
      have heq : st = st' := by simpa [refine, hc, hr] using href
      simpa [← heq] using h
    | some rel =>
      by_cases hz : c.zOnly && !(rel matches .eq | .ne)
      · have heq : st = st' := by
          cases rel <;> simp_all [refine]
        simpa [← heq] using h
      · have hcmp := (h.comparison c hc).1
        have hci := hidx.1 c hc
        have hzr : c.zOnly = true → rel = .eq ∨ rel = .ne := by
          cases rel <;> simp_all
        have hrelation := condRel_sound cond taken rel hcmp hr ht hzr
        cases hleft : ival (st.get c.a) with
        | none =>
          have heq : st = st' := by simpa [refine, hc, hr, hleft] using href
          simpa [← heq] using h
        | some left =>
          rcases left with ⟨a₁, a₂⟩
          cases hright : opndIval st c.b with
          | none =>
            have heq : st = st' := by simpa [refine, hc, hr, hleft, hright] using href
            simpa [← heq] using h
          | some right =>
            rcases right with ⟨b₁, b₂⟩
            have ha := interval_bounds (h.regs c.a hci.1.1 hci.1.2) hleft
            have hb := opndIval_bounds h hci.2 hright
            obtain ⟨x₁, x₂, y₁, y₂, hresult, _⟩ :=
              refineI_sound rel a₁ a₂ b₁ b₂ _ _ ha.1 ha.2.1 hb.1 hb.2.1 hrelation
            have hcore := refine_core_sound w h hidx hci hleft hright hrelation hresult
            cases hop : c.b with
            | imm n =>
              cases rel <;> simp_all [refine, branchFacts]
            | reg r =>
              cases rel <;> simp_all [refine, branchFacts]

/-- The observed branch has a refined successor and that successor preserves
the relational state. -/
theorem refine_observed {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State} (w : StackWindow) (cond : BitVec 4) (taken : Bool)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂)
    (ht : M0Crypto.Thumb.condPassed cond s₁ = taken) :
    ∃ st', refine w st cond.toNat taken = some st' ∧ LowEq p bytes off st' s₁ s₂ := by
  obtain ⟨st', href⟩ := refine_feasible w cond taken hidx h ht
  exact ⟨st', href, refine_sound w cond taken hidx h ht href⟩

end M0Crypto.Release.ConstantTime
