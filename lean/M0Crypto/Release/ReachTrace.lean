import Lean
import M0Crypto.Release.ReachSteps
import M0Crypto.Sym.Access
import M0Crypto.Sym.Norm

set_option linter.unusedSimpArgs false

/-!
# `ReachT`: `ReachS` with a condition on the trace

`ReachT base P s Q Φ` is `ReachS base P s Q` whose run's trace also satisfies `Φ`. Its rules
compose trace conditions from the pieces of a run (`Tr.is`, `Tr.cat`, `Tr.cond`), so one proof
of a run states both what it reaches and what it emits.

A constant-time proof uses it with the trace condition an unknown `?Φ base P` of the public
values `P`, fixed before the state is introduced. Each rule's trace piece then has to be a term
in `base` and `P`: Lean assigns `?Φ` by pattern unification, and a piece that still mentions
the state is rejected. `Tr.Uniq` closes such a proof: a condition built from `Tr.is`, `Tr.cat`
and `Tr.cond` pins down one trace.

A straight-line block's trace is that of a state with only its pc and the registers `L` set
(`blockTr`), when its pcs and access addresses read only those registers (`traceOk`, decided):
the proof shows the values of `L`, not the trace.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-! ## Trace conditions -/

abbrev TrP := List Event → Prop

namespace Tr

/-- Exactly the trace `T`. -/
def is (T : List Event) : TrP := fun tr => tr = T

/-- A trace satisfying `Φ`, then one satisfying `Ψ`. -/
def cat (Φ Ψ : TrP) : TrP := fun tr => ∃ a b, tr = a ++ b ∧ Φ a ∧ Ψ b

/-- `Φ` if `b`, else `Ψ`. -/
def cond (b : Bool) (Φ Ψ : TrP) : TrP := fun tr => (b = true → Φ tr) ∧ (b = false → Ψ tr)

/-- Passes `j`, `j + 1`, … of a loop, `k` of them, each satisfying `Φ` of its index, then `Ψ`. -/
def rep (Φ : Nat → TrP) (j : Nat) : Nat → TrP → TrP
  | 0, Ψ => Ψ
  | k + 1, Ψ => cat (Φ j) (rep Φ (j + 1) k Ψ)

/-- At most one trace satisfies `Φ`. -/
def Uniq (Φ : TrP) : Prop := ∀ a b, Φ a → Φ b → a = b

theorem uniq_is (T : List Event) : Uniq (is T) := fun _ _ ha hb => ha.trans hb.symm

theorem uniq_cat {Φ Ψ : TrP} (h1 : Uniq Φ) (h2 : Uniq Ψ) : Uniq (cat Φ Ψ) := by
  rintro _ _ ⟨a, b, rfl, ha, hb⟩ ⟨a', b', rfl, ha', hb'⟩
  rw [h1 a a' ha ha', h2 b b' hb hb']

theorem uniq_cond {b : Bool} {Φ Ψ : TrP} (h1 : Uniq Φ) (h2 : Uniq Ψ) : Uniq (cond b Φ Ψ) := by
  intro x y hx hy
  cases b
  · exact h2 x y (hx.2 rfl) (hy.2 rfl)
  · exact h1 x y (hx.1 rfl) (hy.1 rfl)

theorem uniq_rep {Φ : Nat → TrP} {Ψ : TrP} (h1 : ∀ j, Uniq (Φ j)) (h2 : Uniq Ψ) :
    ∀ j k, Uniq (rep Φ j k Ψ)
  | _, 0 => h2
  | j, k + 1 => uniq_cat (h1 j) (uniq_rep h1 h2 (j + 1) k)

/-- Some trace satisfies `Φ`. -/
def Ex (Φ : TrP) : Prop := ∃ tr, Φ tr

theorem ex_is (T : List Event) : Ex (is T) := ⟨T, rfl⟩

theorem ex_cat {Φ Ψ : TrP} (h1 : Ex Φ) (h2 : Ex Ψ) : Ex (cat Φ Ψ) :=
  let ⟨a, ha⟩ := h1; let ⟨b, hb⟩ := h2; ⟨a ++ b, a, b, rfl, ha, hb⟩

theorem ex_cond {b : Bool} {Φ Ψ : TrP} (h1 : Ex Φ) (h2 : Ex Ψ) : Ex (cond b Φ Ψ) := by
  cases b
  · obtain ⟨a, ha⟩ := h2; exact ⟨a, nofun, fun _ => ha⟩
  · obtain ⟨a, ha⟩ := h1; exact ⟨a, fun _ => ha, nofun⟩

theorem ex_rep {Φ : Nat → TrP} {Ψ : TrP} (h1 : ∀ j, Ex (Φ j)) (h2 : Ex Ψ) : ∀ j k, Ex (rep Φ j k Ψ)
  | _, 0 => h2
  | j, k + 1 => ex_cat (h1 j) (ex_rep h1 h2 (j + 1) k)

theorem cat_assoc {Φ Ψ Χ : TrP} : ∀ tr, cat Φ (cat Ψ Χ) tr → cat (cat Φ Ψ) Χ tr := by
  rintro _ ⟨a, _, rfl, ha, b, c, rfl, hb, hc⟩
  exact ⟨a ++ b, c, by rw [List.append_assoc], ⟨a, b, rfl, ha, hb⟩, hc⟩

theorem cat_is_cons {e : Event} {l : List Event} {Ψ : TrP} {tr : List Event}
    (h : cat (is [e]) (cat (is l) Ψ) tr) : cat (is (e :: l)) Ψ tr := by
  obtain ⟨a, b, rfl, rfl, c, d, rfl, rfl, hd⟩ := h
  exact ⟨_, d, rfl, rfl, hd⟩

theorem cat_nil {Φ : TrP} : ∀ tr, cat Φ (is []) tr → Φ tr := by
  rintro _ ⟨a, b, rfl, ha, rfl⟩; rwa [List.append_nil]

theorem cat_mono {Φ Φ' Ψ Ψ' : TrP} (h1 : ∀ t, Φ t → Φ' t) (h2 : ∀ t, Ψ t → Ψ' t) :
    ∀ t, cat Φ Ψ t → cat Φ' Ψ' t := fun _ ⟨a, b, he, ha, hb⟩ => ⟨a, b, he, h1 a ha, h2 b hb⟩

/-- **The trace of a code fragment** that ends in its caller's continuation: a transformer `Θ`
of the continuation's condition that keeps one trace, such that `H Θ`. A fragment lemma states
its public values before `HasK`, and the rest inside `H`, so `Θ` depends on its public values
alone. Its callers name `Θ` by the closed term `h.tr`. -/
def HasK (H : (TrP → TrP) → Prop) : Prop :=
  ∃ Θ : TrP → TrP, (∀ Ψ, Uniq Ψ → Uniq (Θ Ψ)) ∧ (∀ Ψ, Ex Ψ → Ex (Θ Ψ)) ∧ H Θ

/-- The trace transformer of a fragment. -/
noncomputable def HasK.tr {H : (TrP → TrP) → Prop} (h : HasK H) : TrP → TrP := h.choose

theorem HasK.uniq {H : (TrP → TrP) → Prop} (h : HasK H) {Ψ : TrP} (hu : Uniq Ψ) :
    Uniq (h.tr Ψ) :=
  h.choose_spec.1 Ψ hu

theorem HasK.ex {H : (TrP → TrP) → Prop} (h : HasK H) {Ψ : TrP} (hx : Ex Ψ) : Ex (h.tr Ψ) :=
  h.choose_spec.2.1 Ψ hx

theorem HasK.run {H : (TrP → TrP) → Prop} (h : HasK H) : H h.tr := h.choose_spec.2.2

/-- A fragment's trace from its proof `h` with the transformer left open (`?Θ`), its uniqueness
and its existence, proved last by `uniq_tac` and `ex_tac`. -/
theorem HasK.intro {H : (TrP → TrP) → Prop} {Θ : TrP → TrP} (h : H Θ)
    (hu : ∀ Ψ, Uniq Ψ → Uniq (Θ Ψ)) (hx : ∀ Ψ, Ex Ψ → Ex (Θ Ψ)) : HasK H := ⟨Θ, hu, hx, h⟩

theorem cat_is_is (a b : List Event) : cat (is a) (is b) = is (a ++ b) :=
  funext fun _ => propext ⟨fun ⟨_, _, h, h1, h2⟩ => h1 ▸ h2 ▸ h, fun h => ⟨a, b, h, rfl, rfl⟩⟩

end Tr

/-- `uniq_tac` closes `Tr.Uniq Φ` for a condition built from `Tr.is`, `Tr.cat` and `Tr.cond`. -/
macro "uniq_tac" : tactic => `(tactic|
  repeat (first | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_cond | apply Tr.uniq_rep |
    apply Tr.HasK.uniq | assumption | intro))

/-- `ex_tac` closes `Tr.Ex Φ` for a condition built like those of `uniq_tac`. -/
macro "ex_tac" : tactic => `(tactic|
  repeat (first | exact Tr.ex_is _ | apply Tr.ex_cat | apply Tr.ex_cond | apply Tr.ex_rep |
    apply Tr.HasK.ex | assumption | intro))

open Lean Elab Tactic Meta in
/-- `trefine e`: `refine' e`, then the new goals that are propositions first and the data last.
A rule's unassigned trace pieces become data goals; the proofs of the propositions assign
them. -/
elab "trefine " e:term : tactic => do
  let rest := (← getGoals).drop 1
  evalTactic (← `(tactic| refine' $e))
  let gs ← getGoals
  let new := gs.filter fun g => !rest.contains g
  let mut ps : Array MVarId := #[]
  let mut ds : Array MVarId := #[]
  for g in new do
    if ← isProp (← g.getType) then ps := ps.push g else ds := ds.push g
  setGoals ((ps ++ ds).toList ++ rest)

/-! ## The judgment -/

def ReachT [CodeBytes B BS] (base : Word) (P : State → Event → Prop) (s : State) (Q : State → Prop) (Φ : TrP) :
    Prop :=
  ∃ n t tr, runH B base n s = .ok (t, tr) ∧ StepsOk base P n s ∧ Q t ∧ Φ tr

variable {base : Word} {P : State → Event → Prop}

theorem ReachT.toS {s : State} {Q : State → Prop} {Φ : TrP} (h : ReachT base P s Q Φ) :
    ReachS base P s Q :=
  let ⟨n, t, tr, hr, hok, hq, _⟩ := h; ⟨n, t, tr, hr, hok, hq⟩

theorem ReachS.toT {s : State} {Q : State → Prop} (h : ReachS base P s Q) :
    ReachT base P s Q fun _ => True :=
  let ⟨n, t, tr, hr, hok, hq⟩ := h; ⟨n, t, tr, hr, hok, hq, trivial⟩

theorem ReachT.done {s : State} {Q : State → Prop} (h : Q s) : ReachT base P s Q (Tr.is []) :=
  ⟨0, s, [], rfl, trivial, h, rfl⟩

theorem ReachT.mono {P' : State → Event → Prop} {s : State} {Q Q' : State → Prop} {Φ Φ' : TrP}
    (h : ReachT base P s Q Φ) (hp : ∀ x e, P x e → P' x e) (hq : ∀ t, Q t → Q' t)
    (hΦ : ∀ tr, Φ tr → Φ' tr) : ReachT base P' s Q' Φ' :=
  let ⟨n, t, tr, hr, hok, hQ, hT⟩ := h; ⟨n, t, tr, hr, hok.mono hp, hq t hQ, hΦ tr hT⟩

/-- A run with an equal trace condition. A fragment proof ends with `retrace … rfl` once its
trace condition has no unassigned pieces, so it can be abstracted over the continuation. -/
theorem ReachT.retrace {s : State} {Q : State → Prop} {Φ Φ' : TrP} (h : ReachT base P s Q Φ)
    (e : Φ = Φ') : ReachT base P s Q Φ' :=
  e ▸ h

/-- A run to `R`, then from every `R` state a run to `Q`. -/
theorem ReachT.seq {s : State} {R Q : State → Prop} {Φ Ψ : TrP} (h : ReachT base P s R Φ)
    (k : ∀ t, R t → ReachT base P t Q Ψ) : ReachT base P s Q (Tr.cat Φ Ψ) := by
  obtain ⟨n, t, tr, hr, hok, hR, hΦ⟩ := h
  obtain ⟨m, u, tail, hr', hok', hq, hΨ⟩ := k t hR
  refine ⟨n + m, u, tr ++ tail, ?_, StepsOk.append hr hok hok', hq, tr, tail, rfl, hΦ, hΨ⟩
  rw [runH_add, hr]; simp only [hr']

/-- One Harvard step in front. -/
theorem ReachT.cons {s s1 : State} {Q : State → Prop} {Ψ : TrP} {e : Event}
    (hs : stepH B base s = .ok (s1, e)) (hp : P s e) (h : ReachT base P s1 Q Ψ) :
    ReachT base P s Q (Tr.cat (Tr.is [e]) Ψ) := by
  obtain ⟨n, u, tr, hr, hok, hq, hΨ⟩ := h
  exact ⟨n + 1, u, e :: tr, by rw [runH_one_step n hs, hr], StepsOk.cons hs hp hok, hq,
    [e], tr, rfl, rfl, hΨ⟩

/-- One instruction. -/
theorem ReachT.step {s s1 : State} {Q : State → Prop} {Ψ : TrP} (hb : base.toNat % 2 = 0)
    (off : Nat) (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hp : P s ⟨s.pc, i, i.accesses s⟩) (hq : ReachT base P s1 Q Ψ) :
    ReachT base P s Q (Tr.cat (Tr.is [⟨s.pc, i, i.accesses s⟩]) Ψ) :=
  ReachT.cons (stepH_of_instr hb B_lt hpc ho hi hsz ha hex) hp hq

/-- A fall-through block. -/
theorem ReachT.block {Q : State → Prop} {Ψ : TrP} (hb : base.toNat % 2 = 0) :
    ∀ (is : List Instr) (off : Nat) (s : State), s.pc = base + BitVec.ofNat 32 off →
      off % 2 = 0 → seqAt B off is = true → is.all Instr.falls = true →
      alignedAll is s = true → BlockOk P is s → ReachT base P (execAll is s) Q Ψ →
      ReachT base P s Q (Tr.cat (Tr.is (traceAll is s)) Ψ)
  | [], _, _, _, _, _, _, _, _, hq => hq.mono (fun _ _ h => h) (fun _ h => h)
      fun tr h => ⟨[], tr, rfl, rfl, h⟩
  | i :: is, off, s, hpc, ho, hseq, hf, ha, hok, hq => by
    simp only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hseq
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [alignedAll, Bool.and_eq_true] at ha
    have hex := exec_ok_of_falls hf.1 s
    have hpc1 : (i.next s).pc = base + BitVec.ofNat 32 (off + i.size) := by
      rw [exec_pc hf.1 hex, hpc, ofNat_add_assoc]
    exact (ReachT.step hb off i hpc ho hseq.1.1 hseq.1.2 ha.1 hex hok.1
      (ReachT.block hb is (off + i.size) (i.next s) hpc1 (by have := instr_size_even i; omega)
        hseq.2 hf.2 ha.2 hok.2 hq)).mono (fun _ _ h => h) (fun _ h => h)
      fun _ h => Tr.cat_is_cons h

/-- A conditional branch at `off` with target offset `tgt`; the trace after it is chosen by
`b`, the branch's outcome. -/
theorem ReachT.bcond {s : State} {Q : State → Prop} {ΨT ΨF : TrP} {b : Bool}
    (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ BS)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .bcond cond imm, []⟩) (hc : condPassed cond s = b)
    (hT : condPassed cond s = true →
      ReachT base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q ΨT)
    (hF : condPassed cond s = false →
      ReachT base P (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q ΨF) :
    ReachT base P s Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 off, .bcond cond imm, []⟩]) (Tr.cond b ΨT ΨF)) := by
  have hsz' : off + (Instr.bcond cond imm).size ≤ B.length := by rw [B_len]; exact hsz
  rw [← hpc]
  cases b
  · refine (ReachT.step hb off _ hpc ho hi hsz' (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, Bool.false_eq_true, ite_false]; rfl)
      (by simpa [Instr.accesses] using hp) ?_).mono (fun _ _ h => h) (fun _ h => h)
      (Tr.cat_mono (fun _ h => by simpa [Instr.accesses] using h)
        fun _ h => ⟨fun e => absurd e (by decide), fun _ => h⟩)
    have := hF hc
    rwa [show s.pc + BitVec.ofNat 32 (Instr.bcond cond imm).size =
        base + BitVec.ofNat 32 (off + 2) by rw [hpc, ofNat_add_assoc]; rfl]
  · refine (ReachT.step hb off _ hpc ho hi hsz' (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, ite_true]; rfl)
      (by simpa [Instr.accesses] using hp) ?_).mono (fun _ _ h => h) (fun _ h => h)
      (Tr.cat_mono (fun _ h => by simpa [Instr.accesses] using h)
        fun _ h => ⟨fun _ => h, fun e => absurd e (by decide)⟩)
    have := hT hc
    rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- An unconditional branch at `off` with target offset `tgt`. -/
theorem ReachT.b {s : State} {Q : State → Prop} {Ψ : TrP} (hb : base.toNat % 2 = 0)
    (off tgt : Nat) (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ BS)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .b imm, []⟩)
    (hq : ReachT base P (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q Ψ) :
    ReachT base P s Q (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 off, .b imm, []⟩]) Ψ) := by
  rw [← hpc]
  refine (ReachT.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by simpa [Instr.accesses] using hp) ?_).mono
    (fun _ _ h => h) (fun _ h => h) (Tr.cat_mono (fun _ h => by simpa [Instr.accesses] using h)
      fun _ h => h)
  rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
    rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- A branch-with-link at `off` with target offset `tgt`. -/
theorem ReachT.bl {s : State} {Q : State → Prop} {Ψ : TrP} (hb : base.toNat % 2 = 0)
    (off tgt : Nat) (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ BS)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hp : P s ⟨s.pc, .bl imm, []⟩)
    (hq : ReachT base P ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q Ψ) :
    ReachT base P s Q (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 off, .bl imm, []⟩]) Ψ) := by
  rw [← hpc]
  refine (ReachT.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by simpa [Instr.accesses] using hp) ?_).mono
    (fun _ _ h => h) (fun _ h => h) (Tr.cat_mono (fun _ h => by simpa [Instr.accesses] using h)
      fun _ h => h)
  rw [show s.pc + 4#32 = base + BitVec.ofNat 32 (off + 4) by rw [hpc, ofNat_add_assoc],
    show base + BitVec.ofNat 32 (off + 4) + imm.signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [← ht, ← ofNat_add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]]
  exact hq

/-! ## Block traces from registers -/

end M0Crypto.Release

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)

mutual
/-- The expression reads no memory, no flags and no register outside `L`. -/
def SExpr.regsIn (L : List Reg) : SExpr → Bool
  | .reg0 r => L.contains r
  | .const _ => true
  | .add a b | .sub a b | .and a b | .or a b | .xor a b | .mul a b => a.regsIn L && b.regsIn L
  | .not a | .uxth a | .lsl a _ | .lsr a _ | .rotl a _ | .asr a _ | .rev a => a.regsIn L
  | .awc a b c | .ror a b c | .lslR a b c | .lsrR a b c => a.regsIn L && b.regsIn L && c.regsIn L
  | .ld32 _ _ | .ld16 _ _ | .ld8 _ _ => false

def SBool.regsIn (L : List Reg) : SBool → Bool
  | .const _ => true
  | .msb a | .isZero a | .lsrC a _ | .asrC a _ => a.regsIn L
  | .lslC a _ c => a.regsIn L && c.regsIn L
  | .awcC a b c | .awcV a b c | .rorC a b c | .lslRC a b c | .lsrRC a b c =>
    a.regsIn L && b.regsIn L && c.regsIn L
  | .n0 | .z0 | .c0 | .v0 => false
end

mutual
theorem SExpr.denote_regsIn {L : List Reg} {s s' : State} (h : ∀ r ∈ L, s.regs r = s'.regs r) :
    ∀ e : SExpr, e.regsIn L = true → e.denote s = e.denote s'
  | .reg0 r, he => h r (by simpa [SExpr.regsIn] using he)
  | .const _, _ => rfl
  | .add a b, he | .sub a b, he | .and a b, he | .or a b, he | .xor a b, he | .mul a b, he => by
    simp only [SExpr.regsIn, Bool.and_eq_true] at he
    simp only [SExpr.denote, SExpr.denote_regsIn h a he.1, SExpr.denote_regsIn h b he.2]
  | .not a, he | .uxth a, he | .lsl a _, he | .lsr a _, he | .rotl a _, he | .asr a _, he
  | .rev a, he => by
    simp only [SExpr.regsIn] at he
    simp only [SExpr.denote, SExpr.denote_regsIn h a he]
  | .awc a b c, he | .ror a b c, he | .lslR a b c, he | .lsrR a b c, he => by
    simp only [SExpr.regsIn, Bool.and_eq_true] at he
    simp only [SExpr.denote, SExpr.denote_regsIn h a he.1.1, SExpr.denote_regsIn h b he.1.2,
      SBool.denote_regsIn h c he.2]
  | .ld32 _ _, he | .ld16 _ _, he | .ld8 _ _, he => by simp [SExpr.regsIn] at he

theorem SBool.denote_regsIn {L : List Reg} {s s' : State} (h : ∀ r ∈ L, s.regs r = s'.regs r) :
    ∀ e : SBool, e.regsIn L = true → e.denote s = e.denote s'
  | .const _, _ => rfl
  | .msb a, he | .isZero a, he | .lsrC a _, he | .asrC a _, he => by
    simp only [SBool.regsIn] at he
    simp only [SBool.denote, SExpr.denote_regsIn h a he]
  | .lslC a _ c, he => by
    simp only [SBool.regsIn, Bool.and_eq_true] at he
    simp only [SBool.denote, SExpr.denote_regsIn h a he.1, SBool.denote_regsIn h c he.2]
  | .awcC a b c, he | .awcV a b c, he | .rorC a b c, he | .lslRC a b c, he | .lsrRC a b c, he => by
    simp only [SBool.regsIn, Bool.and_eq_true] at he
    simp only [SBool.denote, SExpr.denote_regsIn h a he.1.1, SExpr.denote_regsIn h b he.1.2,
      SBool.denote_regsIn h c he.2]
  | .n0, he | .z0, he | .c0, he | .v0, he => by simp [SBool.regsIn] at he
end

end M0Crypto.Sym

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

open M0Crypto.Sym in
/-- The pcs and access addresses of the block `is` read only the pc and the registers `L`. -/
def traceOk (is : List Instr) (L : List Reg) : Bool :=
  (symTrace is SState.init).all fun e =>
    e.1.regsIn (15 :: L) && e.2.2.all fun a => a.addr.regsIn (15 :: L)

/-- The state with pc `pc`, the registers `L` holding `vs`, and nothing else set. -/
def regState (pc : Word) (L : List Reg) (vs : List Word) : State where
  regs := fun r => if r = 15 then pc else ((L.zip vs).lookup r).getD 0
  n := false
  z := false
  c := false
  v := false
  mem := fun _ => 0

/-- The trace of the block `is` from pc `pc` with the registers `L` holding `vs`. -/
def blockTr (is : List Instr) (pc : Word) (L : List Reg) (vs : List Word) : List Event :=
  traceAll is (regState pc L vs)

theorem lookup_zip_map (f : Reg → Word) :
    ∀ (L : List Reg) (r : Reg), r ∈ L → (L.zip (L.map f)).lookup r = some (f r)
  | [], _, h => nomatch h
  | x :: L, r, h => by
    by_cases hx : r = x
    · subst hx; simp [List.lookup]
    · have : (r == x) = false := by simpa using hx
      simp only [List.map_cons, List.zip_cons_cons, List.lookup, this]
      exact lookup_zip_map f L r (by simpa [hx] using h)

/-- `s` and `regState` of its pc and the values of `L` agree on the pc and `L`. -/
theorem regState_agree {s : State} {L : List Reg} {pc : Word} (hpc : s.pc = pc) :
    ∀ r ∈ 15 :: L, s.regs r = (regState pc L (L.map s.regs)).regs r := by
  intro r hr
  by_cases h15 : r = 15
  · subst h15; simpa [regState, State.pc] using hpc
  · have hr' : r ∈ L := by simpa [h15] using hr
    simp [regState, h15, lookup_zip_map s.regs L r hr']

open M0Crypto.Sym in
/-- **A block's trace from its registers**: the block's pcs and addresses read only the pc and
`L`, so its trace from `s` is `blockTr` of `s`'s pc and the values of `L`. -/
theorem traceAll_blockTr {is : List Instr} {L : List Reg} {s : State} {pc : Word}
    {vs : List Word} (hf : is.all Instr.falls = true) (hok : traceOk is L = true)
    (hpc : s.pc = pc) (hv : L.map s.regs = vs) : traceAll is s = blockTr is pc L vs := by
  subst hv
  have hag := regState_agree (L := L) hpc
  have h1 := symTrace_sound is (sound_all hf) s SState.init
  have h2 := symTrace_sound is (sound_all hf) (regState pc L (L.map s.regs)) SState.init
  rw [SState.init_denote] at h1 h2
  rw [blockTr, ← h1, ← h2]
  apply List.map_congr_left
  intro e he
  have hk := List.all_eq_true.mp hok e he
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨pc', i, acc⟩ := e
  simp only [SEvent.denote, SExpr.denote_regsIn hag pc' hk.1, Event.mk.injEq, true_and]
  apply List.map_congr_left
  intro a ha
  simp only [SAccess.denote, SExpr.denote_regsIn hag a.addr (hk.2 a ha)]

end M0Crypto.Release
