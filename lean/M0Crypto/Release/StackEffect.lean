import M0Crypto.Release.TraceSpec
import M0Crypto.Release.RunStates
import M0Crypto.Thumb.SpBlock

/-!
# Byte effects of a trace

`Good sp0 n p tr` folds a trace over an effect state `p`: SP, and the bytes written since they
were last allocated (`U`). Each event must move SP as `spAfter` says, access the `n`-byte window
below `sp0` only at or above SP before or after it, and read window bytes only from `U`. After
the event, `U` holds the bytes at or above the new SP that were in `U` or that the event wrote.
A run from `sp0` whose trace is `Good` from the empty `U` keeps `TraceSpec.StackDiscipline`
(`discipline_of`). The fold composes over appended traces (`good_append`) and is monotone in
`U` (`Good.mono`), so callers state a callee's trace effect once and glue it.
-/

namespace M0Crypto.Release.StackEffect

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release.TraceSpec

/-- SP after `i` from `sp`: the moves of `push`, `pop`, `add sp` and `sub sp`; others keep it. -/
def spAfter : Instr → Word → Word
  | .push l lr, sp => sp - BitVec.ofNat 32 (4 * (bitCount l + lr.toNat))
  | .pop l pc, sp => sp + BitVec.ofNat 32 (4 * (bitCount l + pc.toNat))
  | .addSp k, sp => sp + BitVec.ofNat 32 (k.toNat * 4)
  | .subSp k, sp => sp - BitVec.ofNat 32 (k.toNat * 4)
  | _, sp => sp

/-- `spAfter` is exact for `i`: it moves SP as one of the four, or it does not write SP. -/
def spExact : Instr → Bool
  | .push .. | .pop .. | .addSp _ | .subSp _ => true
  | i => !(i.dsts.contains 13)

theorem exec_sp {i : Instr} {s t : State} (hi : spExact i = true) (h : i.exec s = .ok t) :
    t.regs 13 = spAfter i (s.regs 13) := by
  have hn : i.next s = t := by simp [Instr.next, h]
  cases i
  case push l lr => simp only [Instr.exec, Except.ok.injEq] at h; subst h; rfl
  case addSp k => simp only [Instr.exec, Except.ok.injEq] at h; subst h; rfl
  case subSp k => simp only [Instr.exec, Except.ok.injEq] at h; subst h; rfl
  case pop l pc =>
    simp only [Instr.exec] at h
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · cases h
    · simp only [Except.ok.injEq] at h; subst h; rfl
  all_goals
    rw [← hn]
    exact next_sp (by simpa [spExact, List.contains_eq_mem] using hi) s

theorem step_exec {u t : State} {e : Event} (h : step u = .ok (t, e)) :
    e.instr.exec u = .ok t ∧ e.accesses = e.instr.accesses u := by
  unfold step at h; simp only at h
  split at h; · cases h
  split at h; · cases h
  rename_i i _
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by assumption, rfl⟩
    · cases h
  · cases h

/-- Step `k` of a recorded run goes from `states[k]` to `states[k + 1]` with event `tr[k]`. -/
theorem runStates_at {stop : Word} :
    ∀ {fuel : Nat} {s : State} {states : List State} {tr : List Event},
    runStates stop fuel s = .ok (states, tr) → states[0]? = some s ∧
      ∀ k e, tr[k]? = some e → ∃ u t, states[k]? = some u ∧ states[k + 1]? = some t ∧
        step u = .ok (t, e)
  | 0, s, states, tr, h => by
    unfold runStates at h; split at h
    · cases h; simp
    · cases h
  | fuel + 1, s, states, tr, h => by
    unfold runStates at h
    split at h
    · cases h; simp
    · cases hs : step s with
      | error err => simp [hs] at h
      | ok pr =>
        obtain ⟨s', ev⟩ := pr
        simp only [hs] at h
        cases hr : runStates stop fuel s' with
        | error err => simp [hr] at h
        | ok pr =>
          obtain ⟨rest, es⟩ := pr
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h0, hk⟩ := runStates_at hr
          refine ⟨rfl, fun k e he => ?_⟩
          rcases k with _ | k
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he
            exact ⟨s, s', rfl, by simpa using h0, hs⟩
          · obtain ⟨u, t, hu, ht, hst⟩ := hk k e (by simpa using he)
            exact ⟨u, t, by simpa using hu, by simpa using ht, hst⟩

/-! ## The fold -/

/-- An effect state: SP, and the window bytes written since they were last allocated. -/
structure Ef where
  sp : Word
  U : Word → Prop

def Ef.step (sp0 : Word) (p : Ef) (e : Event) : Ef :=
  ⟨spAfter e.instr p.sp,
    fun y => AtOrAboveSp sp0 (spAfter e.instr p.sp) y ∧ (p.U y ∨ Writes e.accesses y)⟩

def Ef.run (sp0 : Word) (p : Ef) (tr : List Event) : Ef := tr.foldl (Ef.step sp0) p

/-- One event keeps the discipline from `p`. -/
def EvOk (sp0 : Word) (n : Nat) (p : Ef) (e : Event) : Prop :=
  spExact e.instr = true ∧
  (∀ y, (Reads e.accesses y ∨ Writes e.accesses y) → BelowEntry sp0 n y →
    AtOrAboveSp sp0 p.sp y ∨ AtOrAboveSp sp0 (spAfter e.instr p.sp) y) ∧
  (∀ y, Reads e.accesses y → BelowEntry sp0 n y → p.U y)

/-- **A trace keeps the discipline from `p`.** -/
def Good (sp0 : Word) (n : Nat) : Ef → List Event → Prop
  | _, [] => True
  | p, e :: tr => EvOk sp0 n p e ∧ Good sp0 n (p.step sp0 e) tr

variable {sp0 : Word} {n : Nat}

theorem run_append (p : Ef) (a b : List Event) : p.run sp0 (a ++ b) = (p.run sp0 a).run sp0 b := by
  simp [Ef.run, List.foldl_append]

theorem good_append : ∀ (p : Ef) (a b : List Event),
    Good sp0 n p (a ++ b) ↔ Good sp0 n p a ∧ Good sp0 n (p.run sp0 a) b
  | p, [], b => by simp [Good, Ef.run]
  | p, e :: a, b => by
    simp only [List.cons_append, Good, good_append _ a b, Ef.run, List.foldl_cons, and_assoc]

/-- `Good` and the final state are monotone in `U`. -/
theorem Good.mono : ∀ {p q : Ef} {tr : List Event}, p.sp = q.sp → (∀ y, p.U y → q.U y) →
    Good sp0 n p tr → Good sp0 n q tr ∧ (q.run sp0 tr).sp = (p.run sp0 tr).sp ∧
      ∀ y, (p.run sp0 tr).U y → (q.run sp0 tr).U y
  | p, q, [], hs, hU, _ => ⟨trivial, hs.symm, hU⟩
  | p, q, e :: tr, hs, hU, ⟨⟨hx, ha, hr⟩, hg⟩ => by
    have hs' : (p.step sp0 e).sp = (q.step sp0 e).sp := by simp only [Ef.step, hs]
    have hU' : ∀ y, (p.step sp0 e).U y → (q.step sp0 e).U y := fun y ⟨h1, h2⟩ =>
      ⟨hs ▸ h1, h2.imp_left (hU y)⟩
    obtain ⟨g, s, u⟩ := Good.mono hs' hU' hg
    exact ⟨⟨⟨hx, hs ▸ ha, fun y h1 h2 => hU y (hr y h1 h2)⟩, g⟩, s, u⟩

/-- `Good` at event `k`, from the state after the first `k` events. -/
theorem good_at {p : Ef} {tr : List Event} (h : Good sp0 n p tr) {k : Nat} {e : Event}
    (he : tr[k]? = some e) : EvOk sp0 n (p.run sp0 (tr.take k)) e := by
  have hk : k < tr.length := by
    rcases Nat.lt_or_ge k tr.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at he
  rw [← List.take_append_drop k tr, good_append] at h
  have hd : tr.drop k = e :: tr.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]; simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at he
    rw [he]
  rw [hd] at h; exact h.2.1

/-! ## Soundness -/

/-- **A `Good` run keeps the stack discipline** over the `n` bytes below its entry SP. -/
theorem discipline_of {stop : Word} {fuel : Nat} {s : State} {states : List State}
    {tr : List Event} (hr : runStates stop fuel s = .ok (states, tr)) (hsp : s.regs 13 = sp0)
    (hg : Good sp0 n ⟨sp0, fun _ => False⟩ tr) : StackDiscipline sp0 n states tr := by
  obtain ⟨h0, hk⟩ := runStates_at hr
  let p : Ef := ⟨sp0, fun _ => False⟩
  have hlen : ∀ k, tr[k]? ≠ none → k < tr.length := fun k h => by
    rcases Nat.lt_or_ge k tr.length with h' | h'
    · exact h'
    · exact absurd (List.getElem?_eq_none h') h
  have htake : ∀ k e, tr[k]? = some e → tr.take (k + 1) = tr.take k ++ [e] := fun k e he => by
    rw [List.take_add_one, he]; rfl
  -- the SP and the written bytes of each state
  have inv : ∀ k u, states[k]? = some u → k ≤ tr.length →
      u.regs 13 = (p.run sp0 (tr.take k)).sp ∧
      ∀ y, (p.run sp0 (tr.take k)).U y → WrittenSinceAllocated sp0 states tr k y := by
    intro k
    induction k with
    | zero =>
      intro u hu _
      rw [h0] at hu; cases hu
      exact ⟨hsp, fun y hy => hy.elim⟩
    | succ k ih =>
      intro u hu hle
      obtain ⟨e, he⟩ : ∃ e, tr[k]? = some e := ⟨tr[k], List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨u0, t, hu0, ht, hst⟩ := hk k e he
      have e0 : t = u := Option.some.inj (ht.symm.trans hu); subst e0
      obtain ⟨i1, i2⟩ := ih u0 hu0 (by omega)
      have hev := good_at hg he
      obtain ⟨hex, -⟩ := step_exec hst
      have hs1 : t.regs 13 = (p.run sp0 (tr.take (k + 1))).sp := by
        rw [htake k e he, run_append, exec_sp hev.1 hex, i1]; rfl
      refine ⟨hs1, fun y hy => ?_⟩
      rw [htake k e he, run_append] at hy
      obtain ⟨hab, hy⟩ := hy
      have hab' : ∀ i v, k < i → i ≤ k + 1 → states[i]? = some v → AtOrAboveSp sp0 v.sp y :=
        fun i v h1 h2 hv => by
          obtain rfl : i = k + 1 := by omega
          rw [hu] at hv; cases hv
          show AtOrAboveSp sp0 (t.regs 13) y
          rw [hs1, htake k e he, run_append]; exact hab
      rcases hy with hy | hw
      · obtain ⟨j, hj, hwj, hall⟩ := i2 y hy
        refine ⟨j, by omega, hwj, fun i v h1 h2 hv => ?_⟩
        rcases Nat.lt_or_ge k i with h3 | h3
        · exact hab' i v h3 h2 hv
        · exact hall i v h1 h3 hv
      · exact ⟨k, by omega, ⟨e, he, hw⟩, hab'⟩
  refine ⟨fun k e u u' he hu hu' y hy hb => ?_, fun k e he y hy hb => ?_⟩
  · have hl := hlen k (by simp [he])
    obtain ⟨u0, t, hu0, ht, hst⟩ := hk k e he
    have e0 : u0 = u := Option.some.inj (hu0.symm.trans hu); subst e0
    have e1 : t = u' := Option.some.inj (ht.symm.trans hu'); subst e1
    have hev := good_at hg he
    have e1 := (inv k u0 hu0 (by omega)).1
    have e2 := (inv (k + 1) t ht hl).1
    rw [htake k e he, run_append] at e2
    show AtOrAboveSp sp0 (u0.regs 13) y ∨ AtOrAboveSp sp0 (t.regs 13) y
    rw [e1, e2]; exact hev.2.1 y hy hb
  · have hl := hlen k (by simp [he])
    obtain ⟨u0, t, hu0, -, -⟩ := hk k e he
    exact (inv k u0 hu0 (by omega)).2 y ((good_at hg he).2.2 y hy hb)

end M0Crypto.Release.StackEffect
