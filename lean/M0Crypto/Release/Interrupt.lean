import M0Crypto.Release.TraceSpec
import M0Crypto.Release.RunStates
import M0Crypto.Release.FrameBase
import M0Crypto.Thumb.ExecReads

set_option linter.unusedSimpArgs false

/-!
# Interrupted calls

`TraceSpec.irunStates` runs a call with a handler before each instruction. A handler restores
the registers and flags and preserves every byte the call may read or write (`P`) outside the
`K` bytes below SP. If every stack byte the uninterrupted run reads was written since SP last
moved to or below it (`TraceSpec.StackReadsWritten`), the run reads only bytes of `P`, and no
byte of `P` lies in the `K` bytes below the window, then every byte a handler changes is either
never read by the call or written again by the call before the call reads it. So the interrupted
run executes the same steps with the same events, its registers and flags are those of the
uninterrupted run, and its memory agrees with it on `P` outside the window
(`interruptedCall_of`).
-/

namespace M0Crypto.Release.Interrupt
open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.TraceSpec

/-- The run `tr` writes `y` before any step that reads it. -/
def DeadIn (tr : List Event) (y : Word) : Prop :=
  ∀ (k : Nat) (e : Event), tr[k]? = some e → Reads e.accesses y →
    ∃ j < k, ∃ e' : Event, tr[j]? = some e' ∧ Writes e'.accesses y

theorem deadIn_tail {e : Event} {tr : List Event} {y : Word} (h : DeadIn (e :: tr) y)
    (hw : ¬ Writes e.accesses y) : DeadIn tr y := by
  intro k e₂ hk hr
  obtain ⟨j, hj, e', he', hw'⟩ := h (k + 1) e₂ (by simpa using hk) hr
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he'
    subst he'
    exact absurd hw' hw
  | succ j => exact ⟨j, by omega, e', by simpa using he', hw'⟩

theorem deadIn_head {e : Event} {tr : List Event} {y : Word} (h : DeadIn (e :: tr) y) :
    ¬ Reads e.accesses y := fun hr => by
  obtain ⟨j, hj, -⟩ := h 0 e rfl hr
  omega

/-- `w` stands for `s` in the run `tr`: equal registers and flags, and memory that differs only
on bytes of `Z` that `tr` writes before reading. -/
structure Stands (Z : Word → Prop) (tr : List Event) (s w : State) : Prop where
  regs : w.regs = s.regs
  n : w.n = s.n
  z : w.z = s.z
  c : w.c = s.c
  v : w.v = s.v
  mem : ∀ y, w.mem y ≠ s.mem y → Z y ∧ DeadIn tr y

/-- Equal registers and flags, and memory equal outside `Z`. -/
structure Agree (Z : Word → Prop) (s w : State) : Prop where
  regs : w.regs = s.regs
  n : w.n = s.n
  z : w.z = s.z
  c : w.c = s.c
  v : w.v = s.v
  mem : ∀ y, ¬ Z y → w.mem y = s.mem y

theorem Stands.agree {Z : Word → Prop} {tr : List Event} {s w : State} (h : Stands Z tr s w) :
    Agree Z s w :=
  ⟨h.regs, h.n, h.z, h.c, h.v, fun y hy => by
    by_cases he : w.mem y = s.mem y
    · exact he
    · exact absurd (h.mem y he).1 hy⟩

theorem state_eq_withMem {s w : State} (hr : w.regs = s.regs) (hn : w.n = s.n) (hz : w.z = s.z)
    (hc : w.c = s.c) (hv : w.v = s.v) : w = { s with mem := w.mem } := by
  cases w; cases s
  simp only at hr hn hz hc hv
  subst hr hn hz hc hv
  rfl

theorem accesses_withMem (i : Instr) (s : State) (m : Mem) :
    i.accesses { s with mem := m } = i.accesses s := by
  cases i <;> rfl

/-- A step in a memory that agrees with the state's memory on the fetched instruction and on
the bytes the step reads: the same event, registers and flags, and the same memory wherever the
two memories agreed or the step writes. -/
theorem step_withMem {s t : State} {e : Event} {m : Mem} (hst : step s = .ok (t, e))
    (hdec : decode (fetch16 m s.pc) (fetch16 m (s.pc + 2#32)) =
      decode (fetch16 s.mem s.pc) (fetch16 s.mem (s.pc + 2#32)))
    (hrd : ∀ y, Reads e.accesses y → m y = s.mem y) :
    ∃ t', step { s with mem := m } = .ok (t', e) ∧ t'.regs = t.regs ∧ t'.n = t.n ∧
      t'.z = t.z ∧ t'.c = t.c ∧ t'.v = t.v ∧
      ∀ y, (m y = s.mem y ∨ Writes e.accesses y) → t'.mem y = t.mem y := by
  have hpc : ({ s with mem := m } : State).pc = s.pc := rfl
  unfold step at hst ⊢
  simp only [hpc, accesses_withMem, hdec] at hst ⊢
  by_cases hodd : s.pc.getLsbD 0 = true
  · simp [hodd] at hst
  · simp only [hodd, Bool.false_eq_true, ↓reduceIte] at hst ⊢
    cases hd : decode (fetch16 s.mem s.pc) (fetch16 s.mem (s.pc + 2#32)) with
    | none => simp [hd] at hst
    | some i =>
      simp only [hd] at hst ⊢
      by_cases hal : ((i.accesses s).all Access.aligned) = true
      · simp only [hal, ↓reduceIte] at hst ⊢
        have hro := exec_reads_only i s m
        cases hex : i.exec s with
        | error f => simp [hex] at hst
        | ok s₁ =>
          simp only [hex, Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          have hro := hro (fun y hy => hrd y hy)
          rw [hex] at hro
          cases hex' : i.exec { s with mem := m } with
          | error f => rw [hex'] at hro; exact hro.elim
          | ok s₂ =>
            rw [hex'] at hro
            exact ⟨s₂, rfl, hro⟩
      · simp [hal] at hst

/-! ## The simulation -/

/-- Two lists of states that agree outside `Z` element by element. -/
inductive AgreeAll (Z : Word → Prop) : List State → List State → Prop
  | nil : AgreeAll Z [] []
  | cons {s w : State} {l l' : List State} : Agree Z s w → AgreeAll Z l l' →
      AgreeAll Z (s :: l) (w :: l')

/-- The fetched instruction is the same in every memory that agrees with `u.mem` outside `Z`. -/
def FetchStable (Z : Word → Prop) (u : State) : Prop :=
  ∀ m : Mem, (∀ y, ¬ Z y → m y = u.mem y) →
    decode (fetch16 m u.pc) (fetch16 m (u.pc + 2#32)) =
      decode (fetch16 u.mem u.pc) (fetch16 u.mem (u.pc + 2#32))

/-- Step by step: an interrupted run from a state that stands for the uninterrupted one makes
the same events, and its states agree with the uninterrupted states outside `Z`. -/
theorem simulate {K : Nat} {P Z : Word → Prop} {H : Nat → State → State} (hH : Handlers K P H)
    {stop : Word} :
    ∀ (fuel k : Nat) (s w : State) (states : List State) (tr : List Event),
      runStates stop fuel s = .ok (states, tr) →
      (∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ stop → FetchStable Z u) →
      (∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ stop →
        ∀ y, ¬ (P y ∧ ¬ Region (u.sp - BitVec.ofNat 32 K) K y) → Z y ∧ DeadIn (tr.drop i) y) →
      Stands Z tr s w →
      ∃ states', irunStates H stop fuel k w = .ok (states', tr) ∧
        AgreeAll Z states states' := by
  intro fuel
  induction fuel with
  | zero =>
    intro k s w states tr hrun _ _ hs
    have hwpc : w.pc = s.pc := by simp only [State.pc, hs.regs]
    unfold runStates at hrun
    by_cases hpc : s.pc = stop
    · simp only [hpc, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨[w], ?_, .cons hs.agree .nil⟩
      unfold irunStates
      simp [hwpc, hpc]
    · simp [hpc] at hrun
  | succ n ih =>
    intro k s w states tr hrun hfetch hdead hs
    have hwpc : w.pc = s.pc := by simp only [State.pc, hs.regs]
    unfold runStates at hrun
    by_cases hpc : s.pc = stop
    · simp only [hpc, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨[w], ?_, .cons hs.agree .nil⟩
      unfold irunStates
      simp [hwpc, hpc]
    · simp only [hpc, ↓reduceIte] at hrun
      cases hst : step s with
      | error f => simp [hst] at hrun
      | ok p =>
        obtain ⟨s₁, e⟩ := p
        cases hr₁ : runStates stop n s₁ with
        | error f => simp [hst, hr₁] at hrun
        | ok q =>
          obtain ⟨states₁, tr₁⟩ := q
          simp only [hst, hr₁, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨h₁r, h₁n, h₁z, h₁c, h₁v, h₁m⟩ := hH k w
          have hwsp : w.sp = s.sp := by simp only [State.sp, hs.regs]
          -- after the handler, the state still stands for `s`
          have hs₁ : Stands Z (e :: tr₁) s (H k w) := by
            refine ⟨h₁r.trans hs.regs, h₁n.trans hs.n, h₁z.trans hs.z, h₁c.trans hs.c,
              h₁v.trans hs.v, fun y hy => ?_⟩
            by_cases hwy : w.mem y = s.mem y
            · have hch : ¬ (P y ∧ ¬ Region (s.sp - BitVec.ofNat 32 K) K y) := fun ⟨hp, hr⟩ =>
                hy ((h₁m y ⟨hp, by rwa [hwsp]⟩).trans hwy)
              simpa using hdead 0 s (by simp) hpc y hch
            · exact hs.mem y hwy
          have hw₁ := state_eq_withMem hs₁.regs hs₁.n hs₁.z hs₁.c hs₁.v
          obtain ⟨t', hst', htr, htn, htz, htc, htv, htm⟩ := step_withMem (m := (H k w).mem) hst
            (hfetch 0 s (by simp) hpc _ fun y hy => by
              by_cases he : (H k w).mem y = s.mem y
              · exact he
              · exact absurd (hs₁.mem y he).1 hy)
            (fun y hr => by
              by_cases he : (H k w).mem y = s.mem y
              · exact he
              · exact absurd hr (deadIn_head (hs₁.mem y he).2))
          rw [← hw₁] at hst'
          have hs' : Stands Z tr₁ s₁ t' := by
            refine ⟨htr, htn, htz, htc, htv, fun y hy => ?_⟩
            have hny : ¬ ((H k w).mem y = s.mem y ∨ Writes e.accesses y) :=
              fun h => hy (htm y h)
            have hd := hs₁.mem y (fun h => hny (Or.inl h))
            exact ⟨hd.1, deadIn_tail hd.2 (fun h => hny (Or.inr h))⟩
          obtain ⟨states', hrun', hall⟩ := ih (k + 1) s₁ t' states₁ tr₁ hr₁
            (fun i u hu hne => hfetch (i + 1) u (by simpa using hu) hne)
            (fun i u hu hne y hy => by simpa using hdead (i + 1) u (by simpa using hu) hne y hy)
            hs'
          refine ⟨w :: states', ?_, .cons hs.agree hall⟩
          rw [irunStates]
          simp only [hwpc, hpc, ↓reduceIte, hst', hrun']

/-! ## Region arithmetic -/

/-- The `K` bytes below an SP in the window lie in the window or the `K` bytes below it, and
below that SP. -/
theorem below_sp {sp0 sp y : Word} {N K o : Nat} (hroom : N + K ≤ sp0.toNat) (ho : o ≤ N)
    (hsp : sp = sp0 - BitVec.ofNat 32 o) (hy : Region (sp - BitVec.ofNat 32 K) K y) :
    Region (sp0 - BitVec.ofNat 32 (N + K)) (N + K) y ∧ ¬ AtOrAboveSp sp0 sp y := by
  subst hsp
  have h0 := sp0.isLt
  have h1 := y.isLt
  simp only [Region, AtOrAboveSp, BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  omega

/-- A byte of the window and the `K` bytes below it, outside the window, is one of those `K`
bytes. -/
theorem below_window {sp0 y : Word} {N K : Nat}
    (hz : Region (sp0 - BitVec.ofNat 32 (N + K)) (N + K) y) (hb : ¬ BelowEntry sp0 N y) :
    Region (sp0 - BitVec.ofNat 32 (N + K)) K y := by
  have h0 := sp0.isLt
  have h1 := y.isLt
  simp only [Region, BelowEntry, BitVec.toNat_sub, BitVec.toNat_ofNat] at hz hb ⊢
  omega

/-- The bytes a handler may change before step `i` lie outside `P` or in the window and the `K`
bytes below it, and are dead in the rest of the run. -/
theorem handler_dead {K N : Nat} {sp0 : Word} {P : Word → Prop} {states : List State}
    {tr : List Event} (hd : StackReadsWritten sp0 N states tr)
    (hwin : ∀ u ∈ states, InStackWindow sp0 N u.sp) (hroom : HandlerRoom K N sp0 P)
    (hrd : ReadsFrom P tr) :
    ∀ i u, states[i]? = some u → ∀ y, ¬ (P y ∧ ¬ Region (u.sp - BitVec.ofNat 32 K) K y) →
      (Region (sp0 - BitVec.ofNat 32 (N + K)) (N + K) y ∨ ¬ P y) ∧ DeadIn (tr.drop i) y := by
  intro i u hu y hch
  by_cases hp : P y
  · have hy : Region (u.sp - BitVec.ofNat 32 K) K y := Classical.byContradiction fun h => hch ⟨hp, h⟩
    obtain ⟨o, ho, hsp⟩ := hwin u (List.mem_of_getElem? hu)
    obtain ⟨hz, hna⟩ := below_sp hroom.1 ho hsp hy
    refine ⟨Or.inl hz, ?_⟩
    intro k e hk hr
    have hk' : tr[i + k]? = some e := by simpa [List.getElem?_drop] using hk
    by_cases hb : BelowEntry sp0 N y
    · obtain ⟨j, hj, ⟨e', he', hw'⟩, hall⟩ := hd (i + k) e hk' y hr hb
      by_cases hij : i ≤ j
      · refine ⟨j - i, by omega, e', ?_, hw'⟩
        simpa [List.getElem?_drop, show i + (j - i) = j by omega] using he'
      · exact absurd (hall i u (by omega) (by omega) hu) hna
    · exact absurd (hrd e (List.mem_of_getElem? hk') y hr) (hroom.2 y (below_window hz hb))
  · refine ⟨Or.inr hp, fun k e hk hr => absurd (hrd e ?_ y hr) hp⟩
    exact List.mem_of_mem_drop (List.mem_of_getElem? hk)

/-! ## Runs -/

theorem runStates_last {stop : Word} :
    ∀ {fuel : Nat} {s t : State} {tr tr' : List Event} {states : List State},
      Thumb.runUntil stop fuel s = .ok (t, tr) → runStates stop fuel s = .ok (states, tr') →
      tr' = tr ∧ states.getLast? = some t := by
  intro fuel
  induction fuel with
  | zero =>
    intro s t tr tr' states h1 h2
    unfold Thumb.runUntil at h1
    unfold runStates at h2
    by_cases hpc : s.pc = stop
    · simp only [hpc, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      simp
    · simp [hpc] at h1
  | succ n ih =>
    intro s t tr tr' states h1 h2
    unfold Thumb.runUntil at h1
    unfold runStates at h2
    by_cases hpc : s.pc = stop
    · simp only [hpc, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      simp
    · simp only [hpc, ↓reduceIte] at h1 h2
      cases hst : step s with
      | error f => simp [hst] at h1
      | ok p =>
        obtain ⟨s₁, e⟩ := p
        cases hr1 : Thumb.runUntil stop n s₁ with
        | error f => simp [hst, hr1] at h1
        | ok q =>
          cases hr2 : runStates stop n s₁ with
          | error f => simp [hst, hr2] at h2
          | ok q' =>
            obtain ⟨t₁, tr₁⟩ := q
            obtain ⟨states₁, tr₂⟩ := q'
            simp only [hst, hr1, Except.ok.injEq, Prod.mk.injEq] at h1
            simp only [hst, hr2, Except.ok.injEq, Prod.mk.injEq] at h2
            obtain ⟨rfl, rfl⟩ := h1
            obtain ⟨rfl, rfl⟩ := h2
            obtain ⟨rfl, hl⟩ := ih hr1 hr2
            refine ⟨rfl, ?_⟩
            have hne : states₁ ≠ [] := by intro h; simp [h] at hl
            rw [List.getLast?_cons, hl]
            simp

theorem AgreeAll.getLast {Z : Word → Prop} :
    ∀ {l l' : List State} {a : State}, AgreeAll Z l l' → l.getLast? = some a →
      ∃ b, l'.getLast? = some b ∧ Agree Z a b
  | [], _, _, .nil, h => by simp at h
  | [x], [y], a, .cons hxy .nil, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact ⟨y, rfl, hxy⟩
  | x :: x' :: xs, y :: ys, a, .cons _ hrest, h => by
    obtain ⟨b, hb, hab⟩ := AgreeAll.getLast hrest (by simpa using h)
    cases ys with
    | nil => cases hrest
    | cons y' ys => exact ⟨b, by simpa using hb, hab⟩

theorem AgreeAll.mem {Z : Word → Prop} :
    ∀ {l l' : List State} {b : State}, AgreeAll Z l l' → b ∈ l' → ∃ a ∈ l, Agree Z a b
  | [], _, _, .nil, h => by simp at h
  | x :: _, y :: _, b, .cons hxy hrest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨x, List.mem_cons_self .., hxy⟩
    · obtain ⟨a, ha, hab⟩ := AgreeAll.mem hrest h
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- An instruction of the artifact `bytes` at `u.pc`, with the artifact in memory. -/
def CodePos (base : Word) (bytes : List (BitVec 8)) (u : State) : Prop :=
  ∃ off i, u.pc = base + BitVec.ofNat 32 off ∧ instrAt bytes off = some i ∧
    off + i.size ≤ bytes.length ∧ CodeAt u.mem base bytes

theorem CodePos.fetchStable {Z : Word → Prop} {base : Word} {bytes : List (BitVec 8)}
    {u : State} (h : CodePos base bytes u)
    (hcz : ∀ y, Region base bytes.length y → ¬ Z y) : FetchStable Z u := by
  obtain ⟨off, i, hpc, hi, hlen, hcode⟩ := h
  intro m hm
  have hcode' : CodeAt m base bytes := fun j hj => by
    rw [hm _ (hcz _ (Region.mk (o := j) hj rfl))]
    exact hcode j hj
  rw [hpc, decode_at hcode off i hi hlen, decode_at hcode' off i hi hlen]

/-- **Interrupted calls.** A call whose uninterrupted run returns with `Result`, keeps SP in an
`N`-byte window, reads only bytes of `Rd` and reads stack bytes only after writing them, and
whose instructions come from an artifact in `Rd` outside the window, makes `InterruptedCall`
true for the bytes `Rd` and `W` it may read or write. -/
theorem interruptedCall_of {K N : Nat} {sp0 stop base : Word} {bytes : List (BitVec 8)}
    {s : State} {Result : State → Prop} {Rd W : Word → Prop}
    (hcode : ∀ y, Region base bytes.length y → Rd y ∧ ¬ BelowEntry sp0 N y)
    (hcor : ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil stop fuel s = .ok (t, tr) ∧ Result t)
    (hrd : ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil stop fuel s = .ok (t, tr) ∧
      ReadsFrom Rd tr)
    (hstk : ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates stop fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, InStackWindow sp0 N u.sp)
    (hdisc : ∃ n, ∀ fuel, n ≤ fuel → ∃ states tr, runStates stop fuel s = .ok (states, tr) ∧
      StackDiscipline sp0 N states tr ∧
      ∀ (i : Nat) (u : State), states[i]? = some u → u.pc ≠ stop → CodePos base bytes u) :
    InterruptedCall K N sp0 stop s (fun y => Rd y ∨ W y) Result := by
  intro hroom H hH
  -- a byte of `P` outside the window is outside the window and the `K` bytes below it
  have hout : ∀ y, (Rd y ∨ W y) → ¬ BelowEntry sp0 N y →
      ¬ Region (sp0 - BitVec.ofNat 32 (N + K)) (N + K) y :=
    fun y hp hb hz => hroom.2 y (below_window hz hb) hp
  obtain ⟨n₁, h₁⟩ := hcor
  obtain ⟨n₂, h₂⟩ := hrd
  obtain ⟨n₃, h₃⟩ := hstk
  obtain ⟨n₄, h₄⟩ := hdisc
  refine ⟨n₁ + n₂ + n₃ + n₄, fun fuel hf => ?_⟩
  obtain ⟨t₀, tr, hru, hres⟩ := h₁ fuel (by omega)
  obtain ⟨t₂, tr₂, hru₂, hrds⟩ := h₂ fuel (by omega)
  rw [hru] at hru₂
  simp only [Except.ok.injEq, Prod.mk.injEq] at hru₂
  obtain ⟨rfl, rfl⟩ := hru₂
  obtain ⟨states, tr₃, hrs, hwin⟩ := h₃ fuel (by omega)
  obtain ⟨states₄, tr₄, hrs₄, hd, hpos⟩ := h₄ fuel (by omega)
  rw [hrs] at hrs₄
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrs₄
  obtain ⟨rfl, rfl⟩ := hrs₄
  obtain ⟨htr, hlast⟩ := runStates_last hru hrs
  subst tr₃
  have hdead := handler_dead hd.2 hwin hroom fun e he y hy => Or.inl (hrds e he y hy)
  obtain ⟨states', hirun, hall⟩ := simulate
    (Z := fun y => Region (sp0 - BitVec.ofNat 32 (N + K)) (N + K) y ∨ ¬ (Rd y ∨ W y))
    hH fuel 0 s s states tr hrs
    (fun (i : Nat) (u : State) hu hne => (hpos i u hu hne).fetchStable fun y hy hz => by
      obtain ⟨hrd, hnb⟩ := hcode y hy
      rcases hz with hz | hz
      · exact hout y (Or.inl hrd) hnb hz
      · exact hz (Or.inl hrd))
    (fun (i : Nat) (u : State) hu _ y hy => hdead i u hu y hy)
    ⟨rfl, rfl, rfl, rfl, rfl, fun y h => absurd rfl h⟩
  obtain ⟨t, ht, hag⟩ := AgreeAll.getLast hall hlast
  refine ⟨t₀, tr, states', t, hru, hres, hirun, ht,
    ⟨hag.regs, hag.n, hag.z, hag.c, hag.v, fun y ⟨hp, hb⟩ => hag.mem y fun hz => by
      rcases hz with hz | hz
      · exact hout y hp hb hz
      · exact hz hp⟩, fun u' hu' => ?_⟩
  obtain ⟨u, hu, hag'⟩ := AgreeAll.mem hall hu'
  have : u'.sp = u.sp := by simp only [State.sp, hag'.regs]
  rw [this]
  exact hwin u hu

end M0Crypto.Release.Interrupt
