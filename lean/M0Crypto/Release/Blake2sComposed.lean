import M0Crypto.Release.Blake2sHash
import M0Crypto.Release.Blake2sInitConstantTime
import M0Crypto.Release.Blake2sUpdateConstantTime
import M0Crypto.Release.Blake2sFinalConstantTime

set_option linter.unusedSimpArgs false

/-!
# The streaming hash: a trace independent of the message (composed C4)

Two executions of `init; update*; final` on the same context and output pointers, with the same
sequence of lengths, run every library call with equal event traces, whatever the message bytes
and the contexts' other words. The single-call theorems take the context's `used` word as
a hypothesis; here it is derived: it is the length of the pending bytes, and that depends on the
lengths of the inputs alone (`absorb_pend`).
-/

namespace M0Crypto.Release.Blake2sHash

open M0Crypto.Armv6M (Word State Reg Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStream (Ctx bytesAt_length)
open M0Crypto.Release.Blake2sUpdate (LL nn SState UpdateEntry UpdatePost)
open M0Crypto.Spec.Blake2s (absorb Byte)

/-- Two lists related elementwise. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

/-- The public inputs of a call: entry pc, `sp`, `lr` and the first `np` argument registers
agree (`np` = the entry's parameter count: init 1, update 3, final 2). These are the pointer and length arguments. -/
def PubEq (np : Nat) (s s' : State) : Prop :=
  s'.pc = s.pc ∧ s'.regs 13 = s.regs 13 ∧ s'.regs 14 = s.regs 14 ∧
    ∀ r : Reg, r.val < np → s'.regs r = s.regs r

/-- The two calls execute the same event trace for every fuel. -/
def TraceEq (s s' : State) : Prop :=
  ∀ fuel, (runUntil (s.regs 14 &&& ~~~1#32) fuel s).map Prod.snd =
    (runUntil (s.regs 14 &&& ~~~1#32) fuel s').map Prod.snd

theorem push_pend (st : SState) (b : Byte) :
    (st.push b).pending.length = if st.pending.length = 64 then 1 else st.pending.length + 1 := by
  unfold M0Crypto.Spec.Blake2s.State.push
  split
  · simp_all
  · simp_all

/-- The length of the pending bytes after absorbing depends only on the lengths. -/
theorem absorb_pend : ∀ (bs bs' : List Byte) (st st' : SState), bs.length = bs'.length →
    st.pending.length = st'.pending.length →
    (absorb st bs).pending.length = (absorb st' bs').pending.length
  | [], [], st, st', _, hp => by simpa [absorb] using hp
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | b :: bs, b' :: bs', st, st', hl, hp => by
    show (absorb (st.push b) bs).pending.length = (absorb (st'.push b') bs').pending.length
    exact absorb_pend bs bs' _ _ (by simpa using hl) (by rw [push_pend, push_pend, hp])

theorem foldl_pend {xs ys : List (List Byte)}
    (h : All2 (fun a b => a.length = b.length) xs ys) :
    ∀ st st' : SState, st.pending.length = st'.pending.length →
      (xs.foldl absorb st).pending.length = (ys.foldl absorb st').pending.length := by
  induction h with
  | nil => intro st st' hp; simpa using hp
  | cons hab _ ih =>
    intro st st' hp
    exact ih _ _ (absorb_pend _ _ _ _ hab hp)

theorem pubEq_nn {s s' : State} (h : PubEq 3 s s') : nn s' = nn s := by
  simp [nn, h.2.2.2 2 (by decide)]

theorem inputs_len_eq : ∀ {calls calls' : List (State × State)},
    All2 (fun p q => PubEq 3 p.1 q.1) calls calls' →
    All2 (fun a b => a.length = b.length) (inputs calls) (inputs calls')
  | [], [], _ => All2.nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | (s, w) :: rest, (s', w') :: rest', h => by
    cases h with
    | cons hp hr =>
      refine All2.cons ?_ (inputs_len_eq hr)
      have hl : (LL s).length = nn s := by simp [LL, bytesAt_length]
      have hl' : (LL s').length = nn s' := by simp [LL, bytesAt_length]
      rw [hl, hl', pubEq_nn hp]

/-- Every `update` call of two equal-length sequences runs the same trace. -/
theorem calls_trace_eq {base c : Word} : ∀ (calls calls' : List (State × State)) (m m' : Mem)
    (st st' : SState), Calls base c m calls → Calls base c m' calls' → Ctx m c st → Ctx m' c st' →
    st.pending.length = st'.pending.length →
    total st + ((inputs calls).map List.length).sum < 2 ^ 64 →
    total st' + ((inputs calls').map List.length).sum < 2 ^ 64 →
    All2 (fun p q => PubEq 3 p.1 q.1) calls calls' →
    All2 (fun p q => TraceEq p.1 q.1) calls calls'
  | [], [], _, _, _, _, _, _, _, _, _, _, _, _ => All2.nil
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, hF => by cases hF
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, hF => by cases hF
  | (s, w) :: rest, (s', w') :: rest', m, m', st, st',
      ⟨h0, hm, he, hret, ⟨_, _, hrun⟩, hrest⟩, ⟨h0', hm', he', hret', ⟨_, _, hrun'⟩, hrest'⟩,
      hc, hc', hp, hb, hb', hF => by
    cases hF with
    | cons hpub hFrest =>
      rw [inputs_cons, List.map_cons, List.sum_cons] at hb hb'
      have hl : (LL s).length = nn s := by simp [LL, bytesAt_length]
      have hl' : (LL s').length = nn s' := by simp [LL, bytesAt_length]
      have hnn := pubEq_nn hpub
      have ht := total_absorb (LL s) st
      have ht' := total_absorb (LL s') st'
      have hcs : Ctx s.mem (s.regs 0) st := by rw [h0]; exact ctx_congr hc hm
      have hcs' : Ctx s'.mem (s'.regs 0) st' := by rw [h0']; exact ctx_congr hc' hm'
      have e₁ := he st hcs (by omega)
      have e₂ := he' st' hcs' (by omega)
      have hr0 : s'.regs 0 = s.regs 0 := hpub.2.2.2 0 (by decide)
      have hused : read32 s.mem (s.regs 0 + 104#32) = read32 s'.mem (s.regs 0 + 104#32) := by
        have a := hcs.used
        have b := hcs'.used
        rw [hr0] at b
        rw [a, b, hp]
      have hup := update_returns e₁ hret hrun
      have hup' := update_returns e₂ hret' hrun'
      have hc2 : Ctx w.mem c (absorb st (LL s)) := by rw [← h0]; exact hup.ctx
      have hc2' : Ctx w'.mem c (absorb st' (LL s')) := by rw [← h0']; exact hup'.ctx
      refine All2.cons (fun fuel =>
        Blake2sUpdate.update_constant_time e₁ e₂ hret hpub.1 hpub.2.1 hpub.2.2.1 hpub.2.2.2 hused fuel) ?_
      exact calls_trace_eq rest rest' w.mem w'.mem _ _ hrest hrest' hc2 hc2'
        (absorb_pend _ _ _ _ (by rw [hl, hl', hnn]) hp)
        (by rw [ht]; omega) (by rw [ht']; omega) hFrest

/-- **Composed C4.** Two executions of `init; update*; final` on the same context and output
pointers, whose calls have equal public inputs (pointers, lengths, `sp`, `lr`), run every call
with equal event traces, whatever the message bytes. -/
theorem hash_constant_time {base c : Word} {s0 t0 s0' t0' sf sf' : State}
    {calls calls' : List (State × State)}
    (ei : Blake2sInit.InitEntry base s0) (ei' : Blake2sInit.InitEntry base s0')
    (hi0 : s0.regs 0 = c)
    (hreti : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hruni : ∃ fuel tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr))
    (hi0' : s0'.regs 0 = c)
    (hruni' : ∃ fuel tr, Thumb.runUntil (s0'.regs 14 &&& ~~~1#32) fuel s0' = .ok (t0', tr))
    (hpubi : PubEq 1 s0 s0')
    (hcalls : Calls base c t0.mem calls) (hcalls' : Calls base c t0'.mem calls')
    (hpubc : All2 (fun p q => PubEq 3 p.1 q.1) calls calls')
    (hlen : ((inputs calls).map List.length).sum < 2 ^ 64)
    (hlen' : ((inputs calls').map List.length).sum < 2 ^ 64)
    (hf0 : sf.regs 0 = c) (hf0' : sf'.regs 0 = c)
    (hfm : ∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = lastMem t0.mem calls (c + BitVec.ofNat 32 o))
    (hfm' : ∀ o < 112, sf'.mem (c + BitVec.ofNat 32 o) = lastMem t0'.mem calls' (c + BitVec.ofNat 32 o))
    (hfe : ∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st)
    (hfe' : ∀ st, Ctx sf'.mem (sf'.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf' st)
    (hretf : ∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hpubf : PubEq 2 sf sf') :
    TraceEq s0 s0' ∧ All2 (fun p q => TraceEq p.1 q.1) calls calls' ∧ TraceEq sf sf' := by
  obtain ⟨_, _, hruni⟩ := hruni
  obtain ⟨_, _, hruni'⟩ := hruni'
  have hp0 := init_returns ei hreti hruni
  have hreti' : ∀ i < Artifacts.Release.size, s0'.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i := by
    rw [hpubi.2.2.1]; exact hreti
  have hp0' := init_returns ei' hreti' hruni'
  have hc0 : Ctx t0.mem c M0Crypto.Spec.Blake2s.State.init := by rw [← hi0]; exact hp0.ctx
  have hc0' : Ctx t0'.mem c M0Crypto.Spec.Blake2s.State.init := by rw [← hi0']; exact hp0'.ctx
  have htot0 : total M0Crypto.Spec.Blake2s.State.init = 0 := rfl
  refine ⟨fun fuel => Blake2sInit.init_constant_time ei ei' hreti hpubi.1 hpubi.2.1 hpubi.2.2.1
    hpubi.2.2.2 fuel, calls_trace_eq calls calls' _ _ _ _ hcalls hcalls' hc0 hc0' rfl
      (by rw [htot0]; omega) (by rw [htot0]; omega) hpubc, ?_⟩
  obtain ⟨h1, h2⟩ := calls_ctx calls t0.mem _ hcalls hc0 (by rw [htot0]; omega)
  obtain ⟨h1', h2'⟩ := calls_ctx calls' t0'.mem _ hcalls' hc0' (by rw [htot0]; omega)
  have hcf := ctx_congr h1 hfm
  have hcf' := ctx_congr h1' hfm'
  rw [← hf0] at hcf; rw [← hf0'] at hcf'
  have hpend := foldl_pend (inputs_len_eq hpubc) M0Crypto.Spec.Blake2s.State.init
    M0Crypto.Spec.Blake2s.State.init rfl
  have e₁ := hfe _ hcf (by rw [h2, htot0]; omega)
  have e₂ := hfe' _ hcf' (by rw [h2', htot0]; omega)
  have hr0 : sf'.regs 0 = sf.regs 0 := hpubf.2.2.2 0 (by decide)
  have hused : read32 sf.mem (sf.regs 0 + 104#32) = read32 sf'.mem (sf.regs 0 + 104#32) := by
    have a := hcf.used
    have b := hcf'.used
    rw [hr0] at b
    rw [a, b, hpend]
  exact fun fuel => Blake2sFinal.final_constant_time e₁ e₂ hretf hpubf.1 hpubf.2.1 hpubf.2.2.1
    hpubf.2.2.2 hused fuel

end M0Crypto.Release.Blake2sHash
