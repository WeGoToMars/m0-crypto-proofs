import M0Crypto.Release.Blake2sClaims
import M0Crypto.Release.Blake2sStatements

set_option linter.unusedSimpArgs false

/-!
# The streaming hash composed: claims C1 and C4

`hash_correct` (C1) chains the per-function correctness claims: each call's `Result` gives the
stream the next call's context holds, and the digest follows from
`Spec.Blake2s.stream_partition`. `hash_constant_time` (C4) chains the per-function
constant-time claims: the only stream-dependent public input, the number of pending bytes,
depends on the input lengths alone (`absorb_pend`).
-/

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Spec.Blake2s (absorb Byte)
open M0Crypto.Release.Blake2sHash (total total_absorb runUntil_unique)

/-! ## The context across calls -/

/-- A context is a property of its 112 bytes only. -/
theorem holds_congr {m m' : Mem} {c : Word} {st : Spec.Blake2s.State} (h : ContextHolds m c st)
    (hm : ∀ o < contextBytes, m' (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) :
    ContextHolds m' c st :=
  Blake2sClaims.ctx_holds (Blake2sHash.ctx_congr (Blake2sClaims.holds_ctx h) hm)

theorem inputAt_length (s : State) : (inputAt s).length = (s.regs 2).toNat := by
  simp [inputAt, bytesAt]

theorem Init.returns {c : Init.Ctx} {s t : State} {fuel : Nat} {tr : List Event}
    (hp : Init.Pre c s) (hrun : runUntil c.ret fuel s = .ok (t, tr)) : Init.Result c t := by
  obtain ⟨n, hn⟩ := Init.init_correct c s hp
  obtain ⟨t', _, hr, R, _⟩ := hn (max n fuel) (Nat.le_max_left _ _)
  rw [runUntil_unique hrun hr]; exact R

theorem Update.returns {c : Update.Ctx} {s w : State} {fuel : Nat} {tr : List Event}
    (hp : Update.Pre c s) (hrun : runUntil c.ret fuel s = .ok (w, tr)) : Update.Result c w := by
  obtain ⟨n, hn⟩ := Update.update_correct c s hp
  obtain ⟨w', _, hr, R, _⟩ := hn (max n fuel) (Nat.le_max_left _ _)
  rw [runUntil_unique hrun hr]; exact R

/-! ## C1 -/

/-- Every chain of `update` calls meeting their obligations returns, and the context then holds
the stream with all inputs absorbed. -/
theorem updates_return {base c : Word} : ∀ (calls : List State) (m : Mem)
    (st : Spec.Blake2s.State) (K : Mem → Prop), ContextHolds m c st →
    total st + (calls.map fun s => (s.regs 2).toNat).sum < 2 ^ 64 →
    (∀ m', ContextHolds m' c ((calls.map inputAt).foldl absorb st) →
      total ((calls.map inputAt).foldl absorb st) =
        total st + (calls.map fun s => (s.regs 2).toNat).sum → K m') →
    UpdatesReturn base c m calls K
  | [], m, st, K, hc, _, hK => hK m (by simpa using hc) (by simp)
  | s :: rest, m, st, K, hc, hb, hK => by
    intro hm ⟨h0, he⟩
    rw [List.map_cons, List.sum_cons] at hb
    have ht := total_absorb (inputAt s) st
    have hP := he st (holds_congr hc hm) (by unfold total at hb; omega)
    obtain ⟨n, hn⟩ := Update.update_correct _ _ hP
    obtain ⟨w, tr, hru, R, -⟩ := hn n (Nat.le_refl n)
    have hc' : ContextHolds w.mem c (absorb st (inputAt s)) := by rw [← h0]; exact R.holds
    refine ⟨n, w, tr, hru, updates_return rest w.mem _ K hc' (by rw [ht, inputAt_length]; omega)
      (fun m' h1 h2 => hK m' ?_ ?_)⟩
    · simpa [List.foldl_cons] using h1
    · simp only [List.map_cons, List.foldl_cons, List.sum_cons] at h2 ⊢
      rw [h2, ht, inputAt_length]; omega

/-- **Claim C1, total correctness.** From a valid `init` call, `init` returns; then every chain
of `update` calls meeting their obligations returns; then every `final` call meeting its
obligations returns, with the RFC 7693 BLAKE2s-256 digest of the concatenated inputs at its
output pointer. -/
theorem hash_correct : HashCorrect := by
  intro ci s0 calls ⟨hp, hlen⟩
  obtain ⟨n, hn⟩ := Init.init_correct ci s0 hp
  obtain ⟨t0, tr, hru, R0, -⟩ := hn n (Nat.le_refl n)
  refine ⟨n, t0, tr, hru, ?_⟩
  have htot0 : total Spec.Blake2s.State.init = 0 := rfl
  refine updates_return calls t0.mem _ _ R0.holds (by rw [htot0]; omega) (fun m' h1 h2 => ?_)
  intro sf hfm ⟨_, hfe⟩
  rw [htot0] at h2
  have hPf := hfe _ (holds_congr h1 hfm) (by unfold total at h2; omega)
  obtain ⟨nf, hnf⟩ := Final.final_correct _ _ hPf
  obtain ⟨tf, trf, hruf, Rf, -⟩ := hnf nf (Nat.le_refl nf)
  exact ⟨nf, tf, trf, hruf, Rf.out.trans (Spec.Blake2s.stream_partition (calls.map inputAt))⟩

/-! ## C4 -/

theorem push_pend (st : Spec.Blake2s.State) (b : Byte) :
    (st.push b).pending.length = if st.pending.length = 64 then 1 else st.pending.length + 1 := by
  unfold M0Crypto.Spec.Blake2s.State.push
  split
  · simp_all
  · simp_all

/-- The length of the pending bytes after absorbing depends only on the lengths. -/
theorem absorb_pend : ∀ (bs bs' : List Byte) (st st' : Spec.Blake2s.State),
    bs.length = bs'.length → st.pending.length = st'.pending.length →
    (absorb st bs).pending.length = (absorb st' bs').pending.length
  | [], [], st, st', _, hp => by simpa [absorb] using hp
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | b :: bs, b' :: bs', st, st', hl, hp => by
    show (absorb (st.push b) bs).pending.length = (absorb (st'.push b') bs').pending.length
    exact absorb_pend bs bs' _ _ (by simpa using hl) (by rw [push_pend, push_pend, hp])

theorem foldl_pend : ∀ (xs ys : List (List Byte)), xs.map List.length = ys.map List.length →
    ∀ st st' : Spec.Blake2s.State, st.pending.length = st'.pending.length →
      (xs.foldl absorb st).pending.length = (ys.foldl absorb st').pending.length
  | [], [], _, _, _, hp => by simpa using hp
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | x :: xs, y :: ys, h, st, st', hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact foldl_pend xs ys h.2 _ _ (absorb_pend _ _ _ _ h.1 hp)

/-- After a chain of `update` calls that ran, the context holds the stream with all inputs
absorbed. -/
theorem updates_ctx {base c : Word} : ∀ (calls : List (State × State)) (m : Mem)
    (st : Spec.Blake2s.State), UpdatesRan base c m calls → ContextHolds m c st →
    total st + (calls.map fun p => (p.1.regs 2).toNat).sum < 2 ^ 64 →
    ContextHolds (lastMem m calls) c ((calls.map fun p => inputAt p.1).foldl absorb st) ∧
      total ((calls.map fun p => inputAt p.1).foldl absorb st) =
        total st + (calls.map fun p => (p.1.regs 2).toNat).sum
  | [], m, st, _, hc, _ => ⟨by simpa [lastMem] using hc, by simp⟩
  | (s, w) :: rest, m, st, ⟨hm, ⟨h0, he⟩, ⟨_, _, hrun⟩, hrest⟩, hc, hb => by
    simp only [List.map_cons, List.sum_cons, List.foldl_cons] at hb ⊢
    have ht := total_absorb (inputAt s) st
    have hP := he st (holds_congr hc hm) (by unfold total at hb; omega)
    have R := Update.returns hP hrun
    have hc2 : ContextHolds w.mem c (absorb st (inputAt s)) := by rw [← h0]; exact R.holds
    obtain ⟨h1, h2⟩ := updates_ctx rest w.mem _ hrest hc2 (by rw [ht, inputAt_length]; omega)
    exact ⟨h1, by rw [h2, ht, inputAt_length]; omega⟩

/-- Every `update` call of two chains with equal public inputs runs the same trace. -/
theorem updates_trace {base c : Word} : ∀ (calls calls' : List (State × State)) (m m' : Mem)
    (st st' : Spec.Blake2s.State), UpdatesRan base c m calls → UpdatesRan base c m' calls' →
    ContextHolds m c st → ContextHolds m' c st' → st.pending.length = st'.pending.length →
    total st + (calls.map fun p => (p.1.regs 2).toNat).sum < 2 ^ 64 →
    total st' + (calls'.map fun p => (p.1.regs 2).toNat).sum < 2 ^ 64 →
    calls.map (fun p => Update.pubAt p.1) = calls'.map (fun p => Update.pubAt p.1) →
    calls.map (fun p => traceOf p.1) = calls'.map (fun p => traceOf p.1)
  | [], [], _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, h => by simp at h
  | (s, w) :: rest, (s', w') :: rest', m, m', st, st',
      ⟨hm, ⟨h0, he⟩, ⟨_, _, hrun⟩, hrest⟩, ⟨hm', ⟨h0', he'⟩, ⟨_, _, hrun'⟩, hrest'⟩,
      hc, hc', hp, hb, hb', hpub => by
    simp only [List.map_cons, List.cons.injEq] at hpub
    obtain ⟨hq, hpubr⟩ := hpub
    simp only [List.map_cons, List.sum_cons] at hb hb'
    simp only [Update.pubAt, Prod.mk.injEq] at hq
    obtain ⟨q13, q14, q0, q1, q2⟩ := hq
    have hl : (inputAt s).length = (inputAt s').length := by
      rw [inputAt_length, inputAt_length, q2]
    have hP := he st (holds_congr hc hm) (by unfold total at hb; omega)
    have hP' := he' st' (holds_congr hc' hm') (by unfold total at hb'; omega)
    have htr : traceOf s = traceOf s' := funext fun fuel =>
      Update.update_constant_time _ _ _ _ hP hP'
        (by simp only [Update.Ctx.pub, Update.callAt, q13, q14, q0, q1, q2, hp]) fuel
    have R := Update.returns hP hrun
    have R' := Update.returns hP' hrun'
    have hc2 : ContextHolds w.mem c (absorb st (inputAt s)) := by rw [← h0]; exact R.holds
    have hc2' : ContextHolds w'.mem c (absorb st' (inputAt s')) := by rw [← h0']; exact R'.holds
    have ht := total_absorb (inputAt s) st
    have ht' := total_absorb (inputAt s') st'
    simp only [List.map_cons, htr]
    rw [updates_trace rest rest' w.mem w'.mem _ _ hrest hrest' hc2 hc2'
      (absorb_pend _ _ _ _ hl hp) (by rw [ht, inputAt_length]; omega)
      (by rw [ht', inputAt_length]; omega) hpubr]

/-- **Claim C4, constant time composed.** Two executions of `init; update*; final` whose calls
have equal public inputs (pointers, lengths, SP, LR), call by call, run every call with the
same event trace, whatever the message bytes. -/
theorem hash_constant_time : HashConstantTime := by
  intro ci ci' s0 s0' t0 t0' sf sf' calls calls' H
  obtain ⟨_, _, hrun⟩ := H.run
  obtain ⟨_, _, hrun'⟩ := H.run'
  have hpub := H.pub
  simp only [Init.Ctx.pub, Prod.mk.injEq] at hpub
  obtain ⟨-, -, -, hc⟩ := hpub
  have hc0 : ContextHolds t0.mem ci.context Spec.Blake2s.State.init :=
    (Init.returns H.pre hrun).holds
  have hc0' : ContextHolds t0'.mem ci.context Spec.Blake2s.State.init := by
    rw [hc]; exact (Init.returns H.pre' hrun').holds
  have htot0 : total Spec.Blake2s.State.init = 0 := rfl
  have hlen := H.lengthLt
  have hlens : calls.map (fun p => (p.1.regs 2).toNat) = calls'.map (fun p => (p.1.regs 2).toNat) := by
    have := congrArg (List.map fun q : Word × Word × Word × Word × Word => q.2.2.2.2.toNat)
      H.updatesPub
    simpa [List.map_map, Function.comp_def, Update.pubAt] using this
  have hlen' : (calls'.map fun p => (p.1.regs 2).toNat).sum < 2 ^ 64 := by rw [← hlens]; exact hlen
  refine ⟨?_, updates_trace calls calls' _ _ _ _ H.updates H.updates' hc0 hc0' rfl
    (by rw [htot0]; omega) (by rw [htot0]; omega) H.updatesPub, ?_⟩
  · funext fuel
    have := Init.init_constant_time ci ci' s0 s0' H.pre H.pre' H.pub fuel
    simp only [traceOf, returnAddr]
    rw [H.pre.ret_eq, H.pre'.ret_eq]; exact this
  · obtain ⟨h1, h2⟩ := updates_ctx calls t0.mem _ H.updates hc0 (by rw [htot0]; omega)
    obtain ⟨h1', h2'⟩ := updates_ctx calls' t0'.mem _ H.updates' hc0' (by rw [htot0]; omega)
    have hpend := foldl_pend (calls.map fun p => inputAt p.1) (calls'.map fun p => inputAt p.1)
      (by simpa [List.map_map, Function.comp_def, inputAt_length] using hlens)
      Spec.Blake2s.State.init Spec.Blake2s.State.init rfl
    rw [htot0] at h2 h2'
    have hP := H.final.2 _ (holds_congr h1 H.finalKept) (by unfold total at h2; omega)
    have hP' := H.final'.2 _ (holds_congr h1' H.finalKept') (by unfold total at h2'; omega)
    have hfp := H.finalPub
    simp only [Final.pubAt, Prod.mk.injEq] at hfp
    obtain ⟨f13, f14, f0, f1⟩ := hfp
    funext fuel
    exact Final.final_constant_time _ _ _ _ hP hP'
      (by simp only [Final.Ctx.pub, Final.callAt, f13, f14, f0, f1, hpend]) fuel

end M0Crypto.Release.Blake2s
