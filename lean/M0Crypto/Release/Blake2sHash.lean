import M0Crypto.Release.Blake2sUpdateReach
import M0Crypto.Release.Blake2sFinalReach
import M0Crypto.Release.Blake2sInit
import M0Crypto.Spec.Blake2s

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # The streaming interface: `init`, `update`, `final`

Each function's correctness is stated for a run to its return address (`runUntil`), with the
set of memory bytes it may write. the specification-level partition fact is `Spec.Blake2s.stream_partition`;
`hash_machine` chains the three machine contracts with it: any partition of a message into
`update` calls, between `init` and `final`, writes the RFC 7693 BLAKE2s-256 digest of the
message. -/

namespace M0Crypto.Release.Blake2sHash

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)

theorem wr_disj {base a : Word} {n : Nat} (h : Disj base Artifacts.Release.size a n) {o i : Nat}
    (ho : o < n) (hi : i < Artifacts.Release.size) : a + BitVec.ofNat 32 o ≠ base + BitVec.ofNat 32 i :=
  fun eq => M0Crypto.Release.Blake2sInit.disj_ne h hi ho eq.symm

/-- `m0c_blake2s_init(c)`: afterwards the context holds the empty stream. -/
theorem init_correct {base : Word} {s : State} (e : Blake2sInit.InitEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      Blake2sInit.InitPost s t ∧ WritesTo (Blake2sInit.WrI s) tr := by
  obtain ⟨n, h⟩ := Reach.runUntil (P := Blake2sInit.InitPost s) e.code
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact wr_disj e.codeF ho hi
      · exact wr_disj e.codeC ho hi)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((Blake2sInit.init_reach e).mono (fun t ht => ⟨ht.pc, ht⟩))
  exact ⟨n, h⟩

/-- `m0c_blake2s_update(c, p, n)`: the context goes from the stream `st0` to `absorb st0` of the
`n` input bytes. -/
theorem update_correct {base : Word} {s : State} {st0 : Blake2sUpdate.SState}
    (e : Blake2sUpdate.UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      Blake2sUpdate.UpdatePost s st0 t ∧ WritesTo (Blake2sUpdate.WrU s) tr := by
  obtain ⟨n, h⟩ := Reach.runUntil (P := Blake2sUpdate.UpdatePost s st0) e.code
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact wr_disj e.codeF ho hi
      · exact wr_disj e.codeC ho hi)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((Blake2sUpdate.update_reach e).mono (fun t ht => ⟨ht.pc, ht⟩))
  exact ⟨n, h⟩

/-- `m0c_blake2s_final(c, out)`: the 32 output bytes are the digest of the stream `st`. -/
theorem final_correct {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State}
    (e : Blake2sFinal.FinalEntry base s st)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      Blake2sFinal.FinalPost s t st ∧ WritesTo (Blake2sFinal.WrF s) tr := by
  obtain ⟨n, h⟩ := Reach.runUntil (P := fun t => Blake2sFinal.FinalPost s t st) e.code
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact wr_disj e.codeF ho hi
      · exact wr_disj e.codeC ho hi
      · exact wr_disj e.codeO ho hi)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((Blake2sFinal.final_reach e).mono (fun t ht => ⟨ht.pc, ht⟩))
  exact ⟨n, h⟩

/-! ## Machine-level composition

`hash_machine` chains the three contracts across real calls. The caller's code between calls is
arbitrary, except that it leaves the 112 context bytes alone (`Calls`, `hfm`). Each call is given
by its entry state and the state it returns in; `*_returns` says any such returned state
satisfies the post, whatever fuel the run used. -/

open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_length bytesAt_congr)
open M0Crypto.Release.Frame (read32_congr)
open M0Crypto.Release.Blake2sUpdate (LL nn SState UpdateEntry UpdatePost)

/-- A successful run to `stop` has one final state, whatever the fuel. -/
theorem runUntil_unique {stop : Word} : ∀ {n m : Nat} {s t₁ t₂ : State} {tr₁ tr₂ : List Event},
    Thumb.runUntil stop n s = .ok (t₁, tr₁) → Thumb.runUntil stop m s = .ok (t₂, tr₂) → t₁ = t₂
  | 0, m, s, t₁, t₂, tr₁, tr₂, h₁, h₂ => by
    by_cases hpc : s.pc = stop
    · cases m <;> simp [Thumb.runUntil, hpc] at h₁ h₂ <;> exact h₁.1.symm.trans h₂.1
    · simp [Thumb.runUntil, hpc] at h₁
  | n + 1, m, s, t₁, t₂, tr₁, tr₂, h₁, h₂ => by
    by_cases hpc : s.pc = stop
    · cases m <;> simp [Thumb.runUntil, hpc] at h₁ h₂ <;> exact h₁.1.symm.trans h₂.1
    · cases m with
      | zero => simp [Thumb.runUntil, hpc] at h₂
      | succ m =>
        simp only [Thumb.runUntil, hpc, ↓reduceIte] at h₁ h₂
        cases hs : step s with
        | error err => simp [hs] at h₁
        | ok pair =>
          obtain ⟨nx, ev⟩ := pair
          simp only [hs] at h₁ h₂
          cases hr₁ : Thumb.runUntil stop n nx with
          | error err => simp [hr₁] at h₁
          | ok p₁ =>
            cases hr₂ : Thumb.runUntil stop m nx with
            | error err => simp [hr₂] at h₂
            | ok p₂ =>
              simp only [hr₁, hr₂, Except.ok.injEq, Prod.mk.injEq] at h₁ h₂
              have := runUntil_unique hr₁ hr₂
              rw [← h₁.1, ← h₂.1, this]

theorem init_returns {base : Word} {s t : State} {fuel : Nat} {tr : List Event}
    (e : Blake2sInit.InitEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hrun : Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr)) : Blake2sInit.InitPost s t := by
  obtain ⟨n, h⟩ := init_correct e hret
  obtain ⟨t', _, hr, hp, _⟩ := h (max n fuel) (Nat.le_max_left _ _)
  rw [runUntil_unique hrun hr]; exact hp

theorem update_returns {base : Word} {s w : State} {st0 : SState} {fuel : Nat} {tr : List Event}
    (e : UpdateEntry base s st0)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hrun : Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (w, tr)) : UpdatePost s st0 w := by
  obtain ⟨n, h⟩ := update_correct e hret
  obtain ⟨t', _, hr, hp, _⟩ := h (max n fuel) (Nat.le_max_left _ _)
  rw [runUntil_unique hrun hr]; exact hp

theorem final_returns {base : Word} {s t : State} {st : SState} {fuel : Nat} {tr : List Event}
    (e : Blake2sFinal.FinalEntry base s st)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hrun : Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr)) : Blake2sFinal.FinalPost s t st := by
  obtain ⟨n, h⟩ := final_correct e hret
  obtain ⟨t', _, hr, hp, _⟩ := h (max n fuel) (Nat.le_max_left _ _)
  rw [runUntil_unique hrun hr]; exact hp

/-- Bytes absorbed so far, compressed or pending: the quantity the `cnt` preconditions bound. -/
def total (st : SState) : Nat := st.count + st.pending.length

theorem total_push (st : SState) (b : M0Crypto.Spec.Blake2s.Byte) : total (st.push b) = total st + 1 := by
  unfold total M0Crypto.Spec.Blake2s.State.push
  split
  · simp; omega
  · simp; omega

theorem total_absorb (bs : List M0Crypto.Spec.Blake2s.Byte) :
    ∀ st : SState, total (M0Crypto.Spec.Blake2s.absorb st bs) = total st + bs.length := by
  induction bs with
  | nil => intro st; simp [M0Crypto.Spec.Blake2s.absorb]
  | cons b bs ih =>
    intro st
    have := ih (st.push b)
    simp only [M0Crypto.Spec.Blake2s.absorb, List.foldl_cons] at this ⊢
    rw [this, total_push, List.length_cons]; omega

/-- A context is a property of its 112 bytes only. -/
theorem ctx_congr {m m' : Mem} {c : Word} {st : SState} (h : Ctx m c st)
    (hm : ∀ o < 112, m' (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) : Ctx m' c st := by
  have r : ∀ j, j + 4 ≤ 112 → read32 m' (c + BitVec.ofNat 32 j) = read32 m (c + BitVec.ofNat 32 j) := by
    intro j hj
    apply read32_congr
    intro k hk
    rw [ofNat_add_assoc]
    exact hm _ (by omega)
  refine ⟨⟨h.hsz, fun i hi => ?_, ?_, ?_, h.cnt, h.plen, ?_⟩, ?_⟩
  · rw [r (4 * i) (by omega)]; exact h.h i hi
  · rw [show (32#32 : Word) = BitVec.ofNat 32 32 from rfl, r 32 (by omega)]; exact h.clo
  · rw [show (36#32 : Word) = BitVec.ofNat 32 36 from rfl, r 36 (by omega)]; exact h.chi
  · have hp := h.plen
    refine Eq.trans ?_ h.buf
    apply bytesAt_congr
    intro i hi
    rw [show (40#32 : Word) = BitVec.ofNat 32 40 from rfl, ofNat_add_assoc]
    exact hm _ (by omega)
  · rw [show (104#32 : Word) = BitVec.ofNat 32 104 from rfl, r 104 (by omega)]; exact h.used

/-- `calls` are `update` calls on the context at `c`, in order, each given as its entry state and
the state it returns in. The caller enters each with `c` in `r0`, the 112 context bytes as the
previous call (or the memory `m`) left them, and every `UpdateEntry` obligation that is not about
the context (stated for whatever stream the context holds). -/
def Calls (base c : Word) : Mem → List (State × State) → Prop
  | _, [] => True
  | m, (s, w) :: rest =>
      s.regs 0 = c ∧ (∀ o < 112, s.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) ∧
      (∀ st, Ctx s.mem (s.regs 0) st → total st + nn s < 2 ^ 64 → UpdateEntry base s st) ∧
      (∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) ∧
      (∃ fuel tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (w, tr)) ∧
      Calls base c w.mem rest

/-- The memory the last call returned with (`m` if there are none). -/
def lastMem : Mem → List (State × State) → Mem
  | m, [] => m
  | _, (_, w) :: rest => lastMem w.mem rest

/-- The input of each call, as its entry memory holds it. -/
def inputs (calls : List (State × State)) : List (List M0Crypto.Spec.Blake2s.Byte) :=
  calls.map fun p => LL p.1

theorem inputs_cons (s w : State) (rest : List (State × State)) :
    inputs ((s, w) :: rest) = LL s :: inputs rest := rfl

/-- A sequence of `update` calls leaves the context holding the stream absorbed from their inputs. -/
theorem calls_ctx {base c : Word} : ∀ (calls : List (State × State)) (m : Mem) (st : SState),
    Calls base c m calls → Ctx m c st → total st + ((inputs calls).map List.length).sum < 2 ^ 64 →
    Ctx (lastMem m calls) c ((inputs calls).foldl M0Crypto.Spec.Blake2s.absorb st) ∧
      total ((inputs calls).foldl M0Crypto.Spec.Blake2s.absorb st) =
        total st + ((inputs calls).map List.length).sum
  | [], m, st, _, hc, _ => ⟨hc, by simp [inputs]⟩
  | (s, w) :: rest, m, st, ⟨h0, hm, he, hret, ⟨_, _, hrun⟩, hrest⟩, hc, hb => by
    rw [inputs_cons, List.map_cons, List.sum_cons] at hb ⊢
    rw [List.foldl_cons]
    have hl : (LL s).length = nn s := by simp [LL, bytesAt_length]
    have ht := total_absorb (LL s) st
    have hcs : Ctx s.mem (s.regs 0) st := by rw [h0]; exact ctx_congr hc hm
    have hp := update_returns (he st hcs (by omega)) hret hrun
    have hc' : Ctx w.mem c (M0Crypto.Spec.Blake2s.absorb st (LL s)) := by rw [← h0]; exact hp.ctx
    obtain ⟨h1, h2⟩ := calls_ctx rest w.mem _ hrest hc' (by rw [ht]; omega)
    exact ⟨h1, by rw [h2, ht]; omega⟩

/-- Claim C1 at machine level: `init`, then the `update` calls `calls`, then `final`, all on the
context at `c`, write the RFC 7693 BLAKE2s-256 digest of the concatenated inputs to `out`.
Between calls the caller may run any code that leaves the 112 context bytes unchanged. Each
input is the `n` bytes at `p` in that call's entry memory. Hypotheses: each call's own entry
obligations other than the context, and the cumulative length bound. -/
theorem hash_machine {base c : Word} {s0 t0 sf tf : State} {calls : List (State × State)}
    (ei : Blake2sInit.InitEntry base s0) (hi0 : s0.regs 0 = c)
    (hreti : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hruni : ∃ fuel tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr))
    (hcalls : Calls base c t0.mem calls)
    (hlen : ((inputs calls).map List.length).sum < 2 ^ 64)
    (hf0 : sf.regs 0 = c)
    (hfm : ∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = lastMem t0.mem calls (c + BitVec.ofNat 32 o))
    (hfe : ∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st)
    (hretf : ∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (hrunf : ∃ fuel tr, Thumb.runUntil (sf.regs 14 &&& ~~~1#32) fuel sf = .ok (tf, tr)) :
    bytesAt tf.mem (sf.regs 1) 32 = M0Crypto.Spec.Blake2s.blake2s (inputs calls).flatten := by
  obtain ⟨_, _, hruni⟩ := hruni
  obtain ⟨_, _, hrunf⟩ := hrunf
  have hp0 := init_returns ei hreti hruni
  have hc0 : Ctx t0.mem c M0Crypto.Spec.Blake2s.State.init := by rw [← hi0]; exact hp0.ctx
  have htot0 : total M0Crypto.Spec.Blake2s.State.init = 0 := rfl
  obtain ⟨h1, h2⟩ := calls_ctx calls t0.mem _ hcalls hc0 (by rw [htot0]; omega)
  have hcf : Ctx sf.mem (sf.regs 0) ((inputs calls).foldl M0Crypto.Spec.Blake2s.absorb
      M0Crypto.Spec.Blake2s.State.init) := by rw [hf0]; exact ctx_congr h1 hfm
  have hpf := final_returns (hfe _ hcf (by rw [h2, htot0]; omega)) hretf hrunf
  rw [hpf.out]
  exact M0Crypto.Spec.Blake2s.stream_partition (inputs calls)

end M0Crypto.Release.Blake2sHash
