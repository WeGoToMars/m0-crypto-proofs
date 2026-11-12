import M0Crypto.Release.Blake2sHash

set_option linter.unusedSimpArgs false

/-!
# The streaming hash as total correctness (composed C1)

`hash_machine` chains the three contracts over runs that the caller states exist. Here the runs
are derived: each call's entry obligations give a returned state (`update_correct`), the next
call's obligations are then stated about that state's memory, and the digest follows. The
quantification is over entry states only; the caller's code between calls is arbitrary except
that it leaves the 112 context bytes alone, as in `Calls`.
-/

namespace M0Crypto.Release.Blake2sHash

open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStream (Ctx bytesAt)
open M0Crypto.Release.Blake2sUpdate (LL nn SState UpdateEntry)

/-- The input of each call, as its entry memory holds it. -/
def inputsOf (calls : List State) : List (List M0Crypto.Spec.Blake2s.Byte) := calls.map LL

/-- The `update` calls `calls` on the context at `c` all return. The first part of each premise is
the entry obligations (stated for whatever stream the context holds); the caller supplies the
next entry state after the previous call returned, and `K` holds of the memory after the last. -/
def CallsTotal (base c : Word) : Mem → List State → (Mem → Prop) → Prop
  | m, [], K => K m
  | m, s :: rest, K =>
      s.regs 0 = c → (∀ o < 112, s.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) →
      (∀ st, Ctx s.mem (s.regs 0) st → total st + nn s < 2 ^ 64 → UpdateEntry base s st) →
      (∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) →
      ∃ fuel w tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (w, tr) ∧
        CallsTotal base c w.mem rest K

theorem calls_total {base c : Word} : ∀ (calls : List State) (m : Mem) (st : SState) (K : Mem → Prop),
    Ctx m c st → total st + (calls.map nn).sum < 2 ^ 64 →
    (∀ m', Ctx m' c ((inputsOf calls).foldl M0Crypto.Spec.Blake2s.absorb st) →
      total ((inputsOf calls).foldl M0Crypto.Spec.Blake2s.absorb st) = total st + (calls.map nn).sum →
        K m') →
    CallsTotal base c m calls K
  | [], m, st, K, hc, _, hK => hK m (by simpa [inputsOf] using hc) (by simp [inputsOf])
  | s :: rest, m, st, K, hc, hb, hK => by
    intro h0 hm he hret
    rw [List.map_cons, List.sum_cons] at hb
    have hl : (LL s).length = nn s := by simp [LL, M0Crypto.Release.Blake2sStream.bytesAt_length]
    have ht := total_absorb (LL s) st
    have hcs : Ctx s.mem (s.regs 0) st := by rw [h0]; exact ctx_congr hc hm
    obtain ⟨n, hn⟩ := update_correct (he st hcs (by omega)) hret
    obtain ⟨w, tr, hru, hp, -⟩ := hn n (Nat.le_refl n)
    refine ⟨n, w, tr, hru, ?_⟩
    have hc' : Ctx w.mem c (M0Crypto.Spec.Blake2s.absorb st (LL s)) := by rw [← h0]; exact hp.ctx
    refine calls_total rest w.mem _ K hc' (by rw [ht, hl]; omega) (fun m' h1 h2 => hK m' ?_ ?_)
    · simpa [inputsOf, List.foldl_cons] using h1
    · simp only [inputsOf, List.map_cons, List.foldl_cons, List.map_cons, List.sum_cons] at h2 ⊢
      rw [h2, ht, hl]; omega

/-- **Claim C1, total correctness at machine level.** From a context pointer `c` and an entry
state of `init` meeting its obligations, `init` returns; then for any chain of `update` calls
meeting theirs, each returns; then for any entry state of `final` on that context, meeting its
obligations, `final` returns and the 32 bytes at its output pointer are the RFC 7693
BLAKE2s-256 digest of the concatenated inputs. No run is assumed. -/
theorem hash_correct {base c : Word} {s0 : State} (ei : Blake2sInit.InitEntry base s0)
    (hi0 : s0.regs 0 = c)
    (hreti : ∀ i < Artifacts.Release.size, s0.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i)
    (calls : List State) (hlen : (calls.map nn).sum < 2 ^ 64) :
    ∃ fuel t0 tr, Thumb.runUntil (s0.regs 14 &&& ~~~1#32) fuel s0 = .ok (t0, tr) ∧
      CallsTotal base c t0.mem calls (fun m =>
        ∀ sf : State, sf.regs 0 = c → (∀ o < 112, sf.mem (c + BitVec.ofNat 32 o) = m (c + BitVec.ofNat 32 o)) →
          (∀ st, Ctx sf.mem (sf.regs 0) st → total st < 2 ^ 64 → Blake2sFinal.FinalEntry base sf st) →
          (∀ i < Artifacts.Release.size, sf.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) →
          ∃ fuel tf tr, Thumb.runUntil (sf.regs 14 &&& ~~~1#32) fuel sf = .ok (tf, tr) ∧
            bytesAt tf.mem (sf.regs 1) 32 = M0Crypto.Spec.Blake2s.blake2s (inputsOf calls).flatten) := by
  obtain ⟨n, hn⟩ := init_correct ei hreti
  obtain ⟨t0, tr, hru, hp0, -⟩ := hn n (Nat.le_refl n)
  refine ⟨n, t0, tr, hru, ?_⟩
  have hc0 : Ctx t0.mem c M0Crypto.Spec.Blake2s.State.init := by rw [← hi0]; exact hp0.ctx
  have htot0 : total M0Crypto.Spec.Blake2s.State.init = 0 := rfl
  refine calls_total calls t0.mem _ _ hc0 (by rw [htot0]; omega) (fun m' h1 h2 => ?_)
  intro sf hf0 hfm hfe hretf
  have hcf : Ctx sf.mem (sf.regs 0) ((inputsOf calls).foldl M0Crypto.Spec.Blake2s.absorb
      M0Crypto.Spec.Blake2s.State.init) := by rw [hf0]; exact ctx_congr h1 hfm
  obtain ⟨nf, hnf⟩ := final_correct (hfe _ hcf (by rw [h2, htot0]; omega)) hretf
  obtain ⟨tf, trf, hruf, hpf, -⟩ := hnf nf (Nat.le_refl nf)
  refine ⟨nf, tf, trf, hruf, ?_⟩
  rw [hpf.out]
  exact M0Crypto.Spec.Blake2s.stream_partition (inputsOf calls)

end M0Crypto.Release.Blake2sHash
