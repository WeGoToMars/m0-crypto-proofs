import M0Crypto.Release.Blake2sUpdateReach
import M0Crypto.Release.Blake2sFinalReach
import M0Crypto.Release.Blake2sInit
import M0Crypto.Spec.Blake2s

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # The streaming interface: `init`, `update`, `final`

Each function's correctness is stated for a run to its return address (`runUntil`), from the
proofs' entry structures (`InitEntry`, `UpdateEntry`, `FinalEntry`), with the set of memory
bytes it may write. `Blake2sClaims.lean` restates them over the contract's `Pre`;
`Blake2sComposed.lean` chains them over a whole hash. -/

namespace M0Crypto.Release.Blake2sHash

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)

theorem wr_disj {base a : Word} {n : Nat} (h : Disj base Artifacts.Release.size a n) {o i : Nat}
    (ho : o < n) (hi : i < Artifacts.Release.size) : a + BitVec.ofNat 32 o ≠ base + BitVec.ofNat 32 i :=
  fun eq => M0Crypto.Release.Blake2sInit.disj_ne h hi ho eq.symm

/-- `m0c_blake2s_init(c)`: afterwards the context holds the empty stream. -/
theorem init_correct_of_entry {base : Word} {s : State} (e : Blake2sInit.InitEntry base s)
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
theorem update_correct_of_entry {base : Word} {s : State} {st0 : Blake2sUpdate.SState}
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
theorem final_correct_of_entry {base : Word} {s : State} {st : M0Crypto.Spec.Blake2s.State}
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

/-! ## Facts for the composition (`Blake2sComposed.lean`) -/

open M0Crypto.Release.Blake2sStream (Ctx CtxNU bytesAt bytesAt_length bytesAt_congr)
open M0Crypto.Release.Frame (read32_congr)
open M0Crypto.Release.Blake2sUpdate (SState)

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

end M0Crypto.Release.Blake2sHash
