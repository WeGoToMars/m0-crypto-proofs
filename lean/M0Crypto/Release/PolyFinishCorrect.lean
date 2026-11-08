import M0Crypto.Release.PolyFinishRun
import M0Crypto.Release.PolyFinishCheck
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace M0Crypto.Release.PolyFinish
open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.AEAD (p leBytes)

theorem tagState_tag (c : FCtx) (s : State) (he : FEntry c s) : (tagState s).regs 12 = c.tag := by
  rw [tagState, arithmetic_regs _ 12 (by decide) (by decide)]
  exact (header_effect c s he).2.2.1

theorem tagState_mem (c : FCtx) (s : State) (he : FEntry c s) : (tagState s).mem = c.mP := by
  rw [tagState, execAll_mem _ _ calc_noW]
  exact (header_effect c s he).1

theorem leBytes16_mod (x : Nat) : leBytes 16 (x % 2^128) = leBytes 16 x := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 16
  · rw [PolySpec.leBytes_get _ _ _ hi, PolySpec.leBytes_get _ _ _ hi]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [List.getElem?_eq_none (by rw [PolySpec.leBytes_length]; omega),
      List.getElem?_eq_none (by rw [PolySpec.leBytes_length]; omega)]

/-- The 16 caller-visible tag bytes implement final reduction and pad addition. -/
theorem result_tag (c : FCtx) (hv : FValid c) (s t : State) (he : FEntry c s) (ht : FResult c s t)
    (hh : c.acc < 2*p) :
    Ctx.bytesAt t.mem c.tag 16 = leBytes 16 (c.acc % p + c.padVal) := by
  rw [ht.mem, ← tagState_tag c s he, tagMem_bytes, tagState_value c hv s he hh, leBytes16_mod]

/-- Memory outside the tag and 20 saved-register bytes is unchanged. -/
theorem result_frame (c : FCtx) (s t : State) (he : FEntry c s) (ht : FResult c s t) :
    ∀ y, ¬ c.Wr y → t.mem y = c.m0 y := by
  intro y hy
  rw [ht.mem, tagMem, tagState_tag c s he, tagState_mem c s he, storeWords_other]
  · exact mP_other c y (fun h => hy (Or.inl h))
  · intro j k hj hk heq
    apply hy
    right
    refine ⟨4*j+k, by simp at hj; omega, ?_⟩
    rw [heq, ofNat_add_assoc]

/-- Poly1305 finish theorem for the exact release bytes, any tag alignment, and
h < 2p. Return, AAPCS preservation, scratch clearing, frame and writes are explicit. -/
theorem finish_correct (c : FCtx) (hv : FValid c) (s : State) (he : FEntry c s)
    (hh : c.acc < 2*p) (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr,
      Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧ FResult c s t ∧ WritesTo c.Wr tr ∧
      Ctx.bytesAt t.mem c.tag 16 = leBytes 16 (c.acc % p + c.padVal) ∧
      (∀ y, ¬ c.Wr y → t.mem y = c.m0 y) := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  obtain ⟨n, h⟩ := Reach.runUntil (P := FResult c s) hc
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact ne_of_disj hv.codeS.2.1 hv.codeS.1 (Or.symm hv.codeS.2.2) ho hi
      · exact ne_of_disj hv.codeT.2.1 hv.codeT.1 (Or.symm hv.codeT.2.2) ho hi)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((finish_reach c hv s he hlr).mono fun t ht => ⟨ht.ret, ht⟩)
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, hr, ht, hw⟩ := h fuel hf
  exact ⟨t, tr, hr, ht, hw, result_tag c hv s t he ht hh, result_frame c s t he ht⟩
end M0Crypto.Release.PolyFinish
