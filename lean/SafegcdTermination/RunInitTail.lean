import SafegcdTermination.InitTail
import SafegcdTermination.ClearLoop

namespace SafegcdTermination.RunInitTail

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.InitCode SafegcdTermination.InitWords SafegcdTermination.SplitInput
open SafegcdTermination.Bank SafegcdTermination.FrameWords SafegcdTermination.InitTail
open SafegcdTermination.Packing (split_high)
open SafegcdTermination.FoldRefine (vec)
open SafegcdTermination.BatchMachine (Image Slot)
open SafegcdTermination.LoopCounter (initialCount)
open M0Crypto.Armv6M (State)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)
open M0Crypto.Thumb

set_option maxHeartbeats 900000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

def Cleared (s : State) : Prop :=
  ∀ i < 4*clearIterations, stackWord s (4*i) = 0#32

theorem cleared_of_store (s t : State) (hs : t.sp = s.sp)
    (hm : t.mem = storeWords s.mem s.sp (List.replicate (4*clearIterations) 0)) : Cleared t := by
  intro i hi
  unfold stackWord stackAddr
  rw [hs,hm]
  let ws : List Word := List.replicate (4*clearIterations) 0
  have e := store_read (m := s.mem) (sp := s.sp) (dst := 0) (vs := ws) (i := i)
    (by simpa [ws] using hi) (by decide)
  simpa [ws,addr] using e

private theorem safe_initial_words (s : State) :
    WritesOnly s.mem (execAll putInitialWords s).mem s.sp frameBytes := by
  rw [(initial_words s).2]
  exact WritesOnly.trans (WritesOnly.trans (write_frame (dst := bankE) (by decide))
    (write_frame (dst := deltaAt) (by decide))) (write_frame (dst := counterAt) (by decide))

private theorem safe_split_words (s : State) :
    WritesOnly s.mem (execAll putInput s).mem s.sp frameBytes := by
  have h := (split_exec s 8 (by decide)).2
  rw [show (execAll putInput s).mem = _ from h]
  apply store_frame
  rw [split_length]
  decide

private theorem safe_prime_words (s : State) :
    WritesOnly s.mem (execAll putPrime s).mem s.sp frameBytes := by
  rw [(put_prime s).2]
  simpa only [show addr s.sp bankF = s.sp by simp [addr,bankF]] using
    (store_frame (m := s.mem) (sp := s.sp) (dst := bankF) (vs := primeWords) (frame := frameBytes) (by decide))

private theorem split_sp (s : State) : (execAll putInput s).sp = s.sp :=
  (split_exec s 8 (by decide)).1

private theorem init_g (u : State)
    (hTop : stackWord u (bankG+64) = 0#32) :
    let v := execAll putInput u
    let t := execAll putPrime v
    Slot t.mem t.sp bankG (feVal u.mem (addr u.sp temp)) := by
  let v := execAll putInput u
  let t := execAll putPrime v
  have hV : v.sp = u.sp := split_sp u
  have hT : t.sp = v.sp := (put_prime v).1
  have hWord (i : Nat) (hi : i < 17) : vec t.mem (addr t.sp bankG) i = vec v.mem (addr u.sp bankG) i := by
    rw [← hV, stack_vec, stack_vec]
    exact keep_prime_word v _ (by unfold bankG vectorBytes; omega) (by unfold bankG vectorBytes; omega)
  have hZero : vec t.mem (addr t.sp bankG) 16 = 0#32 := by
    rw [hWord 16 (by decide), ← hV, stack_vec]
    exact (keep_split_word u (bankG+64) (by decide) (.inr (by decide))).trans hTop
  have hLimbs (i : Nat) (hi : i < 8) :
      vec t.mem (addr t.sp bankG) (2*i) = low (stackWord u (temp+4*i)) ∧
      vec t.mem (addr t.sp bankG) (2*i+1) = stackWord u (temp+4*i) >>> 16 := by
    rw [hWord _ (by omega),hWord _ (by omega)]
    exact split_limbs u i hi
  refine ⟨?_,formed_of_words (fun i hi => ?_) hZero⟩
  · rw [hT,hV]
    exact split_value u t.mem hLimbs hZero
  · have h := hLimbs (i/2) (by omega)
    by_cases hEven : i % 2 = 0
    · rw [show i = 2*(i/2) by omega, h.1]
      exact low_bound _
    · rw [show i = 2*(i/2)+1 by omega, h.2]
      exact split_high _

private theorem keep_source (s : State) :
    let t := execAll putInitialWords s
    feVal t.mem (addr t.sp temp) = feVal s.mem (addr s.sp temp) := by
  simp only [feVal_psum]
  apply psum_congr
  intro i hi
  simp only [slot_addr]
  exact congrArg BitVec.toNat (keep_initreg s (temp+4*i) (by unfold temp vectorBytes; omega)
    (.inr (by unfold temp bankE vectorBytes; omega))
    (.inl (by unfold temp deltaAt outputAt vectorBytes; omega))
    (.inl (by unfold temp counterAt deltaAt outputAt vectorBytes; omega)))

private theorem cleared_word (s : State) (h : Cleared s) (off : Nat)
    (ha : off % 4 = 0) (ho : off < 4*vectorBytes) : stackWord s off = 0#32 := by
  rw [show off = 4*(off/4) by omega]
  apply h
  have hCnt : 4*clearIterations = vectorBytes := by decide
  omega

/-- Establish the phase-zero image from the cleared frame and copied field input. -/
theorem tail_image (s : State) (h : Cleared s) :
    let t := execAll tail s
    t.sp = s.sp ∧ WritesOnly s.mem t.mem s.sp frameBytes ∧
      Image t (phases 0) (initial (feVal s.mem (addr s.sp temp))) ∧
      stackWord t counterAt = BitVec.ofNat 32 initialCount ∧
      stackWord t outputAt = stackWord s outputAt ∧ stackWord t returnAt = stackWord s returnAt := by
  let u := execAll putInitialWords s
  let v := execAll putInput u
  let t := execAll putPrime v
  have hU : u.sp = s.sp := (initial_words s).1
  have hV : v.sp = u.sp := split_sp u
  have hT : t.sp = v.sp := (put_prime v).1
  have hSp := hT.trans (hV.trans hU)
  have wSplit : WritesOnly u.mem v.mem s.sp frameBytes := by rw [← hU]; exact safe_split_words u
  have wPrime : WritesOnly v.mem t.mem s.sp frameBytes := by rw [← hU,← hV]; exact safe_prime_words v
  have wInit : WritesOnly s.mem u.mem s.sp frameBytes := safe_initial_words s
  have writes := WritesOnly.trans (WritesOnly.trans wInit wSplit) wPrime
  have hConst := word_init s
  have hCtrl (o : Nat) (h0 : 64 ≤ o) (h1 : o+4 ≤ 2^32)
      (h2 : o+4 ≤ bankG ∨ bankG+64 ≤ o) : stackWord t o = stackWord u o :=
    (keep_prime_word v o h0 h1).trans (keep_split_word u o h1 h2)
  have hF : Slot t.mem t.sp bankF p := by
    rw [hT]
    refine prime_slot v ?_
    rw [keep_split_word u _ (by decide) (.inl (by decide)),
      keep_initreg s _ (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide))]
    exact cleared_word s h _ (by decide) (by decide)
  have hg0 : stackWord u (bankG+64) = 0#32 := by
    rw [keep_initreg s _ (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by decide))]
    exact cleared_word s h _ (by decide) (by decide)
  have hG := init_g u hg0
  change Slot t.mem t.sp bankG (feVal u.mem (addr u.sp temp)) at hG
  have hSource : feVal u.mem (addr u.sp temp) = feVal s.mem (addr s.sp temp) := keep_source s
  rw [hSource] at hG
  have hResidue (o i : Nat) (he : o=bankD ∨ o=bankE) (hi : i<17) (hE : o=bankE → i>0) :
      vec t.mem (addr t.sp o) i = 0#32 := by
    rw [stack_vec, hCtrl _ (by rcases he with rfl | rfl <;> simp only [bankD, bankE, vectorBytes] <;> omega)
      (by rcases he with rfl | rfl <;> simp only [bankD, bankE, vectorBytes] <;> omega)
      (.inr (by rcases he with rfl | rfl <;> simp only [bankG, bankD, bankE, vectorBytes] <;> omega))]
    rw [keep_initreg s _ (by rcases he with rfl | rfl <;> simp only [bankD, bankE, vectorBytes] <;> omega)
      (by rcases he with rfl | rfl
          · left; unfold bankD bankE vectorBytes; omega
          · right; simpa only [Nat.add_le_add_iff_left] using (show 4 ≤ 4*i by have := hE rfl; omega))
      (.inl (by rcases he with rfl | rfl <;> simp only [bankD, bankE, deltaAt, outputAt, vectorBytes] <;> omega))
      (.inl (by rcases he with rfl | rfl <;> simp only [bankD, bankE, counterAt, deltaAt, outputAt, vectorBytes] <;> omega))]
    exact cleared_word s h _ (by rcases he with rfl | rfl <;> simp only [bankD, bankE, vectorBytes] <;> omega)
      (by rcases he with rfl | rfl <;> simp only [bankD, bankE, vectorBytes] <;> omega)
  have hDE : bankD ≠ bankE := by decide
  have hD : Slot t.mem t.sp bankD 0 :=
    constant_slot 0 (by decide) (hResidue bankD 0 (.inl rfl) (by decide) (by decide))
      (fun i _ hi => hResidue bankD i (.inl rfl) hi (fun hn => (hDE hn).elim))
  have hE : Slot t.mem t.sp bankE 1 :=
    constant_slot 1 (by decide) (by rw [stack_vec,Nat.mul_zero,Nat.add_zero]; exact
      (hCtrl bankE (by decide) (by decide) (.inr (by decide))).trans hConst.1)
      (fun i hl hi => hResidue bankE i (.inr rfl) hi (fun _ => hl))
  have hDelta := (hCtrl deltaAt (by decide) (by decide) (.inr (by decide))).trans hConst.2.1
  have hCount := (hCtrl counterAt (by decide) (by decide) (.inr (by decide))).trans hConst.2.2
  have hOut := (hCtrl outputAt (by decide) (by decide) (.inr (by decide))).trans
    (keep_initreg s outputAt (by decide) (.inr (by decide)) (.inl (by decide)) (.inl (by decide)))
  have hRet := (hCtrl returnAt (by decide) (by decide) (.inr (by decide))).trans
    (keep_initreg s returnAt (by decide) (.inr (by decide)) (.inr (by decide)) (.inr (by decide)))
  rw [tail,execAll_append,execAll_append]
  exact ⟨hSp,writes,⟨⟨hF,hG,hD,hE⟩,hDelta⟩,hCount,hOut,hRet⟩

end SafegcdTermination.RunInitTail
