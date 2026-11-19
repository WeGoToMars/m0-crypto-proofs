import SafegcdTermination.SplitInput
import SafegcdTermination.FrameWords
import SafegcdTermination.BatchState

namespace SafegcdTermination.InitTail

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.InitCode
open SafegcdTermination.InitWords
open SafegcdTermination.SplitInput
open SafegcdTermination.Bank
open SafegcdTermination.FrameWords
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.BatchMachine (Slot Image)
open SafegcdTermination.LoopCounter (initialCount)
open M0Crypto.Armv6M (State Mem read32 write32 read32_write32_same)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

def initRegs (m : Mem) (sp : Word) : Mem :=
  write32 (write32 (write32 m (addr sp bankE) 1) (addr sp deltaAt) 1)
    (addr sp counterAt) (BitVec.ofNat 32 initialCount)

def splitRegs (s : State) : Mem := storeWords s.mem (addr s.sp bankG) (splitWords s 8)

theorem init_prime_word (i : Nat) (hi : i < 17)
    (s : State) (hTop : stackWord s (bankF+64) = 0#32) :
    stackWord (execAll putPrime s) (bankF+4*i) =
      if i=0 then 65517 else if i=15 then 32767 else if i=16 then 0 else 65535 := by
  obtain ⟨hS,hM⟩ := put_prime s
  have hAddr : addr s.sp bankF = s.sp := by simp [addr,bankF]
  have hLen : primeWords.length = 16 := by decide
  have hM' : (execAll putPrime s).mem = storeWords s.mem (addr s.sp bankF) primeWords := by rw [hM,hAddr]
  unfold stackWord stackAddr at *
  rw [hS,hM']
  change read32 (storeWords s.mem (addr s.sp bankF) primeWords) (addr s.sp (bankF+4*i)) = _
  by_cases e : i=16
  · subst i
    rw [store_read_outside (dst := bankF) (src := bankF+4*16) (vs := primeWords)
      (by decide) (by decide) (.inr (by decide))]
    exact hTop
  · have hRead := store_read (m := s.mem) (sp := s.sp) (dst := bankF) (vs := primeWords)
      (i := i) (by omega) (by decide)
    rw [hRead]
    have h : ∀ j : Fin 16, primeWords[j.val]'(Nat.lt_of_lt_of_le j.isLt (by decide)) =
        (if j.val=0 then 65517 else if j.val=15 then 32767 else if j.val=16 then 0 else 65535) := by
      decide +kernel
    exact h ⟨i,by omega⟩

theorem prime_slot (s : State) (hTop : stackWord s (bankF+64) = 0#32) :
    Slot (execAll putPrime s).mem s.sp bankF p := by
  let t := execAll putPrime s
  let v : Nat → Word := fun i =>
    if i=0 then 65517 else if i=15 then 32767 else if i=16 then 0 else 65535
  have hU := (put_prime s).1
  have hv (i : Nat) (hi : i < 17) : vec t.mem (addr s.sp bankF) i = v i := by
    rw [← hU,stack_vec]
    exact init_prime_word i hi s hTop
  refine ⟨?_,⟨fun i hi => ?_,?_⟩⟩
  · have hEq : value t.mem (addr s.sp bankF) = weighted (limb v) 17 :=
      weighted_congr 17 (fun i hi => by simp only [limb,hv i hi])
    exact hEq.trans (by decide +kernel)
  · rw [hv i (by omega)]
    have hh : ∀ j : Fin 16, (v j.val).toNat < 65536 := by
      dsimp [v]
      decide +kernel
    exact hh ⟨i,hi⟩
  · rw [hv 16 (by decide)]
    decide

theorem keep_prime_word (s : State) (o : Nat)
    (h : 64 ≤ o) (ho : o+4 ≤ 2^32) :
    stackWord (execAll putPrime s) o = stackWord s o := by
  obtain ⟨hSp,hMem⟩ := put_prime s
  have ha : addr s.sp bankF = s.sp := by simp [addr,bankF]
  have hl : primeWords.length = 16 := by decide
  unfold stackWord stackAddr
  rw [hSp,hMem]
  change read32 (storeWords s.mem s.sp primeWords) (addr s.sp o) = read32 s.mem (addr s.sp o)
  have hh := store_read_outside (m := s.mem) (sp := s.sp) (src := o) (dst := bankF) (vs := primeWords)
    ho (by decide) (.inr (by rw [hl]; exact h))
  simpa only [ha] using hh

theorem keep_split_word (s : State) (o : Nat) (ho : o+4 ≤ 2^32)
    (h : o+4 ≤ bankG ∨ bankG+64 ≤ o) :
    stackWord (execAll putInput s) o = stackWord s o := by
  obtain ⟨hSp,hMem⟩ := split_exec s 8 (by decide)
  have hSP : (execAll putInput s).sp = s.sp := hSp
  have hM : (execAll putInput s).mem = splitRegs s := hMem
  unfold stackWord stackAddr
  rw [hSP,hM]
  unfold splitRegs
  apply store_read_outside ho (by rw [split_length]; decide)
  rw [split_length]
  exact h

theorem keep_initreg (s : State) (o : Nat) (ho : o+4 ≤ 2^32)
    (hE : o+4 ≤ bankE ∨ bankE+4 ≤ o) (hD : o+4 ≤ deltaAt ∨ deltaAt+4 ≤ o)
    (hC : o+4 ≤ counterAt ∨ counterAt+4 ≤ o) :
    stackWord (execAll putInitialWords s) o = stackWord s o := by
  obtain ⟨hSp,hMem⟩ := initial_words s
  unfold stackWord stackAddr
  rw [hSp,hMem]
  change read32 (initRegs s.mem s.sp) (addr s.sp o) = read32 s.mem (addr s.sp o)
  rw [initRegs,write_read_outside ho (by decide) hC,write_read_outside ho (by decide) hD,
    write_read_outside ho (by decide) hE]

theorem word_init (s : State) :
    let u := execAll putInitialWords s
    stackWord u bankE = 1#32 ∧ stackWord u deltaAt = 1#32 ∧
      stackWord u counterAt = BitVec.ofNat 32 initialCount := by
  obtain ⟨hSp,hMem⟩ := initial_words s
  dsimp only
  unfold stackWord stackAddr
  rw [hSp,hMem]
  refine ⟨?_,?_,read32_write32_same _ _ _⟩
  · change read32 (initRegs s.mem s.sp) (addr s.sp bankE) = 1#32
    rw [initRegs,write_read_outside (src := bankE) (dst := counterAt) (by decide) (by decide) (.inl (by decide)),
      write_read_outside (src := bankE) (dst := deltaAt) (by decide) (by decide) (.inl (by decide))]
    exact read32_write32_same _ _ _
  · change read32 (initRegs s.mem s.sp) (addr s.sp deltaAt) = 1#32
    rw [initRegs,write_read_outside (src := deltaAt) (dst := counterAt) (by decide) (by decide) (.inl (by decide))]
    exact read32_write32_same _ _ _

theorem formed_of_words {m : Mem} {a : Word}
    (h : ∀ i < 16, (vec m a i).toNat < 65536) (ht : vec m a 16 = 0#32) :
    VecWellFormed (vec m a) := by
  refine ⟨h,?_⟩
  rw [ht]
  decide

theorem constant_slot {m : Mem} {sp : Word} {off : Nat} (w : Word) (hw : w.toNat < 65536)
    (h₀ : vec m (addr sp off) 0 = w) (h : ∀ i, 0 < i → i < 17 → vec m (addr sp off) i = 0#32) :
    Slot m sp off (w.toNat : Int) := by
  refine ⟨?_,formed_of_words (fun i hi => ?_) (h 16 (by decide) (by decide))⟩
  · let f : Nat → Int := fun i => if i=0 then w.toNat else 0
    have e : value m (addr sp off) = weighted f 17 := weighted_congr 17 fun i hi => by
      by_cases e : i=0
      · subst i
        simp [limb,f,h₀]
      · have hz := h i (by omega) hi
        simp [limb,f,hz,e,show (0#32).toInt = 0 from rfl]
    rw [e]
    have hSum : ∀ i, weighted f (i+1) = (w.toNat : Int) := by
      intro i
      induction i with
      | zero => simp [weighted,f]
      | succ i ih =>
        rw [weighted,ih]
        simp [f]
    exact hSum 16
  · by_cases e : i=0
    · subst i
      rwa [h₀]
    · rw [h i (by omega) (by omega)]
      decide

end SafegcdTermination.InitTail
