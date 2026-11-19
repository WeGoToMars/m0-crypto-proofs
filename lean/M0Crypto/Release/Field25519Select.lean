import M0Crypto.Release.Field25519AddSubChain
import M0Crypto.Release.Field25519Word

set_option linter.unusedSimpArgs false

/-!
`select_words` (generator `tools/gen_x25519.py`), inlined in `m0c_x25519`: `dst = r7 = 0 ? a :
b` over eight words, `r0 = dst`, `r1 = a`, `r2 = b`, the mask `r7` either `0` or all ones.

The body is four copies of `selPair`: load two words of `a` and of `b`, select with
`a ^ ((b ^ a) & m)` (`Field25519Word.select_word`), store the two words to `dst`. One generic
lemma (`selPair_step`) carries the invariant over pair `k`: words below `2k` of `dst` are
selected, the others still hold their initial value. An input that is `dst` itself is read at
words `≥ 2k` only, before they are overwritten, so `a` and `b` may each be `dst` or disjoint
from it.
-/

namespace M0Crypto.Release.Field25519Select
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519AddSubChain
open M0Crypto.Release (Region)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Frame (FrameOk upd)
open M0Crypto.Release.Field25519Facts (psum psum_congr)
open M0Crypto.Release.Field25519Block (AccAll AccOk accAll_cons accAll_nil accAll_append)
open M0Crypto.Release.Field25519Mem (toReg0 toReg1 toReg2 toReg3 toReg4 toReg5 toReg6 toReg7)

/-- One pair: `ldm r1!, {r3, r4}; ldm r2!, {r5, r6}`, the select, `stm r0!, {r3, r4}`. -/
def selPair : List Instr :=
  ld34 ++ [.dp .eors 5 3, .dp .eors 6 4, .dp .ands 5 7, .dp .ands 6 7, .dp .eors 3 5,
    .dp .eors 4 6, .stm 0 0x18]

def selBody : List Instr := selPair ++ selPair ++ selPair ++ selPair

theorem selBody_falls : selBody.all Instr.falls = true := by decide +kernel

/-- The selected word. -/
def sel (M x y : Word) : Word := if M = 0 then x else y

private theorem dp_mem (s : State) (op : DpOp) (d m : LowReg) :
    ((Instr.dp op d m).next s).mem = s.mem := next_mem rfl s

/-- The two words a pair stores. -/
def selVs (s : State) : List Word :=
  [sel (s.regs 7) (read32 s.mem (slot (s.regs 1) 0)) (read32 s.mem (slot (s.regs 2) 0)),
    sel (s.regs 7) (read32 s.mem (slot (s.regs 1) 1)) (read32 s.mem (slot (s.regs 2) 1))]

theorem selPair_exec (s : State) (hm : s.regs 7 = 0 ∨ s.regs 7 = BitVec.allOnes 32) :
    let t := execAll selPair s
    t.mem = storeWords s.mem (s.regs 0) (selVs s) ∧
      t.regs 0 = slot (s.regs 0) 2 ∧ t.regs 1 = slot (s.regs 1) 2 ∧ t.regs 2 = slot (s.regs 2) 2 ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t
  obtain ⟨l3, l4, l5, l6, l1, l2, lm, -, lo⟩ := ld34_exec s
  have l7 : (execAll ld34 s).regs 7 = s.regs 7 := lo 7 (by decide) (by decide)
  have l0 : (execAll ld34 s).regs 0 = s.regs 0 := lo 0 (by decide) (by decide)
  simp only [t, selPair, execAll_append]
  generalize execAll ld34 s = s1 at l3 l4 l5 l6 l1 l2 lm lo l7 l0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [execAll, Field25519Mem.mem_stm, dp_mem,
      Field25519Mem.regs_stm, InstrNext.regs_eors, regs_ands, listRegs_18, List.map, State.reg,
      toReg0, toReg3, toReg4, toReg5, toReg6, toReg7, ite_true, ite_false, l3, l4, l5, l6, l7, l0,
      lm]
    rw [Field25519Word.select_word _ _ _ hm, Field25519Word.select_word _ _ _ hm, selVs, sel, sel]
  all_goals
    try simp (config := {decide := true}) only [execAll, Field25519Mem.regs_stm, InstrNext.regs_eors,
      regs_ands, State.reg, toReg0, toReg1, toReg2, toReg3, toReg4, toReg5, toReg6, ite_true,
      ite_false, l0, l1, l2, bitCount_18]
  · simp only [slot, Nat.mul_comm]
  · intro r h15 hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hr'
    simp only [execAll, Field25519Mem.regs_stm _ _ _ _ h15, InstrNext.regs_eors _ _ _ _ h15,
      regs_ands _ _ _ _ h15, toReg0, toReg3, toReg4, toReg5, toReg6, h0, h3, h4, h5, h6,
      ite_false]
    exact lo r h15 (by simp [h1, h2, h3, h4, h5, h6])

/-- The words of `dst` after `k` pairs. -/
def selG (m : Mem) (dst a b M : Word) (k i : Nat) : Word :=
  if i < 2 * k then sel M (read32 m (slot a i)) (read32 m (slot b i)) else read32 m (slot dst i)

/-- The invariant before pair `k`. -/
structure SelInv (m : Mem) (dst a b M : Word) (k : Nat) (s : State) : Prop where
  frame : ∃ F, FrameOk dst 8 m F s.mem ∧ ∀ i < 8, F i = selG m dst a b M k i
  r0 : s.regs 0 = slot dst (2 * k)
  r1 : s.regs 1 = slot a (2 * k)
  r2 : s.regs 2 = slot b (2 * k)
  r7 : s.regs 7 = M

theorem slot_two (p : Word) (k : Nat) : slot (slot p (2 * k)) 2 = slot p (2 * (k + 1)) := by
  rw [slot_slot, Nat.mul_add, Nat.mul_one]

/-- One pair carries the invariant from `k` to `k + 1`. -/
theorem selPair_step {m : Mem} {dst a b M : Word} {k : Nat} (hk : k < 4) {s : State}
    (hm : M = 0 ∨ M = BitVec.allOnes 32) (ha : a = dst ∨ Disj a 32 dst 32)
    (hb : b = dst ∨ Disj b 32 dst 32) (h : SelInv m dst a b M k s) :
    SelInv m dst a b M (k + 1) (execAll selPair s) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) →
        (execAll selPair s).regs r = s.regs r := by
  obtain ⟨⟨F, hF, hFG⟩, e0, e1, e2, e7⟩ := h
  obtain ⟨tm, t0, t1, t2, to⟩ := selPair_exec s (e7 ▸ hm)
  have hG : ∀ i, 2 * k ≤ i → i < 8 → F i = read32 m (slot dst i) := fun i h1 h2 => by
    rw [hFG i h2, selG]; simp only [show ¬ i < 2 * k by omega, ↓reduceIte]
  have rd : ∀ (p : Word), (p = dst ∨ Disj p 32 dst 32) → ∀ q < 2,
      read32 s.mem (slot (slot p (2 * k)) q) = read32 m (slot p (2 * k + q)) := fun p hp q hq => by
    rw [slot_slot]; exact read_in hF hG hp (by omega) (by omega)
  have hF' := hF.storeWords (selVs s) (k := 2 * k)
    (by simp only [selVs, List.length_cons, List.length_nil]; omega)
  rw [← e0, ← tm] at hF'
  refine ⟨⟨⟨_, hF', fun i hi => ?_⟩, ?_, ?_, ?_, ?_⟩, to⟩
  · simp only [upd, selVs, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
    rw [e1, e2, e7, rd a ha 0 (by omega), rd a ha 1 (by omega), rd b hb 0 (by omega),
      rd b hb 1 (by omega), hFG i hi]
    unfold selG
    rcases (show i < 2 * k ∨ i = 2 * k ∨ i = 2 * k + 1 ∨ 2 * k + 2 ≤ i by omega) with
      h | h | h | h
    · simp only [show ¬(2 * k ≤ i ∧ i < 2 * k + 2) by omega, show i < 2 * k by omega,
        show i < 2 * (k + 1) by omega, ↓reduceIte]
    · subst h; simp
    · subst h; simp [show 2 * k + 1 < 2 * (k + 1) by omega]
    · simp only [show ¬(2 * k ≤ i ∧ i < 2 * k + 2) by omega, show ¬ i < 2 * k by omega,
        show ¬ i < 2 * (k + 1) by omega, ↓reduceIte]
  · rw [t0, e0, slot_two]
  · rw [t1, e1, slot_two]
  · rw [t2, e2, slot_two]
  · rw [to 7 (by decide) (by decide), e7]

theorem selBody_split : selBody = selPair ++ (selPair ++ (selPair ++ selPair)) := by
  simp only [selBody, List.append_assoc]

/-- The whole body: `dst` holds `a` if `r7 = 0`, else `b`; bytes outside `dst` and registers
from `r7` up are unchanged. -/
theorem sel_exec (s : State) {dst a b : Word} (h0 : s.regs 0 = dst) (h1 : s.regs 1 = a)
    (h2 : s.regs 2 = b) (hm : s.regs 7 = 0 ∨ s.regs 7 = BitVec.allOnes 32)
    (hf : dst.toNat + 32 ≤ 2 ^ 32) (ha : a = dst ∨ Disj a 32 dst 32)
    (hb : b = dst ∨ Disj b 32 dst 32) :
    let t := execAll selBody s
    Field25519Routines.feVal t.mem dst =
        (if s.regs 7 = 0 then Field25519Routines.feVal s.mem a else Field25519Routines.feVal s.mem b) ∧
      (∀ y, ¬ Region dst 32 y → t.mem y = s.mem y) ∧
      ∀ r : Reg, r ≠ 15 → r ∉ ([0, 1, 2, 3, 4, 5, 6] : List Reg) → t.regs r = s.regs r := by
  intro t
  have I0 : SelInv s.mem dst a b (s.regs 7) 0 s :=
    ⟨⟨_, frame_init s.mem hf, fun i _ => by simp [selG]⟩, by rw [h0, slot_zero],
      by rw [h1, slot_zero], by rw [h2, slot_zero], rfl⟩
  simp only [t, selBody_split, execAll_append]
  obtain ⟨I1, o1⟩ := selPair_step (by decide) hm ha hb I0
  generalize execAll selPair s = s1 at I1 o1
  obtain ⟨I2, o2⟩ := selPair_step (by decide) hm ha hb I1
  generalize execAll selPair s1 = s2 at I2 o2
  obtain ⟨I3, o3⟩ := selPair_step (by decide) hm ha hb I2
  generalize execAll selPair s2 = s3 at I3 o3
  obtain ⟨I4, o4⟩ := selPair_step (by decide) hm ha hb I3
  generalize execAll selPair s3 = s4 at I4 o4
  obtain ⟨⟨F, hF, hFG⟩, -, -, -, -⟩ := I4
  refine ⟨?_, fun y hy => frame_out hF y hy, fun r h15 hr => by
    rw [o4 r h15 hr, o3 r h15 hr, o2 r h15 hr, o1 r h15 hr]⟩
  rw [feVal_frame hF]
  split
  · rename_i hz
    rw [Field25519Facts.feVal_psum]
    exact psum_congr fun i hi => by
      rw [hFG i hi, selG, sel]; simp only [show i < 2 * 4 by omega, hz, ↓reduceIte]
  · rename_i hz
    rw [Field25519Facts.feVal_psum]
    exact psum_congr fun i hi => by
      rw [hFG i hi, selG, sel]; simp only [show i < 2 * 4 by omega, hz, ↓reduceIte]

end M0Crypto.Release.Field25519Select
