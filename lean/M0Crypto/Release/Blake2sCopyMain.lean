import M0Crypto.Release.Blake2sCopyFlow
import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.ReachN

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_copy`: the function-level contract -/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Blake2sPro (regs_push mem_push)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

theorem l4567 : listRegs (240 : BitVec 8) = [4, 5, 6, 7] := by decide
theorem b4567 : bitCount (240 : BitVec 8) = 4 := by decide

theorem pro_eff (s : State) :
    (execAll proL s).regs 13 = s.regs 13 - 20#32 ∧ (execAll proL s).regs 4 = 3#32 ∧
    (∀ r : Reg, r.val ≠ 4 → r.val ≠ 13 → r.val ≠ 15 → (execAll proL s).regs r = s.regs r) ∧
    (execAll proL s).mem = storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] := by
  have e13 : ((Instr.push 0xF0 true).next s).regs 13 = s.regs 13 - 20#32 := by
    rw [regs_push _ _ _ _ (by decide)]; rfl
  have eo : ∀ r : Reg, r ≠ 13 → r ≠ 15 → ((Instr.push 0xF0 true).next s).regs r = s.regs r := by
    intro r h13 h15; rw [regs_push _ _ _ _ h15]; simp [h13]
  have em : ((Instr.push 0xF0 true).next s).mem = storeWords s.mem (s.regs 13 - 20#32)
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14] := by
    rw [mem_push, l4567, b4567]; rfl
  have hp : proL = [Instr.push 0xF0 true, Instr.movImm 4 3] := rfl
  have hx : execAll proL s = (Instr.movImm 4 3).next ((Instr.push 240 true).next s) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hx, M0Crypto.Release.Blake2s.regs_movImm _ _ _ _ (by decide)]
    rw [show LowReg.toReg 4 = (4 : Reg) from rfl, if_neg (by decide), e13]
  · rw [hx, M0Crypto.Release.Blake2s.regs_movImm _ _ _ _ (by decide)]
    rw [show LowReg.toReg 4 = (4 : Reg) from rfl, if_pos rfl]; rfl
  · intro r h4 h13 h15
    have h4' : r ≠ 4 := fun e => h4 (by rw [e]; rfl)
    have h13' : r ≠ 13 := fun e => h13 (by rw [e]; rfl)
    have h15' : r ≠ 15 := fun e => h15 (by rw [e]; rfl)
    rw [hx, M0Crypto.Release.Blake2s.regs_movImm _ _ _ _ h15']
    rw [show LowReg.toReg 4 = (4 : Reg) from rfl, if_neg h4', eo r h13' h15']
  · rw [hx, M0Crypto.Release.Blake2s.mem_movImm, em]


/-! ## Entry contract -/

/-- Frame base of a call entered in state `s` (the 20-byte `push {r4-r7,lr}` frame). -/
def fr (s : State) : Word := s.regs 13 - 20#32

/-- The write window: the frame and the destination. -/
def WrC (s : State) : Word → Prop := fun y =>
  (∃ o < 20, y = fr s + BitVec.ofNat 32 o) ∨ (∃ o < (s.regs 2).toNat, y = s.regs 0 + BitVec.ofNat 32 o)

/-- The entry state of `m0c_blake2s_copy(dst = r0, src = r1, n = r2)` for an artifact loaded at `base`. -/
structure CopyEntry (base : Word) (s : State) : Prop where
  base4 : base.toNat % 4 = 0
  pc : s.pc = base + BitVec.ofNat 32 cStart
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  spLo : 20 ≤ (s.regs 13).toNat
  lr : (s.regs 14).getLsbD 0 = true
  n1 : 1 ≤ (s.regs 2).toNat
  n64 : (s.regs 2).toNat ≤ 64
  dj : Disj (s.regs 0) (s.regs 2).toNat (s.regs 1) (s.regs 2).toNat
  codeD : Disj base Artifacts.Release.size (s.regs 0) (s.regs 2).toNat
  codeF : Disj base Artifacts.Release.size (fr s) 20
  dstF : Disj (s.regs 0) (s.regs 2).toNat (fr s) 20
  srcF : Disj (s.regs 1) (s.regs 2).toNat (fr s) 20

/-- What the call leaves: `dst[0,n) = src[0,n)`, callee-saved registers and `sp` restored,
memory unchanged outside the destination and the frame. -/
structure CopyPost (s t : State) : Prop where
  pc : t.pc = s.regs 14 &&& ~~~1#32
  sp : t.regs 13 = s.regs 13
  r4 : t.regs 4 = s.regs 4
  r5 : t.regs 5 = s.regs 5
  r6 : t.regs 6 = s.regs 6
  r7 : t.regs 7 = s.regs 7
  r8 : t.regs 8 = s.regs 8
  r9 : t.regs 9 = s.regs 9
  r10 : t.regs 10 = s.regs 10
  r11 : t.regs 11 = s.regs 11
  copy : ∀ i < (s.regs 2).toNat, t.mem (s.regs 0 + BitVec.ofNat 32 i) = s.mem (s.regs 1 + BitVec.ofNat 32 i)
  mem : ∀ y, (∀ o < 20, y ≠ fr s + BitVec.ofNat 32 o) → (∀ o < (s.regs 2).toNat, y ≠ s.regs 0 + BitVec.ofNat 32 o) →
    t.mem y = s.mem y

theorem ne_frame {a f : Word} {n : Nat} (hD : Disj a n f 20) {i : Nat} (hi : i < n) {j k : Nat}
    (hj : j < 5) (hk : k < 4) : a + BitVec.ofNat 32 i ≠ f + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 k := by
  obtain ⟨h1, h2, h3⟩ := hD
  intro eq
  have := congrArg BitVec.toNat eq
  rw [ofNat_add_assoc, toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
  omega


/-- The source bytes. -/
def SrcR (s : State) : Word → Prop := fun y => ∃ o < (s.regs 2).toNat, y = s.regs 1 + BitVec.ofNat 32 o

theorem copy_reachR {base : Word} {s : State} (e : CopyEntry base s) :
    ReachNR base (WrC s) (SrcR s) s (CopyPost s) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : (s.regs 2).toNat < 2 ^ 31 := by have := e.n64; omega
  refine ReachNR.symBlock hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 - 20#32), 20)] [] proL cStart e.pc
    (by decide) pro_at (by decide) ?_ ?_ (by simp) (by decide +kernel) (by decide +kernel) ?_
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact e.sp4
  · apply Reach.region_one
    intro o ho
    exact Or.inl ⟨o, ho, by unfold fr; bv_omega⟩
  obtain ⟨p13, p4, po, pm⟩ := pro_eff s
  have hpc1 : (execAll proL s).pc = base + BitVec.ofNat 32 oTst := by
    rw [execAll_pc _ _ (by decide), e.pc, ofNat_add_assoc]; rfl
  have hci : CI (execAll proL s).regs (execAll proL s).mem (s.regs 0) (s.regs 1) (s.regs 2).toNat 0
      (execAll proL s) := by
    refine ⟨?_, ?_, ?_, cp_zero _ _ _, fun r _ _ => rfl, Nat.zero_le _⟩
    · rw [po 0 (by decide) (by decide) (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [po 1 (by decide) (by decide) (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [po 2 (by decide) (by decide) (by decide)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.sub_zero]
      exact (Nat.mod_eq_of_lt (s.regs 2).isLt).symm
  have hal := align_loop (Wr := WrC s) (Rd := SrcR s) (R := (execAll proL s).regs) (m0 := (execAll proL s).mem)
    (d := s.regs 0) (s := s.regs 1) (n := (s.regs 2).toNat) hb2 e.dj hn
    (fun i hi => Or.inr ⟨i, hi, rfl⟩) (fun i hi => ⟨i, hi, rfl⟩) 0 _ hpc1 hci (by have := e.n1; omega) p4
  refine ReachNR.bind (ReachNR.mono hal (fun u hu => ?_))
  obtain ⟨hpcU, hciU⟩ := hu
  have U13 : u.regs 13 = fr s := by
    rw [hciU.hi 13 (by decide) (by decide)]; exact p13
  have key : ∀ i (hi : i < 5), read32 u.mem (fr s + BitVec.ofNat 32 (4 * i)) =
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14][i]'(by simpa using hi) := by
    intro i hi
    have h1 : read32 u.mem (fr s + BitVec.ofNat 32 (4 * i)) =
        read32 (execAll proL s).mem (fr s + BitVec.ofNat 32 (4 * i)) := by
      apply read32_congr
      intro k hk
      exact hciU.cp.2 _ (fun j hj => (ne_frame e.dstF hj hi hk).symm)
    rw [h1, pm]
    exact M0Crypto.Release.Frame.read32_storeWords_same _ (fr s) _ i (by simpa using hi) (by simp)
  have k0 : read32 u.mem (fr s) = s.regs 4 := by
    have := key 0 (by decide); rwa [show fr s + BitVec.ofNat 32 (4 * 0) = fr s by bv_omega] at this
  have k1 : read32 u.mem (fr s + 4#32) = s.regs 5 := by
    have := key 1 (by decide); rwa [show BitVec.ofNat 32 (4 * 1) = 4#32 from rfl] at this
  have k2 : read32 u.mem (fr s + 8#32) = s.regs 6 := by
    have := key 2 (by decide); rwa [show BitVec.ofNat 32 (4 * 2) = 8#32 from rfl] at this
  have k3 : read32 u.mem (fr s + 12#32) = s.regs 7 := by
    have := key 3 (by decide); rwa [show BitVec.ofNat 32 (4 * 3) = 12#32 from rfl] at this
  have k4 : read32 u.mem (fr s + 16#32) = s.regs 14 := by
    have := key 4 (by decide); rwa [show BitVec.ofNat 32 (4 * 4) = 16#32 from rfl] at this
  have hbit : (read32 u.mem (u.regs 13 + 16#32)).getLsbD 0 = true := by
    rw [U13, k4]; exact e.lr
  obtain ⟨s1, hex, sm, s13', s4, s5, s6, s7, so, spc⟩ :=
    M0Crypto.Release.Blake2sCompress.pop_exec u hbit
  refine ReachNR.step hb2 oDone popL hpcU (by decide) done_at (by rw [B_len]; decide) ?_ hex ?_ ?_
  · have hb4 : bitCount (240 : BitVec 8) = 4 := b4567
    simp only [popL, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
      Access.aligned, State.sp, hb4, U13]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Bool.toNat_true] at hi
    have : (fr s + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      have := e.sp4; have := e.spLo; have := (s.regs 13).isLt
      unfold fr
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simpa using this
  · intro y ⟨a, ha, hk, _⟩
    simp only [popL, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp at hk
  · refine ReachNR.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [spc, U13, k4]
    · rw [s13', U13]; unfold fr; bv_omega
    · rw [s4, U13, k0]
    · rw [s5, U13, k1]
    · rw [s6, U13, k2]
    · rw [s7, U13, k3]
    · rw [so 8 (Or.inr ⟨by decide, by decide⟩), hciU.hi 8 (by decide) (by decide), po 8 (by decide) (by decide) (by decide)]
    · rw [so 9 (Or.inr ⟨by decide, by decide⟩), hciU.hi 9 (by decide) (by decide), po 9 (by decide) (by decide) (by decide)]
    · rw [so 10 (Or.inr ⟨by decide, by decide⟩), hciU.hi 10 (by decide) (by decide), po 10 (by decide) (by decide) (by decide)]
    · rw [so 11 (Or.inr ⟨by decide, by decide⟩), hciU.hi 11 (by decide) (by decide), po 11 (by decide) (by decide) (by decide)]
    · intro i hi
      rw [sm, hciU.cp.1 i hi, pm]
      refine storeWords_other _ _ _ _ (fun j k hj hk eq => ?_)
      exact ne_frame e.srcF hi (by simpa using hj) hk eq
    · intro y hy1 hy2
      rw [sm, hciU.cp.2 y hy2, pm]
      refine storeWords_other _ _ _ _ (fun j k hj hk eq => ?_)
      exact hy1 (4 * j + k) (by simp at hj; omega) (by rw [eq, ofNat_add_assoc]; rfl)

theorem copy_reach {base : Word} {s : State} (e : CopyEntry base s) :
    ReachN base (WrC s) s (CopyPost s) :=
  ReachS.mono (copy_reachR e) (P' := PN fun _ => WrC s) (fun _ _ p => p.pn) (fun _ h => h)

/-- **`m0c_blake2s_copy` is correct.** Entered at the function start with `1 ≤ n ≤ 64`, disjoint
source and destination, neither overlapping the code or the 20-byte frame, and returning to an
address outside the code: the run returns with `CopyPost` after enough steps, writing only the
frame and the destination. -/
theorem copy_correct {base : Word} {s : State} (e : CopyEntry base s)
    (hret : ∀ i < Artifacts.Release.size, s.regs 14 &&& ~~~1#32 ≠ base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      CopyPost s t ∧ WritesTo (WrC s) tr := by
  obtain ⟨n, h⟩ := Reach.runUntil (P := CopyPost s) e.code
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := e.codeF
        intro eq
        have := congrArg BitVec.toNat eq
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
        omega
      · obtain ⟨h1, h2, h3⟩ := e.codeD
        intro eq
        have := congrArg BitVec.toNat eq
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
        omega)
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((copy_reach e).toReach.mono (fun t ht => ⟨ht.pc, ht⟩))
  exact ⟨n, h⟩

/-! ## Non-vacuity -/

/-- A concrete entry state: artifact at 0, unaligned `dst` and `src`, `n = 64`. -/
def wState : State where
  regs := fun r =>
    if r = 0 then 0x20000001#32 else if r = 1 then 0x20000102#32 else if r = 2 then 64#32
    else if r = 13 then 0x20001000#32 else if r = 14 then 0x00010001#32
    else if r = 15 then BitVec.ofNat 32 cStart else 0#32
  n := false
  z := false
  c := false
  v := false
  mem := fun a => B.getD a.toNat 0

/-- The hypotheses of `copy_correct` are satisfiable (`wState` meets them). -/
theorem copy_correct_nonvacuous : CopyEntry 0 wState ∧
    ∀ i < Artifacts.Release.size, wState.regs 14 &&& ~~~1#32 ≠ 0 + BitVec.ofNat 32 i := by
  have hlen := B_len
  refine ⟨⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hi' : i < 2 ^ 32 := by rw [hlen] at hi; unfold Artifacts.Release.size at hi; omega
    have e : (0 + BitVec.ofNat 32 i).toNat = i := by
      have h0 : (0 : Word).toNat = 0 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h0]; omega
    show B.getD (0 + BitVec.ofNat 32 i).toNat 0 = _
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  all_goals first
    | (intro i hi heq; have := congrArg BitVec.toNat heq; simp [wState] at this
       unfold Artifacts.Release.size at hi; omega)
    | (simp only [Disj, fr, wState, Artifacts.Release.size]; decide)

end M0Crypto.Release.Blake2sCopy
