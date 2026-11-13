import M0Crypto.Release.X25519CRExec
import M0Crypto.Release.X25519Block

set_option linter.unusedSimpArgs false

/-!
The data accesses of `combineReduce`: every access is word-aligned, the only writes are the
four words over `H0..H3` (phase C) and the eight output words.

One generic lemma `accAll_inv` checks a block instruction by instruction under an invariant
on the state. Phases A and B (and the add step of C) keep `sp` and `r7` aligned (`SA`); the top
word keeps `sp` aligned; the loop keeps `sp` aligned and `r0` at the output pointer. The
phase-C store is checked with the frame pointer from `addH_exec`.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Macros (sl SH SP_ SPP SN SDST combineReduce reducePhaseA reducePhaseB
  reducePhaseC reduceTop reduceLoop reduceWord xorN)

/-- A block whose every instruction keeps the invariant `I` and has accesses satisfying `P`
under it. -/
theorem accAll_inv {P : Access → Prop} (I : State → Prop) :
    ∀ (is : List Instr) (s : State), I s →
      (∀ i ∈ is, ∀ t, I t → I (i.next t) ∧ ∀ a ∈ i.accesses t, P a) → AccAll P is s
  | [], s, _, _ => accAll_nil P s
  | i :: is, s, hs, h => by
    obtain ⟨h1, h2⟩ := h i List.mem_cons_self s hs
    exact accAll_cons h2 (accAll_inv I is _ h1 fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem next_regs_other (i : Instr) (s : State) (r : Reg) (h15 : r.val ≠ 15)
    (h : r.val ∉ i.dsts) : (i.next s).regs r = s.regs r :=
  execAll_regs_other [i] s r h15 (by simp [h])

/-- `sp` and `r7` word-aligned. -/
def SA (s : State) : Prop := s.sp.toNat % 4 = 0 ∧ (s.reg 7).toNat % 4 = 0

/-- Instruction `i` keeps the invariant `I` and its accesses are `AccOk Wr` under it. -/
@[irreducible] def IOk (I : State → Prop) (Wr : Word → Prop) (i : Instr) : Prop :=
  ∀ t, I t → I (i.next t) ∧ ∀ a ∈ i.accesses t, AccOk Wr a

theorem IOk.mk {I : State → Prop} {Wr : Word → Prop} {i : Instr}
    (h : ∀ t, I t → I (i.next t) ∧ ∀ a ∈ i.accesses t, AccOk Wr a) : IOk I Wr i := by
  unfold IOk; exact h

theorem IOk.elim {I : State → Prop} {Wr : Word → Prop} {i : Instr} (h : IOk I Wr i) :
    ∀ t, I t → I (i.next t) ∧ ∀ a ∈ i.accesses t, AccOk Wr a := by
  unfold IOk at h; exact h

theorem accAll_iok {Wr : Word → Prop} (I : State → Prop) (is : List Instr) (s : State) (hs : I s)
    (h : ∀ i ∈ is, IOk I Wr i) : AccAll (AccOk Wr) is s :=
  accAll_inv I is s hs fun i hi => (h i hi).elim

section
variable {Wr : Word → Prop}

theorem sa_plain (i : Instr) (h7 : 7 ∉ i.dsts) (h13 : 13 ∉ i.dsts) (ha : ∀ t, i.accesses t = []) :
    IOk SA Wr i := by
  refine IOk.mk fun t ⟨hs, h7'⟩ => ?_
  refine ⟨⟨?_, ?_⟩, by rw [ha]; intro a h; cases h⟩
  · simp only [State.sp]; rw [next_regs_other i t 13 (by decide) h13]; exact hs
  · simp only [State.reg]; rw [next_regs_other i t _ (by decide) h7]; exact h7'

theorem sa_ldrSp (d : LowReg) (k : BitVec 8) (h7 : d ≠ 7) : IOk SA Wr (Instr.ldrSp d k) := by
  refine IOk.mk fun t ⟨hs, h7'⟩ => ?_
  have h7v : (7 : Nat) ∉ (Instr.ldrSp d k).dsts := by
    simp only [Instr.dsts, List.mem_singleton]; intro e; apply h7; exact Fin.ext e.symm
  refine ⟨sa_plain_regs hs h7' h7v (by simp [Instr.dsts]; omega), ?_⟩
  intro a ha
  simp only [Instr.accesses, List.mem_singleton] at ha
  subst ha
  exact ⟨aligned_word (word_add_aligned hs (by omega)), fun h => by cases h⟩
where
  sa_plain_regs {t : State} (hs : t.sp.toNat % 4 = 0) (h7' : (t.reg 7).toNat % 4 = 0)
      (h7v : (7 : Nat) ∉ (Instr.ldrSp d k).dsts) (h13 : (13 : Nat) ∉ (Instr.ldrSp d k).dsts) :
      SA ((Instr.ldrSp d k).next t) := by
    refine ⟨?_, ?_⟩
    · simp only [State.sp]; rw [next_regs_other _ t 13 (by decide) h13]; exact hs
    · simp only [State.reg]; rw [next_regs_other _ t _ (by decide) h7v]; exact h7'

theorem sa_addRdSp (k : BitVec 8) (t : State) (hs : t.sp.toNat % 4 = 0) :
    SA ((Instr.addRdSp 7 k).next t) := by
  refine ⟨?_, ?_⟩
  · simp only [State.sp]; rw [next_regs_other _ t 13 (by decide) (by simp [Instr.dsts]; decide)]
    exact hs
  · simp only [State.reg, toReg7, regs_addRdSp _ _ _ _ (by decide : (7 : Reg) ≠ 15), ite_true]
    exact word_add_aligned hs (by omega)

theorem sa_addRdSp_ok (k : BitVec 8) : IOk SA Wr (Instr.addRdSp 7 k) :=
  IOk.mk fun t h => ⟨sa_addRdSp k t h.1, fun a h => by simp [Instr.accesses] at h⟩

theorem sa_ldm (l : BitVec 8) (h7 : (7 : Reg) ∉ (listRegs l).map LowReg.toReg) :
    IOk SA Wr (Instr.ldm 7 l) := by
  refine IOk.mk fun t ⟨hs, h7'⟩ => ?_
  have h13 : (13 : Reg) ∉ (listRegs l).map LowReg.toReg := by
    simp only [List.mem_map, not_exists, not_and]
    intro x _ e; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [State.sp]
    rw [regs_ldm _ _ _ _ (by decide), ite_eq_right_of_eq_false _ _ (eq_false h13),
      ite_eq_right_of_eq_false _ _ (by decide)]; exact hs
  · simp only [State.reg, toReg7]
    rw [regs_ldm _ _ _ _ (by decide), ite_eq_right_of_eq_false _ _ (eq_false h7)]
    simp only [toReg7, ite_true]
    exact word_add_aligned h7' (by omega)
  · intro a ha
    simp only [Instr.accesses] at ha
    exact wordAccesses_ok h7' (fun h => by cases h) a ha

/-- A block that sets `r7 := sp + 4k` first and then keeps `SA`. -/
theorem accAll_r7 (k : BitVec 8) (rest : List Instr) (s : State) (hs : s.sp.toNat % 4 = 0)
    (h : ∀ i ∈ rest, IOk SA Wr i) :
    AccAll (AccOk Wr) (.addRdSp 7 k :: rest) s :=
  accAll_cons (fun a h => by simp [Instr.accesses] at h) (accAll_iok SA rest _ (sa_addRdSp k s hs) h)

/-- One instruction of a phase-A/B block: plain, `ldrSp` or `ldm r7!`. -/
macro "sa_step" : tactic => `(tactic| first
  | (intro _ h; exact h.elim)
  | exact sa_ldm _ (by decide)
  | exact sa_ldrSp _ _ (by decide)
  | exact sa_addRdSp_ok _
  | exact sa_plain _ (by decide) (by decide) (fun _ => rfl))

theorem phaseA_split (sq : Bool) :
    reducePhaseA sq = [.movHi 3 1, .movHi 2 0] ++ (.addRdSp 7 (sl SPP) ::
      ([.ldm 7 0x03] ++ xorN sq 4 ++
      [if sq then .dp .cmp 0 0 else .lsrImm 4 4 1, .addRdSp 7 (sl SP_),
       .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6, .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6,
       .movImm 4 0, .dp .adcs 4 4,
       .addRdSp 7 (sl SH), .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
       .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5,
       .movHi 8 0, .movHi 10 1, .movHi 11 2, .movHi 12 3])) := rfl

theorem phaseA_acc (sq : Bool) (s : State) (hs : s.sp.toNat % 4 = 0) :
    AccAll (AccOk Wr) (reducePhaseA sq) s := by
  rw [phaseA_split]
  refine accAll_append (accAll_none _ _ fun i hi t => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h <;> subst h <;> rfl) (accAll_r7 _ _ _ ?_ ?_)
  · simp only [State.sp, execAll]
    rw [next_regs_other _ _ 13 (by decide) (by simp [Instr.dsts]; decide),
      next_regs_other _ _ 13 (by decide) (by simp [Instr.dsts]; decide)]
    exact hs
  · cases sq <;>
    simp only [xorN, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
      List.forall_mem_nil, and_true, Bool.false_eq_true, ite_true, ite_false] <;>
    repeat' constructor
    all_goals sa_step

theorem phaseB_acc (sq : Bool) (s : State) (hs : s.sp.toNat % 4 = 0) :
    AccAll (AccOk Wr) (reducePhaseB sq) s := by
  cases sq <;>
  simp only [reducePhaseB, xorN, List.cons_append, List.nil_append, Bool.false_eq_true, ite_true,
    ite_false] <;>
  refine accAll_r7 _ _ _ hs ?_ <;>
  simp only [List.forall_mem_cons, List.not_mem_nil, List.forall_mem_nil, and_true] <;>
  repeat' constructor
  all_goals sa_step

theorem sp_keep (is : List Instr) (s : State) (h : is.all (fun i => !(i.dsts.contains 13)) = true) :
    (execAll is s).sp = s.sp :=
  execAll_regs_other is s 13 (by decide) h

theorem phaseC_acc (s : State) (hs : s.sp.toNat % 4 = 0)
    (hW : ∀ j < 16, Wr (slot s.sp SH + BitVec.ofNat 32 j)) :
    AccAll (AccOk Wr) reducePhaseC s := by
  rw [reducePhaseC_split]
  refine accAll_append ?_ ?_
  · refine accAll_r7 _ _ _ hs ?_
    simp only [List.forall_mem_cons, List.not_mem_nil, List.forall_mem_nil, and_true]
    repeat' constructor
    all_goals sa_step
  · obtain ⟨-, -, r7, -⟩ := addH_exec s SH (by decide)
    generalize execAll (addH SH) s = s1 at r7
    refine accAll_cons (fun a h => by simp [Instr.accesses] at h)
      (accAll_cons (fun a h => by simp [Instr.accesses] at h) (accAll_cons ?_ (accAll_nil _ _)))
    intro a ha
    have e : ((Instr.subImm8 7 16).next ((Instr.movHi 9 6).next s1)).reg 7 = slot s.sp SH := by
      simp only [State.reg, toReg7, regs_subImm8 _ _ _ _ (by decide : (7 : Reg) ≠ 15), ite_true,
        Blake2s.regs_movHi _ _ _ _ (by decide : (7 : Reg) ≠ 15), ite_eq_right_of_eq_false _ _ (by decide : ((7 : Reg) = 9) = False)]
      rw [r7, slot_sub16]
    simp only [Instr.accesses, e, bitCount_0f] at ha
    have hal : (slot s.sp SH).toNat % 4 = 0 := word_add_aligned hs (by omega)
    refine wordAccesses_ok hal (fun _ i hi q hq => ?_) a ha
    rw [ofNat_add_assoc]; exact hW _ (by omega)

/-- `sp` word-aligned. -/
def SPA (s : State) : Prop := s.sp.toNat % 4 = 0

theorem tp_plain (i : Instr) (h13 : 13 ∉ i.dsts) (ha : ∀ t, i.accesses t = []) : IOk SPA Wr i :=
  IOk.mk fun t hs => ⟨by
    simp only [SPA, State.sp]; rw [next_regs_other i t 13 (by decide) h13]; exact hs,
    by rw [ha]; intro a h; cases h⟩

theorem tp_ldrSp (d : LowReg) (k : BitVec 8) : IOk SPA Wr (Instr.ldrSp d k) :=
  IOk.mk fun t hs => ⟨by
    simp only [SPA, State.sp]
    rw [next_regs_other _ t 13 (by decide) (by simp [Instr.dsts]; omega)]; exact hs, by
    intro a ha
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    exact ⟨aligned_word (word_add_aligned hs (by omega)), fun h => by cases h⟩⟩

theorem top_acc (s : State) (hs : s.sp.toNat % 4 = 0) : AccAll (AccOk Wr) reduceTop s := by
  refine accAll_iok SPA _ s hs ?_
  simp only [reduceTop, List.forall_mem_cons, List.not_mem_nil, List.forall_mem_nil, and_true]
  repeat' constructor
  all_goals first
    | (intro _ h; exact h.elim)
    | exact tp_ldrSp _ _
    | (apply tp_plain <;> first | decide | exact fun _ => rfl)

/-- `sp` word-aligned and `r0` the output pointer `d`. -/
def LI (d : Word) (s : State) : Prop := s.sp.toNat % 4 = 0 ∧ s.reg 0 = d

theorem lp_plain (d : Word) (i : Instr) (h0 : 0 ∉ i.dsts) (h13 : 13 ∉ i.dsts)
    (ha : ∀ t, i.accesses t = []) : IOk (LI d) Wr i :=
  IOk.mk fun t ⟨hs, h0'⟩ => ⟨⟨by simp only [State.sp]; rw [next_regs_other i t 13 (by decide) h13]; exact hs,
    by simp only [State.reg]; rw [next_regs_other i t _ (by decide) h0]; exact h0'⟩,
    by rw [ha]; intro a h; cases h⟩

theorem lp_ldrSp (d : Word) (r : LowReg) (k : BitVec 8) (h0 : r ≠ 0) : IOk (LI d) Wr (Instr.ldrSp r k) :=
  IOk.mk fun t ⟨hs, h0'⟩ => ⟨⟨by
    simp only [State.sp]
    rw [next_regs_other _ t 13 (by decide) (by simp [Instr.dsts]; omega)]; exact hs, by
    simp only [State.reg]
    rw [next_regs_other _ t _ (by decide) (by
      simp only [Instr.dsts, List.mem_singleton]; intro e; exact h0 (Fin.ext e.symm))]
    exact h0'⟩, by
    intro a ha
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    exact ⟨aligned_word (word_add_aligned hs (by omega)), fun h => by cases h⟩⟩

theorem lp_str (d : Word) (hd : d.toNat % 4 = 0) (hW : ∀ j < 32, Wr (d + BitVec.ofNat 32 j))
    (l : LowReg) (i : BitVec 5) (hi : i.toNat < 8) : IOk (LI d) Wr (Instr.memImm .str l 0 i) :=
  IOk.mk fun t ⟨hs, h0'⟩ => ⟨⟨by
    simp only [State.sp]
    rw [next_regs_other _ t 13 (by decide) (by simp [Instr.dsts, MemOp.isLoad])]; exact hs, by
    simp only [State.reg]
    rw [next_regs_other _ t _ (by decide) (by simp [Instr.dsts, MemOp.isLoad])]
    exact h0'⟩, by
    intro a ha
    simp only [Instr.accesses, MemOp.isLoad, MemOp.width, List.mem_singleton] at ha
    subst ha
    simp only [State.reg, toReg0] at h0'
    simp only [State.reg, toReg0, h0']
    refine ⟨aligned_word (word_add_aligned hd (by omega)), fun _ k (hk : k < 4) => ?_⟩
    rw [ofNat_add_assoc]; exact hW _ (by omega)⟩

theorem loop_acc (d : Word) (hd : d.toNat % 4 = 0) (hW : ∀ j < 32, Wr (d + BitVec.ofNat 32 j))
    (s : State) (hs : s.sp.toNat % 4 = 0) (h0 : s.reg 0 = d) : AccAll (AccOk Wr) reduceLoop s := by
  refine accAll_iok (LI d) _ s ⟨hs, h0⟩ ?_
  simp only [reduceLoop, reduceWord, List.cons_append, List.nil_append, List.append_assoc,
    List.forall_mem_cons, List.not_mem_nil, List.forall_mem_nil, and_true, Nat.reduceEqDiff,
    ite_true, ite_false]
  repeat' constructor
  all_goals first
    | (intro _ h; exact h.elim)
    | exact lp_ldrSp _ _ _ (by decide)
    | exact lp_str d hd hW _ _ (by decide)
    | (apply lp_plain <;> first | decide | exact fun _ => rfl)

end

end M0Crypto.Release.X25519CR
