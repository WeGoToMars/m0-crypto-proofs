import M0Crypto.Release.X25519Mem
import M0Crypto.Release.ReachSteps

/-!
Blocks with memory accesses in `ReachW` proofs (plan `x25519-proofs.md`, phase 8).

`AccAll P is s`: every data access of the block's trace satisfies `P`. One statement gives both
side conditions of `ReachW.block`: alignment (`alignedAll_of_acc`) and the write set
(`writesTo_of_acc`). `AccOk Wr` is the access predicate of a routine: aligned, and a write
covers only bytes in `Wr`. A macro proves `AccAll` by evaluating its trace symbolically,
the same way it evaluates its registers.
-/

namespace M0Crypto.Release.X25519Block
open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion WritesTo)

/-- Every access of the block's trace satisfies `P`. -/
def AccAll (P : Access → Prop) (is : List Instr) (s : State) : Prop :=
  ∀ e ∈ traceAll is s, ∀ a ∈ e.accesses, P a

/-- Aligned, and a write covers only bytes in `Wr`. -/
def AccOk (Wr : Word → Prop) (a : Access) : Prop :=
  a.aligned = true ∧ (a.kind = .write → ∀ k < a.width, Wr (a.addr + BitVec.ofNat 32 k))

theorem accAll_nil (P : Access → Prop) (s : State) : AccAll P [] s := by
  intro e he; cases he

theorem accAll_cons {P : Access → Prop} {i : Instr} {is : List Instr} {s : State}
    (h1 : ∀ a ∈ i.accesses s, P a) (h2 : AccAll P is (i.next s)) : AccAll P (i :: is) s := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h
  · exact h1
  · exact h2 e h

theorem accAll_append {P : Access → Prop} {is js : List Instr} {s : State}
    (h1 : AccAll P is s) (h2 : AccAll P js (execAll is s)) : AccAll P (is ++ js) s := by
  intro e he
  rw [traceAll_append] at he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

/-- A block without memory accesses. -/
theorem accAll_none {P : Access → Prop} :
    ∀ (is : List Instr) (s : State), (∀ i ∈ is, ∀ t, i.accesses t = []) → AccAll P is s
  | [], s, _ => accAll_nil P s
  | i :: is, s, h => accAll_cons (by rw [h i List.mem_cons_self s]; intro a ha; cases ha)
      (accAll_none is _ fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem alignedAll_of_acc {P : Access → Prop} (hP : ∀ a, P a → a.aligned = true) :
    ∀ (is : List Instr) (s : State), AccAll P is s → alignedAll is s = true
  | [], _, _ => rfl
  | i :: is, s, h => by
    simp only [alignedAll, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun a ha => hP a (h _ List.mem_cons_self a ha),
      alignedAll_of_acc hP is _ fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem writesTo_of_acc {Wr : Word → Prop} {is : List Instr} {s : State}
    (h : AccAll (AccOk Wr) is s) : WritesTo Wr (traceAll is s) := by
  intro e he y ⟨a, ha, hw, k, hk, hy⟩
  rw [hy]; exact (h e he a ha).2 hw k hk

/-- `ReachW.block` with both side conditions from `AccAll`. -/
theorem ReachW.blockAcc {base : Word} {Pc Wr : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hacc : AccAll (AccOk Wr) is s) (hr : InRegion Pc base off (seqSize is))
    (hq : ReachW base Pc Wr (execAll is s) Q) : ReachW base Pc Wr s Q :=
  Release.ReachW.block hb is off hpc ho hseq hf (alignedAll_of_acc (fun _ h => h.1) is s hacc)
    (writesTo_of_acc hacc) hr hq

/-! Accesses of the instruction forms of the field routines. -/

theorem aligned_word {a : Word} (h : a.toNat % 4 = 0) : (Access.mk k a 4).aligned = true := by
  simp [Access.aligned, h]

theorem word_add_aligned {a : Word} {n : Nat} (ha : a.toNat % 4 = 0) (hn : n % 4 = 0) :
    (a + BitVec.ofNat 32 n).toNat % 4 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A word transfer of `n` words from `a`: aligned if `a` is, and its bytes are those of
the `n` words from `a`. -/
theorem wordAccesses_ok {Wr : Word → Prop} {k : Kind} {a : Word} {n : Nat} (ha : a.toNat % 4 = 0)
    (hw : k = .write → ∀ i < n, ∀ q < 4, Wr (a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 q)) :
    ∀ x ∈ wordAccesses k a n, AccOk Wr x := by
  intro x hx
  simp only [wordAccesses, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨aligned_word (word_add_aligned ha (by omega)), fun hk q hq => hw hk i hi q hq⟩

theorem aligned_of_alignedAll : ∀ (is : List Instr) (s : State), alignedAll is s = true →
    ∀ e ∈ traceAll is s, ∀ a ∈ e.accesses, a.aligned = true
  | [], _, _, e, he => by cases he
  | i :: is, s, h, e, he => by
    simp only [alignedAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact aligned_of_alignedAll is _ h.2 e he

/-- `AccAll` from alignment and the write set. -/
theorem accAll_of {Wr : Word → Prop} {is : List Instr} {s : State} (h1 : alignedAll is s = true)
    (h2 : WritesTo Wr (traceAll is s)) : AccAll (AccOk Wr) is s :=
  fun e he a ha => ⟨aligned_of_alignedAll is s h1 e he a ha,
    fun hw k hk => h2 e he _ ⟨a, ha, hw, k, hk, rfl⟩⟩

theorem wordAccesses_aligned {k : Kind} {a : Word} {n : Nat} (ha : a.toNat % 4 = 0) :
    (wordAccesses k a n).all Access.aligned = true := by
  simp only [List.all_eq_true]
  intro x hx
  simp only [wordAccesses, List.mem_map, List.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact aligned_word (word_add_aligned ha (by omega))

/-- A block run: its accesses satisfy `P`, and its final state satisfies `Q`. Composes over
`++` (`Runs.append`), so a macro made of pieces is one `ReachW` block. -/
def Runs (P : Access → Prop) (is : List Instr) (s : State) (Q : State → Prop) : Prop :=
  AccAll P is s ∧ Q (execAll is s)

theorem Runs.append {P : Access → Prop} {is js : List Instr} {s : State} {Q1 Q2 : State → Prop}
    (h1 : Runs P is s Q1) (h2 : ∀ t, Q1 t → Runs P js t Q2) : Runs P (is ++ js) s Q2 :=
  ⟨accAll_append h1.1 (h2 _ h1.2).1, by rw [execAll_append]; exact (h2 _ h1.2).2⟩

theorem Runs.mono {P : Access → Prop} {is : List Instr} {s : State} {Q1 Q2 : State → Prop}
    (h : Runs P is s Q1) (hq : ∀ t, Q1 t → Q2 t) : Runs P is s Q2 := ⟨h.1, hq _ h.2⟩

/-- A register-only block. -/
theorem Runs.reg {Wr : Word → Prop} {is : List Instr} {s : State} {Q : State → Prop}
    (hreg : is.all X25519Mul.regOnly = true) (hnw : is.all (!·.writesMem) = true)
    (hq : Q (execAll is s)) : Runs (AccOk Wr) is s Q :=
  ⟨accAll_of (X25519Mul.alignedAll_regOnly _ _ hreg) (WritesTo.of_noWritesMem _ _ hnw _), hq⟩

/-- A `ReachW` block from a run. -/
theorem ReachW.blockRuns {base : Word} {Pc Wr : Word → Prop} {s : State} {Q R : State → Prop}
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hrun : Runs (AccOk Wr) is s R) (hr : InRegion Pc base off (seqSize is))
    (k : ∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize is) → R t → ReachW base Pc Wr t Q) :
    ReachW base Pc Wr s Q :=
  ReachW.blockAcc hb is off hpc ho hseq hf hrun.1 hr
    (k _ (by rw [execAll_pc _ _ hf, hpc, ofNat_add_assoc]) hrun.2)

end M0Crypto.Release.X25519Block
