import SafegcdTermination.PhaseOperands

namespace SafegcdTermination.RunRows

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.BatchLinks
open SafegcdTermination.BatchSlots (row row_layout)
open SafegcdTermination.Bank
open SafegcdTermination.BatchMachine (VectorsAt Range Slot)
open SafegcdTermination.PhaseData
open SafegcdTermination.PhaseOperands
open SafegcdTermination.RunRow
open SafegcdTermination.RowCalls (Setup)
open M0Crypto.Armv6M (State Mem read32)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

def rowPc (q : Targets) (start : Nat) (phase : Fin 3) (i : Nat) : Nat :=
  rowOffset q start (rowCalls (phases phase)) i

theorem offset_succ (q : Targets) (start : Nat) (rs : List RowCall) (i : Nat) (hi : i < rs.length) :
    rowOffset q start rs (i+1) = rowOffset q start rs i + seqSize (rowCode q (rowOffset q start rs i) rs[i]) := by
  induction rs generalizing start i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => cases rs <;> rfl
    | succ i => exact ih _ i (by simpa using hi)

theorem offset_even (q : Targets) (start : Nat) (rs : List RowCall) (i : Nat) (h : start % 2 = 0) :
    rowOffset q start rs i % 2 = 0 := by
  induction rs generalizing start i with
  | nil => cases i <;> simpa only [rowOffset] using h
  | cons r rs ih =>
    cases i with
    | zero => exact h
    | succ i =>
      apply ih
      have he := seqSize_mod_two (rowCode q start r)
      omega

theorem offset_end (q : Targets) (o : Nat) (rs : List RowCall) :
    rowOffset q o rs rs.length = o + seqSize (rowsCode q o rs) := by
  induction rs generalizing o with
  | nil => simp [rowOffset, rowsCode, seqSize]
  | cons r rs ih =>
    simp only [List.length_cons, rowOffset, rowsCode, seqSize_append, ih, Nat.add_assoc]

def literalAt (base : Word) (q : Targets) (o : Nat) (r : RowCall) : Word :=
  ((base + BitVec.ofNat 32 (o + seqSize (prepareRow r) + seqSize correctionPrefix + 4)) &&& ~~~3#32) +
    BitVec.ofNat 32 (4 * (rowLit q o r).toNat)

theorem literal_matches_pc (base : Word) (q : Targets) (o : Nat) (r : RowCall) (s : State)
    (hpc : s.pc = base + BitVec.ofNat 32 o) :
    literalAddress (execAll (prepareRow r) s) (rowLit q o r) = literalAt base q o r := by
  simp only [literalAddress, literalAt, execAll_pc (prepareRow r) s (RowCalls.prepareRow_falls r),
    hpc, ofNat_add_assoc, Nat.add_assoc]

def CoefficientsAt (s : State) (phase : Fin 3) (m : Matrix) : Prop :=
  ∀ i : Fin 4,
    stackWord s (matrixAt+4*(row phase i).coeff) = BitVec.ofInt 32 (coefficients m i).a ∧
    stackWord s (matrixAt+4*((row phase i).coeff+1)) = BitVec.ofInt 32 (coefficients m i).b

def LiteralAtRows (s : State) (base : Word) (q : Targets) (start : Nat) (phase : Fin 3) : Prop :=
  ∀ i : Fin 4, (row phase i).modular = true →
    let a := literalAt base q (rowPc q start phase i.val) (row phase i)
    read32 s.mem a = 2587#32 ∧
      ∀ j < 4, ∀ k < frameBytes, a + BitVec.ofNat 32 j ≠ s.sp + BitVec.ofNat 32 k

def rowsTrace (q : Targets) (base sp : Word) (start : Nat) (phase : Fin 3) : Nat → List Event
  | 0 => []
  | n+1 => rowsTrace q base sp start phase n ++
      rowTrace q base sp (rowPc q start phase n) (row phase (Fin.ofNat 4 n))

theorem run_rows {code : List (BitVec 8)} {base : Word} {s : State}
    (q : Targets) (start : Nat) (phase : Fin 3) (x : BatchState)
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (hEven : start % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 start) (hst : FrameOk s.sp) (hx : Range x)
    (hImage : VectorsAt s (phases phase) x) (links : LeafLinks code q)
    (hRows : seqAt code start (rowsCode q start (rowCalls (phases phase))) = true)
    (hM : CoefficientsAt s phase (accumulate x.scalar batchSteps).2)
    (hL : LiteralAtRows s base q start phase)
    (n : Nat) (hn : n ≤ 4) :
    ∃ t k, runH code base k s = .ok (t, rowsTrace q base s.sp start phase n) ∧
      t.sp = s.sp ∧ t.pc = base + BitVec.ofNat 32 (rowPc q start phase n) ∧
      Progress s.mem t.mem s.sp phase n x.next := by
  induction n with
  | zero =>
    exact ⟨s, 0, rfl, rfl, hpc, progress_start _ _ _ _⟩
  | succ n ih =>
    obtain ⟨t, k, hRun, hSp, hPc, hProg⟩ := ih (by omega)
    let i : Fin 4 := ⟨n, by omega⟩
    let r := row phase i
    let off := rowPc q start phase n
    let m := coefficients (accumulate x.scalar batchSteps).2 i
    let X := operandX x i
    let Y := operandY x i
    let N := rowResult x.next i
    have hre : seqAt code off (rowCode q off r) = true := by
      have hi : n < (rowCalls (phases phase)).length := by
        simp only [rowCalls, List.length_cons, List.length_nil]; omega
      exact row_links q start _ hRows n hi
    have he : off % 2 = 0 := offset_even q start _ n hEven
    have hSt : Setup t.sp r := by rw [hSp]; exact row_layout phase i _ hst
    obtain ⟨hX, hY⟩ := row_slots (i := i) hImage hProg
    rw [← hSp] at hX hY
    obtain ⟨hA, hB⟩ := hM i
    have hC (j : Nat) (hj : j ≤ 3) :
        stackWord t (matrixAt+4*j) = stackWord s (matrixAt+4*j) := by
      unfold stackWord stackAddr
      rw [hSp]
      have hN : 5*vectorBytes ≤ matrixAt := by decide
      have hEnd : matrixAt + 16 < 2^32 := by decide
      exact hProg.registers _ (by omega) (by omega)
    have hCoeff := hSt.coeff
    rw [← hC _ (by omega : r.coeff ≤ 3)] at hA
    rw [← hC _ (by omega : r.coeff + 1 ≤ 3)] at hB
    have hLit : r.modular = true → read32 t.mem
        (literalAddress (execAll (prepareRow r) t) (rowLit q off r)) = 2587#32 := by
      intro hMod
      rw [literal_matches_pc base q off r t hPc]
      obtain ⟨hVal, hDisj⟩ := hL i hMod
      have hBound : 5*vectorBytes ≤ frameBytes := by decide
      exact (hProg.read_outside (fun j hj k hk => hDisj j hj k (Nat.lt_of_lt_of_le hk hBound))).trans hVal
    obtain ⟨hnorm, hrange, hExact, heq⟩ := row_math x hx phase i
    obtain ⟨u, hU, hP, hStack, hSlot, hMem⟩ :=
      core_row q off r m hb hlen hPc he links hre hSt hnorm hA hB hLit
        X Y hX hY hrange N (fun h => (hExact h).1) (fun h => (hExact h).2)
    rw [hSp] at hSlot hMem
    have hEq : rightValue r m X Y = N := heq
    have hSlot' : Slot u.mem s.sp r.dst N := by rwa [hEq] at hSlot
    have iEq : Fin.ofNat 4 n = i := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have hRun' := runH_compose hRun hU
    rw [hSp] at hRun'
    refine ⟨u, k + rowSteps q off r, ?_, hStack.trans hSp, ?_, progress_next (i := i) hst hProg hSlot' hMem⟩
    · simpa only [rowsTrace, iEq, off, r] using hRun'
    · have hOff := offset_succ q start (rowCalls (phases phase)) n (by
        simp only [rowCalls, List.length_cons, List.length_nil]; omega)
      change u.pc = base + BitVec.ofNat 32 (rowOffset q start (rowCalls (phases phase)) (n+1))
      rw [hOff]
      exact hP

end SafegcdTermination.RunRows
