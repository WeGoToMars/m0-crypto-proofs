import SafegcdTermination.RunRows
import SafegcdTermination.SaveMatrix

namespace SafegcdTermination.RunBatch

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchSlots (row)
open SafegcdTermination.BatchLinks
open SafegcdTermination.BatchMachine (Image VectorsAt Range Slot)
open SafegcdTermination.PhaseOperands
open SafegcdTermination.RunRow
open SafegcdTermination.RunRows
open SafegcdTermination.MatrixCall
open SafegcdTermination.SaveMatrix
open SafegcdTermination.PublicTrace
open M0Crypto.Armv6M (State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr)

set_option maxRecDepth 20000
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

theorem save_vectors {s : State} {phase : Fin 3} {x : BatchState}
    (h : VectorsAt s (phases phase) x) :
    VectorsAt (execAll saveMatrix s) (phases phase) x := by
  obtain ⟨hm, hs⟩ := matrix_saved s
  have hm' : (execAll saveMatrix s).mem = SaveMatrix.result s := hm
  have hf : (phases phase).f + vectorBytes ≤ deltaAt := by
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  have hd : (phases phase).d + vectorBytes ≤ deltaAt := by
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hm', hs]
  · exact Slot.read_eq h.f (lower_slot _ _ hf)
  · exact Slot.read_eq h.g (lower_slot _ _ (by decide))
  · exact Slot.read_eq h.d (lower_slot _ _ hd)
  · exact Slot.read_eq h.e (lower_slot _ _ (by decide))

theorem save_coefficients (s : State) (phase : Fin 3) (v : DivstepState) (m : Matrix)
    (h : MatrixCode.output s = (BitVec.ofInt 32 v.delta, BitVec.ofInt 32 m.f.a, BitVec.ofInt 32 m.f.b,
      BitVec.ofInt 32 m.g.a, BitVec.ofInt 32 m.g.b)) :
    CoefficientsAt (execAll saveMatrix s) phase m := by
  simp only [MatrixCode.output, Prod.mk.injEq] at h
  intro i
  have ha := saved_reads s 0 (by decide)
  have hb := saved_reads s 1 (by decide)
  have hc := saved_reads s 2 (by decide)
  have hd := saved_reads s 3 (by decide)
  obtain ⟨_, hA, hB, hC, hD⟩ := h
  have hidx : ∀ (phase : Fin 3) (i : Fin 4), (row phase i).coeff = 2 * (i.val % 2) := by
    decide +kernel
  rw [hidx]
  rcases row_cases i with rfl | rfl | rfl | rfl
  · exact ⟨ha.trans hA, hb.trans hB⟩
  · exact ⟨hc.trans hC, hd.trans hD⟩
  · exact ⟨ha.trans hA, hb.trans hB⟩
  · exact ⟨hc.trans hC, hd.trans hD⟩

theorem save_frame (s : State) : WritesOnly s.mem (execAll saveMatrix s).mem s.sp frameBytes := by
  have hM : (execAll saveMatrix s).mem = SaveMatrix.result s := (matrix_saved s).1
  rw [hM]
  intro a ha
  apply outside_regs
  · intro i hi
    simp only [addr, ofNat_add_assoc]
    have hD : deltaAt + 4 ≤ frameBytes := by decide
    exact ha _ (by omega)
  · intro i hi
    simp only [addr, ofNat_add_assoc]
    have hD : matrixAt + 16 ≤ frameBytes := by decide
    exact ha _ (by omega)

def batchTrace (q : Targets) (base sp : Word) (off : Nat) (phase : Fin 3) : List Event :=
  let b := phases phase
  let pre := prepareMatrix b
  let call := off+seqSize pre
  let lin := base + BitVec.ofNat 32 q.matrix
  traceAll pre (stackState (base + BitVec.ofNat 32 off) sp) ++
    (⟨base + BitVec.ofNat 32 call, callTo call q.matrix, []⟩ ::
      (annotate lin MatrixCode.body [] ++ [⟨nextPC lin MatrixCode.body, .bx 14, []⟩])) ++
    traceAll saveMatrix (stackState (base + BitVec.ofNat 32 (saveOff q off b)) sp) ++
    rowsTrace q base sp (firstRow q off b) phase 4

theorem run_batch {code : List (BitVec 8)} {base : Word} {s : State}
    (q : Targets) (off : Nat) (phase : Fin 3) (x : BatchState)
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (ho : off % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 off) (hst : FrameOk s.sp)
    (hx : Range x) (hδ : magnitude (x.scalar.delta) ≤ 1205) (hImage : Image s (phases phase) x)
    (links : LeafLinks code q) (hAt : seqAt code off (batchCode q off (phases phase)) = true)
    (hLit : LiteralAtRows s base q (firstRow q off (phases phase)) phase) :
    ∃ t n, runH code base n s = .ok (t, batchTrace q base s.sp off phase) ∧
      t.pc = base + BitVec.ofNat 32 (off + seqSize (batchCode q off (phases phase))) ∧ t.sp = s.sp ∧
      Image t (phases phase).next x.next ∧ WritesOnly s.mem t.mem s.sp frameBytes ∧
      (∀ o, PreservedWord o → stackWord t o = stackWord s o) := by
  let b := phases phase
  let start := firstRow q off b
  let save := saveOff q off b
  obtain ⟨hMat, hSave, hRows⟩ := batch_links _ _ _ hAt
  have hlen' : code.length < 2^32 := by omega
  have hP := (seqAt_size _ _ _ hMat).resolve_right (by simp [matrixPre, prepareMatrix])
  have hL := (seqAt_size _ _ _ links.mat).resolve_right (by simp)
  have hSize : seqSize (matrixPre off q.matrix b) = seqSize (prepareMatrix b) + 4 := by
    rw [matrixPre, seqSize_append]
    rfl
  have hSz : off + seqSize (prepareMatrix (phases phase)) + 4 < 2^23 := by
    change off + seqSize (matrixPre off q.matrix b) ≤ code.length at hP
    rw [hSize] at hP
    change off + seqSize (prepareMatrix b) + 4 < 2^23
    omega
  obtain ⟨u, hRun, hOut, hPc, hSp, hM⟩ :=
    run_matrix_call hb hlen' hp ho links.even.1 phase x hImage hx.odd hδ hst
      hSz (by omega) hMat links.mat
  have huPc : u.pc = base + BitVec.ofNat 32 save := by
    simpa only [save, saveOff, hSize, Nat.add_assoc] using hPc
  have hEven : save % 2 = 0 := by
    have hv := seqSize_mod_two (matrixPre off q.matrix b)
    change (off + seqSize (matrixPre off q.matrix b)) % 2 = 0
    omega
  have hStU : FrameOk u.sp := by rwa [hSp]
  let v := execAll saveMatrix u
  obtain ⟨hRunSave, hPcSave⟩ := execute_pre hb hlen' huPc hEven hSave (by rfl) (save_aligned u hStU)
  have hU : VectorsAt u b x := by
    have ht := hImage.toVectorsAt
    exact ⟨by simpa only [hM, hSp] using ht.f, by simpa only [hM, hSp] using ht.g,
      by simpa only [hM, hSp] using ht.d, by simpa only [hM, hSp] using ht.e⟩
  have hV := save_vectors hU
  have hSpV : v.sp = s.sp := (matrix_saved u).2.trans hSp
  have hPcV : v.pc = base + BitVec.ofNat 32 start := hPcSave
  have hStV : FrameOk v.sp := by rwa [hSpV]
  have hVmem : WritesOnly s.mem v.mem s.sp frameBytes := by
    have hF := save_frame u
    simpa only [hM, hSp] using hF
  have hLitV : LiteralAtRows v base q start phase := by
    intro i hi
    obtain ⟨hL, hDisj⟩ := hLit i hi
    dsimp only at hL hDisj ⊢
    refine ⟨?_, by simpa only [hSpV] using hDisj⟩
    rw [read32_congr (fun j hj => hVmem _ (hDisj j hj))]
    exact hL
  have hStartEven : start % 2 = 0 := by
    have he := seqSize_mod_two saveMatrix
    change (save + seqSize saveMatrix) % 2 = 0
    omega
  let next := (accumulate x.scalar batchSteps).1
  let m := (accumulate x.scalar batchSteps).2
  have hCoeff : CoefficientsAt v phase m := save_coefficients u phase next m hOut
  obtain ⟨t, n, hT, hTsp, hTpc, hProof⟩ :=
    run_rows q start phase x hb hlen hStartEven hPcV hStV hx hV links hRows hCoeff hLitV 4 (by decide)
  have hRunAll := runH_compose (runH_compose hRun hRunSave) hT
  have hTsp' : t.sp = s.sp := hTsp.trans hSpV
  refine ⟨t, ((prepareMatrix b).length + (MatrixCode.body.length + 1 + 1)) + saveMatrix.length + n, ?_, ?_, hTsp', ?_, ?_, ?_⟩
  · have prep := traceAll_sp_congr (prepareMatrix b) s (stackState (base + BitVec.ofNat 32 off) s.sp)
      ((matrix_pre_sp phase).mono (fun _ _ => trivial)) (matrix_pre_falls phase) hp rfl
    have hs := stack_trace (is := saveMatrix) (by decide) (by decide +kernel) u
    rw [prep,hs,huPc,hSp,hSpV] at hRunAll
    simpa only [batchTrace, b, save, start, List.append_assoc] using hRunAll
  · have h4 : (rowCalls b).length = 4 := rfl
    rw [← h4, rowPc, offset_end] at hTpc
    have hh : off + seqSize (batchCode q off b) = start + seqSize (rowsCode q start (rowCalls b)) := by
      simp only [batchCode, start, firstRow, saveOff, seqSize_append, Nat.add_assoc]
    exact hTpc.trans (congrArg (fun o => base + BitVec.ofNat 32 o) hh.symm)
  · have hEq : stackWord t deltaAt = BitVec.ofInt 32 x.next.scalar.delta := by
      unfold stackWord stackAddr
      rw [hTsp]
      have hE : read32 t.mem (addr v.sp deltaAt) = read32 v.mem (addr v.sp deltaAt) :=
        hProof.registers deltaAt (by decide) (by decide)
      change read32 t.mem (addr v.sp deltaAt) = _
      rw [hE]
      exact (saved_delta u).trans (congrArg (fun r => r.1) hOut)
    have hf := hProof.after 0 (by decide)
    have hg := hProof.after 1 (by decide)
    have hd := hProof.after 2 (by decide)
    have hE := hProof.after 3 (by decide)
    have hS : VectorsAt t b.next x.next :=
      ⟨by rw [hTsp]; exact hf, by rw [hTsp]; exact hg, by rw [hTsp]; exact hd, by rw [hTsp]; exact hE⟩
    exact ⟨hS, hEq⟩
  · intro a ha
    have hB : 5*vectorBytes ≤ frameBytes := by decide
    exact (hProof.outside a (by rw [hSpV]; exact fun i hi => ha i (Nat.lt_of_lt_of_le hi hB))).trans (hVmem a ha)

  · intro o h
    have hb := preserved_bound h
    have hb' : frameBytes ≤ 2^32 := by decide
    have he : stackWord t o = stackWord v o := by
      unfold stackWord stackAddr
      rw [hTsp]
      exact hProof.registers o hb.1 (Nat.le_trans hb.2 hb')
    refine he.trans ((saved_preserves u o h).trans ?_)
    unfold stackWord stackAddr
    rw [hM, hSp]

end SafegcdTermination.RunBatch
