import SafegcdTermination.BatchState
import SafegcdTermination.RowCalls

namespace SafegcdTermination.MatrixCall

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchMachine (Image Range)
open SafegcdTermination.RowCalls (entered_lr entered_regs entered_pc entered_mem entered_sp linkedRet_odd linkedRet_clear)
open SafegcdTermination.MatrixRefine (matrix_at)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

theorem matrix_pre_sp (phase : Fin 3) :
    SpBlock (prepareMatrix (phases phase)) (fun p => p.2 % 4 = 0) := by
  have h := spBlock_of_B (is := prepareMatrix (phases phase)) (ok := fun p => p.2 % 4 == 0) (by
    rcases phase_cases phase with rfl | rfl | rfl <;> decide +kernel)
  exact h.mono (fun _ hp => beq_iff_eq.mp hp)

theorem matrix_pre_falls (phase : Fin 3) :
    (prepareMatrix (phases phase)).all Instr.falls = true := rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem run_matrix_call {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (phase : Fin 3) (v : BatchState) (hImg : Image s (phases phase) v)
    (hOdd : v.scalar.f % 2 = 1) (hδ : magnitude (v.scalar.delta) ≤ 1205) (hst : FrameOk s.sp)
    (hob : off + seqSize (prepareMatrix (phases phase)) + 4 < 2^23) (hdb : dest < 2^23)
    (hlink : seqAt code off (prepareMatrix (phases phase) ++
      [callTo (off + seqSize (prepareMatrix (phases phase))) dest]) = true)
    (hmat : seqAt code dest (MatrixCode.body ++ [.bx 14]) = true) :
    let pre := prepareMatrix (phases phase)
    let call := off + seqSize pre
    let (out, m) := accumulate v.scalar batchSteps
    ∃ t, runH code base (pre.length + ((MatrixCode.body.length + 1) + 1)) s =
      .ok (t, traceAll pre s ++
        (⟨base + BitVec.ofNat 32 call, callTo call dest, []⟩ ::
         (annotate (base + BitVec.ofNat 32 dest) MatrixCode.body [] ++
          [⟨nextPC (base + BitVec.ofNat 32 dest) MatrixCode.body, .bx 14, []⟩]))) ∧
      MatrixCode.output t = (BitVec.ofInt 32 out.delta, BitVec.ofInt 32 m.f.a, BitVec.ofInt 32 m.f.b,
        BitVec.ofInt 32 m.g.a, BitVec.ofInt 32 m.g.b) ∧
      t.pc = base + BitVec.ofNat 32 (call + 4) ∧ t.sp = s.sp ∧ t.mem = s.mem := by
  let pre := prepareMatrix (phases phase)
  let call := off + seqSize pre
  let u := execAll pre s
  let entry := entered base call dest u
  have hCallEven : call % 2 = 0 := by
    have he := seqSize_mod_two pre
    change (off + seqSize pre) % 2 = 0
    omega
  obtain ⟨hF, hG, hD, hMem, hSp⟩ := matrix_arguments phase s
  have hf := Vectors.value_low_word s.mem (addr s.sp (phases phase).f) hImg.f.formed.1
  rw [stack_vec, stack_vec, hImg.f.value] at hf
  have hg := Vectors.value_low_word s.mem (addr s.sp bankG) hImg.g.formed.1
  rw [stack_vec, stack_vec, hImg.g.value] at hg
  have hF' : entry.regs 0 = BitVec.ofInt 32 v.scalar.f :=
    (entered_regs _ _ _ _ 0 (by decide) (by decide)).trans (hF.trans hf)
  have hG' : entry.regs 1 = BitVec.ofInt 32 v.scalar.g :=
    (entered_regs _ _ _ _ 1 (by decide) (by decide)).trans (hG.trans hg)
  have hD' : entry.regs 2 = BitVec.ofInt 32 v.scalar.delta :=
    (entered_regs _ _ _ _ 2 (by decide) (by decide)).trans (hD.trans hImg.delta)
  have hr : (entry.regs 14).getLsbD 0 = true := by rw [entered_lr]; exact linkedRet_odd _ _
  have hPE : entry.pc = base + BitVec.ofNat 32 dest := entered_pc _ _ _ _
  obtain ⟨t, ht, hv, hm, hs, hp⟩ :=
    matrix_at hb hlen hPE hd hmat hr v.scalar hOdd hδ hF' hG' hD'
  rw [seqAt_append, Bool.and_eq_true] at hlink
  obtain ⟨hrun, hu⟩ := execute_pre hb hlen hpc ho hlink.1 (matrix_pre_falls phase)
    (alignedAll_sp pre s (matrix_pre_sp phase) hst.1)
  have hc := run_call hb hlen hu hCallEven hob hdb hlink.2 ht
  rw [hu, hPE] at hc
  refine ⟨t, runH_compose hrun hc, hv, ?_, hs.trans ((entered_sp _ _ _ _).trans hSp),
    hm.trans ((entered_mem _ _ _ _).trans hMem)⟩
  rw [hp, entered_lr, linkedRet_clear hb hCallEven]

end SafegcdTermination.MatrixCall
