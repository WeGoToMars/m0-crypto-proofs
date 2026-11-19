import SafegcdTermination.LoopLinks

namespace SafegcdTermination.RunLoop

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchMachine (Image)
open SafegcdTermination.RunRows (LiteralAtRows)
open SafegcdTermination.RunBatch (run_batch batchTrace)
open SafegcdTermination.LoopCounter
open SafegcdTermination.LoopControl
open SafegcdTermination.LoopLinks
open SafegcdTermination.LoopMemory
open SafegcdTermination.SaveMatrix (PreservedWord)
open M0Crypto.Armv6M (State read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_congr)

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

structure Entry (code : List (BitVec 8)) (base : Word) (q : Targets) (entry done : Nat)
    (s : State) (z : Int) : Prop where
  aligned : base.toNat % 2 = 0
  length : code.length < 2^23
  even : entry % 2 = 0
  linked : Place code q entry done
  frame : FrameOk s.sp
  zNonneg : 0 ≤ z
  zCanonical : z < p
  literal : ∀ i, LiteralAtRows s base q (firstRow q (phaseAt q entry done i) (phases i)) i

structure Live (root current : State) (phase : Fin 3) (z : Int) (rounds : Nat) : Prop where
  sp : current.sp = root.sp
  outside : WritesOnly root.mem current.mem root.sp frameBytes
  image : Image current (phases phase) (iterate z rounds)
  output : stackWord current outputAt = stackWord root outputAt
  ret : stackWord current (frameBytes-4) = stackWord root (frameBytes-4)

theorem literal_read {s t : State} {base : Word} {q : Targets} {o : Nat} {phase : Fin 3}
    (hs : LiteralAtRows s base q o phase) (hsp : t.sp = s.sp)
    (hm : WritesOnly s.mem t.mem s.sp frameBytes) : LiteralAtRows t base q o phase := by
  intro i h
  obtain ⟨hv, hD⟩ := hs i h
  refine ⟨?_, by simpa only [hsp] using hD⟩
  exact (read32_congr (fun j hj => hm _ (hD j hj))).trans hv

theorem phase_run {code : List (BitVec 8)} {base : Word} {q : Targets} {entry done : Nat}
    {root s : State} {z : Int} {i : Fin 3} {j : Nat}
    (env : Entry code base q entry done root z)
    (live : Live root s i z j) (hj : j ≤ batchCount)
    (hp : s.pc = base + BitVec.ofNat 32 (phaseAt q entry done i)) :
    ∃ t k, runH code base k s = .ok (t, batchTrace q base root.sp (phaseAt q entry done i) i) ∧
      t.pc = base + BitVec.ofNat 32 (batchEnd q (phaseAt q entry done i) i) ∧
      Live root t (i+1) z (j+1) ∧ stackWord t counterAt = stackWord s counterAt := by
  have hf : FrameOk s.sp := by rw [live.sp]; exact env.frame
  have hlit := literal_read (env.literal i) live.sp live.outside
  obtain ⟨t, k, hr, hp', hsp, hImg, hm, hw⟩ :=
    run_batch q (phaseAt q entry done i) i (iterate z j) env.aligned env.length (phase_even _ env.even i)
      hp hf (BatchMachine.iterate_range env.zNonneg env.zCanonical j) (BatchMachine.iterate_delta z j hj)
      live.image env.linked.leaves (env.linked.phase i) hlit
  have hFrame : WritesOnly root.mem t.mem root.sp frameBytes := by
    intro a ha
    exact (hm a (by rwa [live.sp])).trans (live.outside a ha)
  have hState : Image t (phases (i+1)) (iterate z (j+1)) := by
    rw [next_phase] at hImg
    exact hImg
  rw [live.sp] at hr
  exact ⟨t, k, hr, hp', ⟨hsp.trans live.sp, hFrame, hState,
    (hw _ (.inl rfl)).trans live.output, (hw _ (.inr (.inr rfl))).trans live.ret⟩,
    hw _ (.inr (.inl rfl))⟩

theorem Live.after_count {root s t : State} {i : Fin 3} {z : Int} {j : Nat} {cnt : Word}
    (h : Live root s i z j) (hS : t.sp = s.sp)
    (hM : t.mem = M0Crypto.Armv6M.write32 s.mem (addr s.sp counterAt) cnt) :
    Live root t i z j := by
  refine ⟨hS.trans h.sp, ?_, count_image h.image hS hM, ?_, ?_⟩
  · intro a ha
    exact (count_frame hM a (by rwa [h.sp])).trans (h.outside a ha)
  · have hOut := count_preserves_word s cnt outputAt (by decide +kernel) (by decide +kernel)
    unfold stackWord stackAddr
    rw [hM, hS]
    exact hOut.trans h.output
  · have hRet := count_preserves_word s cnt (frameBytes-4) (by decide +kernel) (by decide +kernel)
    unfold stackWord stackAddr
    rw [hM, hS]
    exact hRet.trans h.ret

theorem Live.after_branch {root s : State} {i : Fin 3} {z : Int} {j : Nat}
    (h : Live root s i z j) (pc : Word) : Live root (s.setReg 15 pc) i z j := by
  have hsp : (s.setReg 15 pc).sp = s.sp := by simp [State.sp, State.setReg]
  have hm : (s.setReg 15 pc).mem = s.mem := rfl
  refine ⟨hsp.trans h.sp, ?_, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simpa only [hm] using h.outside
  · simpa only [hm, hsp] using h.image.f
  · simpa only [hm, hsp] using h.image.g
  · simpa only [hm, hsp] using h.image.d
  · simpa only [hm, hsp] using h.image.e
  · simpa only [stackWord, stackAddr, hm, hsp] using h.image.delta
  · simpa only [stackWord, stackAddr, hm, hsp] using h.output
  · simpa only [stackWord, stackAddr, hm, hsp] using h.ret

end SafegcdTermination.RunLoop
