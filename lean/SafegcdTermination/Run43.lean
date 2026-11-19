import SafegcdTermination.RunLoop

namespace SafegcdTermination.Run43

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.LoopCounter
open SafegcdTermination.LoopControl
open SafegcdTermination.LoopMemory
open SafegcdTermination.LoopLinks
open SafegcdTermination.RunLoop
open SafegcdTermination.RunBatch (batchTrace)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000

def tripletTrace (q : Targets) (base sp : Word) (entry done : Nat) : List Event :=
  let back := backSite q entry done
  batchTrace q base sp entry 0 ++
    countTrace base sp (counterSite q entry) done false ++
    batchTrace q base sp (phaseAt q entry done 1) 1 ++
    batchTrace q base sp (phaseAt q entry done 2) 2 ++
    [⟨base + BitVec.ofNat 32 back,bTo back entry,[]⟩]

def tripletsTrace (q : Targets) (base sp : Word) (entry done : Nat) : Nat → List Event
  | 0 => []
  | k+1 => tripletsTrace q base sp entry done k ++ tripletTrace q base sp entry done

def loopTrace (q : Targets) (base sp : Word) (entry done : Nat) : List Event :=
  tripletsTrace q base sp entry done triplets ++ batchTrace q base sp entry 0 ++
    countTrace base sp (counterSite q entry) done true

/-- One trip through the three sites while the decremented counter is nonzero. -/
theorem triplet {code : List (BitVec 8)} {base : Word} {q : Targets} {entry done : Nat}
    {root s : State} {z : Int} {k : Nat}
    (env : Entry code base q entry done root z) (hk : k < triplets)
    (live : Live root s 0 z (3*k)) (hp : s.pc = base + BitVec.ofNat 32 entry)
    (hc : stackWord s counterAt = BitVec.ofNat 32 (initialCount-k)) :
    ∃ t n, runH code base n s = .ok (t, tripletTrace q base root.sp entry done) ∧
      t.pc = base + BitVec.ofNat 32 entry ∧ Live root t 0 z (3*(k+1)) ∧
      stackWord t counterAt = BitVec.ofNat 32 (initialCount-(k+1)) := by
  have hK := loop_bounds (Nat.le_of_lt hk)
  have hExit : initialCount-k ≠ 1 := by
    unfold initialCount
    omega
  have hMore := (extra_two (Nat.le_of_lt hk) hExit).2
  have hLen : code.length < 2^32 := by have := env.length; omega
  obtain ⟨u, nu, hU, hUpc, hUlive, hUcnt⟩ := phase_run env live (by omega) hp
  have hUpc' : u.pc = base + BitVec.ofNat 32 (counterSite q entry) := hUpc
  have hF : FrameOk u.sp := by rw [hUlive.sp]; exact env.frame
  obtain ⟨v, hV, hVpc, hVsp, hVmem⟩ := route_count env.aligned hLen hUpc'
    (end_even q 0 env.even) hF hK.2.1 hK.1 (hUcnt.trans hc) env.linked.count env.linked.countTarget
  have hVlive : Live root v 1 z (3*k+1) := hUlive.after_count hVsp hVmem
  have hVpc' : v.pc = base + BitVec.ofNat 32 (phaseAt q entry done 1) := by
    simp only [phaseAt, after_counter]
    simpa only [hExit, ite_false, Nat.add_assoc] using hVpc
  have hVcnt : stackWord v counterAt = BitVec.ofNat 32 (initialCount - (k+1)) := by
    simpa only [Nat.sub_sub] using count_write hVsp hVmem
  obtain ⟨w, nw, hW, hWpc, hWlive, hWcnt⟩ := phase_run env hVlive (by omega) hVpc'
  have hWpc' : w.pc = base + BitVec.ofNat 32 (phaseAt q entry done 2) := hWpc
  have hWlive' : Live root w 2 z (3*k+2) := hWlive
  obtain ⟨a, na, hA, hApc, hAlive, hAcnt⟩ := phase_run env hWlive' (by omega) hWpc'
  have hApc' : a.pc = base + BitVec.ofNat 32 (backSite q entry done) := hApc
  have hBack := branch_run env.aligned hLen hApc' (end_even q 2 (phase_even q env.even 2))
    env.linked.back env.linked.backTarget
  have hV' : runH code base (updateCounter.length + 1) u =
      .ok (v, countTrace base root.sp (counterSite q entry) done false) := by
    simpa only [hExit, ite_false, hUlive.sp, beq_eq_false_iff_ne.mpr hExit] using hV
  let t := a.setReg 15 (base + BitVec.ofNat 32 entry)
  have hr := runH_compose (runH_compose (runH_compose (runH_compose hU hV') hW) hA) hBack
  refine ⟨t, nu+(updateCounter.length+1)+nw+na+1, ?_, ?_, ?_, ?_⟩
  · rw [hApc'] at hr
    simpa only [tripletTrace,phaseAt,List.append_assoc] using hr
  · simp [t, State.pc, State.setReg]
  · have hIdx : 3*k+2+1 = 3*(k+1) := by omega
    have hh := hAlive.after_branch (base + BitVec.ofNat 32 entry)
    have hi : (2 + 1 : Fin 3) = 0 := by decide
    simpa only [hIdx, hi] using hh
  · have hWord : stackWord t counterAt = stackWord a counterAt := by
      simp [t, stackWord, stackAddr, State.sp, State.setReg]
    exact hWord.trans (hAcnt.trans (hWcnt.trans hVcnt))

theorem completed_triplets {code : List (BitVec 8)} {base : Word} {q : Targets} {entry done : Nat}
    {s : State} {z : Int} (env : Entry code base q entry done s z)
    (init : BatchMachine.Image s (phases 0) (initial z))
    (hp : s.pc = base + BitVec.ofNat 32 entry) (hc : stackWord s counterAt = BitVec.ofNat 32 initialCount)
    (k : Nat) (hk : k ≤ triplets) :
    ∃ t n, runH code base n s = .ok (t, tripletsTrace q base s.sp entry done k) ∧
      t.pc = base + BitVec.ofNat 32 entry ∧ Live s t 0 z (3*k) ∧
      stackWord t counterAt = BitVec.ofNat 32 (initialCount-k) := by
  induction k with
  | zero => exact ⟨s, 0, rfl, hp, ⟨rfl, fun _ _ => rfl, init, rfl, rfl⟩, hc⟩
  | succ k ih =>
    obtain ⟨u, n, hU, hpc, hl, hcnt⟩ := ih (by omega)
    obtain ⟨t, ni, ht, hp', hl', hc'⟩ := triplet env (by omega) hl hpc hcnt
    exact ⟨t, n+ni, runH_compose hU ht, hp', hl', hc'⟩

theorem forty_three {code : List (BitVec 8)} {base : Word} {q : Targets} {entry done : Nat}
    {s : State} {z : Int} (env : Entry code base q entry done s z)
    (init : BatchMachine.Image s (phases 0) (initial z))
    (hp : s.pc = base + BitVec.ofNat 32 entry) (hc : stackWord s counterAt = BitVec.ofNat 32 initialCount) :
    ∃ t n, runH code base n s = .ok (t, loopTrace q base s.sp entry done) ∧
      t.pc = base + BitVec.ofNat 32 done ∧ Live s t 1 z batchCount ∧ stackWord t counterAt = 0 := by
  obtain ⟨u, nu, hU, hUpc, hUl, hcU⟩ := completed_triplets env init hp hc triplets (by omega)
  have hK : 3*triplets ≤ batchCount := by decide
  obtain ⟨v, nv, hV, hpV, hLive, hcnt⟩ := phase_run env hUl hK hUpc
  have hpV' : v.pc = base + BitVec.ofNat 32 (counterSite q entry) := hpV
  have hf : FrameOk v.sp := by rw [hLive.sp]; exact env.frame
  have hc' : stackWord v counterAt = BitVec.ofNat 32 1 := hcnt.trans hcU
  have hB : code.length < 2^32 := by have := env.length; omega
  obtain ⟨t, hT, hpT, hSp, hMem⟩ := route_count env.aligned hB hpV'
    (end_even q 0 env.even) hf (by decide) (by decide) hc' env.linked.count env.linked.countTarget
  have hT' : runH code base (updateCounter.length+2) v =
      .ok (t, countTrace base s.sp (counterSite q entry) done true) := by
    simpa only [hLive.sp,beq_self_eq_true,ite_true] using hT
  have hr := runH_compose (runH_compose hU hV) hT'
  exact ⟨t,nu+nv+(updateCounter.length+2),hr,hpT,hLive.after_count hSp hMem,count_write hSp hMem⟩

end SafegcdTermination.Run43
