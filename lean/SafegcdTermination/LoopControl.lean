import SafegcdTermination.LoopCounter
import SafegcdTermination.PublicTrace

namespace SafegcdTermination.LoopControl

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.LoopCounter SafegcdTermination.PublicTrace
open M0Crypto.Armv6M (State Mem write32 read32_write32_same)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 180000

def bTo (off dest : Nat) : Instr :=
  .b (BitVec.ofInt 11 (((dest : Int) - (off+4)) / 2))

def TargetMatches (off dest : Nat) : Prop :=
  let d := BitVec.ofInt 11 (((dest : Int) - (off+4)) / 2)
  BitVec.ofNat 32 off + 4#32 + (d ++ 0#1).signExtend 32 = BitVec.ofNat 32 dest

theorem branch_run {code : List (BitVec 8)} {base : Word} {s : State} {off dest : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hp : s.pc = base + BitVec.ofNat 32 off) (he : off % 2 = 0)
    (hat : seqAt code off [bTo off dest] = true) (hm : TargetMatches off dest) :
    runH code base 1 s = .ok (s.setReg 15 (base + BitVec.ofNat 32 dest), [⟨s.pc, bTo off dest, []⟩]) := by
  have h := (by
    simpa only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hat :
    (instrAt code off = some (bTo off dest) ∧ off + (bTo off dest).size ≤ code.length) ∧ True).1
  have hex : (bTo off dest).exec s = .ok (s.setReg 15 (base + BitVec.ofNat 32 dest)) := by
    unfold bTo Instr.exec
    dsimp only [TargetMatches] at hm
    rw [hp, ← hm]
    simp only [BitVec.add_assoc]
  have hs := stepH_of_instr hb hlen hp he h.1 h.2 (by rfl) hex
  exact runH_one_step 0 hs

theorem cond_run {code : List (BitVec 8)} {base : Word} {s : State} {off : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hp : s.pc = base + BitVec.ofNat 32 off) (he : off % 2 = 0)
    (hat : seqAt code off [.bcond 1 0] = true) :
    let dest := off + if s.z then 2 else 4
    runH code base 1 s = .ok (s.setReg 15 (base + BitVec.ofNat 32 dest), [⟨s.pc, .bcond 1 0, []⟩]) := by
  have h := (by
    simpa only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hat :
    (instrAt code off = some (.bcond 1 0) ∧ off + (Instr.bcond 1 0).size ≤ code.length) ∧ True).1
  have hex : (Instr.bcond 1 0).exec s =
      .ok (s.setReg 15 (base + BitVec.ofNat 32 (off + if s.z then 2 else 4))) := by
    rw [Instr.exec]
    simp only [condPassed, hp]
    cases s.z <;> simp [Instr.size, ← BitVec.add_assoc, ofNat_add_assoc]
  have hs := stepH_of_instr hb hlen hp he h.1 h.2 (by rfl) hex
  exact runH_one_step 0 hs

private theorem set_pc_pc (s : State) (pc : Word) : (s.setReg 15 pc).pc = pc := by
  simp [State.pc, State.setReg]

private theorem set_pc_sp (s : State) (pc : Word) : (s.setReg 15 pc).sp = s.sp := by
  simp [State.sp, State.setReg]

def countControl (off done : Nat) : List Instr :=
  let o := off + seqSize updateCounter
  updateCounter ++ [.bcond 1 0, bTo (o+2) done]

def countTrace (base sp : Word) (off done : Nat) (last : Bool) : List Event :=
  let o := off + seqSize updateCounter
  traceAll updateCounter (stackState (base + BitVec.ofNat 32 off) sp) ++
    [⟨base + BitVec.ofNat 32 o, .bcond 1 0, []⟩] ++
      if last then [⟨base + BitVec.ofNat 32 (o+2), bTo (o+2) done, []⟩] else []

theorem route_count {code : List (BitVec 8)} {base : Word} {s : State} {off done n : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hp : s.pc = base + BitVec.ofNat 32 off) (he : off % 2 = 0)
    (hst : FrameOk s.sp) (hn : n ≤ initialCount) (hnz : n > 0)
    (hc : stackWord s counterAt = BitVec.ofNat 32 n)
    (hat : seqAt code off (countControl off done) = true)
    (hm : TargetMatches (off + seqSize updateCounter + 2) done) :
    let o := off + seqSize updateCounter
    ∃ t, runH code base (updateCounter.length + if n=1 then 2 else 1) s = .ok (t, countTrace base s.sp off done (n == 1)) ∧
      t.pc = base + BitVec.ofNat 32 (if n=1 then done else o+4) ∧
      t.sp = s.sp ∧ t.mem = write32 s.mem (addr s.sp counterAt) (BitVec.ofNat 32 (n-1)) := by
  let o := off + seqSize updateCounter
  let u := execAll updateCounter s
  have hal := alignedAll_sp updateCounter s
    ((spBlock_of_B (ok := fun p => p.2 % 4 == 0) (by decide +kernel)).mono (fun _ h => beq_iff_eq.mp h))
    hst.1
  simp only [countControl, seqAt_append, Bool.and_eq_true] at hat
  have hAt : seqAt code o ([.bcond 1 0] ++ [bTo (o+2) done]) = true := hat.2
  rw [seqAt_append, Bool.and_eq_true] at hAt
  have hsz : seqSize [.bcond 1 0] = 2 := rfl
  rw [hsz] at hAt
  obtain ⟨hR, ho⟩ := execute_pre hb hlen hp he hat.1 (by rfl) hal
  have heO : o % 2 = 0 := by
    have h := seqSize_mod_two updateCounter
    change (off + seqSize updateCounter) % 2 = 0
    omega
  have hTrace := stack_trace (is := updateCounter) (by decide) (by decide +kernel) s
  rw [hp] at hTrace
  obtain ⟨hmem, hz, hsp⟩ := count_effect s n hn hnz hc
  have hB := cond_run hb hlen ho heO hAt.1
  dsimp only at hB
  by_cases h : n = 1
  · simp only [hz, h, beq_self_eq_true, ite_true] at hB
    let v := u.setReg 15 (base + BitVec.ofNat 32 (o+2))
    have hv : v.pc = base + BitVec.ofNat 32 (o+2) := set_pc_pc _ _
    have hV := branch_run hb hlen hv (by omega) hAt.2 hm
    have hRv := runH_compose hR (runH_compose hB hV)
    refine ⟨v.setReg 15 (base + BitVec.ofNat 32 done), ?_, ?_, ?_, hmem⟩
    · rw [hTrace,ho,hv] at hRv
      simpa only [h, beq_self_eq_true, ite_true, countTrace, o, List.append_assoc] using hRv
    · simpa only [h, ite_true] using (set_pc_pc v (base + BitVec.ofNat 32 done))
    · exact (set_pc_sp v _).trans ((set_pc_sp u _).trans hsp)
  · simp only [hz, show (n == 1) = false from beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ite_false] at hB
    have hRv := runH_compose hR hB
    refine ⟨u.setReg 15 (base + BitVec.ofNat 32 (o+4)), ?_, ?_, ?_, hmem⟩
    · rw [hTrace,ho] at hRv
      simpa only [h, show (n == 1) = false from beq_eq_false_iff_ne.mpr h,
        Bool.false_eq_true, ite_false, countTrace, o, List.append_nil] using hRv
    · simpa only [h, ite_false] using (set_pc_pc u (base + BitVec.ofNat 32 (o+4)))
    · exact (set_pc_sp u _).trans hsp

end SafegcdTermination.LoopControl
