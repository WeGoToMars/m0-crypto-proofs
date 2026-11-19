import SafegcdTermination.FinalSub
import SafegcdTermination.RunInit

namespace SafegcdTermination.FinalSelect

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open SafegcdTermination.FinalCode SafegcdTermination.FinalWords SafegcdTermination.FinalPrepare
open SafegcdTermination.FinalArithmetic SafegcdTermination.FinalSub
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.RowCalls (entered_regs entered_mem entered_pc)
open SafegcdTermination.PublicTrace
open SafegcdTermination.Leaf
open M0Crypto.Armv6M (State Reg read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj ne_of_disj read32_congr)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Select (selBody sel_exec)

set_option maxHeartbeats 1300000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false

structure OutputOk (sp dst : Word) : Prop where
  align : dst.toNat % 4 = 0
  positive : sp = dst ∨ Disj sp 32 dst 32
  negative : addr sp bankE = dst ∨ Disj (addr sp bankE) 32 dst 32
  ret : Disj dst 32 (addr sp returnAt) 4

private theorem move_mask (s : State) :
    let u := execAll [.movHi 7 3] s
    u.regs 7 = s.regs 3 ∧ u.regs 0 = s.regs 0 ∧ u.regs 1 = s.regs 1 ∧ u.regs 2 = s.regs 2 ∧ u.mem = s.mem := by
  row_simps

private theorem select_value (s : State) (sp dst : Word) (negative : Prop) [Decidable negative]
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = sp) (h2 : s.regs 2 = addr sp bankE)
    (hm : s.regs 3 = if negative then -1#32 else 0#32) (h : OutputOk sp dst) :
    feVal (execAll selectBody s).mem dst =
      if negative then feVal s.mem (addr sp bankE) else feVal s.mem sp := by
  let u := execAll [.movHi 7 3] s
  obtain ⟨u7,u0,u1,u2,uM⟩ := move_mask s
  have uMask : u.regs 7 = 0 ∨ u.regs 7 = BitVec.allOnes 32 := by
    rw [u7,hm]
    split <;> decide
  have he : feVal (execAll selBody u).mem dst =
      if u.regs 7 = 0 then feVal u.mem sp else feVal u.mem (addr sp bankE) :=
    (sel_exec u (u0.trans h0) (u1.trans h1) (u2.trans h2) uMask h.ret.1 h.positive h.negative).1
  rw [uM,u7,hm] at he
  have hExec : execAll selectBody s = execAll selBody u := by
    change execAll ([.movHi 7 3] ++ selBody) s = _
    rw [execAll_append]
  rw [hExec,he]
  split <;> simp_all

private theorem ret_after_select {s t : State} {dst : Word}
    (hs : t.sp = s.sp) (hw : WritesOnly s.mem t.mem dst 32)
    (h : Disj dst 32 (addr s.sp returnAt) 4) : stackWord t returnAt = stackWord s returnAt := by
  unfold stackWord stackAddr
  rw [hs]
  change read32 t.mem (addr s.sp returnAt) = read32 s.mem (addr s.sp returnAt)
  apply read32_congr
  intro i hi
  apply hw
  intro j hj
  exact (ne_of_disj h.1 h.2.1 h.2.2 hj hi).symm

structure Links (code : List (BitVec 8)) (off dest : Nat) : Prop where
  args : seqAt code off selectArgs = true
  call : seqAt code (off+seqSize selectArgs) [callTo (off+seqSize selectArgs) dest] = true
  leaf : seqAt code dest (selectBody ++ [.bx 14]) = true
  even : dest % 2 = 0

def pickTrace (base sp dst : Word) (off dest : Nat) : List Event :=
  callTrace selectBody base off dest
    (publicState [(15,base+BitVec.ofNat 32 dest),(0,dst),(1,sp),(2,addr sp bankE)])

def selectTrace (base sp dst : Word) (off dest : Nat) : List Event :=
  traceAll selectArgs (stackState (base+BitVec.ofNat 32 off) sp) ++
    pickTrace base sp dst (off+seqSize selectArgs) dest

private theorem run_pick {code : List (BitVec 8)} {base : Word} {call dest : Nat} {s : State}
    {dst : Word} (negative : Prop) [Decidable negative]
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (he : call % 2 = 0) (hd : dest % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 call)
    (hCall : seqAt code call [callTo call dest] = true)
    (hLeaf : seqAt code dest (selectBody ++ [.bx 14]) = true)
    (hf : FrameOk s.sp) (hOk : OutputOk s.sp dst)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = s.sp) (h2 : s.regs 2 = addr s.sp bankE)
    (h3 : s.regs 3 = if negative then -1#32 else 0#32) :
    ∃ t, runH code base (selectBody.length+1+1) s = .ok (t,pickTrace base s.sp dst call dest) ∧
      t.pc = base + BitVec.ofNat 32 (call+4) ∧ t.sp = s.sp ∧
      WritesOnly s.mem t.mem dst 32 ∧ stackWord t returnAt = stackWord s returnAt ∧
      feVal t.mem dst = if negative then feVal s.mem (addr s.sp bankE) else feVal s.mem s.sp := by
  have alignments : ∀ p ∈ ([(0,4),(1,4),(2,4)] : List (Reg × Nat)),
      p.1 ≠ 14 ∧ p.1 ≠ 15 ∧ (s.regs p.1).toNat % p.2 = 0 := by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with h | h | h <;> subst j
    · exact ⟨by decide,by decide,by rw [h0]; exact hOk.align⟩
    · exact ⟨by decide,by decide,by rw [h1]; exact hf.1⟩
    · exact ⟨by decide,by decide,by rw [h2]; exact aligned hf (ha := (by unfold InSlot; decide : InSlot bankE))⟩
  obtain ⟨t,hRun,hPc,hSp,hM,hW⟩ := run_leaf_call hb hlen hp he hd hCall hLeaf checked_select alignments (by decide)
  rw [h0] at hW
  let u := entered base call dest s
  have h0' : u.regs 0 = dst := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h0
  have h1' : u.regs 1 = s.sp := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h1
  have h2' : u.regs 2 = addr s.sp bankE := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h2
  have h3' : u.regs 3 = if negative then -1#32 else 0#32 := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h3
  have hm : u.mem = s.mem := entered_mem _ _ _ _
  have hValue := select_value u s.sp dst negative h0' h1' h2' h3' hOk
  rw [hm] at hValue
  have hTr : callTrace selectBody base call dest u = pickTrace base s.sp dst call dest := by
    unfold pickTrace
    apply call_trace_congr (regs := [15,0,1,2]) (by decide) (by decide +kernel)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e | e | e | e <;> subst r
    · exact entered_pc _ _ _ _
    · exact h0'
    · exact h1'
    · exact h2'
  rw [hTr] at hRun
  exact ⟨t,hRun,hPc,hSp,hW,ret_after_select hSp hW hOk.ret,by rw [hM]; exact hValue⟩

theorem run_select {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State}
    {dst : Word} {d : Int} (negative : Prop) [Decidable negative]
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (he : off % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 off) (hLink : Links code off dest)
    (hf : FrameOk s.sp) (hOk : OutputOk s.sp dst) (hOut : stackWord s outputAt = dst)
    (hSign : (stackWord s signAt).toInt < 0 ↔ negative) (h : Operands s d) :
    ∃ t, runH code base (selectArgs.length+(selectBody.length+1+1)) s = .ok (t,selectTrace base s.sp dst off dest) ∧
      t.pc = base + BitVec.ofNat 32 (off+seqSize selectArgs+4) ∧ t.sp = s.sp ∧
      WritesOnly s.mem t.mem dst 32 ∧ stackWord t returnAt = stackWord s returnAt ∧
      ((feVal t.mem dst : Int) ≡ (if negative then -d else d) [ZMOD p]) ∧
      (¬ negative → (feVal t.mem dst : Int) = d) := by
  let u := execAll selectArgs s
  have hLen : code.length < 2^32 := by omega
  have hAl : alignedAll selectArgs s = true := RunInit.align_from_sp _ (by decide) (by decide) s hf.1
  obtain ⟨hU,hPc⟩ := execute_pre hb hLen hp he hLink.args (by decide) hAl
  obtain ⟨r3,r0,r1,r2,uM,uS⟩ := select_args s
  have r3' : u.regs 3 = if negative then -1#32 else 0#32 := by rw [r3,sign_word]; simp only [hSign]
  have r0' : u.regs 0 = dst := r0.trans hOut
  have r1' : u.regs 1 = u.sp := r1.trans uS.symm
  have r2' : u.regs 2 = addr u.sp bankE := r2.trans (congrArg (fun a => addr a bankE) uS.symm)
  have hEven : (off+seqSize selectArgs) % 2 = 0 := by have h := seqSize_mod_two selectArgs; omega
  obtain ⟨t,hT,hP,hSp,hW,hRet,hVal⟩ := run_pick negative hb hlen hEven hLink.even hPc hLink.call hLink.leaf
    (by rw [uS]; exact hf) (by rw [uS]; exact hOk) r0' r1' r2' r3'
  rw [uS,uM] at hVal
  have hRet' : stackWord u returnAt = stackWord s returnAt := by unfold stackWord stackAddr; rw [uS,uM]
  have hTr := stack_trace (is := selectArgs) (by decide) (by decide +kernel) s
  rw [hp] at hTr
  rw [hTr] at hU
  rw [uS] at hT
  refine ⟨t,runH_compose hU hT,hP,hSp.trans uS,by simpa only [uM] using hW,hRet.trans hRet',?_⟩
  constructor
  · rw [hVal]
    by_cases hN : negative
    · simpa only [hN,ite_true] using h.negative
    · simp only [hN,ite_false,h.packed]
      rfl
  · intro hN
    rw [hVal]
    simp only [hN,ite_false,h.packed]

end SafegcdTermination.FinalSelect
