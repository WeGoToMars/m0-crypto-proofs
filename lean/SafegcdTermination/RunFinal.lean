import SafegcdTermination.FinalSelect

namespace SafegcdTermination.RunFinal

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open SafegcdTermination.FinalCode SafegcdTermination.FinalWords SafegcdTermination.FinalPrepare
open SafegcdTermination.FinalSub SafegcdTermination.FinalSelect
open SafegcdTermination.PublicTrace
open SafegcdTermination.Leaf (callTrace)
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.FoldCall (fold_call)
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.BatchMachine (Slot iterate_range)
open SafegcdTermination.RowCalls (Setup)
open M0Crypto.Armv6M (State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519Routines (feVal)

set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
set_option linter.unusedSimpArgs false

def foldSite (o : Nat) : Nat := o + seqSize (prepareFold finalRow)

def packSite (o : Nat) : Nat := foldSite o + 4

def subSite (o : Nat) : Nat := packSite o + seqSize subPrep

def selectSite (o : Nat) : Nat := subSite o + 4

def retSite (o : Nat) : Nat := selectSite o + seqSize selectArgs + 4

structure Place (code : List (BitVec 8)) (q : Targets) (off sub select : Nat) : Prop where
  foldCall : seqAt code off (prepareFold finalRow ++ [callTo (foldSite off) q.fold]) = true
  foldLeaf : seqAt code q.fold (FoldCode.body ++ [.bx 14]) = true
  foldEven : q.fold % 2 = 0
  pre : seqAt code (packSite off) subPrep = true
  subCall : seqAt code (subSite off) [callTo (subSite off) sub] = true
  subLeaf : seqAt code sub (subBody ++ [.bx 14]) = true
  subEven : sub % 2 = 0
  selectLink : Links code (selectSite off) select
  ret : seqAt code (retSite off) FinalCode.ret = true

theorem place_of_link {code : List (BitVec 8)} {q : Targets} {off sub select : Nat}
    (h : seqAt code off (FinalCode.tail q off sub select) = true)
    (hF : seqAt code q.fold (FoldCode.body ++ [.bx 14]) = true) (hFE : q.fold % 2 = 0)
    (hSub : seqAt code sub (subBody ++ [.bx 14]) = true) (hSE : sub % 2 = 0)
    (hSel : seqAt code select (selectBody ++ [.bx 14]) = true) (hSLE : select % 2 = 0) : Place code q off sub select := by
  have sz (a b : Nat) : seqSize [callTo a b] = 4 := rfl
  simp only [FinalCode.tail, seqAt_append, Bool.and_eq_true, and_assoc, seqSize_append, sz, Nat.add_assoc] at h
  obtain ⟨hP,hFold,hPack,hZero,hSubArgs,hSubCall,hSelArgs,hSelCall,hRet⟩ := h
  refine ⟨?_,hF,hFE,?_,?_,hSub,hSE,⟨?_,?_,hSel,hSLE⟩,?_⟩
  · rw [seqAt_append,Bool.and_eq_true]
    exact ⟨hP,hFold⟩
  · simp only [packSite,foldSite,subPrep,seqAt_append,Bool.and_eq_true,seqSize_append,Nat.add_assoc]
    exact ⟨⟨hPack,hZero⟩,hSubArgs⟩
  all_goals simp only [retSite,selectSite,subSite,packSite,foldSite,subPrep,seqSize_append,Nat.add_assoc] at *
  · exact hSubCall
  · exact hSelArgs
  · exact hSelCall
  · exact hRet

private theorem from_frame {sp : Word} (h : FrameOk sp) : Setup sp finalRow :=
  ⟨h,by unfold InSlot; decide,by unfold InSlot; decide,by unfold InSlot; decide,.inl rfl,.inl rfl,by decide⟩

private theorem nonzero_size_le {code : List (BitVec 8)} {o : Nat} {is : List Instr}
    (h : seqAt code o is = true) (he : is ≠ []) : o+seqSize is ≤ code.length :=
  (seqAt_size _ _ _ h).resolve_right he

def retTrace (base sp : Word) (off : Nat) : List Event :=
  let is := [loadSp 3 returnAt]
  traceAll is (stackState (base + BitVec.ofNat 32 off) sp) ++
    [⟨base + BitVec.ofNat 32 (off+seqSize is),.bx 3,[]⟩]

def finalTrace (q : Targets) (base sp dst : Word) (off sub select : Nat) : List Event :=
  traceAll (prepareFold finalRow) (stackState (base+BitVec.ofNat 32 off) sp) ++
    (⟨base+BitVec.ofNat 32 (foldSite off),callTo (foldSite off) q.fold,[]⟩ ::
      FoldCode.predictedTrace (base+BitVec.ofNat 32 q.fold) sp) ++
    traceAll subPrep (stackState (base+BitVec.ofNat 32 (packSite off)) sp) ++
    subTrace base sp (subSite off) sub ++ selectTrace base sp dst (selectSite off) select ++
    retTrace base sp (retSite off)

private theorem run_ret {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32) (he : off % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 off) (hAt : seqAt code off FinalCode.ret = true)
    (ha : s.sp.toNat % 4 = 0) (hR : (stackWord s returnAt).getLsbD 0 = true) :
    ∃ t, runH code base FinalCode.ret.length s = .ok (t,retTrace base s.sp off) ∧
      t.pc = stackWord s returnAt &&& ~~~1#32 ∧ t.sp = s.sp ∧ t.mem = s.mem := by
  let l := [loadSp 3 returnAt]
  let u := execAll l s
  have hAlign : alignedAll l s = true := RunInit.align_from_sp l (by decide) (by decide) s ha
  have hLoad : u.regs 3 = stackWord s returnAt ∧ u.sp = s.sp ∧ u.mem = s.mem := by
    unfold u l loadSp imm stackWord stackAddr returnAt frameBytes
    row_simps
  have hEven : (off+seqSize l) % 2 = 0 := by have h := seqSize_mod_two l; omega
  have hAt' : seqAt code off (l ++ [.bx 3]) = true := hAt
  have hLeaf := runH_leaf (ret := 3) hb hlen hp he hAt' (by decide) hAlign hEven (by rw [hLoad.1]; exact hR)
  let t := u.setReg 15 (u.regs 3 &&& ~~~1#32)
  have hTr := stack_trace (is := l) (by decide) (by decide +kernel) s
  rw [hp] at hTr
  have hU : u.pc = base+BitVec.ofNat 32 (off+seqSize l) := by
    change (execAll l s).pc = _
    rw [execAll_pc _ _ (by decide),hp,ofNat_add_assoc]
  dsimp only at hLeaf
  rw [hTr,hU] at hLeaf
  refine ⟨t,hLeaf,?_,?_,hLoad.2.2⟩
  · simp [t,State.pc,State.setReg,hLoad.1]
  · simpa [t,State.sp,State.setReg] using hLoad.2.1

def WritesFrameAndOut (m m' : Mem) (sp dst : Word) : Prop :=
  ∀ a, (∀ i < frameBytes, a ≠ sp + BitVec.ofNat 32 i) → (∀ i < 32, a ≠ dst + BitVec.ofNat 32 i) → m' a = m a

structure Result (s t : State) (dst lr : Word) (z : Int) : Prop where
  value : (feVal t.mem dst : Int) ≡ z ^ (p.toNat-2) [ZMOD p]
  zero : z % p = 0 → feVal t.mem dst = 0
  outside : WritesFrameAndOut s.mem t.mem s.sp dst
  sp : t.sp = s.sp
  pc : t.pc = lr &&& ~~~1#32

/-- Fold the final residue until it fits eight packed words, compute both signs,
    select by the high limb of the terminal odd scalar, and return. -/
theorem run_final {code : List (BitVec 8)} {q : Targets} {base : Word} {off sub select : Nat}
    {root s : State} {z : Int} {dst lr : Word}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (he : off % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 off) (hLinks : Place code q off sub select)
    (hf : FrameOk s.sp) (hOut : OutputOk s.sp dst) (hr : lr.getLsbD 0 = true)
    (hDst : stackWord root outputAt = dst) (hRet : stackWord root returnAt = lr)
    (hz : 0 ≤ z) (hzp : z < p) (h : RunLoop.Live root s 1 z batchCount) :
    ∃ t n, runH code base n s = .ok (t,finalTrace q base s.sp dst off sub select) ∧ Result s t dst lr z := by
  have hLen : code.length < 2^32 := by omega
  have hF0 : Slot s.mem s.sp temp (iterate z batchCount).scalar.f := h.image.f
  have hD0 : Slot s.mem s.sp bankF (iterate z batchCount).d := h.image.d
  have hRd := (iterate_range hz hzp batchCount).d
  have hR : 38 ≤ 2*foldRadix := by decide
  have hLo : -2*foldRadix ≤ (iterate z batchCount).d := by have := hRd.1; omega
  have hHi : (iterate z batchCount).d < 3*foldRadix := by have := hRd.2; omega
  have hFoldBound : off+seqSize (prepareFold finalRow)+4 < 2^23 := by
    have hB := nonzero_size_le hLinks.foldCall (by simp [prepareFold]);
    rw [seqSize_append, show seqSize [callTo (foldSite off) q.fold] = 4 from rfl] at hB
    omega
  have hFoldDst : q.fold < 2^23 := by have := nonzero_size_le hLinks.foldLeaf (by simp); omega
  obtain ⟨a,hA,hAP,aS,aVal,aForm,aW⟩ := fold_call hb hLen hp he hLinks.foldEven hFoldBound hFoldDst
    hLinks.foldCall hLinks.foldLeaf (from_frame hf) hD0.formed.1
    (by change -2*foldRadix ≤ value s.mem (addr s.sp bankF); rw [hD0.value]; exact hLo)
    (by change value s.mem (addr s.sp bankF) < 3*foldRadix; rw [hD0.value]; exact hHi)
  change value a.mem (addr s.sp bankF) = fold (value s.mem (addr s.sp bankF)) at aVal
  change VecWellFormed (vec a.mem (addr s.sp bankF)) at aForm
  let d := fold (iterate z batchCount).d
  have aV : value a.mem a.sp = d := by rw [aS,← at_base s.sp,aVal,hD0.value]
  have aF : VecWellFormed (vec a.mem a.sp) := by simpa only [at_base,aS] using aForm
  have aZero : vec a.mem a.sp 16 = 0#32 := top_zero _ _ aF.1 (by rw [aV]; exact last_fold_range hRd)
  have hf' : FrameOk a.sp := by rw [aS]; exact hf
  have hPackE : (packSite off) % 2 = 0 := by
    have hSz := seqSize_mod_two (prepareFold finalRow)
    unfold packSite foldSite
    omega
  have align : alignedAll subPrep a = true := RunInit.align_from_sp _ (by decide) (by decide +kernel) a hf'.1
  obtain ⟨hP,hPP⟩ := execute_pre hb hLen hAP hPackE hLinks.pre (by decide) align
  have hPrep := sub_ready a aF aZero
  rw [aV] at hPrep
  have hSubE : (subSite off) % 2 = 0 := by
    have hE := seqSize_mod_two subPrep
    unfold subSite
    omega
  obtain ⟨b,hB,hBP,bVal⟩ := run_sub hb hlen hPP hSubE hLinks.subEven hLinks.subCall hLinks.subLeaf
    (by rw [hPrep.sp]; exact hf') hPrep
  have bS := bVal.sp.trans aS
  have hAW : WritesOnly s.mem a.mem (addr s.sp bankF) vectorBytes := aW
  have kept (o : Nat) (h0 : o+4 ≤ 2^32) (h1 : bankF+vectorBytes ≤ o) : stackWord a o = stackWord s o :=
    keep_stack_word aS hAW h0 (by decide) (.inr h1)
  have hOutA : stackWord a outputAt = dst := (kept _ (by decide) (by decide)).trans (h.output.trans hDst)
  have hRetA : stackWord a returnAt = lr := (kept _ (by decide) (by decide)).trans (h.ret.trans hRet)
  have hSignA : (stackWord a signAt).toInt < 0 ↔ (iterate z batchCount).scalar.f < 0 := by
    rw [kept _ (by decide) (by decide), show signAt = temp+4*16 by decide, ← stack_vec,
      (top_sign _ _ hF0.formed.1), hF0.value]
  have hSelE : (selectSite off) % 2 = 0 := by unfold selectSite; omega
  obtain ⟨c,hC,hCP,cS,cW,cR,cVal⟩ := run_select ((iterate z batchCount).scalar.f < 0) hb hlen hSelE hBP
    hLinks.selectLink (by rw [bS]; exact hf) (by rw [bS]; exact hOut) (bVal.output.trans hOutA)
    (by rw [bVal.sign]; exact hSignA) bVal.toOperands
  have cS' := cS.trans bS
  have cR' := cR.trans (bVal.ret.trans hRetA)
  have hRetE : (retSite off) % 2 = 0 := by
    have hSz := seqSize_mod_two selectArgs
    unfold retSite
    omega
  obtain ⟨t,hT,hTP,tS,tM⟩ := run_ret hb hLen hRetE hCP hLinks.ret
    (by rw [cS']; exact hf.1) (by rw [cR']; exact hr)
  have hW : WritesOnly s.mem b.mem s.sp frameBytes :=
    WritesOnly.trans (restrict_frame (by decide : bankF+vectorBytes ≤ frameBytes) hAW)
      (by rw [← aS]; exact bVal.outside)
  have trA := stack_trace (is := prepareFold finalRow) (by decide) (by decide +kernel) s
  have trP := stack_trace (is := subPrep) (by decide) (by decide +kernel) a
  rw [hp] at trA
  rw [hAP,aS] at trP
  rw [trA,show addr s.sp finalRow.dst = s.sp from at_base s.sp] at hA
  rw [trP] at hP
  rw [hPrep.sp,aS] at hB
  rw [bS] at hC
  rw [cS'] at hT
  let hSteps := (prepareFold finalRow).length+(FoldCode.body.length+1+1)+subPrep.length+
    (subBody.length+1+1)+(selectArgs.length+(selectBody.length+1+1))+FinalCode.ret.length
  refine ⟨t,hSteps,?_,⟨?_,?_,?_,tS.trans cS',by rw [cR'] at hTP; exact hTP⟩⟩
  · have hRun := runH_compose (runH_compose (runH_compose (runH_compose hA hP) hB) hC) hT
    simpa only [hSteps,finalTrace,subSite,foldSite,packSite,List.append_assoc] using hRun
  · rw [tM]
    exact cVal.1.trans (inverse_power hz hzp)
  · intro hz0
    have h0 : z = 0 := (Int.emod_eq_of_lt hz hzp).symm.trans hz0
    have hN : ¬ (iterate z batchCount).scalar.f < 0 := by
      rw [h0,zero_final_f]
      exact Int.not_lt_of_ge (Int.le_of_lt p_pos)
    have hExact := cVal.2 hN
    have hZero : d = 0 := by
      unfold d
      rw [h0,(zero_iterate batchCount).1]
      rfl
    rw [hZero] at hExact
    rw [tM]
    omega
  · intro y h1 h2
    rw [tM,cW y h2,hW y h1]

end SafegcdTermination.RunFinal
