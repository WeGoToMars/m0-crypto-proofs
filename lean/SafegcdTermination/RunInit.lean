import SafegcdTermination.Canon
import SafegcdTermination.Leaf
import SafegcdTermination.RunInitTail
import SafegcdTermination.Literal

namespace SafegcdTermination.RunInit

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.InitCode SafegcdTermination.InitWords SafegcdTermination.RunInitTail
open SafegcdTermination.Bank SafegcdTermination.FrameWords SafegcdTermination.ClearLoop SafegcdTermination.Leaf
open SafegcdTermination.BatchMachine (Image)
open SafegcdTermination.LoopCounter (initialCount)
open SafegcdTermination.RowCalls (entered_regs entered_mem entered_pc)
open SafegcdTermination.PublicTrace
open M0Crypto.Armv6M (State Mem read32 write32 read32_write32_same)
open M0Crypto.Thumb M0Crypto.Sym
open M0Crypto.Release.Frame (Disj ne_of_disj read32_congr toNat_add_ofNat)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Facts (feVal_psum psum_congr)
open M0Crypto.Release.Field25519Reduce (pN)

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

def canonSite (start : Nat) : Nat := start + seqSize saveAndCall

def setupSite (start : Nat) : Nat := canonSite start + 4

def clearSite (start : Nat) : Nat := setupSite start + seqSize clearSetup

def tailSite (start : Nat) : Nat := clearSite start + seqSize (clearBlock ++ [clearBranch])

def loopSite (start : Nat) : Nat := tailSite start + seqSize tail

structure Place (code : List (BitVec 8)) (start canon : Nat) : Prop where
  save : seqAt code start saveAndCall = true
  canonCall : seqAt code (canonSite start) [callTo (canonSite start) canon] = true
  canonLeaf : seqAt code canon (canonBody ++ [.bx 14]) = true
  setup : seqAt code (setupSite start) clearSetup = true
  clear : seqAt code (clearSite start) (clearBlock ++ [clearBranch]) = true
  tail : seqAt code (tailSite start) tail = true
  canonEven : canon % 2 = 0

theorem place_of_link {code : List (BitVec 8)} {start canon : Nat}
    (hi : seqAt code start (initCode start canon) = true)
    (hc : seqAt code canon (canonBody ++ [.bx 14]) = true) (he : canon % 2 = 0) : Place code start canon := by
  have call_size (off dest : Nat) : seqSize [callTo off dest] = 4 := rfl
  simp only [initCode, clearCode, seqAt_append, Bool.and_eq_true, and_assoc,
    seqSize_append, call_size, clearBranch, Nat.add_assoc] at hi
  obtain ⟨hS,hC,hSetup,hClear,hB,hTail⟩ := hi
  refine ⟨hS,?_,hc,?_,?_,?_,he⟩
  · simpa only [canonSite] using hC
  · simpa only [setupSite,canonSite,Nat.add_assoc] using hSetup
  · rw [seqAt_append, Bool.and_eq_true]
    refine ⟨?_,?_⟩
    · simpa only [clearSite,setupSite,canonSite,Nat.add_assoc] using hClear
    · simpa only [clearSite,setupSite,canonSite,Nat.add_assoc,clearBranch] using hB
  · simpa only [tailSite,clearSite,setupSite,canonSite,seqSize_append,
      clearBranch,Instr.size,Nat.add_assoc,Nat.add_zero] using hTail

structure SourceOk (s : State) : Prop where
  align : (s.regs 1).toNat % 4 = 0
  copy : Disj (addr s.sp temp) 32 (s.regs 1) 32
  output : Disj (addr s.sp outputAt) 4 (s.regs 1) 32
  ret : Disj (addr s.sp returnAt) 4 (s.regs 1) 32

structure Started (root current : State) (z : Nat) : Prop where
  sp : current.sp = root.sp
  outside : WritesOnly root.mem current.mem root.sp frameBytes
  image : Image current (phases 0) (initial z)
  counter : stackWord current counterAt = BitVec.ofNat 32 initialCount
  output : stackWord current outputAt = root.regs 0
  ret : stackWord current returnAt = root.regs 14

private theorem keep_input_write {m : Mem} {a src value : Word}
    (h : Disj a 4 src 32) : feVal (write32 m a value) src = feVal m src := by
  simp only [feVal_psum]
  apply psum_congr
  intro i hi
  apply congrArg BitVec.toNat
  apply read32_congr
  intro j hj
  apply M0Crypto.Armv6M.write32_other
  intro k hk
  rw [M0Crypto.Armv6M.slot,ofNat_add_assoc]
  exact (ne_of_disj h.1 h.2.1 h.2.2 hk (by omega : 4*i+j < 32)).symm

private theorem saved (s : State) (hs : SourceOk s) :
    let t := execAll saveAndCall s
    t.regs 0 = addr s.sp temp ∧ t.regs 1 = s.regs 1 ∧ t.sp = s.sp ∧
      feVal t.mem (s.regs 1) = feVal s.mem (s.regs 1) ∧
      WritesOnly s.mem t.mem s.sp frameBytes ∧
      stackWord t outputAt = s.regs 0 ∧ stackWord t returnAt = s.regs 14 := by
  obtain ⟨h0,h1,hSp,hMem⟩ := save_arguments s
  dsimp only
  refine ⟨h0,h1,hSp,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [hMem, keep_input_write hs.output, keep_input_write hs.ret]
  · rw [hMem]
    exact WritesOnly.trans (write_frame (dst := returnAt) (by decide)) (write_frame (dst := outputAt) (by decide))
  · unfold stackWord stackAddr
    rw [hSp,hMem]
    exact read32_write32_same _ _ _
  · unfold stackWord stackAddr
    rw [hSp,hMem]
    change read32 (write32 (write32 s.mem (addr s.sp returnAt) (s.regs 14)) (addr s.sp outputAt) (s.regs 0))
      (addr s.sp returnAt) = s.regs 14
    rw [write_read_outside (dst := outputAt) (src := returnAt) (by decide) (by decide) (.inr (by decide))]
    exact read32_write32_same _ _ _

private theorem canon_at_temp {s t : State} {base : Word} {off leaf : Nat}
    (h0 : s.regs 0 = addr s.sp temp) (hSp : t.sp = s.sp)
    (hM : t.mem = (execAll canonBody (entered base off leaf s)).mem)
    (hC : Disj (addr s.sp temp) 32 (s.regs 1) 32) :
    feVal t.mem (addr t.sp temp) = feVal s.mem (s.regs 1) % pN := by
  let u := entered base off leaf s
  have u0 : u.regs 0 = addr s.sp temp := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h0
  have u1 : u.regs 1 = s.regs 1 := entered_regs _ _ _ _ _ (by decide) (by decide)
  have hm : u.mem = s.mem := entered_mem _ _ _ _
  have hArg : Disj (u.regs 0) 32 (u.regs 1) 32 := by rwa [u0,u1]
  have hVal := Canon.body_value u hArg.1 hArg.2.1 hArg.2.2
  rw [u0,u1,hm] at hVal
  rw [hM,hSp]
  exact hVal


theorem align_from_sp (is : List Instr) (hf : is.all Instr.falls = true)
    (hc : alignChk [(13,4)] is = true) (s : State) (ha : s.sp.toNat % 4 = 0) :
    alignedAll is s = true := by
  apply alignChk_sound [(13,4)] is (sound_all hf) s
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact ha
  · exact hc

private theorem even_add_seq {o : Nat} (h : o % 2 = 0) (is : List Instr) : (o+seqSize is) % 2 = 0 := by
  have := seqSize_mod_two is
  omega

def initTrace (base sp src : Word) (start canon : Nat) : List Event :=
  traceAll saveAndCall (stackState (base + BitVec.ofNat 32 start) sp) ++
    callTrace canonBody base (canonSite start) canon
      (publicState [(15,base+BitVec.ofNat 32 canon),(0,addr sp temp),(1,src)]) ++
    traceAll clearSetup (stackState (base + BitVec.ofNat 32 (setupSite start)) sp) ++
    clearTrace base (clearSite start) sp clearIterations ++
    traceAll tail (stackState (base + BitVec.ofNat 32 (tailSite start)) sp)

/-- The prologue saves both public pointers, canonicalizes the source before
    clearing any overlapping banks, and establishes the phase-zero invariant. -/
theorem run_init {code : List (BitVec 8)} {base : Word} {start canon : Nat} (s : State)
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23) (he : start % 2 = 0)
    (hp : s.pc = base + BitVec.ofNat 32 start) (hf : FrameOk s.sp)
    (hs : SourceOk s) (hl : Place code start canon) :
    ∃ t n, runH code base n s = .ok (t,initTrace base s.sp (s.regs 1) start canon) ∧
      t.pc = base + BitVec.ofNat 32 (loopSite start) ∧ Started s t (feVal s.mem (s.regs 1) % pN) := by
  have hLen : code.length < 2^32 := by omega
  have hal : alignedAll saveAndCall s = true := align_from_sp _ (by decide) (by decide) _ hf.1
  let a := execAll saveAndCall s
  obtain ⟨hA,hAP⟩ := execute_pre hb hLen hp he hl.save (by decide) hal
  obtain ⟨a0,a1,aS,aVal,aSafe,aOut,aRet⟩ := saved s hs
  have hAl : ∀ p ∈ ([(0,4),(1,4)] : List (M0Crypto.Armv6M.Reg × Nat)),
      p.1 ≠ 14 ∧ p.1 ≠ 15 ∧ (a.regs p.1).toNat % p.2 = 0 := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with h | h
    · subst p
      refine ⟨by decide,by decide,?_⟩
      rw [a0]
      exact aligned hf (ha := (by unfold InSlot; decide : InSlot temp))
    · subst p
      exact ⟨by decide,by decide,by rw [a1]; exact hs.align⟩
  have hc : (canonSite start) % 2 = 0 := even_add_seq he _
  obtain ⟨b,hB,hBP,bS,bM,bSafe⟩ := run_leaf_call (off := canonSite start) hb hlen hAP hc hl.canonEven hl.canonCall
    hl.canonLeaf checked_canon hAl (by decide)
  have bS' : b.sp = s.sp := bS.trans aS
  have bSafe' : WritesOnly a.mem b.mem (addr a.sp temp) 32 := by rwa [a0, ← aS] at bSafe
  have aCopy : Disj (addr a.sp temp) 32 (a.regs 1) 32 := by rw [aS,a1]; exact hs.copy
  have bVal := canon_at_temp a0 bS bM (by rw [aS]; exact aCopy)
  have bVal' : feVal b.mem (addr b.sp temp) = feVal s.mem (s.regs 1) % pN := by rw [bVal,a1,aVal]
  have bOut := (keep_stack_word (off := outputAt) bS bSafe' (by decide) (by decide) (.inr (by decide))).trans aOut
  have bRet := (keep_stack_word (off := returnAt) bS bSafe' (by decide) (by decide) (.inr (by decide))).trans aRet
  let c := execAll clearSetup b
  have hCs : (setupSite start) % 2 = 0 := by unfold setupSite; omega
  have hcAlign : b.sp.toNat % 4 = 0 := by rw [bS']; exact hf.1
  have hSC : alignedAll clearSetup b = true := align_from_sp _ (by decide) (by decide) _ hcAlign
  obtain ⟨hC,hCP⟩ := execute_pre hb hLen hBP hCs hl.setup (by decide) hSC
  obtain ⟨hReady,cM,cS,cA⟩ := setup_ready b hcAlign
  have hC' : (clearSite start) % 2 = 0 := even_add_seq hCs _
  obtain ⟨d,hD,hDP,dM,dS⟩ := run_clear hb hLen hC' hl.clear clearIterations (by decide) (by decide) c hCP hReady
  have dS' : d.sp = b.sp := dS.trans cS
  have dStore : d.mem = storeWords b.mem b.sp (List.replicate (4*clearIterations) 0) := by
    rw [dM,cA,cM,clear_as_store]
  have dSafe : WritesOnly b.mem d.mem (addr b.sp 0) (4*vectorBytes) := by
    intro x hx
    rw [dStore]
    apply storeWords_other
    intro i k hi hk
    rw [List.length_replicate] at hi
    rw [ofNat_add_assoc, ← show addr b.sp 0 = b.sp by simp [addr]]
    have hb : 4*clearIterations = vectorBytes := by decide
    exact hx (4*i+k) (by omega)
  have dClear := cleared_of_store b d dS' dStore
  have dVal := (keep_field (off := temp) dS' dSafe (by decide) (by decide) (.inr (by decide))).trans bVal'
  have dOut := (keep_stack_word (off := outputAt) dS' dSafe (by decide) (by decide) (.inr (by decide))).trans bOut
  have dRet := (keep_stack_word (off := returnAt) dS' dSafe (by decide) (by decide) (.inr (by decide))).trans bRet
  have hTs : (tailSite start) % 2 = 0 := even_add_seq hC' _
  have hTA : alignedAll tail d = true := align_from_sp _ (by decide) (by decide +kernel) d (by rw [dS']; exact hcAlign)
  obtain ⟨hT,hTP⟩ := execute_pre hb hLen hDP hTs hl.tail (by decide) hTA
  let t := execAll tail d
  obtain ⟨tS,tSafe,tImg,tCnt,tOut,tRet⟩ := tail_image d dClear
  have aFrame : WritesOnly a.mem b.mem s.sp frameBytes := by
    rw [← aS]
    exact restrict_frame (by decide : temp+32 ≤ frameBytes) bSafe'
  have bFrame : WritesOnly b.mem d.mem s.sp frameBytes := by
    rw [← bS']
    exact restrict_frame (by decide : 0+4*vectorBytes ≤ frameBytes) dSafe
  have tFrame : WritesOnly d.mem t.mem s.sp frameBytes := by
    rw [← bS', ← dS']; exact tSafe
  have trA := stack_trace (is := saveAndCall) (by decide) (by decide +kernel) s
  have trB : callTrace canonBody base (canonSite start) canon (entered base (canonSite start) canon a) =
      callTrace canonBody base (canonSite start) canon
        (publicState [(15,base+BitVec.ofNat 32 canon),(0,addr s.sp temp),(1,s.regs 1)]) := by
    apply call_trace_congr (regs := [15,0,1]) (by decide) (by decide +kernel)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e | e | e <;> subst r
    · exact entered_pc _ _ _ _
    · exact (entered_regs _ _ _ _ _ (by decide) (by decide)).trans a0
    · exact (entered_regs _ _ _ _ _ (by decide) (by decide)).trans a1
  have trC := stack_trace (is := clearSetup) (by decide) (by decide +kernel) b
  have trT := stack_trace (is := tail) (by decide) (by decide +kernel) d
  rw [hp] at trA
  rw [hBP,bS'] at trC
  rw [hDP,dS',bS'] at trT
  rw [trA] at hA
  rw [trB] at hB
  rw [trC] at hC
  rw [cA,bS'] at hD
  rw [trT] at hT
  have hTotal := runH_compose (runH_compose (runH_compose (runH_compose hA hB) hC) hD) hT
  have hw := WritesOnly.trans (WritesOnly.trans (WritesOnly.trans aSafe aFrame) bFrame) tFrame
  rw [dVal] at tImg
  let hSteps := saveAndCall.length+(canonBody.length+1+1)+clearSetup.length+
    ((clearBlock.length+1)*clearIterations)+tail.length
  refine ⟨t,hSteps,?_,hTP,⟨tS.trans (dS'.trans bS'),hw,tImg,tCnt,tOut.trans dOut,tRet.trans dRet⟩⟩
  simpa only [hSteps,t,initTrace,tailSite,setupSite,List.append_assoc] using hTotal

end SafegcdTermination.RunInit
