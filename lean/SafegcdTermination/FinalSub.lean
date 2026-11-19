import SafegcdTermination.FinalPrepare
import SafegcdTermination.Leaf

namespace SafegcdTermination.FinalSub

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open SafegcdTermination.FinalCode SafegcdTermination.FinalPrepare
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.RowCalls (entered_regs entered_mem entered_pc)
open SafegcdTermination.PublicTrace
open SafegcdTermination.Leaf
open M0Crypto.Armv6M (State Reg)
open M0Crypto.Thumb
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519AddSub (feSub_exec)

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option linter.unusedSimpArgs false

structure Operands (s : State) (d : Int) : Prop where
  packed : (feVal s.mem s.sp : Int) = d
  negative : (feVal s.mem (addr s.sp bankE) : Int) ≡ -d [ZMOD p]

structure Finished (root t : State) (d : Int) : Prop extends Operands t d where
  sp : t.sp = root.sp
  outside : WritesOnly root.mem t.mem root.sp frameBytes
  sign : stackWord t signAt = stackWord root signAt
  output : stackWord t outputAt = stackWord root outputAt
  ret : stackWord t returnAt = stackWord root returnAt

private theorem sub_value {s t : State} {d : Int} {base : Word} {off dest : Nat}
    (h0 : s.regs 0 = addr s.sp bankE) (h1 : s.regs 1 = addr s.sp bankG)
    (h2 : s.regs 2 = s.sp) (hPacked : (feVal s.mem s.sp : Int) = d)
    (hZero : feVal s.mem (addr s.sp bankG) = 0)
    (hFrame : FrameOk s.sp) (hSp : t.sp = s.sp)
    (hM : t.mem = (execAll subBody (entered base off dest s)).mem) :
    (feVal t.mem (addr t.sp bankE) : Int) ≡ -d [ZMOD p] := by
  let u := entered base off dest s
  have u0 : u.regs 0 = addr s.sp bankE := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h0
  have u1 : u.regs 1 = addr s.sp bankG := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h1
  have u2 : u.regs 2 = s.sp := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans h2
  have uM : u.mem = s.mem := entered_mem _ _ _ _
  have hDst : (u.regs 0).toNat+32 ≤ 2^32 := by
    rw [u0,addr_nat hFrame _ (by decide)]
    have ho : bankE + 32 ≤ frameBytes := by decide
    have := hFrame.2
    omega
  have hVal := (feSub_exec u hDst).1
  change (feVal (execAll subBody u).mem (u.regs 0) : Int) % p =
    ((feVal u.mem (u.regs 1) : Int) - feVal u.mem (u.regs 2)) % p at hVal
  rw [u0,u1,u2,uM,hZero,hPacked] at hVal
  change (feVal t.mem (addr t.sp bankE) : Int) % p = (-d) % p
  rw [hSp,hM]
  simpa only [Int.natCast_zero,Int.zero_sub] using hVal

private theorem sub_align {s : State} {root : State} {d : Int} (h : Ready root s d)
    (hf : FrameOk s.sp) : ∀ p ∈ ([(0,4),(1,4),(2,4)] : List (Reg × Nat)),
    p.1 ≠ 14 ∧ p.1 ≠ 15 ∧ (s.regs p.1).toNat % p.2 = 0 := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h0 | h1 | h2 <;> subst i
  · exact ⟨by decide,by decide,by rw [h.r0]; exact aligned hf (ha := (by unfold InSlot; decide : InSlot bankE))⟩
  · exact ⟨by decide,by decide,by rw [h.r1]; exact aligned hf (ha := (by unfold InSlot; decide : InSlot bankG))⟩
  · exact ⟨by decide,by decide,by rw [h.r2]; exact hf.1⟩

def subTrace (base sp : Word) (off dest : Nat) : List Event :=
  callTrace subBody base off dest
    (publicState [(15,base+BitVec.ofNat 32 dest),(0,addr sp bankE),(1,addr sp bankG),(2,sp)])

theorem run_sub {code : List (BitVec 8)} {base : Word} {off dest : Nat} {root s : State} {d : Int}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23)
    (hp : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (hCall : seqAt code off [callTo off dest] = true) (hLeaf : seqAt code dest (subBody ++ [.bx 14]) = true)
    (hFrame : FrameOk s.sp) (hReady : Ready root s d) :
    ∃ t, runH code base (subBody.length+1+1) s = .ok (t,subTrace base s.sp off dest) ∧
      t.pc = base + BitVec.ofNat 32 (off+4) ∧ Finished root t d := by
  obtain ⟨t,hRun,hPc,hSp,hM,hW⟩ := run_leaf_call hb hlen hp ho hd hCall hLeaf
    checked_sub (sub_align hReady hFrame) (by decide)
  rw [hReady.r0] at hW
  have hVal := sub_value hReady.r0 hReady.r1 hReady.r2 hReady.packed hReady.zero hFrame hSp hM
  have hPos := keep_field (off := bankF) hSp hW (by decide) (by decide) (.inl (by decide))
  rw [at_base,at_base] at hPos
  have hOut : WritesOnly s.mem t.mem root.sp frameBytes := by
    rw [← hReady.sp]
    exact restrict_frame (by decide : bankE+32 ≤ frameBytes) hW
  have hSaved (o : Nat) (h0 : o+4 ≤ 2^32) (h1 : bankE+32 ≤ o) : stackWord t o = stackWord s o :=
    keep_stack_word hSp hW h0 (by decide) (.inr h1)
  have hTr : callTrace subBody base off dest (entered base off dest s) = subTrace base s.sp off dest := by
    unfold subTrace
    apply call_trace_congr (regs := [15,0,1,2]) (by decide) (by decide +kernel)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e | e | e | e <;> subst r
    · exact entered_pc _ _ _ _
    · exact (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hReady.r0
    · exact (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hReady.r1
    · exact (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hReady.r2
  rw [hTr] at hRun
  refine ⟨t,hRun,hPc,⟨⟨?_,hVal⟩,hSp.trans hReady.sp,WritesOnly.trans hReady.outside hOut,?_,?_,?_⟩⟩
  · rw [hPos,hReady.packed]
  · exact (hSaved signAt (by decide) (by decide)).trans hReady.sign
  · exact (hSaved outputAt (by decide) (by decide)).trans hReady.output
  · exact (hSaved returnAt (by decide) (by decide)).trans hReady.ret

end SafegcdTermination.FinalSub
