import SafegcdTermination.InitCode
import SafegcdTermination.Bank
import SafegcdTermination.PublicTrace
import M0Crypto.Sym.Block
import M0Crypto.Release.Field25519Mul128

namespace SafegcdTermination.ClearLoop

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.InitCode
open SafegcdTermination.Bank
open M0Crypto.Armv6M (State write32)
open M0Crypto.Thumb
open SafegcdTermination.PublicTrace

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 190000
set_option maxRecDepth 6000

structure Ready (s : State) (n : Nat) : Prop where
  count : s.regs 5 = BitVec.ofNat 32 n
  zeros : s.regs 1 = 0 ∧ s.regs 2 = 0 ∧ s.regs 3 = 0 ∧ s.regs 4 = 0
  align : (s.regs 0).toNat % 4 = 0

theorem setup_ready (s : State) (ha : s.sp.toNat % 4 = 0) :
    let t := execAll clearSetup s
    Ready t clearIterations ∧ t.mem = s.mem ∧ t.sp = s.sp ∧ t.regs 0 = s.sp := by
  unfold clearSetup
  constructor
  · constructor <;> row_simps
    exact ha
  · row_simps

def blockWords : List Word := [0,0,0,0]

theorem block_effect (s : State) (n : Nat) (hn : n ≤ clearIterations) (hp : n > 0) (h : Ready s n) :
    let t := execAll clearBlock s
    Ready t (n-1) ∧ t.z = (n == 1) ∧ t.mem = storeWords s.mem (s.regs 0) blockWords ∧
      t.sp = s.sp ∧ t.regs 0 = s.regs 0 + 16#32 := by
  have h15 : listRegs (30#8) = [1,2,3,4] := by decide
  have count : s.regs 5 - 1#32 = BitVec.ofNat 32 (n-1) := by
    rw [h.count]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have hN : clearIterations < 4294967296 := by decide
    omega
  have hq : (BitVec.ofNat 32 (n-1) == 0#32) = (n == 1) := by
    by_cases he : n = 1
    · simp [he]
    · have hn' : BitVec.ofNat 32 (n-1) ≠ 0#32 := by
        intro hh
        have h' := congrArg BitVec.toNat hh
        simp only [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reducePow] at h'
        have hN : clearIterations < 4294967296 := by decide
        omega
      rw [beq_eq_false_iff_ne.mpr hn', beq_eq_false_iff_ne.mpr he]
  have hs : (M0Crypto.Armv6M.addWithCarry (s.regs 5) 4294967294#32 true).1 =
      BitVec.ofNat 32 (n-1) := (M0Crypto.Release.sub_flags _ 1#32).trans count
  have ha : (s.regs 0 + 16#32).toNat % 4 = 0 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    have := h.align
    omega
  obtain ⟨h1,h2,h3,h4⟩ := h.zeros
  have hN : bitCount (30#8) = 4 := by decide
  have hEffect :
      let t := execAll clearBlock s
      t.regs 0 = s.regs 0 + 16#32 ∧ t.regs 5 = BitVec.ofNat 32 (n-1) ∧
      t.z = (n == 1) ∧ t.mem = storeWords s.mem (s.regs 0) blockWords ∧ t.sp = s.sp := by
    unfold clearBlock
    row_simps
    change (M0Crypto.Armv6M.addWithCarry (s.regs (M0Crypto.Armv6M.LowReg.toReg 5)) 4294967294#32 true).1 =
      BitVec.ofNat 32 (n-1) at hs
    unfold M0Crypto.Armv6M.LowReg.toReg at hs
    rw [hs]
    simp only [hN, Nat.reduceMul, show BitVec.ofNat 32 16 = 16#32 from rfl, h15, List.map_cons,
      List.map_nil, blockWords, M0Crypto.Release.Field25519Mem.toReg1, M0Crypto.Release.Field25519Mem.toReg2,
      M0Crypto.Release.Field25519Mem.toReg3, M0Crypto.Release.Field25519Mem.toReg4,
      h1,h2,h3,h4, and_true, true_and]
    exact ⟨hq, by
      change storeWords s.mem (s.regs 0) [s.regs 1,s.regs 2,s.regs 3,s.regs 4] =
        storeWords s.mem (s.regs 0) [0,0,0,0]
      rw [h1,h2,h3,h4]⟩
  obtain ⟨h0,h5,hZ,hM,hSp⟩ := hEffect
  refine ⟨⟨h5, ?_, by rw [h0]; exact ha⟩,hZ,hM,hSp,h0⟩
  unfold clearBlock
  row_simps
  exact ⟨h1,h2,h3,h4⟩

def clearBranch : Instr := .bcond 1 (BitVec.ofInt 8 (-4))

theorem block_align (s : State) (n : Nat) (h : Ready s n) :
    alignedAll clearBlock s = true := by
  apply M0Crypto.Sym.alignChk_sound [(0,4)] clearBlock
    (M0Crypto.Sym.sound_all (by decide)) s
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact h.align
  · decide +kernel

theorem branch_step {code : List (BitVec 8)} {base : Word} {s : State} {o : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hP : s.pc = base + BitVec.ofNat 32 (o + seqSize clearBlock)) (he : o % 2 = 0)
    (hat : seqAt code (o + seqSize clearBlock) [clearBranch] = true) :
    let dest := if s.z then o + seqSize clearBlock + clearBranch.size else o
    runH code base 1 s = .ok (s.setReg 15 (base + BitVec.ofNat 32 dest), [⟨s.pc,clearBranch,[]⟩]) := by
  obtain ⟨⟨hi, hs⟩, _⟩ := (by simpa only [seqAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hat :
    (instrAt code (o + seqSize clearBlock) = some clearBranch ∧
      o + seqSize clearBlock + clearBranch.size ≤ code.length) ∧ True)
  have hz : seqSize clearBlock = 4 := rfl
  have hE : (o + seqSize clearBlock) % 2 = 0 := by rw [hz]; omega
  have hx : clearBranch.exec s = .ok (s.setReg 15 (base + BitVec.ofNat 32
      (if s.z then o + seqSize clearBlock + clearBranch.size else o))) := by
    have hDest : clearBranch.size = 2 := rfl
    rw [hz, hDest]
    have hBranch : clearBranch.exec s = .ok (s.setReg 15 (if s.z then s.pc + 2#32 else s.pc - 4#32)) := by
      cases hZ : s.z <;> simp only [clearBranch, Instr.exec, Instr.size, condPassed, hZ,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
      · have hd : ((BitVec.ofInt 8 (-4) ++ 0#1).signExtend 32) = -8#32 := by decide
        rw [hd]
        apply congrArg (fun pc => Except.ok (s.setReg 15 pc))
        bv_omega
      · rfl
    rw [hBranch]
    have hP' : s.pc = base + BitVec.ofNat 32 o + 4#32 := by
      rw [hP, hz, BitVec.ofNat_add, ← BitVec.add_assoc]
    rw [hP']
    cases s.z <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · apply congrArg (fun pc => Except.ok (s.setReg 15 pc))
      bv_omega
    · apply congrArg (fun pc => Except.ok (s.setReg 15 pc))
      rw [BitVec.ofNat_add, BitVec.ofNat_add]
      bv_omega
  have hStep := stepH_of_instr hb hlen hP hE hi hs (by rfl) hx
  exact runH_one_step 0 hStep

def clearMemory : M0Crypto.Armv6M.Mem → Word → Nat → M0Crypto.Armv6M.Mem
  | m, _, 0 => m
  | m, a, n+1 => clearMemory (storeWords m a blockWords) (a+16#32) n

def clearStepTrace (base : Word) (o : Nat) (a : Word) : List Event :=
  traceAll clearBlock (publicState [(15,base+BitVec.ofNat 32 o),(0,a)]) ++
    [⟨base + BitVec.ofNat 32 (o+seqSize clearBlock),clearBranch,[]⟩]

def clearTrace (base : Word) (o : Nat) (a : Word) : Nat → List Event
  | 0 => []
  | n+1 => clearStepTrace base o a ++ clearTrace base o (a+16#32) n

private theorem finish_iter {code : List (BitVec 8)} {base : Word} {o n : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32) (he : o % 2 = 0)
    (hat : seqAt code (o + seqSize clearBlock) [clearBranch] = true)
    (s u : State) (tr : List Event)
    (hRun : runH code base clearBlock.length s = .ok (u,tr))
    (hPcU : u.pc = base + BitVec.ofNat 32 (o+seqSize clearBlock))
    (hR : Ready u (n-1)) (hZ : u.z = (n == 1))
    (hMem : u.mem = storeWords s.mem (s.regs 0) blockWords) (hSp : u.sp = s.sp)
    (hAddr : u.regs 0 = s.regs 0+16#32) :
    ∃ t, runH code base (clearBlock.length+1) s = .ok (t,tr ++
      [⟨base + BitVec.ofNat 32 (o+seqSize clearBlock),clearBranch,[]⟩]) ∧
      t.pc = base + BitVec.ofNat 32 (if n=1 then o+seqSize (clearBlock ++ [clearBranch]) else o) ∧
      t.mem = storeWords s.mem (s.regs 0) blockWords ∧ t.sp = s.sp ∧
      Ready t (n-1) ∧ t.regs 0 = s.regs 0+16#32 := by
  let d := if n=1 then o+seqSize (clearBlock ++ [clearBranch]) else o
  have hh : (if u.z then o+seqSize clearBlock+clearBranch.size else o) = d := by
    rw [hZ]
    by_cases hn' : n=1
    · simp only [d, hn', beq_self_eq_true, ite_true]
      rw [seqSize_append]
      rfl
    · simp only [d, hn', beq_eq_false_iff_ne.mpr hn', Bool.false_eq_true, ite_false]
  have hBranch := branch_step hb hlen hPcU he hat
  dsimp only at hBranch
  rw [hh] at hBranch
  let dst := base + BitVec.ofNat 32 d
  let t := u.setReg 15 dst
  have pc : t.pc = dst := by simp [t, State.pc, State.setReg]
  have hReady : Ready t (n-1) := by
    obtain ⟨hC,hZeros,hA⟩ := hR
    refine ⟨?_,?_,?_⟩
    · simpa [t, State.setReg] using hC
    · simpa [t, State.setReg] using hZeros
    · simpa [t, State.setReg] using hA
  rw [hPcU] at hBranch
  exact ⟨t, runH_compose hRun hBranch,pc,hMem,hSp,hReady,hAddr⟩

theorem clear_iter {code : List (BitVec 8)} {base : Word} {o : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32) (he : o % 2 = 0)
    (hat : seqAt code o (clearBlock ++ [clearBranch]) = true)
    (n : Nat) (hp : n > 0) (hn : n ≤ clearIterations) (s : State)
    (hPc : s.pc = base + BitVec.ofNat 32 o) (h : Ready s n) :
    ∃ t, runH code base (clearBlock.length+1) s = .ok (t,clearStepTrace base o (s.regs 0)) ∧
      t.pc = base + BitVec.ofNat 32 (if n=1 then o+seqSize (clearBlock ++ [clearBranch]) else o) ∧
      t.mem = storeWords s.mem (s.regs 0) blockWords ∧ t.sp = s.sp ∧
      Ready t (n-1) ∧ t.regs 0 = s.regs 0+16#32 := by
  rw [seqAt_append, Bool.and_eq_true] at hat
  obtain ⟨hRun,hPcU⟩ := execute_pre hb hlen hPc he hat.1 (by decide) (block_align s n h)
  obtain ⟨hR,hZ,hMem,hSp,hAddr⟩ := block_effect s n hn hp h
  have ht : traceAll clearBlock s = traceAll clearBlock (publicState [(15,base+BitVec.ofNat 32 o),(0,s.regs 0)]) := by
    apply trace_chk_sound (regs := [15,0]) (by decide) (by decide +kernel)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with e | e <;> subst r
    · exact hPc
    · rfl
  rw [ht] at hRun
  exact finish_iter hb hlen he hat.2 s (execAll clearBlock s) _ hRun hPcU hR hZ hMem hSp hAddr

theorem run_clear {code : List (BitVec 8)} {base : Word} {o : Nat}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32) (he : o % 2 = 0)
    (hat : seqAt code o (clearBlock ++ [clearBranch]) = true)
    (n : Nat) (hp : n > 0) (hn : n ≤ clearIterations) (s : State)
    (hPc : s.pc = base + BitVec.ofNat 32 o) (h : Ready s n) :
    ∃ t, runH code base ((clearBlock.length+1)*n) s = .ok (t,clearTrace base o (s.regs 0) n) ∧
      t.pc = base + BitVec.ofNat 32 (o+seqSize (clearBlock ++ [clearBranch])) ∧
      t.mem = clearMemory s.mem (s.regs 0) n ∧ t.sp = s.sp := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    obtain ⟨u,hU,hPcU,hMem,hSp,hR,hAddr⟩ := clear_iter hb hlen he hat (n+1) hp hn s hPc h
    cases n with
    | zero =>
      simp only [Nat.zero_add, ite_true] at hPcU
      exact ⟨u,by simpa only [clearTrace,List.append_nil,Nat.zero_add,Nat.mul_one] using hU,hPcU,hMem,hSp⟩
    | succ n =>
      have hn' : n+1+1 ≠ 1 := by omega
      simp only [hn', ite_false] at hPcU
      have hReady : Ready u (n+1) := hR
      obtain ⟨v,hV,hVP,hVM,hVS⟩ := ih (by omega) (by omega) u hPcU hReady
      refine ⟨v,?_,hVP,?_,hVS.trans hSp⟩
      · rw [Nat.mul_succ, Nat.add_comm, clearTrace, ← hAddr]
        exact runH_compose hU hV
      · change v.mem = clearMemory (storeWords s.mem (s.regs 0) blockWords) (s.regs 0+16#32) (n+1)
        rw [← hMem, ← hAddr]
        exact hVM

theorem clear_as_store (m : M0Crypto.Armv6M.Mem) (a : Word) (n : Nat) :
    clearMemory m a n = storeWords m a (List.replicate (4*n) 0) := by
  induction n generalizing m a with
  | zero => rfl
  | succ n ih =>
    rw [clearMemory, ih]
    have h : (4 : Nat) * (n+1) = 4+4*n := by omega
    rw [h, ← List.replicate_append_replicate, M0Crypto.Release.Field25519Mul128.storeWords_append]
    rfl

end SafegcdTermination.ClearLoop
