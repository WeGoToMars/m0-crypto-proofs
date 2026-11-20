import M0Crypto.Release.Ed25519Leaf
import M0Crypto.Release.Ed25519CallProgStitchGood
import M0Crypto.Release.Ed25519SignProg

set_option linter.unusedSimpArgs false

/-! Exact comparison of two potentially unaligned 32-byte strings. The only branch
uses the public countdown, and the accumulator receives the OR of the byte XORs. -/

namespace M0Crypto.Release.Ed25519BytesDiff

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.StackEffect
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (bytes_diff32 bytes_diff32_loop)

abbrev Byte := BitVec 8

def accum (a b : Nat → Byte) : Nat → Word → Word
  | 0, d => d
  | n + 1, d => accum a b n (d ||| ((a n ^^^ b n).zeroExtend 32))

theorem accum_zero (a b : Nat → Byte) : ∀ n d, accum a b n d = 0 ↔ d = 0 ∧ ∀ i < n, a i = b i
  | 0, _ => by simp [accum]
  | n + 1, d => by
    have h : ∀ d : Word, ∀ x y : Byte, (d ||| ((x ^^^ y).zeroExtend 32)) = 0 ↔ d = 0 ∧ x = y := by
      intro d x y
      have extend_zero (z : Byte) : z.zeroExtend 32 = 0#32 ↔ z = 0#8 := by
        constructor
        · intro hz
          change z.setWidth 32 = 0#32 at hz
          have narrowed := congrArg (BitVec.setWidth 8) hz
          rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),BitVec.setWidth_eq,
            BitVec.setWidth_zero] at narrowed
          exact narrowed
        · rintro rfl
          rfl
      change (d ||| ((x ^^^ y).zeroExtend 32)) = 0#32 ↔ d = 0#32 ∧ x = y
      rw [BitVec.or_eq_zero_iff,extend_zero,BitVec.xor_eq_zero_iff]
    rw [accum, accum_zero, h]
    constructor
    · rintro ⟨⟨hd, hn⟩, hi⟩
      exact ⟨hd, fun i h => if he : i = n then he ▸ hn else hi i (by omega)⟩
    · rintro ⟨hd, hi⟩
      exact ⟨⟨hd, hi n (by omega)⟩, fun i h => hi i (by omega)⟩

def atByte (m : Mem) (a : Word) (i : Nat) : Byte := m (a + BitVec.ofNat 32 i)

def status (s : State) : Word := accum (atByte s.mem (s.regs 0)) (atByte s.mem (s.regs 1)) 32 0

def io : Iface :=
  { ins := [(0,0,.view (.bytes 32)),(1,0,.raw (.k 32))],
    outs := [], wr := [], rd := [⟨0,0,.k 32⟩,⟨1,0,.k 32⟩], al := [] }

def diffS : CalleeS := calleeAt bytes_diff32 io [0,1]

private def init : List Instr := [.movImm 2 32,.movImm 3 0]
private def body : List Instr :=
  [.subImm8 2 1,.memReg .ldrb 4 0 2,.memReg .ldrb 5 1 2,.dp .eors 4 5,.dp .orrs 3 4,.cmpImm 2 0]
private def branchOff := bytes_diff32_loop + seqSize body
private def branchImm := BitVec.ofInt 8 (((bytes_diff32_loop : Int) - (branchOff + 4)) / 2)
private def tailOff := branchOff + 2
private def tail : List Instr := [.movHi 0 3]
private def retOff := tailOff + seqSize tail
private def insns : List Instr := init ++ body ++ [.bcond 1 branchImm] ++ tail ++ [.bx 14]

private theorem code (b : Build) : seqAt b.bytes bytes_diff32 insns = true := by
  rw [seqAt_eq_scan]
  cases b <;> decide +kernel

private def stepRead (r : Reg) : M0Crypto.Sym.SExpr :=
  .add (.reg0 r) (.awc (.reg0 2) (.const (~~~1#32)) (.const true))

private def stepReads : List (M0Crypto.Sym.SExpr × Nat) := [(stepRead 0,1),(stepRead 1,1)]

private theorem body_checked :
    M0Crypto.Sym.rgnChk .read stepReads body = true ∧ traceOk body [0,1,2] = true := by decide +kernel

private theorem decWord (n : Nat) :
    (M0Crypto.Armv6M.addWithCarry (BitVec.ofNat 32 (n+1)) (~~~1#32) true).1 = BitVec.ofNat 32 n := by
  rw [sub_flags,BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

private theorem next_regs (s : State) (n : Nat) (hn : n < 32)
    (hn' : s.regs 2 = BitVec.ofNat 32 (n+1)) :
    (execAll body s).regs 2 = BitVec.ofNat 32 n ∧
    (execAll body s).regs 3 = (s.regs 3 |||
      ((atByte s.mem (s.regs 0) n ^^^ atByte s.mem (s.regs 1) n).zeroExtend 32)) ∧
    condPassed 1 (execAll body s) = decide (0 < n) := by
  have hn0 : (BitVec.ofNat 32 n == 0#32) = decide (n = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
    · intro h
      rw [h]
  have hdec : (M0Crypto.Armv6M.addWithCarry (BitVec.ofNat 32 (n+1)) 4294967294#32 true).1 =
      BitVec.ofNat 32 n := decWord n
  have hcmp (x : Word) : (M0Crypto.Armv6M.addWithCarry x 4294967295#32 true).1 = x := by
    simpa using sub_flags x 0
  have e0 : LowReg.toReg 0 = 0 := rfl
  have e1 : LowReg.toReg 1 = 1 := rfl
  have e2 : LowReg.toReg 2 = 2 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  have e4 : LowReg.toReg 4 = 4 := rfl
  have e5 : LowReg.toReg 5 = 5 := rfl
  simp (config := {decide := true}) [body,execAll,Instr.next,Instr.exec,Instr.exec.memOp,
    addFlags,State.setNZCV,State.setNZ,State.setReg,State.reg,condPassed,atByte,read8,
    e0,e1,e2,e3,e4,e5,hn',hdec,hcmp,hn0,BitVec.zeroExtend]
  cases n <;> simp_all

private def R : Routine where
  entry := bytes_diff32
  code := [(bytes_diff32,retOff+2)]
  stack := 0
  Pre := fun _ _ => True
  wr := fun _ => []
  rd := fun s => [⟨s.regs 0,32⟩,⟨s.regs 1,32⟩]
  clob := Ed25519Routines.hiRegs
  Post := fun s _ w => w = status s

private def initTrace (base : Word) : List Event :=
  blockTr init (base+BitVec.ofNat 32 bytes_diff32) [] []

private def passTrace (base a b : Word) (n : Nat) : List Event :=
  blockTr body (base+BitVec.ofNat 32 bytes_diff32_loop) [0,1,2] [a,b,BitVec.ofNat 32 n]

private def branchEvent (base : Word) : Event := ⟨base+BitVec.ofNat 32 branchOff,.bcond 1 branchImm,[]⟩
private def tailTrace (base : Word) : List Event := blockTr tail (base+BitVec.ofNat 32 tailOff) [] []
private def retEvent (base : Word) : Event := ⟨base+BitVec.ofNat 32 retOff,.bx 14,[]⟩

private def loopTrace (base a b : Word) : Nat → List Event
  | 0 => tailTrace base ++ [retEvent base]
  | n+1 => passTrace base a b (n+1) ++ branchEvent base :: loopTrace base a b n

private def trace (base : Word) (p : Nat → Word) : List Event :=
  initTrace base ++ loopTrace base (p 0) (p 1) 32

private def xp (s : State) : List Word := [status s]

private theorem code_parts (b : Build) :
    seqAt b.bytes bytes_diff32 init = true ∧
    seqAt b.bytes bytes_diff32_loop body = true ∧
    instrAt b.bytes branchOff = some (.bcond 1 branchImm) ∧
    seqAt b.bytes tailOff tail = true ∧
    instrAt b.bytes retOff = some (.bx 14) := by
  have h := code b
  simp only [insns,seqAt_append,seqSize_append,Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,instrAt_of_seqAt h.1.1.2,h.1.2,instrAt_of_seqAt h.2⟩

private theorem within {base : Word} {o n : Nat} (h1 : bytes_diff32 ≤ o) (h2 : o+n ≤ retOff+2) :
    InRegion (R.PcP base) base o n :=
  PcIn.region (List.mem_singleton_self _) h1 h2

private theorem reads_in (s : State) {i : Nat} (hi : i < 32) (hc : s.regs 2 = BitVec.ofNat 32 (i+1)) :
    ∀ y, Has (sregions s stepReads) y → Has (R.rd s) y := by
  intro y h
  obtain ⟨r,hm,hw⟩ := h
  unfold sregions at hm
  obtain ⟨expr,hExpr,hrEq⟩ := (List.mem_map
    (f := fun r : M0Crypto.Sym.SExpr × Nat => (⟨r.1.denote s,r.2⟩ : Rgn)) (l := stepReads)).mp hm
  rw [← hrEq] at hw
  change expr ∈ [(stepRead 0,1),(stepRead 1,1)] at hExpr
  have addr (r : Reg) : (stepRead r).denote s = s.regs r + BitVec.ofNat 32 i := by
    change s.regs r + (M0Crypto.Armv6M.addWithCarry (s.regs 2) (~~~1#32) true).1 = _
    rw [hc,decWord]
  rcases List.mem_cons.mp hExpr with h | h
  · rw [h] at hw
    obtain ⟨j,hj,hy⟩ := hw
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
    refine ⟨⟨s.regs 0,32⟩,List.mem_cons_self,i,hi,?_⟩
    rw [hj0] at hy
    change y = (stepRead 0).denote s + 0#32 at hy
    simpa only [BitVec.add_zero,addr] using hy
  · rw [List.mem_singleton.mp h] at hw
    obtain ⟨j,hj,hy⟩ := hw
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
    refine ⟨⟨s.regs 1,32⟩,List.mem_cons_of_mem _ (List.mem_singleton_self _),i,hi,?_⟩
    rw [hj0] at hy
    change y = (stepRead 1).denote s + 0#32 at hy
    simpa only [BitVec.add_zero,addr] using hy

private structure Kept (s t : State) : Prop where
  a : t.regs 0 = s.regs 0
  b : t.regs 1 = s.regs 1
  sp : t.regs 13 = s.regs 13
  lr : t.regs 14 = s.regs 14
  mem : t.mem = s.mem

private theorem Kept.stepBody {s u : State} (h : Kept s u) : Kept s (execAll body u) :=
  ⟨(execAll_regs_other _ _ _ (by decide) (by decide)).trans h.a,
   (execAll_regs_other _ _ _ (by decide) (by decide)).trans h.b,
   (execAll_regs_other _ _ _ (by decide) (by decide)).trans h.sp,
   (execAll_regs_other _ _ _ (by decide) (by decide)).trans h.lr,
   (funext fun y => execAll_memEq u (is := body) (wg := []) (by decide) (by decide) y
     (by simp [regions,Has])).trans h.mem⟩

private theorem Kept.pc {s u : State} (h : Kept s u) (pc : Word) : Kept s (u.setReg 15 pc) :=
  ⟨h.a,h.b,h.sp,h.lr,h.mem⟩

private theorem sp_ok {s u : State} (h : Kept s u) : R.SpP s (u.regs 13) :=
  ⟨0,by decide,by simp [h.sp]⟩

private theorem body_pc {base : Word} {u : State} (h : u.pc = base+BitVec.ofNat 32 bytes_diff32_loop) :
    (execAll body u).pc = base+BitVec.ofNat 32 branchOff := by
  rw [execAll_pc _ _ (by decide),h,ofNat_add_assoc]
  rfl

private theorem start_run {B : List Byte} {BS : Nat} [cb : CodeBytes B BS] {base : Word} {s : State} {tailEvents : List Event}
    (entry : @Routine.Entry B BS R cb base s)
    (hInit : seqAt B bytes_diff32 init = true)
    (next : @ReachFT B BS cb base (R.PcP base)
      (@Routine.RdP B BS cb R base s) (R.WrP s) (R.SpP s)
      (execAll init s) (R.Ret s) (Tr.is tailEvents)) :
    @ReachFT B BS cb base (R.PcP base)
      (@Routine.RdP B BS cb R base s) (R.WrP s)
      (R.SpP s) s (R.Ret s) (Tr.is (initTrace base ++ tailEvents)) := by
  have hEven : base.toNat % 2 = 0 := by have := entry.base4; omega
  rw [← Tr.cat_is_is (initTrace base) tailEvents]
  exact @ReachFT.block B BS cb base _ _ _ _ s (R.Ret s) (Tr.is tailEvents)
    (initTrace base) hEven init bytes_diff32 entry.pc
    (by decide) hInit (by decide) (by decide) (within (by decide) (by decide)) [] [] []
    (by decide) (by decide) (by decide) (by simp) (by simp [regions,Has]) (by simp [regions,Has])
    ⟨0,by decide,by simp⟩ (traceAll_blockTr (L := []) (by decide) (by decide) entry.pc rfl) next

private def acc (s : State) (n : Nat) (u : State) :=
  accum (atByte s.mem (s.regs 0)) (atByte s.mem (s.regs 1)) n (u.regs 3)

private theorem return_run {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s u : State}
    (entry : @Routine.Entry B BS R cb base s)
    (hTail : seqAt B tailOff tail = true)
    (hRet : instrAt B retOff = some (.bx 14))
    (hSize : retOff + 2 ≤ B.length)
    (hu : u.pc = base + BitVec.ofNat 32 tailOff)
    (hk : Kept s u) (hval : u.regs 3 = status s) :
    ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) u (R.Ret s)
      (Tr.is (tailTrace base ++ [retEvent base])) := by
  have hEven : base.toNat % 2 = 0 := by have := entry.base4; omega
  have hu' : u.pc = base+BitVec.ofNat 32 tailOff := hu
  refine ReachT.retrace ?_ (Tr.cat_is_is (tailTrace base) [retEvent base])
  refine ReachFT.block hEven tail tailOff hu' (by decide) hTail (by decide) (by decide)
    (within (by decide) (by decide)) [] [] [] (by decide) (by decide) (by decide)
    (by simp) (by simp [regions,Has]) (by simp [regions,Has]) (sp_ok hk)
    (traceAll_blockTr (L := []) (by decide) (by decide) hu' rfl) ?_
  let t := execAll tail u
  have hpc : t.pc = base+BitVec.ofNat 32 retOff := by
    rw [show t = execAll tail u from rfl,execAll_pc _ _ (by decide),hu',ofNat_add_assoc]
    rfl
  have hlr : t.regs 14 = s.regs 14 := hk.lr
  have hsp : t.regs 13 = s.regs 13 := hk.sp
  have he : (Instr.bx 14).exec t = .ok (t.setReg 15 (s.regs 14 &&& ~~~1#32)) := by
    simp [Instr.exec,hlr,entry.lr]
  refine ReachT.retrace ?_ (Tr.cat_is_is [retEvent base] [])
  refine ReachFT.step hEven (.bx 14) hpc (by decide) hRet hSize rfl he
    (within (o := retOff) (n := 2) (by decide) (by decide) 0 (by decide))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    ⟨0,by decide,by rw [hsp]; exact (BitVec.sub_zero _).symm⟩
    (by change (⟨t.pc,.bx 14,[]⟩ : Event) = retEvent base; rw [hpc]; rfl)
    (ReachT.done ⟨rfl,hsp,fun r hr hl hn => absurd (Ed25519Routines.mem_hiRegs hr hl) hn,hval⟩)

private theorem pass_run {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s u : State} {n : Nat} {nextTrace : TrP} {Q : State → Prop}
    (hEven : base.toNat % 2 = 0)
    (hBody : seqAt B bytes_diff32_loop body = true)
    (hu : u.pc = base + BitVec.ofNat 32 bytes_diff32_loop)
    (hk : Kept s u) (hn : n < 32) (hc : u.regs 2 = BitVec.ofNat 32 (n+1))
    (next : ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s)
      (execAll body u) Q nextTrace) :
    ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) u Q
      (Tr.cat (Tr.is (passTrace base (s.regs 0) (s.regs 1) (n+1))) nextTrace) := by
  refine Ed25519Leaf.ReachFT.blockE hEven body bytes_diff32_loop hu (by decide) hBody
    (by decide) (by decide) (within (by decide) (by decide)) stepReads [] stepReads
    (by decide) (by decide) body_checked.1 (by simp [stepReads,Nat.mod_one]) (by simp [sregions,Has])
    (fun y hy => by
      have h := reads_in u hn hc y hy
      simp only [R,hk.a,hk.b] at h
      obtain ⟨r,hr,hy⟩ := h
      exact ⟨r,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr),hy⟩)
    (sp_ok hk) (traceAll_blockTr (L := [0,1,2]) (by decide) body_checked.2 hu
      (by simp [hk.a,hk.b,hc])) next

private theorem loop_branch {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s t : State} {n : Nat} {Q : State → Prop} {expected : Word}
    (hEven : base.toNat % 2 = 0)
    (hBranch : instrAt B branchOff = some (.bcond 1 branchImm))
    (hBranchSize : branchOff + 2 ≤ BS)
    (hn : n+1 ≤ 32) (hpc : t.pc = base + BitVec.ofNat 32 branchOff)
    (kt : Kept s t) (hc : t.regs 2 = BitVec.ofNat 32 n)
    (hcond : condPassed 1 t = decide (0 < n))
    (haf : ∀ pc, acc s n (t.setReg 15 pc) = expected)
    (ih : ∀ v : State, n ≤ 32 →
      v.pc = base + BitVec.ofNat 32 (if n = 0 then tailOff else bytes_diff32_loop) →
      Kept s v → v.regs 2 = BitVec.ofNat 32 n → acc s n v = expected →
      ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) v Q
        (Tr.is (loopTrace base (s.regs 0) (s.regs 1) n))) :
    ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) t Q
      (Tr.is (branchEvent base :: loopTrace base (s.regs 0) (s.regs 1) n)) := by
  let nextSite := if n = 0 then tailOff else bytes_diff32_loop
  let next := t.setReg 15 (base + BitVec.ofNat 32 nextSite)
  have target : BitVec.ofNat 32 branchOff + 4#32 + (branchImm ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 bytes_diff32_loop := by decide
  have step : (Instr.bcond 1 branchImm).exec t = .ok next := by
    simp only [Instr.exec,hcond]
    by_cases hn0 : n = 0
    · subst n
      change Except.ok (t.setReg 15 (t.pc + 2#32)) = .ok next
      rw [hpc,ofNat_add_assoc]
      rfl
    · have hp : 0 < n := Nat.pos_of_ne_zero hn0
      have pcTaken : t.pc + 4#32 + (branchImm ++ 0#1).signExtend 32 =
          base + BitVec.ofNat 32 bytes_diff32_loop := by
        simp only [BitVec.add_assoc] at target
        simp only [hpc, BitVec.add_assoc, target]
      have hnSite : nextSite = bytes_diff32_loop := by simp [nextSite, hn0]
      simp only [decide_eq_true hp, ite_true, pcTaken, next, hnSite]
  have cont := ih next (Nat.le_trans (Nat.le_succ _) hn) rfl (kt.pc _) hc (haf _)
  have hlen : branchOff + (Instr.bcond 1 branchImm).size ≤ B.length := by
    rw [CodeBytes.len (B := B)]
    exact hBranchSize
  refine ReachT.retrace ?_ (Tr.cat_is_is [branchEvent base] (loopTrace base (s.regs 0) (s.regs 1) n))
  exact ReachFT.step hEven (.bcond 1 branchImm) hpc (by decide) hBranch hlen rfl step
    (within (o := branchOff) (n := 2) (by decide) (by decide) 0 (by decide))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    (sp_ok kt)
    (by change (⟨t.pc,.bcond 1 branchImm,[]⟩ : Event) = branchEvent base; rw [hpc]; rfl)
    cont

private theorem acc_step {s u t : State} {n : Nat} (hk : Kept s u)
    (hacc : t.regs 3 = (u.regs 3 |||
      ((atByte u.mem (u.regs 0) n ^^^ atByte u.mem (u.regs 1) n).zeroExtend 32))) :
    ∀ pc, acc s n (t.setReg 15 pc) = acc s (n+1) u := by
  intro pc
  change accum (atByte s.mem (s.regs 0)) (atByte s.mem (s.regs 1)) n (t.regs 3) = _
  rw [hacc, hk.a, hk.b, hk.mem]
  rfl

private theorem loop_continue {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s u : State} {n : Nat} {Q : State → Prop} {expected : Word}
    (hEven : base.toNat % 2 = 0)
    (hBody : seqAt B bytes_diff32_loop body = true)
    (hBranch : instrAt B branchOff = some (.bcond 1 branchImm))
    (hBranchSize : branchOff + 2 ≤ BS)
    (hn : n+1 ≤ 32) (hu : u.pc = base + BitVec.ofNat 32 bytes_diff32_loop)
    (hk : Kept s u) (hc : u.regs 2 = BitVec.ofNat 32 (n+1)) (ha : acc s (n+1) u = expected)
    (ih : ∀ v : State, n ≤ 32 →
      v.pc = base + BitVec.ofNat 32 (if n = 0 then tailOff else bytes_diff32_loop) →
      Kept s v → v.regs 2 = BitVec.ofNat 32 n → acc s n v = expected →
      ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) v Q
        (Tr.is (loopTrace base (s.regs 0) (s.regs 1) n))) :
    ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) u Q
      (Tr.is (loopTrace base (s.regs 0) (s.regs 1) (n+1))) := by
  have hlt : n < 32 := by omega
  have regs := next_regs u n hlt hc
  have cont := @loop_branch B BS cb base s (execAll body u) n Q expected
    hEven hBranch hBranchSize hn (body_pc hu) hk.stepBody regs.1 regs.2.2
    (fun pc => (acc_step hk regs.2.1 pc).trans ha) ih
  have pass := pass_run hEven hBody hu hk hlt hc cont
  rw [Tr.cat_is_is] at pass
  exact pass

private theorem loop_run {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s : State}
    (entry : @Routine.Entry B BS R cb base s)
    (hBody : seqAt B bytes_diff32_loop body = true)
    (hBranch : instrAt B branchOff = some (.bcond 1 branchImm))
    (hTail : seqAt B tailOff tail = true)
    (hRet : instrAt B retOff = some (.bx 14))
    (hSize : retOff + 2 ≤ B.length)
    (hBranchSize : branchOff + 2 ≤ BS) :
    ∀ n (u : State), n ≤ 32 →
      u.pc = base + BitVec.ofNat 32 (if n = 0 then tailOff else bytes_diff32_loop) →
      Kept s u → u.regs 2 = BitVec.ofNat 32 n → acc s n u = status s →
      ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) u (R.Ret s)
        (Tr.is (loopTrace base (s.regs 0) (s.regs 1) n)) := by
  have hEven : base.toNat % 2 = 0 := by have := entry.base4; omega
  intro n
  induction n with
  | zero =>
    intro u _ hu hk _ hval
    exact return_run entry hTail hRet hSize hu hk hval
  | succ n ih =>
    intro u hn hu hk hc ha
    exact loop_continue hEven hBody hBranch hBranchSize hn hu hk hc ha ih

private theorem run_core {B : List Byte} {BS : Nat} [cb : CodeBytes B BS]
    (hInit : seqAt B bytes_diff32 init = true)
    (hBody : seqAt B bytes_diff32_loop body = true)
    (hBranch : instrAt B branchOff = some (.bcond 1 branchImm))
    (hTail : seqAt B tailOff tail = true)
    (hRet : instrAt B retOff = some (.bx 14))
    (hSize : retOff + 2 ≤ B.length) :
    R.SpecT fun base s => Tr.is (trace base (diffS.pubX xp s)) := by
  intro base s entry
  have hBranchSize : branchOff+2 ≤ BS := by
    rw [← CodeBytes.len (B := B)]
    exact Nat.le_trans (by decide) hSize
  have p0 : diffS.pubX xp s 0 = s.regs 0 := rfl
  have p1 : diffS.pubX xp s 1 = s.regs 1 := rfl
  change ReachFT base (R.PcP base) (R.RdP base s) (R.WrP s) (R.SpP s) s (R.Ret s)
    (Tr.is (initTrace base ++ loopTrace base (diffS.pubX xp s 0) (diffS.pubX xp s 1) 32))
  rw [p0,p1]
  have initPc : (execAll init s).pc = base+BitVec.ofNat 32 bytes_diff32_loop := by
    rw [execAll_pc _ _ (by decide),entry.pc,ofNat_add_assoc]
    rfl
  have initAcc : (execAll init s).regs 3 = 0 := rfl
  have initVal (n : Nat) : acc s n (execAll init s) =
      accum (atByte s.mem (s.regs 0)) (atByte s.mem (s.regs 1)) n 0 := by
    unfold acc
    rw [initAcc]
  have initKept : Kept s (execAll init s) := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have initCount : (execAll init s).regs 2 = BitVec.ofNat 32 32 := rfl
  have initResult : acc s 32 (execAll init s) = status s := initVal 32
  generalize hTrace : loopTrace base (s.regs 0) (s.regs 1) 32 = tailEvents
  refine @start_run B BS cb base s tailEvents entry hInit ?_
  rw [← hTrace]
  exact loop_run entry hBody hBranch hTail hRet hSize hBranchSize
    32 (execAll init s) (Nat.le_refl _) initPc initKept initCount initResult

private theorem run (b : Build) : letI := b.codeBytes
    R.SpecT fun base s => Tr.is (trace base (diffS.pubX xp s)) := by
  letI := b.codeBytes
  obtain ⟨hInit,hBody,hBranch,hTail,hRet⟩ := code_parts b
  refine @run_core b.bytes b.size b.codeBytes hInit hBody hBranch hTail hRet ?_
  rw [CodeBytes.len (B := b.bytes)]
  cases b <;> decide +kernel

private theorem seg_cat {sp0 sp : Word} {n : Nat} {F : Word → Prop} {a b : List Event}
    (ha : Seg sp0 n sp F a (fun _ => False)) (hb : Seg sp0 n sp F b (fun _ => False)) :
    Seg sp0 n sp F (a ++ b) (fun _ => False) :=
  (ha.cat hb).mono (fun _ h => h) (fun _ h => h.elim)

private theorem seg_block {sp0 sp : Word} {n : Nat} {F : Word → Prop} {g : List Instr} (pc : Word)
    (hg : blkChk [] [] [] g = true) :
    Seg sp0 n sp F (blockTr g pc [] []) (fun _ => False) :=
  (blk_seg (X := F) hg (regState pc [] []) (by simp [InR]) (by simp [InR])).mono
    (fun _ h => h) (fun _ h => h.elim)

private theorem seg_event {sp0 sp : Word} {n : Nat} {F : Word → Prop} {ev : Event}
    (ha : ev.accesses = []) (hx : spExact ev.instr = true) (hs : spAfter ev.instr sp = sp) :
    Seg sp0 n sp F [ev] (fun _ => False) :=
  (ev_seg (X := F) hx hs
    (fun y hy _ => by rw [ha] at hy; exact (hy.elim (reads_nil y) (writes_nil y)).elim)
    (fun y hy _ => by rw [ha] at hy; exact (reads_nil y hy).elim)).mono
    (fun _ h => h) (fun _ h => h.elim)

private theorem loop_seg {sp0 sp : Word} {n : Nat} (base a b : Word)
    (hF : ∀ y, Has [⟨a,32⟩,⟨b,32⟩] y → TraceSpec.BelowEntry sp0 n y → TraceSpec.AtOrAboveSp sp0 sp y) :
    ∀ k ≤ 32, Seg sp0 n sp (Has [⟨a,32⟩,⟨b,32⟩]) (loopTrace base a b k) (fun _ => False)
  | 0, _ => seg_cat (seg_block _ (by decide)) (seg_event rfl rfl rfl)
  | k+1, hk => by
    let u := regState (base+BitVec.ofNat 32 bytes_diff32_loop) [0,1,2] [a,b,BitVec.ofNat 32 (k+1)]
    have hReads : ∀ y, InR u stepReads y → Has [⟨a,32⟩,⟨b,32⟩] y := by
      intro y hy
      obtain ⟨r,hr,i,hi,hy⟩ := hy
      exact reads_in u (by omega) rfl y ⟨⟨r.1.denote u,r.2⟩,List.mem_map.mpr ⟨r,hr,rfl⟩,i,hi,hy⟩
    have hb : Seg sp0 n sp (Has [⟨a,32⟩,⟨b,32⟩]) (passTrace base a b (k+1)) (fun _ => False) :=
      (blk_seg (is := body) (ini := stepReads) (fp := stepReads) (wo := []) (by decide) u hReads
        (fun y hy => hF y (hReads y hy))).mono (fun _ h => h) (fun _ h => h.elim)
    exact seg_cat hb (seg_cat (seg_event rfl rfl rfl) (loop_seg base a b hF k (by omega)))

private theorem effect (b : Build) (base : Word) (p : Nat → Word) :
    @CalleeS.Eff diffS p b.bytes b.size b.codeBytes base (trace base p) := by
  letI := b.codeBytes
  intro sp0 n q hsp _ _ hU hF hRq
  change q.sp = p 2 at hsp
  have reg0 : diffS.reg p 0 = p 0 := rfl
  have reg1 : diffS.reg p 1 = p 1 := rfl
  let F := Has [⟨p 0,32⟩,⟨p 1,32⟩]
  have hFp : ∀ y, F y → diffS.Fp p base y := by
    intro y hy
    obtain ⟨r,hr,hy⟩ := hy
    refine ⟨r,List.mem_cons_of_mem _ ?_,hy⟩
    have hrd : rgnsC (diffS.reg p) diffS.io.rd = [⟨p 0,32⟩,⟨p 1,32⟩] := by
      change ([⟨diffS.reg p 0 + 0#32,32⟩,⟨diffS.reg p 1 + 0#32,32⟩] : List Rgn) = _
      simp only [reg0,reg1,BitVec.add_zero]
    have hwr : rgnsC (diffS.reg p) diffS.io.wr = [] := rfl
    rw [hrd,hwr]
    exact hr
  have inRegion (a : Word) (y : Word) (hy : (⟨a,32⟩ : Rgn).Has y) : Region a 32 y := by
    obtain ⟨j,hj,rfl⟩ := hy
    change j < 32 at hj
    change (a + BitVec.ofNat 32 j - a).toNat < 32
    rw [BitVec.add_comm,BitVec.add_sub_cancel,BitVec.toNat_ofNat]
    omega
  have hReq : ∀ y, F y → diffS.Rq p base y := by
    rintro y ⟨r,hr,hy⟩
    change r ∈ [⟨p 0,32⟩,⟨p 1,32⟩] at hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      refine .inr ⟨(0,0,.view (.bytes 32)),List.mem_cons_self,?_⟩
      change Region (diffS.reg p 0 + 0#32) 32 y
      simpa only [reg0,BitVec.add_zero] using inRegion (p 0) y hy
    · have hr' := List.mem_singleton.mp hr
      subst r
      refine .inr ⟨(1,0,.raw (.k 32)),List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
      change Region (diffS.reg p 1 + 0#32) 32 y
      simpa only [reg1,BitVec.add_zero] using inRegion (p 1) y hy
  have step : Seg sp0 n (p 2) F (trace base p) (fun _ => False) :=
    seg_cat (seg_block _ (by decide))
      (loop_seg base (p 0) (p 1) (fun y hy hb => hsp ▸ hF y (hFp y hy) hb) 32 (by decide))
  obtain ⟨hg,hs,hu,-⟩ := step q hsp (fun y hy => hsp ▸ hU y hy) (fun y hy => hRq y (hReq y hy))
  exact ⟨hg,hs.trans hsp.symm,hu,by simp [CalleeS.Wd,diffS,calleeAt,io]⟩

private def statusBytes (a b : List Byte) : Word :=
  accum (fun i => a[i]?.getD 0) (fun i => b[i]?.getD 0) 32 0

private def xpv : List V → List Word
  | [.b a,.b b] => [statusBytes a b]
  | _ => []

def ok : List V → Bool
  | [.b a,.b b] => decide (a = b)
  | _ => false

private theorem in_bytes (Rs : Rels) {c : Ctx} {sp : Word} {s : State} {vs : List V}
    (h : InsRel Rs c sp io s vs) :
    vs = [.b (bytesAt s.mem (s.regs 0) 32),.b (bytesAt s.mem (s.regs 1) 32)] := by
  rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩⟩ <;>
    simp only [InsRel,All2,io,Rel,In.kd,BitVec.add_zero,and_false,false_and,and_true] at h
  simp only [ALen.val] at h
  rw [h.1,h.2]

private theorem bytes_elem (m : Mem) (a : Word) {i : Nat} (hi : i < 32) :
    (bytesAt m a 32)[i]?.getD 0 = atByte m a i := by simp [bytesAt,atByte,List.getElem?_range,hi]

private theorem status_bytes (s : State) :
    status s = statusBytes (bytesAt s.mem (s.regs 0) 32) (bytesAt s.mem (s.regs 1) 32) := by
  have h : ∀ n ≤ 32, ∀ d, accum (atByte s.mem (s.regs 0)) (atByte s.mem (s.regs 1)) n d =
      accum (fun i => (bytesAt s.mem (s.regs 0) 32)[i]?.getD 0)
        (fun i => (bytesAt s.mem (s.regs 1) 32)[i]?.getD 0) n d := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro hn d
      simp only [accum,bytes_elem _ _ (by omega : n < 32)]
      exact ih (by omega) _
  exact h 32 (by decide) 0

private theorem status_zero (Rs : Rels) {c : Ctx} {sp : Word} {s : State} {vs : List V}
    (h : InsRel Rs c sp io s vs) : status s = 0 ↔ ok vs = true := by
  rw [in_bytes Rs h]
  simp only [status,accum_zero,true_and,ok,decide_eq_true_eq]
  constructor
  · intro hEq
    apply List.ext_getElem (by simp [bytesAt])
    intro i hi _
    have hi' : i < 32 := by simpa [bytesAt] using hi
    simpa [bytesAt,atByte] using hEq i hi'
  · intro hEq i hi
    have hElem := congrArg (fun l : List Byte => l[i]?.getD 0) hEq
    simpa only [bytes_elem _ _ hi] using hElem

private def te (b : Build) : letI := b.codeBytes
    R.TE (fun _ s => diffS.pubX xp s) (fun base p => diffS.Eff p base) :=
  letI := b.codeBytes
  ⟨trace,run b,effect b⟩

noncomputable def diffAd (b : Build) (Rs : Rels) : AdX Rs (cb := b.codeBytes) diffS :=
  letI := b.codeBytes
  AdX.ofTE { R with code := diffS.code } rfl rfl (by decide)
    xp xpv (fun _ _ s _ hi => by rw [in_bytes Rs hi]; simp only [xp,xpv,status_bytes])
    ((te b).code _ (by decide)) (fun _ => True) (fun _ _ _ _ h => h) (fun _ => True) (fun _ => [])
    (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ => rfl)
    (fun st => by simp [R,diffS,calleeAt,io,rgnsC,SRgn.rgnC,ALen.val])
    (fun _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel,All2,diffS,calleeAt,io])
    (fun _ _ _ _ _ _ _ _ => trivial)

noncomputable def diffZ (b : Build) (Rs : Rels) : ZSt Rs (cb := b.codeBytes) (diffAd b Rs) :=
  letI := b.codeBytes
  { ok := ok
    okr := fun _ _ st _ _ vs _ hin _ h => by
      change _ = status st at h
      rw [h]
      exact status_zero Rs hin
    co := []
    csem := fun _ => []
    cpost := fun _ _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel,All2]
    okp := fun p => p 3 == 0
    okp_of := fun _ _ s _ _ _ hi _ => by
      change (status s == 0) = _
      exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq,status_zero Rs hi])
    cef := fun base p hp _ => CalleeS.eff_withCo_nil ((diffAd b Rs).ef base p hp) }

end M0Crypto.Release.Ed25519BytesDiff
