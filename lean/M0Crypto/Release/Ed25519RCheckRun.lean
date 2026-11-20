import M0Crypto.Release.Ed25519RCheckCode
import M0Crypto.Release.Ed25519Leaf
import M0Crypto.Release.Ed25519CallProgStitchGood
import M0Crypto.Release.RoutineBranch

/-! Execution of the early encoding check. Its input bytes and branch
    decisions are public to signature verification. -/

namespace M0Crypto.Release.Ed25519RCheck

open M0Crypto.Armv6M (LowReg State Word)
open M0Crypto.Thumb
open M0Crypto.Release.Footprint
open M0Crypto.Release.Routine
open M0Crypto.Release.Ed25519VerifyEncode (earlyScan)
open M0Crypto.Artifacts.Ed25519Compact
  (r_encoding_check r_check_pass r_check_scan r_check_high r_check_high_middle r_check_middle)

def status (s : State) : Word :=
  if rejected (readByte s.mem (s.regs 0)) then 1 else 0

def routine : Routine where
  entry := r_encoding_check
  code := [(r_encoding_check,r_encoding_check + seqSize instructions)]
  stack := 0
  Pre := fun _ _ => True
  wr := fun _ => []
  rd := fun s => [⟨s.regs 0,32⟩]
  clob := Ed25519Routines.hiRegs
  Post := fun s _ w => w = status s

private theorem within {base : Word} {o n : Nat}
    (h1 : r_encoding_check ≤ o) (h2 : o + n ≤ r_encoding_check + seqSize instructions) :
    InRegion (routine.PcP base) base o n :=
  PcIn.region (List.mem_singleton_self _) h1 h2

def exitValue (reject : Bool) : Instr := .movImm 0 (if reject then 1 else 0)
def exitSite (reject : Bool) : Nat := if reject then r_check_pass - 4 else r_check_pass

def exitTrace (base : Word) (reject : Bool) : List Event :=
  [⟨base + BitVec.ofNat 32 (exitSite reject),exitValue reject,[]⟩,
    ⟨base + BitVec.ofNat 32 (exitSite reject + 2),.bx 14,[]⟩]

private theorem exit_capture {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS]
    {base : Word} {s t : State} (entry : routine.Entry base s) (reject : Bool)
    (hlen : exitSite reject + 4 ≤ B.length) (hpc : t.pc = base + BitVec.ofNat 32 (exitSite reject))
    (hImm : instrAt B (exitSite reject) = some (exitValue reject))
    (hRet : instrAt B (exitSite reject + 2) = some (.bx 14))
    (hsp : t.regs 13 = s.regs 13) (hlr : t.regs 14 = s.regs 14)
    (hStatus : status s = if reject then 1 else 0) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t
      (routine.Ret s) (Tr.is (exitTrace base reject)) := by
  let w := (exitValue reject).next t
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  have siteEven : exitSite reject % 2 = 0 := by cases reject <;> decide
  have retEven : (exitSite reject + 2) % 2 = 0 := by omega
  have siteSize : (exitValue reject).size = 2 := by cases reject <;> rfl
  have immExec : (exitValue reject).exec t = .ok w := by cases reject <;> rfl
  have wPC : w.pc = base + BitVec.ofNat 32 (exitSite reject + 2) := by
    have hp : w.pc = t.pc + 2#32 := by cases reject <;> rfl
    rw [hp,hpc,ofNat_add_assoc]
  have wSP : w.regs 13 = s.regs 13 := (show w.regs 13 = t.regs 13 from by cases reject <;> rfl).trans hsp
  have wLR : w.regs 14 = s.regs 14 := (show w.regs 14 = t.regs 14 from by cases reject <;> rfl).trans hlr
  have wVal : w.regs 0 = status s := by cases reject <;> exact hStatus.symm
  let u := w.setReg 15 (s.regs 14 &&& ~~~1#32)
  have bxExec : (Instr.bx 14).exec w = .ok u := by
    simp only [Instr.exec,wLR,entry.lr,ite_true,u]
  have out : routine.Ret s u :=
    ⟨rfl,wSP,fun _ lo hi h => absurd (Ed25519Routines.mem_hiRegs lo hi) h,wVal⟩
  have pcOk (i : Nat) (hi : i < 4) : routine.PcP base (base + BitVec.ofNat 32 (exitSite reject + i)) :=
    within (o := exitSite reject) (n := 4) (by cases reject <;> decide)
      (by cases reject <;> decide) i hi
  have quiet : (exitValue reject).accesses t = [] := by cases reject <;> rfl
  have spOk (v : State) (h : v.regs 13 = s.regs 13) : routine.SpP s (v.regs 13) :=
    ⟨0,by decide,by simp [h]⟩
  refine ReachT.retrace ?_ (Tr.cat_is_is
    [⟨base + BitVec.ofNat 32 (exitSite reject),exitValue reject,[]⟩]
    [⟨base + BitVec.ofNat 32 (exitSite reject + 2),.bx 14,[]⟩])
  refine ReachFT.step even (exitValue reject) hpc siteEven hImm
    (siteSize ▸ Nat.le_trans (Nat.le_add_right (exitSite reject + 2) 2) hlen)
    (by rw [quiet]; rfl) immExec (by simpa only [Nat.add_zero] using pcOk 0 (by decide))
    (fun y hy => by rw [quiet] at hy; exact absurd hy (writes_nil y))
    (fun y hy => by rw [quiet] at hy; exact absurd hy (reads_nil y))
    (spOk t hsp) (by rw [hpc,quiet]) ?_
  refine ReachT.retrace ?_ (Tr.cat_is_is [⟨base + BitVec.ofNat 32 (exitSite reject + 2),.bx 14,[]⟩] [])
  exact ReachFT.step even (.bx 14) wPC retEven hRet
    (by change exitSite reject + 2 + 2 ≤ B.length; omega)
    rfl bxExec (pcOk 2 (by decide))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    (spOk w wSP) (by change (⟨w.pc,.bx 14,[]⟩ : Event) = _; rw [wPC])
    (ReachT.done out)

private def scanAddress : M0Crypto.Sym.SExpr := .add (.reg0 0) (.reg0 1)
private def scanReads : List (M0Crypto.Sym.SExpr × Nat) := [(scanAddress,1)]

def scanTestTrace (base a : Word) (i : Nat) : List Event :=
  blockTr scanTest (base + BitVec.ofNat 32 r_check_scan) [0,1] [a,BitVec.ofNat 32 i]

/-- One byte-tested iteration prefix, before the mismatch or countdown branches. -/
private theorem scan_test_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} {i : Nat} {Q : State → Prop} {Ψ : TrP}
    (even : base.toNat % 2 = 0) (hCode : seqAt B r_check_scan scanTest = true)
    (hPC : t.pc = base + BitVec.ofNat 32 r_check_scan)
    (hA : t.regs 0 = s.regs 0) (hI : t.regs 1 = BitVec.ofNat 32 i) (hi : i < 32)
    (hSP : t.regs 13 = s.regs 13)
    (next : ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      (execAll scanTest t) Q Ψ) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      t Q (Tr.cat (Tr.is (scanTestTrace base (s.regs 0) i)) Ψ) := by
  refine Ed25519Leaf.ReachFT.blockE even scanTest r_check_scan hPC (by decide) hCode
    (by decide) (by decide) (within (by decide) (by decide)) scanReads [] scanReads
    (by decide) (by decide) (by decide) (by simp [scanReads,Nat.mod_one]) (by simp [sregions,Has])
    ?_ ⟨0,by decide,by simp [hSP]⟩
    (traceAll_blockTr (L := [0,1]) (by decide) (by decide) hPC (by simp [hA,hI])) next
  intro y hy
  have hReg : sregions t scanReads = [⟨s.regs 0 + BitVec.ofNat 32 i,1⟩] := by
    change ([⟨t.regs 0 + t.regs 1,1⟩] : List Rgn) = _
    rw [hA,hI]
  rw [hReg] at hy
  rcases hy with ⟨r,hr,j,hj,hy⟩
  have he := List.mem_singleton.mp hr
  subst r
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  subst j
  refine ⟨⟨s.regs 0,32⟩, by simp [routine], i, hi, ?_⟩
  change y = s.regs 0 + BitVec.ofNat 32 i + 0#32 at hy
  simpa only [BitVec.add_zero] using hy

private theorem decrement_value (t : State) {n : Nat}
    (hn : n < 30) (hI : t.regs 1 = BitVec.ofNat 32 (n+1)) :
    let u := (Instr.subImm8 1 1).next t
    u.regs 1 = BitVec.ofNat 32 n ∧ condPassed 1 u = decide (0 < n) := by
  have r1 : LowReg.toReg 1 = 1 := rfl
  have hSub : (M0Crypto.Armv6M.addWithCarry (t.regs 1) 4294967294#32 true).1 = BitVec.ofNat 32 n := by
    change (M0Crypto.Armv6M.addWithCarry (t.regs 1) (~~~1#32) true).1 = _
    rw [sub_flags,hI,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hZero : (BitVec.ofNat 32 n == 0#32) = decide (n = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at ht
      omega
    · rintro rfl
      rfl
  simp (config := {decide := true}) [Instr.next,Instr.exec,addFlags,State.setNZCV,
    State.setNZ,State.setReg,State.reg,r1,condPassed,hSub,hZero]
  cases n <;> simp

private def event (base : Word) (site : Nat) (op : Instr) : Event :=
  ⟨base + BitVec.ofNat 32 site, op, []⟩

private def mismatchSite := r_check_scan + seqSize scanTest
private def decrementSite := mismatchSite + 2
private def backSite := decrementSite + 2

def scanTrace (base a : Word) (read : Nat → BitVec 8) (mask : BitVec 8) : Nat → List Event
  | 0 => exitTrace base true
  | n+1 => scanTestTrace base a (n+1) ++
    event base mismatchSite (branch 1 mismatchSite r_check_pass) ::
      if read (n+1) == mask then
        event base decrementSite (.subImm8 1 1) ::
          event base backSite (branch 1 backSite r_check_scan) :: scanTrace base a read mask n
      else exitTrace base false

private structure Kept (s t : State) : Prop where
  addr : t.regs 0 = s.regs 0
  sp : t.regs 13 = s.regs 13
  lr : t.regs 14 = s.regs 14
  mem : t.mem = s.mem

private theorem Kept.pc {s t : State} (h : Kept s t) (x : Word) : Kept s (t.setReg 15 x) :=
  ⟨h.addr,h.sp,h.lr,h.mem⟩

private theorem Kept.block {s t : State} (h : Kept s t) {g : List Instr}
    (ha : g.all (fun i => !(i.dsts.contains 0)) = true)
    (hs : g.all (fun i => !(i.dsts.contains 13)) = true)
    (hl : g.all (fun i => !(i.dsts.contains 14)) = true)
    (hw : M0Crypto.Sym.writeChk [] g = true) (hf : g.all Instr.falls = true) :
    Kept s (execAll g t) :=
  ⟨(execAll_regs_other _ _ _ (by decide) ha).trans h.addr,
   (execAll_regs_other _ _ _ (by decide) hs).trans h.sp,
   (execAll_regs_other _ _ _ (by decide) hl).trans h.lr,
   (funext fun y => execAll_memEq t hf hw y (by simp [regions,Has])).trans h.mem⟩

private theorem quiet_branch {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} {site target : Nat} {c : BitVec 4} {take : Bool}
    {Q : State → Prop} {es : List Event}
    (even : base.toNat % 2 = 0) (hs : site % 2 = 0) (hBound : site + 2 ≤ BS)
    (hpc : t.pc = base + BitVec.ofNat 32 site)
    (hx : instrAt B site = some (branch c site target))
    (wherePC : routine.PcP base (base + BitVec.ofNat 32 site))
    (sp : t.regs 13 = s.regs 13) (taken : condPassed c t = take)
    (delta : BitVec.ofNat 32 site + 4#32 +
      ((BitVec.ofInt 8 (((target : Int) - (site + 4)) / 2)) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 target)
    (next : ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      (t.setReg 15 (base + BitVec.ofNat 32 (if take then target else site + 2))) Q (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      t Q (Tr.is (event base site (branch c site target) :: es)) := by
  rw [show event base site (branch c site target) :: es = [event base site (branch c site target)] ++ es from rfl,
    ← Tr.cat_is_is]
  have hsp : routine.SpP s (t.regs 13) := ⟨0,by decide,by simp [sp]⟩
  have condSame (b : Bool) : Tr.cond b (Tr.is es) (Tr.is es) = Tr.is es := by
    funext tr
    cases b <;> simp [Tr.cond]
  cases take
  · rw [← condSame false]
    change _ = false at taken
    exact ReachFT.bcond (b := false) (ΨT := Tr.is es) even target c _ hpc hs hx hBound delta wherePC hsp taken
      (fun h => by rw [taken] at h; contradiction) (fun _ => next)
  · rw [← condSame true]
    change _ = true at taken
    exact ReachFT.bcond (b := true) (ΨF := Tr.is es) even target c _ hpc hs hx hBound delta wherePC hsp taken
      (fun _ => next) (fun h => by rw [taken] at h; contradiction)

private def quietTrace (base : Word) (site : Nat) (g : List Instr) : List Event :=
  blockTr g (base + BitVec.ofNat 32 site) [] []

private theorem quiet_block {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} {site : Nat} {g : List Instr} {es : List Event} {Q : State → Prop}
    (even : base.toNat % 2 = 0) (hs : site % 2 = 0)
    (seq : seqAt B site g = true) (hPC : t.pc = base + BitVec.ofNat 32 site)
    (hr : InRegion (routine.PcP base) base site (seqSize g))
    (hfalls : g.all Instr.falls = true) (hsp : keepsSp g = true)
    (ha : M0Crypto.Sym.alignChk [] g = true) (hw : M0Crypto.Sym.writeChk [] g = true)
    (hd : M0Crypto.Sym.readChk (fun _ => true) [] g = true)
    (ht : traceOk g [] = true) (kept : Kept s t)
    (next : ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      (execAll g t) Q (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t Q
      (Tr.is (quietTrace base site g ++ es)) := by
  rw [← Tr.cat_is_is]
  exact ReachFT.block even g site hPC hs seq hfalls hsp hr [] [] [] ha hw hd
    (by simp) (by simp [regions,Has]) (by simp [regions,Has])
    ⟨0,by decide,by simp [kept.sp]⟩ (traceAll_blockTr (L := []) hfalls ht hPC rfl) next

private structure ScanCode (B : List (BitVec 8)) (BS : Nat) : Prop where
  test : seqAt B r_check_scan scanTest = true
  mismatch : instrAt B mismatchSite = some (branch 1 mismatchSite r_check_pass)
  decrement : seqAt B decrementSite [.subImm8 1 1] = true
  back : instrAt B backSite = some (branch 1 backSite r_check_scan)
  exitSize : ∀ reject, exitSite reject + 4 ≤ BS
  exitImm : ∀ reject, instrAt B (exitSite reject) = some (exitValue reject)
  exitRet : ∀ reject, instrAt B (exitSite reject + 2) = some (.bx 14)

private theorem scan_code {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    (h : seqAt B r_encoding_check instructions = true) : ScanCode B BS := by
  have hb : r_encoding_check + seqSize instructions ≤ BS := by
    rw [← CodeBytes.len (B := B)]
    exact (seqAt_size _ _ _ h).resolve_right (by decide)
  simp only [instructions, scanByte, seqAt_append, seqSize_append, Bool.and_eq_true] at h
  have hTest : seqAt B r_check_scan scanTest = true := h.1.2.1
  have hRest : seqAt B mismatchSite
      [branch 1 mismatchSite r_check_pass, .subImm8 1 1, branch 1 backSite r_check_scan] = true :=
    h.1.2.2
  have hExit : seqAt B (exitSite true) [.movImm 0 1, .bx 14, .movImm 0 0, .bx 14] = true :=
    h.2
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq] at hRest hExit
  refine ⟨hTest,hRest.1.1,?_,hRest.2.2.1.1,?_,?_,?_⟩
  · have hI : instrAt B decrementSite = some (.subImm8 1 1) := hRest.2.1.1
    have hN : decide (decrementSite + (Instr.subImm8 1 1).size ≤ B.length) = true := hRest.2.1.2
    simp only [seqAt, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hI,hN⟩
  · intro reject
    cases reject
    · exact hb
    · exact Nat.le_trans (by decide) hb
  · intro reject
    cases reject
    · exact hExit.2.2.1.1
    · exact hExit.1.1
  · intro reject
    cases reject
    · exact hExit.2.2.2.1.1
    · exact hExit.2.1.1

private theorem return_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} (entry : routine.Entry base s) (hCode : ScanCode B BS)
    (reject : Bool) (hk : Kept s t) (hpc : t.pc = base + BitVec.ofNat 32 (exitSite reject))
    (hResult : status s = if reject then 1 else 0) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      t (routine.Ret s) (Tr.is (exitTrace base reject)) :=
  exit_capture entry reject (CodeBytes.len (B := B) ▸ hCode.exitSize reject)
    hpc (hCode.exitImm reject) (hCode.exitRet reject) hk.sp hk.lr hResult

private def afterTest (base a : Word) (read : Nat → BitVec 8) (mask : BitVec 8)
    (n : Nat) : List Event :=
  event base mismatchSite (branch 1 mismatchSite r_check_pass) ::
    if read (n+1) == mask then
      event base decrementSite (.subImm8 1 1) ::
        event base backSite (branch 1 backSite r_check_scan) :: scanTrace base a read mask n
    else exitTrace base false

private theorem after_mismatch (read : Nat → BitVec 8) (mask : BitVec 8) (n : Nat)
    (h : (read (n+1) == mask) = false) :
    (if earlyScan read mask (n+1) then (1 : Word) else 0) = 0 := by
  simp only [earlyScan,h,Bool.false_and]
  rfl

private theorem after_match (read : Nat → BitVec 8) (mask : BitVec 8) (n : Nat)
    (h : (read (n+1) == mask) = true) :
    (if earlyScan read mask (n+1) then (1 : Word) else 0) =
      (if earlyScan read mask n then 1 else 0) := by
  simp only [earlyScan,h,Bool.true_and]

private theorem scan_back {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s d : State} {n : Nat} {mask : BitVec 8} {es : List Event} {Q : State → Prop}
    (even : base.toNat % 2 = 0) (hCode : ScanCode B BS) (kept : Kept s d)
    (hPC : d.pc = base + BitVec.ofNat 32 backSite)
    (hCount : d.regs 1 = BitVec.ofNat 32 n) (hMask : d.regs 4 = mask.zeroExtend 32)
    (hCond : condPassed 1 d = decide (0 < n))
    (next : ∀ v, Kept s v →
      v.pc = base + BitVec.ofNat 32 (if n = 0 then exitSite true else r_check_scan) →
      v.regs 1 = BitVec.ofNat 32 n → v.regs 4 = mask.zeroExtend 32 →
      ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
        v Q (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) d
      Q (Tr.is (event base backSite (branch 1 backSite r_check_scan) :: es)) := by
  have size : backSite + 2 ≤ BS := Nat.le_trans (by decide) (hCode.exitSize false)
  refine quiet_branch even (by decide) size hPC hCode.back
    (within (o := backSite) (n := 2) (by decide) (by decide) 0 (by decide)) kept.sp hCond (by decide) ?_
  have site : (if decide (0 < n) then r_check_scan else backSite+2) =
      (if n = 0 then exitSite true else r_check_scan) := by cases n <;> rfl
  exact next _ (kept.pc _) (congrArg (fun o => base + BitVec.ofNat 32 o) site) hCount hMask

private theorem scan_matched {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s w : State} {n : Nat} {mask : BitVec 8} {es : List Event} {Q : State → Prop}
    (even : base.toNat % 2 = 0) (hCode : ScanCode B BS)
    (hn : n < 30) (kept : Kept s w)
    (wpc : w.pc = base + BitVec.ofNat 32 decrementSite)
    (hCount : w.regs 1 = BitVec.ofNat 32 (n+1))
    (hMask : w.regs 4 = mask.zeroExtend 32)
    (next : ∀ v, Kept s v →
      v.pc = base + BitVec.ofNat 32 (if n = 0 then exitSite true else r_check_scan) →
      v.regs 1 = BitVec.ofNat 32 n → v.regs 4 = mask.zeroExtend 32 →
      ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
        v Q (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      w Q (Tr.is (event base decrementSite (.subImm8 1 1) ::
        event base backSite (branch 1 backSite r_check_scan) :: es)) := by
  let d := (Instr.subImm8 1 1).next w
  have dPC : d.pc = base + BitVec.ofNat 32 backSite := by
    change w.pc + 2#32 = _
    rw [wpc,ofNat_add_assoc]
    rfl
  have keptD : Kept s d := kept.block (g := [.subImm8 1 1]) rfl rfl rfl rfl rfl
  have maskD : d.regs 4 = mask.zeroExtend 32 :=
    (show d.regs 4 = w.regs 4 from rfl).trans hMask
  obtain ⟨count,flags⟩ := decrement_value w hn hCount
  have hLen : decrementSite + (Instr.subImm8 1 1).size ≤ B.length :=
    Nat.le_trans (by decide) (CodeBytes.len (B := B) ▸ hCode.exitSize false)
  refine ReachT.retrace ?_ (Tr.cat_is_is [event base decrementSite (.subImm8 1 1)] _)
  exact ReachFT.step even (.subImm8 1 1) wpc (by decide)
    (instrAt_of_seqAt hCode.decrement) hLen rfl rfl
    (within (o := decrementSite) (n := 2) (by decide) (by decide) 0 (by decide))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    ⟨0,by decide,by simp [kept.sp]⟩ (by change (⟨w.pc,.subImm8 1 1,[]⟩ : Event) = _; rw [wpc]; rfl)
    (scan_back even hCode keptD dPC count maskD flags next)

private theorem scan_next {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s u : State} {n : Nat} {mask : BitVec 8}
    (entry : routine.Entry base s) (hCode : ScanCode B BS)
    (hn : n+1 ≤ 30) (kept : Kept s u)
    (hpc : u.pc = base + BitVec.ofNat 32 mismatchSite)
    (hCount : u.regs 1 = BitVec.ofNat 32 (n+1))
    (hMask : u.regs 4 = mask.zeroExtend 32)
    (mismatch : condPassed 1 u = !(readByte s.mem (s.regs 0) (n+1) == mask))
    (hResult : status s = (if earlyScan (readByte s.mem (s.regs 0)) mask (n+1) then 1 else 0))
    (next : ∀ (v : State), n ≤ 30 → Kept s v →
      v.pc = base + BitVec.ofNat 32 (if n = 0 then exitSite true else r_check_scan) →
      v.regs 1 = BitVec.ofNat 32 n → v.regs 4 = mask.zeroExtend 32 →
      status s = (if earlyScan (readByte s.mem (s.regs 0)) mask n then 1 else 0) →
      ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
        v (routine.Ret s) (Tr.is (scanTrace base (s.regs 0) (readByte s.mem (s.regs 0)) mask n))) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      u (routine.Ret s) (Tr.is (afterTest base (s.regs 0) (readByte s.mem (s.regs 0)) mask n)) := by
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  have extent := hCode.exitSize false
  unfold afterTest
  cases hMatch : (readByte s.mem (s.regs 0) (n+1) == mask)
  · rw [hMatch] at mismatch
    exact quiet_branch (take := true) even (by decide) (Nat.le_trans (by decide) extent)
      hpc hCode.mismatch (within (o := mismatchSite) (n := 2) (by decide) (by decide) 0 (by decide))
      kept.sp mismatch (by decide) (return_run entry hCode false (kept.pc _) rfl
        (hResult.trans (after_mismatch _ _ _ hMatch)))
  · rw [hMatch] at mismatch
    simp only [ite_true]
    refine quiet_branch (take := false) even (by decide) (Nat.le_trans (by decide) extent)
      hpc hCode.mismatch (within (o := mismatchSite) (n := 2) (by decide) (by decide) 0 (by decide))
      kept.sp mismatch (by decide) ?_
    exact scan_matched even hCode (Nat.lt_of_succ_le hn) (kept.pc _) rfl hCount hMask
      (fun v hv hp cnt hm => next v (Nat.le_of_succ_le hn) hv hp cnt hm
        (hResult.trans (after_match _ _ _ hMatch)))

private theorem scan_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s : State} (entry : routine.Entry base s) (hCode : ScanCode B BS) (mask : BitVec 8) :
    ∀ n (t : State), n ≤ 30 → Kept s t →
      t.pc = base + BitVec.ofNat 32 (if n = 0 then exitSite true else r_check_scan) →
      t.regs 1 = BitVec.ofNat 32 n → t.regs 4 = mask.zeroExtend 32 →
      status s = (if earlyScan (readByte s.mem (s.regs 0)) mask n then 1 else 0) →
      ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
        t (routine.Ret s) (Tr.is (scanTrace base (s.regs 0) (readByte s.mem (s.regs 0)) mask n)) := by
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  intro n
  induction n with
  | zero =>
    intro t _ hk hpc _ _ hResult
    exact return_run entry hCode true hk hpc hResult
  | succ n ih =>
    intro t hn hk hpc hCount hMask hResult
    have hScanPC : t.pc = base + BitVec.ofNat 32 r_check_scan := hpc
    have mismatch := scan_equal t (n+1) hCount mask hMask
    rw [hk.addr,hk.mem] at mismatch
    have pcTest : (execAll scanTest t).pc = base + BitVec.ofNat 32 mismatchSite := by
      rw [execAll_pc _ _ rfl,hScanPC,ofNat_add_assoc]
      rfl
    have keptTest := hk.block (g := scanTest) rfl rfl rfl rfl rfl
    change ReachFT _ _ _ _ _ t _ (Tr.is (scanTestTrace base (s.regs 0) (n+1) ++
      afterTest base (s.regs 0) (readByte s.mem (s.regs 0)) mask n))
    rw [← Tr.cat_is_is]
    exact scan_test_run even hCode.test hScanPC hk.addr hCount (by omega) hk.sp
      (scan_next entry hCode hn keptTest pcTest
        ((execAll_regs_other scanTest t 1 (by decide) rfl).trans hCount)
        ((execAll_regs_other scanTest t 4 (by decide) rfl).trans hMask) mismatch hResult ih)

/-! The selector is a tree of immediate compares with shared exit and scan sites. -/

private inductive Route where
  | pass
  | lowMask (site : Nat)
  | highMask
  | test (site : Nat) (reg : LowReg) (imm : BitVec 8) (cc : BitVec 4)
      (taken fall : Route)

private def Route.site : Route → Nat
  | .pass => r_check_pass
  | .lowMask site => site
  | .highMask => r_check_high_middle
  | .test site .. => site

private def highRoute : Route :=
  .test r_check_high 3 237 2 .highMask
    (.test (r_check_high + 4) 2 255 1 .pass
      (.test (r_check_high + 8) 3 236 1 .pass .highMask))

private def selectorSite := r_encoding_check + seqSize endpoints

private def selector : Route :=
  .test selectorSite 2 255 0 highRoute
    (.test (selectorSite + 4) 2 127 0 highRoute
      (.test (selectorSite + 8) 2 128 1 .pass
        (.test (selectorSite + 12) 3 1 1 .pass (.lowMask (selectorSite + 16)))))

private def endpoint (lo hi : BitVec 8) (r : LowReg) : BitVec 8 :=
  if r = 2 then hi else lo

private def testByte (c : BitVec 4) (k x : BitVec 8) : Bool :=
  if c = 0 then decide (x = k) else
    if c = 1 then decide (x ≠ k) else decide (k.toNat ≤ x.toNat)

private def Route.mask (lo hi : BitVec 8) : Route → Option (BitVec 8)
  | .pass => none
  | .lowMask _ => some 0
  | .highMask => some 255
  | .test _ r k c y n =>
    if testByte c k (endpoint lo hi r) then y.mask lo hi else n.mask lo hi

private theorem selector_mask (lo hi : BitVec 8) :
    selector.mask lo hi = Ed25519VerifyEncode.earlyMask lo hi := by
  by_cases h255 : hi = 255 <;> by_cases h127 : hi = 127 <;>
    by_cases h128 : hi = 128 <;> by_cases h1 : lo = 1 <;>
    by_cases h236 : lo = 236 <;> by_cases h237 : 237 ≤ lo.toNat <;>
    simp_all [selector,highRoute,Route.mask,endpoint,testByte,Ed25519VerifyEncode.earlyMask]
  all_goals split at * <;> simp_all

private def Route.trace (base a : Word) (read : Nat → BitVec 8) : Route → List Event
  | .pass => exitTrace base false
  | .highMask =>
    quietTrace base r_check_high_middle [.movImm 4 255,.movImm 1 30] ++
      scanTrace base a read 255 30
  | .lowMask site =>
    event base site (.movImm 4 0) ::
      event base (site + 2) (jump (site + 2) r_check_middle) ::
      event base r_check_middle (.movImm 1 30) :: scanTrace base a read 0 30
  | .test site r k c y n =>
    event base site (.cmpImm r k) :: event base (site + 2) (branch c (site + 2) y.site) ::
      if testByte c k (endpoint (read 0) (read 31) r) then y.trace base a read else n.trace base a read

private def siteRange (site len : Nat) : Bool :=
  decide (r_encoding_check ≤ site ∧ site + len ≤ r_encoding_check + seqSize instructions)

private def cmpCode (B : List (BitVec 8)) (BS site : Nat) (r : LowReg) (k : BitVec 8) (c : BitVec 4)
    (y n : Nat) : Bool :=
  seqAt B site [.cmpImm r k, branch c (site + 2) y] &&
    decide (site % 2 = 0 ∧ site + 4 ≤ BS ∧ n = site + 4 ∧ (r = 2 ∨ r = 3) ∧ (c = 0 ∨ c = 1 ∨ c = 2)) &&
    siteRange site 4 &&
    decide (BitVec.ofNat 32 (site + 2) + 4#32 +
      ((BitVec.ofInt 8 (((y : Int) - (site + 2 + 4)) / 2)) ++ 0#1).signExtend 32 = BitVec.ofNat 32 y)

private def Route.code (B : List (BitVec 8)) (BS : Nat) : Route → Bool
  | .pass => true
  | .highMask => seqAt B r_check_high_middle [.movImm 4 255,.movImm 1 30]
  | .lowMask site => seqAt B site [.movImm 4 0,jump (site+2) r_check_middle] &&
    seqAt B r_check_middle [.movImm 1 30] && decide (site = selectorSite + 16)
  | .test site r k c y n =>
    cmpCode B BS site r k c y.site n.site && y.code B BS && n.code B BS

private theorem selector_code (b : M0Crypto.Release.Ed25519.Build) :
    selector.code b.bytes b.size = true := by
  cases b <;> simp only [selector,highRoute,Route.code,cmpCode,seqAt_eq_scan] <;> decide +kernel

private structure Ready (s t : State) : Prop extends Kept s t where
  lo : t.regs 3 = (readByte s.mem (s.regs 0) 0).zeroExtend 32
  hi : t.regs 2 = (readByte s.mem (s.regs 0) 31).zeroExtend 32

private theorem compare_taken (t : State) (r : LowReg) (k : BitVec 8) (c : BitVec 4)
    (x : BitVec 8) (hx : t.regs r.toReg = x.zeroExtend 32) (hc : c = 0 ∨ c = 1 ∨ c = 2) :
    condPassed c ((Instr.cmpImm r k).next t) = testByte c k x := by
  obtain ⟨carry,zero⟩ := RoutineBranch.cmpImm_flags r k t
  have hnat : (x.zeroExtend 32).toNat = x.toNat := BitVec.toNat_setWidth_of_le (by decide)
  rw [hx,hnat] at carry zero
  rcases hc with rfl | rfl | rfl
  · change _ = decide (x = k)
    rw [RoutineBranch.cond_eq,zero]
    simp only [BitVec.toNat_inj]
  · change _ = decide (x ≠ k)
    rw [RoutineBranch.cond_ne,zero]
    simp only [BitVec.toNat_inj,decide_not]
  · exact carry

private def selectSite (take : Bool) (yes no : Nat) : Nat := if take then yes else no

private theorem compare_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} {site y n : Nat} {r : LowReg} {k : BitVec 8} {c : BitVec 4}
    {es : List Event} {Q : State → Prop}
    (even : base.toNat % 2 = 0) (hCode : cmpCode B BS site r k c y n = true)
    (hPC : t.pc = base + BitVec.ofNat 32 site) (ready : Ready s t)
    (next : ∀ u, Ready s u →
      u.pc = base + BitVec.ofNat 32 (selectSite
        (testByte c k (endpoint (readByte s.mem (s.regs 0) 0) (readByte s.mem (s.regs 0) 31) r)) y n) →
      ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) u Q
        (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t Q
      (Tr.is (event base site (.cmpImm r k) :: event base (site + 2) (branch c (site + 2) y) :: es)) := by
  simp only [cmpCode,Bool.and_eq_true,decide_eq_true_eq,siteRange] at hCode
  obtain ⟨⟨⟨seq,align,extent,rfl,hReg,hCond⟩,lower,upper⟩,delta⟩ := hCode
  have parts : seqAt B site [.cmpImm r k] = true ∧
      seqAt B (site+2) [branch c (site+2) y] = true := by
    change seqAt B site ([.cmpImm r k] ++ [branch c (site+2) y]) = true at seq
    rw [seqAt_append,Bool.and_eq_true] at seq
    exact seq
  have hd (i : Nat) (hi : i ≤ 2) : InRegion (routine.PcP base) base (site+i) 2 :=
    within (by omega) (by omega)
  have traceCmp : quietTrace base site [.cmpImm r k] = [event base site (.cmpImm r k)] := rfl
  change ReachFT _ _ _ _ _ t Q (Tr.is ([event base site (.cmpImm r k)] ++ _))
  rw [← traceCmp]
  refine quiet_block even align parts.1 hPC (hd 0 (by decide))
    rfl rfl rfl rfl rfl rfl ready.toKept ?_
  have hv : t.regs r.toReg =
      (endpoint (readByte s.mem (s.regs 0) 0) (readByte s.mem (s.regs 0) 31) r).zeroExtend 32 := by
    rcases hReg with rfl | rfl
    · exact ready.hi
    · exact ready.lo
  have cond := compare_taken t r k c _ hv hCond
  have hpc' : (execAll [.cmpImm r k] t).pc = base + BitVec.ofNat 32 (site+2) := by
    rw [execAll_pc _ _ rfl,hPC,ofNat_add_assoc]
    rfl
  have kept := ready.toKept.block (g := [.cmpImm r k]) rfl rfl rfl rfl rfl
  refine quiet_branch even (by omega) (by omega) hpc' (instrAt_of_seqAt parts.2)
    (hd 2 (by decide) 0 (by decide)) kept.sp cond delta ?_
  apply next
  · exact ⟨kept.pc _,ready.lo,ready.hi⟩
  · rfl

private def scanResult (s : State) : Option (BitVec 8) → Word
  | none => 0
  | some mask => if earlyScan (readByte s.mem (s.regs 0)) mask 30 then 1 else 0

private theorem high_mask_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} (entry : routine.Entry base s) (hScan : ScanCode B BS)
    (hCode : seqAt B r_check_high_middle [.movImm 4 255,.movImm 1 30] = true)
    (keep : Kept s t) (hPC : t.pc = base + BitVec.ofNat 32 r_check_high_middle)
    (result : status s = scanResult s (some 255)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t
      (routine.Ret s) (Tr.is (Route.trace base (s.regs 0) (readByte s.mem (s.regs 0)) .highMask)) := by
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  refine quiet_block even (by decide) hCode hPC (within (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) keep ?_
  have hk := keep.block (g := [.movImm 4 255,.movImm 1 30]) rfl rfl rfl rfl rfl
  have pcNext : (execAll [.movImm 4 255,.movImm 1 30] t).pc = base + BitVec.ofNat 32 r_check_scan := by
    rw [execAll_pc _ _ rfl,hPC,ofNat_add_assoc]
    rfl
  exact scan_run entry hScan 255 30 _ (by decide) hk pcNext rfl rfl result

private theorem quiet_jump {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} {site target : Nat} {Q : State → Prop} {es : List Event}
    (even : base.toNat % 2 = 0) (hs : site % 2 = 0) (hBound : site + 2 ≤ BS)
    (hPC : t.pc = base + BitVec.ofNat 32 site)
    (hI : instrAt B site = some (jump site target))
    (wherePC : routine.PcP base (base + BitVec.ofNat 32 site))
    (sp : t.regs 13 = s.regs 13)
    (delta : BitVec.ofNat 32 site + 4#32 +
      ((BitVec.ofInt 11 (((target : Int) - (site + 4)) / 2)) ++ 0#1).signExtend 32 =
      BitVec.ofNat 32 target)
    (next : ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      (t.setReg 15 (base + BitVec.ofNat 32 target)) Q (Tr.is es)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s)
      t Q (Tr.is (event base site (jump site target) :: es)) := by
  change ReachFT _ _ _ _ _ t Q (Tr.is ([event base site (jump site target)] ++ es))
  rw [← Tr.cat_is_is]
  refine ReachT.b even site target _ hPC hs hI hBound delta ?_ next
  exact ⟨hPC.symm ▸ wherePC,fun y hy => absurd hy (writes_nil y),
    fun y hy => absurd hy (reads_nil y), ⟨0,by decide,by simp [sp]⟩⟩

private theorem low_mask_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s t : State} (entry : routine.Entry base s) (hScan : ScanCode B BS)
    (hCode : seqAt B (selectorSite+16) [.movImm 4 0,jump (selectorSite+18) r_check_middle] = true)
    (hMiddle : seqAt B r_check_middle [.movImm 1 30] = true)
    (keep : Kept s t) (hPC : t.pc = base + BitVec.ofNat 32 (selectorSite+16))
    (result : status s = scanResult s (some 0)) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t
      (routine.Ret s) (Tr.is (Route.trace base (s.regs 0) (readByte s.mem (s.regs 0))
        (.lowMask (selectorSite+16)))) := by
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  have parts : seqAt B (selectorSite+16) [.movImm 4 0] = true ∧
      seqAt B (selectorSite+18) [jump (selectorSite+18) r_check_middle] = true := by
    rw [show [.movImm 4 0,jump (selectorSite+18) r_check_middle] =
        [.movImm 4 0] ++ [jump (selectorSite+18) r_check_middle] from rfl,
      seqAt_append,Bool.and_eq_true] at hCode
    exact hCode
  change ReachFT _ _ _ _ _ t _
    (Tr.is (quietTrace base (selectorSite+16) [.movImm 4 0] ++ _))
  refine quiet_block even (by decide) parts.1 hPC (within (by decide) (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) keep ?_
  have pcMov : (execAll [.movImm 4 0] t).pc = base + BitVec.ofNat 32 (selectorSite+18) := by
    rw [execAll_pc _ _ rfl,hPC,ofNat_add_assoc]
    rfl
  have keptMov := keep.block (g := [.movImm 4 0]) rfl rfl rfl rfl rfl
  refine quiet_jump even (by decide) (Nat.le_trans (by decide) (hScan.exitSize false)) pcMov
    (instrAt_of_seqAt parts.2) (within (o := selectorSite+18) (n := 2) (by decide) (by decide) 0 (by decide))
    keptMov.sp (by decide) ?_
  let w := (execAll [.movImm 4 0] t).setReg 15 (base + BitVec.ofNat 32 r_check_middle)
  change ReachFT _ _ _ _ _ w _
    (Tr.is (quietTrace base r_check_middle [.movImm 1 30] ++ _))
  refine quiet_block even (by decide) hMiddle (show w.pc = _ from rfl)
    (within (by decide) (by decide)) rfl rfl rfl rfl rfl rfl (keptMov.pc _) ?_
  have pcCount : (execAll [.movImm 1 30] w).pc = base + BitVec.ofNat 32 r_check_scan := by
    rw [execAll_pc _ _ rfl,show w.pc = base+BitVec.ofNat 32 r_check_middle from rfl,ofNat_add_assoc]
    rfl
  have keptCount := (keptMov.pc (base + BitVec.ofNat 32 r_check_middle)).block
    (g := [.movImm 1 30]) rfl rfl rfl rfl rfl
  exact scan_run entry hScan 0 30 _ (by decide) keptCount pcCount rfl rfl result

private theorem route_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s : State} (entry : routine.Entry base s) (hScan : ScanCode B BS)
    (route : Route) (hCode : route.code B BS = true) {t : State} (ready : Ready s t)
    (hPC : t.pc = base + BitVec.ofNat 32 route.site)
    (result : status s = scanResult s (route.mask (readByte s.mem (s.regs 0) 0)
      (readByte s.mem (s.regs 0) 31))) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) t
      (routine.Ret s) (Tr.is (route.trace base (s.regs 0) (readByte s.mem (s.regs 0)))) := by
  induction route generalizing t with
  | pass => exact return_run entry hScan false ready.toKept hPC result
  | highMask => exact high_mask_run entry hScan hCode ready.toKept hPC result
  | lowMask site =>
    simp only [Route.code,Bool.and_eq_true,decide_eq_true_eq] at hCode
    obtain ⟨⟨hHead,hMiddle⟩,rfl⟩ := hCode
    exact low_mask_run entry hScan hHead hMiddle ready.toKept hPC result
  | test site r k c y n hy hn =>
    simp only [Route.code,Bool.and_eq_true] at hCode
    obtain ⟨⟨hTest,hyCode⟩,hnCode⟩ := hCode
    have even : base.toNat % 2 = 0 := by have := entry.base4; omega
    unfold Route.trace
    unfold Route.mask at result
    refine compare_run even hTest hPC ready ?_
    intro u hu hp
    cases h : testByte c k (endpoint (readByte s.mem (s.regs 0) 0) (readByte s.mem (s.regs 0) 31) r)
    · exact hn hnCode hu (by simpa [selectSite,h] using hp) (by simpa [h] using result)
    · exact hy hyCode hu (by simpa [selectSite,h] using hp) (by simpa [h] using result)

private def endpointTrace (base a : Word) : List Event :=
  blockTr endpoints (base + BitVec.ofNat 32 r_encoding_check) [0] [a]

private def endpointReads : List (M0Crypto.Sym.SExpr × Nat) :=
  [(.add (.reg0 0) (.const 31#32),1),(.reg0 0,1)]

private theorem end_reads (s : State) :
    ∀ y, Has (sregions s endpointReads) y → Has [⟨s.regs 0,32⟩] y := by
  intro y h
  change Has [⟨s.regs 0+31#32,1⟩,⟨s.regs 0,1⟩] y at h
  obtain ⟨r,hr,j,hj,hy⟩ := h
  rcases List.mem_cons.mp hr with hr | hr
  · subst r
    have hj0 : j = 0 := by change j < 1 at hj; omega
    subst j
    exact ⟨_,List.mem_singleton_self _,31,(by change 31 < 32; decide),by simpa only [BitVec.add_zero] using hy⟩
  · have hr' := List.mem_singleton.mp hr
    subst r
    have hj0 : j = 0 := by change j < 1 at hj; omega
    subst j
    exact ⟨_,List.mem_singleton_self _,0,(by change 0 < 32; decide),hy⟩

private theorem intrinsic_run {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
    {base : Word} {s : State} (entry : routine.Entry base s)
    (hLink : seqAt B r_encoding_check instructions = true)
    (hCode : selector.code B BS = true) :
    ReachFT base (routine.PcP base) (routine.RdP base s) (routine.WrP s) (routine.SpP s) s
      (routine.Ret s) (Tr.is (endpointTrace base (s.regs 0) ++
        selector.trace base (s.regs 0) (readByte s.mem (s.regs 0)))) := by
  have hScan := scan_code hLink
  simp only [instructions,seqAt_append,Bool.and_eq_true] at hLink
  have hEnd : seqAt B r_encoding_check endpoints = true := hLink.1.1.1.1.1
  have even : base.toNat % 2 = 0 := by have := entry.base4; omega
  rw [← Tr.cat_is_is]
  refine Ed25519Leaf.ReachFT.blockE even endpoints r_encoding_check entry.pc (by decide) hEnd
    rfl rfl (within (by decide) (by decide)) endpointReads [] endpointReads
    (by decide) rfl (by decide) (by simp [endpointReads,Nat.mod_one]) (by simp [sregions,Has])
    (fun y hy => by
      obtain ⟨r,hr,hh⟩ := end_reads s y hy
      exact ⟨r,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr),hh⟩) ⟨0,by decide,by simp⟩
    (traceAll_blockTr (L := [0]) (by decide) (by decide) entry.pc rfl) ?_
  have keep : Kept s s := ⟨rfl,rfl,rfl,rfl⟩
  have hNext : (execAll endpoints s).pc = base + BitVec.ofNat 32 selectorSite := by
    rw [execAll_pc _ _ rfl,entry.pc,ofNat_add_assoc]
    rfl
  obtain ⟨hi,lo⟩ := endpoints_value s
  exact route_run entry hScan selector hCode ⟨keep.block rfl rfl rfl rfl rfl,lo,hi⟩ hNext (by
    rw [selector_mask]
    cases hm : Ed25519VerifyEncode.earlyMask (readByte s.mem (s.regs 0) 0)
      (readByte s.mem (s.regs 0) 31) <;> simp only [status,rejected,hm,scanResult] <;> rfl)

private theorem scanTrace_congr (base a : Word) (read other : Nat → BitVec 8) (mask : BitVec 8)
    (agree : ∀ i < 32, read i = other i) :
    ∀ n ≤ 30, scanTrace base a read mask n = scanTrace base a other mask n
  | 0, _ => rfl
  | n+1, hn => by
    simp only [scanTrace,agree (n+1) (by omega),scanTrace_congr base a read other mask agree n (by omega)]

private theorem routeTrace_congr (base a : Word) {read other : Nat → BitVec 8}
    (agree : ∀ i < 32, read i = other i) (route : Route) :
    route.trace base a read = route.trace base a other := by
  induction route with
  | pass => rfl
  | highMask => simp only [Route.trace,scanTrace_congr base a read other 255 agree 30 (by decide)]
  | lowMask site => simp only [Route.trace,scanTrace_congr base a read other 0 agree 30 (by decide)]
  | test site r k c y n hy hn =>
    simp only [Route.trace,agree 0 (by decide),agree 31 (by decide),hy,hn]

open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.StackEffect

private def xp (s : State) : List Word :=
  (List.range 32).map fun i => (readByte s.mem (s.regs 0) i).zeroExtend 32

private def pubRead (p : Nat → Word) (i : Nat) : BitVec 8 := (p (i+2)).truncate 8

private def trace (base : Word) (p : Nat → Word) : List Event :=
  endpointTrace base (p 0) ++ selector.trace base (p 0) (pubRead p)

private theorem pub_agrees (s : State) (i : Nat) (hi : i < 32) :
    pubRead (checkS.pubX xp s) i = readByte s.mem (s.regs 0) i := by
  change (((xp s)[i]?).getD 0).truncate 8 = _
  simp only [xp,List.getElem?_map,List.getElem?_range,hi]
  change ((readByte s.mem (s.regs 0) i).setWidth 32).setWidth 8 = _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),BitVec.setWidth_eq]

private theorem run (b : M0Crypto.Release.Ed25519.Build) : letI := b.codeBytes
    routine.SpecT fun base s => Tr.is (trace base (checkS.pubX xp s)) := by
  letI := b.codeBytes
  intro base s entry
  have ha : checkS.pubX xp s 0 = s.regs 0 := rfl
  change ReachFT _ _ _ _ _ s _ (Tr.is (trace base (checkS.pubX xp s)))
  unfold trace
  rw [ha,routeTrace_congr base (s.regs 0) (pub_agrees s) selector]
  exact intrinsic_run entry (linked b) (selector_code b)

private abbrev Readable (a : Word) : Word → Prop := Has [⟨a,32⟩]

private theorem seg_cat {sp0 sp a : Word} {n : Nat} {xs ys : List Event}
    (hx : Seg sp0 n sp (Readable a) xs (fun _ => False))
    (hy : Seg sp0 n sp (Readable a) ys (fun _ => False)) :
    Seg sp0 n sp (Readable a) (xs ++ ys) (fun _ => False) :=
  (hx.cat hy).mono (fun _ h => h) (fun _ h => h.elim)

private theorem quiet_seg {sp0 sp a : Word} {n : Nat} {e : Event}
    (hOnly : e.accesses = []) (hSP : spExact e.instr = true) (hSame : spAfter e.instr sp = sp) :
    Seg sp0 n sp (Readable a) [e] (fun _ => False) :=
  (ev_seg (X := Readable a) hSP hSame
    (fun y h _ => by rw [hOnly] at h; exact (h.elim (reads_nil y) (writes_nil y)).elim)
    (fun y h _ => by rw [hOnly] at h; exact (reads_nil y h).elim)).mono
    (fun _ h => h) (fun _ h => h.elim)

private theorem quiet_cons {sp0 sp a : Word} {n : Nat} {es : List Event} (e : Event)
    (hOnly : e.accesses = []) (hSP : spExact e.instr = true) (hSame : spAfter e.instr sp = sp)
    (tail : Seg sp0 n sp (Readable a) es (fun _ => False)) :
    Seg sp0 n sp (Readable a) (e :: es) (fun _ => False) :=
  seg_cat (quiet_seg hOnly hSP hSame) tail

private theorem exit_seg {sp0 sp a : Word} {n : Nat} (base : Word) (reject : Bool) :
    Seg sp0 n sp (Readable a) (exitTrace base reject) (fun _ => False) := by
  cases reject <;> exact seg_cat (quiet_seg rfl rfl rfl) (quiet_seg rfl rfl rfl)

private theorem scan_seg {sp0 sp : Word} {n : Nat} (base a : Word)
    (read : Nat → BitVec 8) (mask : BitVec 8)
    (allowed : ∀ y, Readable a y → TraceSpec.BelowEntry sp0 n y → TraceSpec.AtOrAboveSp sp0 sp y) :
    ∀ k ≤ 30, Seg sp0 n sp (Readable a) (scanTrace base a read mask k) (fun _ => False)
  | 0, _ => exit_seg base true
  | k+1, hk => by
    let u := regState (base + BitVec.ofNat 32 r_check_scan) [0,1] [a,BitVec.ofNat 32 (k+1)]
    have hRead : ∀ y, InR u scanReads y → Readable a y := by
      rintro y ⟨r,hr,i,hi,hy⟩
      have he := List.mem_singleton.mp hr
      subst r
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
      subst i
      refine ⟨_,List.mem_singleton_self _,k+1,by change k+1 < 32; omega,?_⟩
      change y = a + BitVec.ofNat 32 (k+1) + 0#32 at hy
      simpa only [BitVec.add_zero] using hy
    have hs : Seg sp0 n sp (Readable a) (scanTestTrace base a (k+1)) (fun _ => False) :=
      (blk_seg (is := scanTest) (ini := scanReads) (fp := scanReads) (wo := [])
        (by decide) u hRead (fun y hy => allowed y (hRead y hy))).mono
          (fun _ h => h) (fun _ h => h.elim)
    refine seg_cat hs (seg_cat (quiet_seg rfl rfl rfl) ?_)
    split
    · exact seg_cat (quiet_seg rfl rfl rfl)
        (seg_cat (quiet_seg rfl rfl rfl) (scan_seg base a read mask allowed k (Nat.le_of_succ_le hk)))
    · exact exit_seg base false

private theorem route_seg {sp0 sp : Word} {n : Nat} (base a : Word) (read : Nat → BitVec 8)
    (allowed : ∀ y, Readable a y → TraceSpec.BelowEntry sp0 n y → TraceSpec.AtOrAboveSp sp0 sp y)
    (r : Route) : Seg sp0 n sp (Readable a) (r.trace base a read) (fun _ => False) := by
  induction r with
  | pass => exact exit_seg base false
  | lowMask site =>
    exact quiet_cons _ rfl rfl rfl (quiet_cons _ rfl rfl rfl (quiet_cons _ rfl rfl rfl
      (scan_seg base a read 0 allowed 30 (by decide))))
  | highMask =>
    let g := [Instr.movImm 4 255,Instr.movImm 1 30]
    let u := regState (base + BitVec.ofNat 32 r_check_high_middle) [] []
    have block : Seg sp0 n sp (Readable a) (quietTrace base r_check_high_middle g) (fun _ => False) :=
      (blk_seg (X := Readable a) (is := g) (ini := []) (fp := []) (wo := [])
        (by decide) u (by simp [InR]) (by simp [InR])).mono (fun _ h => h) (fun _ h => h.elim)
    exact seg_cat block (scan_seg base a read 255 allowed 30 (by decide))
  | test site r k c y n hy hn =>
    unfold Route.trace
    refine quiet_cons _ rfl rfl rfl (quiet_cons _ rfl rfl rfl ?_)
    split <;> assumption

private theorem endpoint_seg {sp0 sp : Word} {n : Nat} (base a : Word)
    (allowed : ∀ y, Readable a y → TraceSpec.BelowEntry sp0 n y → TraceSpec.AtOrAboveSp sp0 sp y) :
    Seg sp0 n sp (Readable a) (endpointTrace base a) (fun _ => False) := by
  let u := regState (base + BitVec.ofNat 32 r_encoding_check) [0] [a]
  have hr : ∀ y, InR u endpointReads y → Readable a y := by
    rintro y ⟨r,hr,j,hj,hy⟩
    exact end_reads u y ⟨⟨r.1.denote u,r.2⟩,List.mem_map.mpr ⟨r,hr,rfl⟩,j,hj,hy⟩
  exact (blk_seg (is := endpoints) (ini := endpointReads) (fp := endpointReads) (wo := [])
    (by decide) u hr (fun y hy => allowed y (hr y hy))).mono (fun _ h => h) (fun _ h => h.elim)

private theorem effect (b : M0Crypto.Release.Ed25519.Build) (base : Word) (p : Nat → Word) :
    @CalleeS.Eff checkS p b.bytes b.size b.codeBytes base (trace base p) := by
  letI := b.codeBytes
  intro sp0 n q hsp _ _ hU hF hRq
  change q.sp = p 1 at hsp
  have reg0 : checkS.reg p 0 = p 0 := rfl
  have hFp : ∀ y, Readable (p 0) y → checkS.Fp p base y := by
    intro y hy
    obtain ⟨r,hr,hy⟩ := hy
    refine ⟨r,List.mem_cons_of_mem _ ?_,hy⟩
    have hrd : rgnsC (checkS.reg p) checkS.io.rd = [⟨p 0,32⟩] := by
      change ([⟨checkS.reg p 0 + 0#32,32⟩] : List Rgn) = _
      rw [reg0,BitVec.add_zero]
    have hwr : rgnsC (checkS.reg p) checkS.io.wr = [] := rfl
    rw [hrd,hwr]
    exact hr
  have hReq : ∀ y, Readable (p 0) y → checkS.Rq p base y := by
    rintro y ⟨r,hr,j,hj,hy⟩
    have he := List.mem_singleton.mp hr
    subst r
    refine .inr ⟨(0,0,.raw (.k 32)),List.mem_singleton_self _,?_⟩
    change Region (checkS.reg p 0 + 0#32) 32 y
    change j < 32 at hj
    change y = p 0 + BitVec.ofNat 32 j at hy
    rw [reg0,BitVec.add_zero,hy]
    unfold Region
    rw [BitVec.add_comm,BitVec.add_sub_cancel,BitVec.toNat_ofNat]
    omega
  have allowed y hy hb : TraceSpec.AtOrAboveSp sp0 (p 1) y :=
    hsp ▸ hF y (hFp y hy) hb
  have tr : Seg sp0 n (p 1) (Readable (p 0)) (trace base p) (fun _ => False) :=
    seg_cat (endpoint_seg base (p 0) allowed)
      (route_seg base (p 0) (pubRead p) allowed selector)
  obtain ⟨hg,hs,hu,-⟩ := tr q hsp (fun y hy => hsp ▸ hU y hy) (fun y hy => hRq y (hReq y hy))
  exact ⟨hg,hs.trans hsp.symm,hu,by simp [CalleeS.Wd,checkS,calleeAt,io]⟩

private def xpv : List V → List Word
  | [.b bs] => bs.map (·.zeroExtend 32)
  | _ => []

def ok : List V → Bool
  | [.b bs] => !rejectedBytes bs
  | _ => false

private theorem in_bytes (Rs : Rels) {c : Ctx} {sp : Word} {s : State} {vs : List V}
    (h : InsRel Rs c sp io s vs) : vs = [.b (bytesAt s.mem (s.regs 0) 32)] := by
  rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | ⟨_,_⟩⟩ <;>
    simp only [InsRel,All2,io,Rel,In.kd,BitVec.add_zero,and_false,and_true] at h
  rw [show ALen.val s.regs (.k 32) = 32 from rfl] at h
  rw [h]

private theorem status_zero (Rs : Rels) {c : Ctx} {sp : Word} {s : State} {vs : List V}
    (h : InsRel Rs c sp io s vs) : status s = 0 ↔ ok vs = true := by
  rw [in_bytes Rs h]
  simp only [ok,rejectedBytes_mem,status]
  cases rejected (readByte s.mem (s.regs 0)) <;> decide

private def te (b : M0Crypto.Release.Ed25519.Build) : letI := b.codeBytes
    routine.TE (fun _ s => checkS.pubX xp s) (fun base p => checkS.Eff p base) :=
  letI := b.codeBytes
  ⟨trace,run b,effect b⟩

noncomputable def checkAd (b : M0Crypto.Release.Ed25519.Build) (Rs : Rels) :
    AdX Rs (cb := b.codeBytes) checkS :=
  letI := b.codeBytes
  AdX.ofTE { routine with code := checkS.code } rfl rfl (by decide)
    xp xpv (fun _ _ s _ hi => by
      rw [in_bytes Rs hi]
      simp only [xp,xpv,bytesAt,List.map_map]
      rfl)
    ((te b).code _ (by decide)) (fun _ => True) (fun _ _ _ _ h => h) (fun _ => True) (fun _ => [])
    (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ => rfl)
    (fun st => by simp [routine,checkS,calleeAt,io,rgnsC,SRgn.rgnC,ALen.val])
    (fun _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel,All2,checkS,calleeAt,io])
    (fun _ _ _ _ _ _ _ _ => trivial)

noncomputable def checkZ (b : M0Crypto.Release.Ed25519.Build) (Rs : Rels) :
    ZSt Rs (cb := b.codeBytes) (checkAd b Rs) :=
  letI := b.codeBytes
  { ok := ok
    okr := fun _ _ st _ _ vs _ hin _ h => by
      change _ = status st at h
      rw [h]
      exact status_zero Rs hin
    co := []
    csem := fun _ => []
    cpost := fun _ _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel,All2]
    okp := fun p => !rejected (pubRead p)
    okp_of := fun _ _ s _ _ _ hi _ => by
      change (!rejected (pubRead (checkS.pubX xp s))) = _
      rw [rejected_congr (pub_agrees s),in_bytes Rs hi]
      simp only [ok,rejectedBytes_mem]
    cef := fun base p hp _ => CalleeS.eff_withCo_nil ((checkAd b Rs).ef base p hp) }

theorem reject_of_failure (m : M0Crypto.Armv6M.Mem) (a : Word)
    (h : ok [.b (bytesAt m a 32)] = false) :
    Ed25519VerifyEncode.earlyReject (bytesAt m a 32) := by
  apply rejected_sound
  cases hReject : rejected (readByte m a) <;> simp [ok,rejectedBytes_mem,hReject] at h ⊢

end M0Crypto.Release.Ed25519RCheck
