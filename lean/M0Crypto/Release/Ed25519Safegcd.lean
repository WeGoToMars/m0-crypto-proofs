import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519SafegcdLink
import SafegcdTermination.StackFootprint

namespace M0Crypto.Release.Ed25519Safegcd

open M0Crypto.Armv6M (Word State Reg Mem)
open M0Crypto.Artifacts.Ed25519Compact (fe_inv fe_inv_shared)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg M0Crypto.Release.Ed25519FePow
open M0Crypto.Release.Routine M0Crypto.Release.Footprint M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (BelowEntry AtOrAboveSp)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)
open M0Crypto.Release.Ed25519FeCanon (feVal_congr)
open M0Crypto.Release.Ed25519SafegcdLink
open M0Crypto.Thumb
open SafegcdRow.BatchCode (frameBytes callTo call_at entered)
open SafegcdTermination
open SafegcdTermination.Bank (addr)
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.RowCalls (entered_regs entered_sp entered_mem entered_lr
  entered_pc linkedRet_odd linkedRet_clear)

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

def invS : CalleeS := calleeAt fe_inv ioPow [0, 1]

def invR : Routine :=
  { entry := fe_inv
    code := footprint fe_inv
    stack := stackOf fe_inv
    Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0
    wr := fun s => [⟨s.regs 0, 32⟩]
    rd := fun s => [⟨s.regs 1, 32⟩]
    Post := fun s m _ => ModP (feVal m (s.regs 0)) ((feVal s.mem (s.regs 1) : Int)^powE 0)
    clob := Ed25519Routines.hiRegs }

abbrev mask : BitVec 8 := 16
abbrev slots : Nat := frameBytes / 4

def prologue : List Instr := [.push mask true, .subSp (BitVec.ofNat 7 slots)]
def callSite : Nat := fe_inv + seqSize prologue
def invoke : Instr := callTo callSite fe_inv_shared
def epiSite : Nat := callSite + invoke.size
def epilogue : List Instr := [.addSp (BitVec.ofNat 7 slots), .pop mask true]

theorem stack_size : invR.stack = 4 * nSaved mask + frameBytes := by decide +kernel

private theorem cut {a b : Word} {n lo w m : Nat} (h : Disj a n b m) (hw : 0 < w)
    (hFit : lo+w ≤ n) : Disj (addr a lo) w b m := by
  obtain ⟨ha,hb,hsep⟩ := h
  have he := toNat_add_ofNat a lo (by omega)
  unfold addr
  rw [Disj,he]
  exact ⟨by omega,hb,hsep.imp (fun h => by omega) (fun h => by omega)⟩

private theorem disj_symm {a b : Word} {n m : Nat} (h : Disj a n b m) : Disj b m a n :=
  ⟨h.2.1,h.1,h.2.2.symm⟩

private theorem has_region {f : List Rgn} {a y : Word} {n : Nat}
    (h : (⟨a,n⟩ : Rgn) ∈ f) (hy : Region a n y) : Has f y :=
  ⟨_,h,hy.exists⟩

private theorem covered (base : Word) {y : Word}
    (h : Region (base+BitVec.ofNat 32 layout.first) layout.length y) :
    invR.PcP base y := by
  have hc : (List.range layout.length).all (fun i =>
      invR.code.any fun r => decide (r.1 ≤ layout.first+i ∧ layout.first+i < r.2)) = true := by
    decide +kernel
  obtain ⟨o,ho,rfl⟩ := h.exists
  obtain ⟨r,hr,hrange⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc o (List.mem_range.mpr ho))
  obtain ⟨h₁,h₂⟩ := of_decide_eq_true hrange
  rw [ofNat_add_assoc]
  exact PcIn.at hr h₁ h₂

def middleTrace (base sp dst src : Word) : List Event :=
  ⟨base+BitVec.ofNat 32 callSite,invoke,[]⟩ :: layout.trace base sp dst src

private theorem body {b : Build} {base : Word} {s : State} (e : @Routine.Entry b.bytes b.size invR b.codeBytes base s)
    (t : State) (htPc : t.pc = base+BitVec.ofNat 32 callSite)
    (htSp : t.sp = (invR.win s).a)
    (ht0 : t.regs 0 = s.regs 0) (ht1 : t.regs 1 = s.regs 1)
    (htMem : MemEq [saved mask s] s.mem t.mem) (htCode : CodeAt t.mem base b.bytes) :
    letI := b.codeBytes
    ReachFT base (invR.PcP base) (invR.RdP base s) (Has (lowWin invR mask s :: invR.wr s))
      (invR.SpP s) t (fun u => u.pc = base+BitVec.ofNat 32 epiSite ∧ u.sp = t.sp ∧
        (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ invR.clob → u.regs r = s.regs r) ∧
        invR.Post s u.mem (u.regs 0))
      (Tr.is (middleTrace base t.sp (s.regs 0) (s.regs 1))) := by
  letI := b.codeBytes
  let root := entered base callSite fe_inv_shared t
  have hr0 : root.regs 0 = s.regs 0 := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans ht0
  have hr1 : root.regs 1 = s.regs 1 := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans ht1
  have hrSp : root.sp = t.sp := entered_sp _ _ _ _
  have hrMem : root.mem = t.mem := entered_mem _ _ _ _
  have hDst : Disj (s.regs 0) 32 t.sp invR.stack :=
    htSp.symm ▸ e.sepWr ⟨s.regs 0,32⟩ (by simp [invR]) (invR.win s) (by simp)
  have hSrc : Disj (s.regs 1) 32 t.sp invR.stack :=
    htSp.symm ▸ e.sepRd ⟨s.regs 1,32⟩ (by simp [invR]) (invR.win s) (by simp)
  have hCodeFrame : Disj base b.bytes.length t.sp invR.stack := by
    rw [b.bytes_length,htSp]
    exact e.sepCode (codeR base) (by simp) (invR.win s) (by simp)
  have hCodeDst : Disj base b.bytes.length (s.regs 0) 32 := by
    rw [b.bytes_length]
    exact e.sepCode (codeR base) (by simp) ⟨s.regs 0,32⟩ (by simp [invR])
  have ht4 : t.sp.toNat % 4 = 0 := by
    have hr := e.room
    have hs := e.sp4
    have hs' : invR.stack = 384 := by decide +kernel
    rw [htSp,Routine.win,BitVec.toNat_sub,BitVec.toNat_ofNat,hs']
    omega
  have hPre : LinkedInversion.Pre root base b.bytes layout := by
    refine ⟨?_,e.base4,by rw [hrMem]; exact htCode,?_,?_,?_,?_,?_,?_⟩
    · exact entered_pc _ _ _ _
    · rw [hrSp]
      simpa [addr] using disj_symm (cut (disj_symm hCodeFrame) (lo := 0) (by decide) (by decide +kernel)
        : Disj (addr t.sp 0) frameBytes base b.bytes.length)
    · rwa [hr0]
    · rw [hrSp]
      refine ⟨ht4, ?_⟩
      have hh := hCodeFrame.2.1
      have hs : frameBytes ≤ invR.stack := by decide +kernel
      omega
    · refine ⟨by rw [hr1]; exact e.pre.2,?_,?_,?_⟩ <;>
        rw [hrSp,hr1] <;> exact cut (disj_symm hSrc) (by decide) (by decide +kernel)
    · rw [hrSp,hr0]
      refine ⟨e.pre.1,.inr ?_, .inr ?_, ?_⟩
      · simpa [addr] using (cut (lo := 0) (w := 32) (disj_symm hDst) (by decide) (by decide +kernel))
      · exact cut (disj_symm hDst) (by decide) (by decide +kernel)
      · exact disj_symm (cut (disj_symm hDst) (by decide) (by decide +kernel))
    · rw [show root.regs 14 = _ from entered_lr _ _ _ _]
      exact linkedRet_odd _ _
  obtain ⟨u, hRun, hv, _, hw, hp⟩ := LinkedInversion.run (checked b) hPre
  obtain ⟨hRead,_,hStack⟩ := LinkedInversion.trace_io (checked b) hPre
  have hSp : invR.SpP s t.sp := by
    exact ⟨invR.stack,Nat.le_refl _,htSp⟩
  have hFrame : (⟨t.sp,frameBytes⟩ : Rgn) = lowWin invR mask s := by
    rw [htSp]
    rfl
  have hRW (y : Word) (hy : Region t.sp frameBytes y) :
      Has (lowWin invR mask s :: invR.wr s) y := has_region (by rw [hFrame]; exact List.mem_cons_self) hy
  have hFW (y : Word) (hy : Region t.sp frameBytes y) : invR.RdP base s y := by
    refine has_region (a := (invR.win s).a) (n := invR.stack) ?_ ?_
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [← htSp]
      exact Nat.lt_of_lt_of_le hy (by decide +kernel : frameBytes ≤ invR.stack)
  have hWindow : (layout.window b.bytes).length = layout.length := by
    simp only [LinkedInversion.Layout.window,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by have h := (checked b).bounds; omega)
  have hf : ∀ f ∈ layout.trace base root.sp (root.regs 0) (root.regs 1),
      invR.PcP base f.pc ∧
      (∀ y, Writes f.accesses y → Has (lowWin invR mask s :: invR.wr s) y) ∧
      (∀ y, Reads f.accesses y → invR.RdP base s y) := by
    intro f hf
    refine ⟨covered base (hWindow ▸ hp f hf),?_,?_⟩
    · intro y hy
      have h := hw f hf y hy
      rw [hrSp,hr0] at h
      rcases h with ha | ha
      · exact hRW y ha
      · exact has_region (by simp [invR]) ha
    · intro y hy
      have h := hRead f hf y hy
      rw [hrSp,hr1] at h
      rcases h with ha | ha | ha
      · exact hFW y ha
      · exact has_region (by simp [invR]) ha
      · obtain ⟨j,hj,rfl⟩ := ha.exists
        refine ⟨codeR base,List.mem_cons_self,layout.first+layout.targets.literal+j,?_,?_⟩
        · change _ < b.size
          rw [← b.bytes_length]
          have h := (checked b).bounds
          have sub := (checked b).place.literal.1
          rw [hWindow] at sub
          omega
        · change _ = base+BitVec.ofNat 32 (layout.first+layout.targets.literal+j)
          rw [ofNat_add_assoc]
  have hSteps : StepsOk base (Step (invR.PcP base) (invR.RdP base s)
      (Has (lowWin invR mask s :: invR.wr s)) (invR.SpP s))
      (layout.trace base root.sp (root.regs 0) (root.regs 1)).length root := by
    apply StepsOk.mono _ (SafegcdTermination.CodeStack.steps_of_run hRun hf hStack)
    intro x f h
    exact ⟨h.1.1,h.1.2.1,h.1.2.2,by change invR.SpP s x.sp; rw [h.2,hrSp]; exact hSp⟩
  have hSrcEq : feVal t.mem (s.regs 1) = feVal s.mem (s.regs 1) := by
    apply feVal_congr
    intro y hy
    apply htMem
    intro hh
    have hSub : Sub [saved mask s] [invR.win s] := by
      intro a ha
      rw [List.mem_singleton] at ha
      subst a
      have hroom : 384 ≤ s.sp.toNat := e.room
      have hs := s.sp.isLt
      have h₁ : (s.sp - 8#32).toNat = s.sp.toNat - 8 := by
        rw [BitVec.toNat_sub]
        change (2^32 - 8 + s.sp.toNat) % 2^32 = _
        omega
      have h₂ : (s.sp - 384#32).toNat = s.sp.toNat - 384 := by
        rw [BitVec.toNat_sub]
        change (2^32 - 384 + s.sp.toNat) % 2^32 = _
        omega
      refine ⟨invR.win s, List.mem_singleton_self _, ?_, ?_, ?_⟩
      · change (s.sp - 384#32).toNat ≤ (s.sp - 8#32).toNat
        rw [h₁, h₂]
        omega
      · change (s.sp - 8#32).toNat + 8 ≤ (s.sp - 384#32).toNat + 384
        rw [h₁, h₂]
        omega
      · change (s.sp - 384#32).toNat + 384 ≤ 2^32
        rw [h₂]
        omega
    exact Sep.not_has e.sepRd hy (hSub.has hh)
  have he2 : base.toNat % 2 = 0 := by have h := e.base4; omega
  have hReturn : u.pc = base + BitVec.ofNat 32 epiSite := by
    rw [hv.pc, show root.regs 14 = _ from entered_lr _ _ _ _, linkedRet_clear he2 (by decide)]
    rfl
  have hPost : invR.Post s u.mem (u.regs 0) := by
    have hv' := hv.value
    rw [hr0,hr1,hrMem,hSrcEq] at hv'
    rw [show SafegcdTermination.p.toNat-2 = powE 0 by decide +kernel] at hv'
    exact hv'
  have hR : ReachFT base (invR.PcP base) (invR.RdP base s) (Has (lowWin invR mask s :: invR.wr s))
      (invR.SpP s) root (fun u => u.pc = base+BitVec.ofNat 32 epiSite ∧ u.sp = t.sp ∧
        (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ invR.clob → u.regs r = s.regs r) ∧
        invR.Post s u.mem (u.regs 0))
      (Tr.is (layout.trace base root.sp (root.regs 0) (root.regs 1))) :=
    ⟨_,u,_,hRun,hSteps,⟨hReturn,hv.sp.trans hrSp,
      fun r h4 h11 _ hn => absurd (Ed25519Routines.mem_hiRegs h4 h11) hn,hPost⟩,rfl⟩
  have hCall : seqAt b.bytes callSite [invoke] = true := by cases b <;> decide +kernel
  have hB := call_at he2 (checked b).length htPc (by decide : callSite % 2 = 0)
    (by decide : callSite+4 < 2^23) (by decide : fe_inv_shared < 2^23) hCall
  have hAt : invR.PcP base t.pc := by
    rw [htPc]
    apply PcIn.at (lo := fe_inv) (hi := layout.first) (off := callSite) <;> decide +kernel
  have hAll := ReachT.cons hB (show Step (invR.PcP base) (invR.RdP base s)
      (Has (lowWin invR mask s :: invR.wr s)) (invR.SpP s) t ⟨t.pc,invoke,[]⟩ from
      ⟨hAt, fun y h => absurd h (writes_nil y),fun y h => absurd h (reads_nil y),hSp⟩) hR
  simpa only [Tr.cat_is_is,middleTrace,invoke,htPc,hrSp,hr0,hr1,List.singleton_append] using hAll

private def workSp (sp : Word) : Word :=
  sp - BitVec.ofNat 32 (4*nSaved mask) - BitVec.ofNat 32 (4*slots)

private theorem workSp_eq (sp : Word) : workSp sp = sp - 384#32 := by
  change sp - 8#32 - 376#32 = _
  bv_omega

private def frameTrace (base sp : Word) (mid : List Event) : List Event :=
  [⟨base+BitVec.ofNat 32 fe_inv, .push mask true,
    wordAccesses .write (sp-BitVec.ofNat 32 (4*nSaved mask)) (nSaved mask)⟩,
   ⟨base+BitVec.ofNat 32 (fe_inv+2),.subSp (BitVec.ofNat 7 slots),[]⟩] ++
    (mid ++
      [⟨base+BitVec.ofNat 32 epiSite,.addSp (BitVec.ofNat 7 slots),[]⟩,
       ⟨base+BitVec.ofNat 32 (epiSite+2),.pop mask true,
         wordAccesses .read (sp-BitVec.ofNat 32 (4*nSaved mask)) (nSaved mask)⟩])

private theorem frame_trace (base sp : Word) (mid : List Event) :
    frameTr base fe_inv epiSite mask slots sp (Tr.is mid) = Tr.is (frameTrace base sp mid) := by
  simp only [frameTr, frameTrace, Tr.cat_is_is, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]

private def wrapperTrace (base sp dst src : Word) : List Event :=
  frameTrace base sp (middleTrace base (workSp sp) dst src)

private theorem spec (b : Build) : letI := b.codeBytes
    invR.SpecT (fun base s => Tr.is (wrapperTrace base s.sp (s.regs 0) (s.regs 1))) := by
  letI := b.codeBytes
  intro base s e
  have hT := ReachFT.frameK (f := invR) (mask := mask) (k := slots) (epi := epiSite)
    (sp := s.sp) (Ψ := Tr.is (middleTrace base (workSp s.sp) (s.regs 0) (s.regs 1)))
    (by intro x hx; revert x; decide)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by decide) (by decide) (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by decide +kernel) (by decide) (by decide +kernel) e rfl
    (fun t hp hs hr hm hc => by
      have hw : t.sp = (invR.win s).a := by
        have he : invR.stack = 4*nSaved mask + 4*slots := by decide +kernel
        change t.regs 13 = s.regs 13 - BitVec.ofNat 32 invR.stack
        rw [he]
        exact hs
      apply ReachT.retrace (body e t hp hw (hr 0 (by decide) (by decide))
        (hr 1 (by decide) (by decide)) hm hc)
      rw [show t.sp = workSp s.sp from hs.trans (workSp_eq s.sp).symm])
  exact ReachT.retrace hT (frame_trace base s.sp _)

private def alignedBase (base : Word) : Word := base &&& ~~~3#32

private theorem base4 (base : Word) : (alignedBase base).toNat % 4 = 0 := by
  rw [alignedBase,Frame.and_not3_toNat]
  omega

private theorem align_eq {base : Word} (h : base.toNat % 4 = 0) : alignedBase base = base := by
  apply BitVec.eq_of_toNat_eq
  simp only [alignedBase,Frame.and_not3_toNat,h,Nat.sub_zero]

private def trace (base : Word) (p : Nat → Word) : List Event :=
  wrapperTrace (alignedBase base) (invS.reg p 13) (invS.reg p 0) (invS.reg p 1)

private theorem literal_in_code {b : Build} {base y : Word}
    (h : layout.literalRegion (alignedBase base) y) :
    letI := b.codeBytes
    Has [codeR base] y := by
  letI := b.codeBytes
  let off := layout.first + layout.targets.literal
  have hlo : 3 ≤ off := by decide
  have hhi : off+4 ≤ b.size := by cases b <;> decide
  have hd : alignedBase base = base - BitVec.ofNat 32 (base.toNat % 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [alignedBase,Frame.and_not3_toNat,BitVec.toNat_sub,BitVec.toNat_ofNat]
    have := base.isLt
    omega
  have hL : alignedBase base+BitVec.ofNat 32 layout.first+BitVec.ofNat 32 layout.targets.literal =
      base+BitVec.ofNat 32 (off-base.toNat % 4) := by
    rw [hd,ofNat_add_assoc]
    change base - BitVec.ofNat 32 (base.toNat % 4) + BitVec.ofNat 32 off = _
    have he : off = off-base.toNat%4+base.toNat%4 := by omega
    conv => lhs; rw [he,BitVec.ofNat_add]
    bv_omega
  obtain ⟨j,hj,rfl⟩ := h.exists
  refine ⟨codeR base,List.mem_singleton_self _,off-base.toNat%4+j,?_,?_⟩
  · change _ < b.size
    omega
  · change _ = base+BitVec.ofNat 32 (off-base.toNat%4+j)
    rw [hL,ofNat_add_assoc]

private theorem trace_effect (b : Build) (base : Word) (p : Nat → Word) :
    letI := b.codeBytes
    invS.Eff p base (trace base p) := by
  letI := b.codeBytes
  let a := alignedBase base
  let sp := invS.reg p 13
  let dst := invS.reg p 0
  let src := invS.reg p 1
  let d := workSp sp
  let S := Region (sp-BitVec.ofNat 32 (4*nSaved mask)) (4*nSaved mask)
  let D := Region dst 32
  let F := invS.Fp p base
  let R := invS.Rq p base
  let T := layout.trace a d dst src
  have sBytes : invS.stack = 384 := by decide +kernel
  have hDst : ∀ y, D y → F y := fun y hy =>
    has_region (by simp [F,CalleeS.Fp,invS,ioPow,calleeAt,rgnsC,SRgn.rgnC,ALen.val,dst]) hy
  have hSrc : ∀ y, Region src 32 y → F y := fun y hy =>
    has_region (by simp [F,CalleeS.Fp,invS,ioPow,calleeAt,rgnsC,SRgn.rgnC,ALen.val,src]) hy
  have hLit : ∀ y, layout.literalRegion a y → Has [codeR base] y := fun y h =>
    literal_in_code (b := b) h
  have hRin : ∀ y, layout.required a src y → R y := by
    rintro y (hy | hy)
    · refine .inr ⟨(1,0,.view .fe),by simp [invS,ioPow,calleeAt],?_⟩
      simpa [src,CalleeS.iniIn,Kd.sz] using hy
    · exact .inl (hLit y hy)
  have hOut : ∀ y, invS.Wd p y → D y := by
    intro y ⟨o,ho,hy⟩
    simp only [invS,calleeAt,ioPow,List.mem_singleton] at ho
    subst o
    simpa [D,dst,CalleeS.iniOut,Kd.sz] using hy
  change EffT invS.stack F R (invS.Wd p) sp (wrapperTrace a sp dst src)
  refine EffT.mono ?_ (Nat.le_refl invS.stack) (fun _ h => h) (fun _ h => h) hOut
  refine effT_of_gp fun sp0 n U hroom hn hF hR => ?_
  have hRoom : (sp0-sp).toNat + 384 < 2^32 := by rw [sBytes] at hroom; omega
  have dpos : (sp0-d).toNat ≤ n := by
    have he : sp0-d = (sp0-sp)+384#32 := by
      rw [show d = sp - 384#32 from workSp_eq sp]
      bv_omega
    rw [he,BitVec.toNat_add,show (384#32).toNat = 384 from rfl]
    rw [sBytes] at hroom
    omega
  let Ini := fun y => U y ∨ S y
  let Out := fun y => Ini y ∨ D y ∧ BelowEntry sp0 n y
  have hCoreEff := LinkedInversion.stack_effect_aligned (checked b) (base4 base) d dst src
  have hLower : d = sp - 384#32 := workSp_eq sp
  have hCode (y : Word) (h : Has [codeR base] y) : F y :=
    h.append_left (rgnsC (invS.reg p) invS.io.rd ++ rgnsC (invS.reg p) invS.io.wr)
  have hAbove : ∀ y, layout.footprint a d dst src y → BelowEntry sp0 n y → AtOrAboveSp sp0 d y := by
    rintro y (h | h | h) hb <;> rw [hLower]
    · rw [hLower] at h
      exact reg_sub_above (d := 384) h (by decide : frameBytes ≤ 384) hRoom
    · exact above_sub (hF y (hDst y h) hb) hRoom
    · rcases h with h | h
      · exact above_sub (hF y (hSrc y h) hb) hRoom
      · exact above_sub (hF y (hCode y (hLit y h)) hb) hRoom
  have hG : GP sp0 n (SIR sp0 d Ini) (Tr.is T) (SIR sp0 d Out) :=
    gp_effT hCoreEff (by simpa only [Nat.add_zero] using dpos) hn hAbove
      (fun y h hb => .inl (hR y (hRin y h) hb))
  have hB : GP sp0 n (SIR sp0 d Ini) (Tr.is (middleTrace a d dst src)) (SIR sp0 d Out) := by
    have hA : GP sp0 n (SIR sp0 d Ini)
        (Tr.is [⟨a+BitVec.ofNat 32 callSite,invoke,[]⟩]) (SIR sp0 d Ini) :=
      sir_quietC rfl rfl rfl
    exact GP.is_of (hA.cat hG) ⟨_,_,rfl,rfl,rfl⟩
  refine GP.is_of (Φ := frameTr a fe_inv epiSite mask slots sp (Tr.is (middleTrace a d dst src))) ?_ ?_
  · apply frameK_gp (U := U) (R2 := Out) (by decide) hRoom hB
      (fun _ h => .inl (.inr h)) _ (fun _ h => .inl (.inl h))
    intro y h
    rcases h with h | h
    · exact .inl h
    · exact .inr ⟨hF y (hDst y h.1) h.2,.inr h⟩
  · rw [frame_trace]
    exact rfl

private def te (b : Build) : letI := b.codeBytes
    invR.TE invS.pub (fun base p => invS.Eff p base) := by
  letI := b.codeBytes
  refine ⟨trace,?_,trace_effect b⟩
  intro base s e
  have hn := align_eq e.base4
  have hr0 : invS.reg (invS.pub base s) 0 = s.regs 0 := rfl
  have hr1 : invS.reg (invS.pub base s) 1 = s.regs 1 := rfl
  have hr13 : invS.reg (invS.pub base s) 13 = s.sp := rfl
  simpa only [trace,hn,hr0,hr1,hr13] using spec b base s e

/-- Shared inversion as a two-argument internal field call. -/
noncomputable def invAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) invS :=
  letI := b.codeBytes
  Ad.ofTSpec invR rfl rfl rfl (te b) (fun _ _ _ h => h) (powSem 0)
    (fun _ _ _ _ _ hg _ _ => ⟨hg.1 0 (by decide),hg.1 1 (by decide)⟩)
    (fun _ => by simp [invR,invS,ioPow,calleeAt,rgnsC,SRgn.rgnC,ALen.val])
    (fun _ => by simp [invR,invS,ioPow,calleeAt,rgnsC,SRgn.rgnC,ALen.val])
    fun _ _ _ _ _ vs _ hi hp => by
      rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, invS, calleeAt, ioPow, Rel, In.kd, and_false, false_and, and_true] at hi
      simp only [OutsRel, All2, invS, calleeAt, ioPow, powSem, Rel, BitVec.add_zero, and_true] at hi ⊢
      exact ModP.trans hp (ModP.pow hi _)

end M0Crypto.Release.Ed25519Safegcd
