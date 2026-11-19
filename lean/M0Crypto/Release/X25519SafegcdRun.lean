import M0Crypto.Release.X25519SafegcdSave

namespace M0Crypto.Release.X25519SafegcdRun

open M0Crypto.Armv6M (Mem State Word)
open M0Crypto.Release (Region)
open M0Crypto.Release.X25519Layout M0Crypto.Release.X25519SafegcdCode
open M0Crypto.Release.X25519SafegcdFrame M0Crypto.Release.X25519SafegcdSave
open M0Crypto.Release.Frame (Disj ne_of_disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Thumb M0Crypto.Sym
open SafegcdRow.BatchCode (frameBytes callTo run_call execute_pre entered)
open SafegcdTermination
open SafegcdTermination.Bank (WritesOnly addr)
open SafegcdTermination.FrameWords (keep_field restrict_frame WritesOnly.trans)
open SafegcdTermination.RowCalls (entered_regs entered_pc entered_sp entered_mem entered_lr linkedRet_clear linkedRet_odd)
open SafegcdTermination.PublicTrace (stackState stack_trace)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

structure Pre (code : List (BitVec 8)) (base : Word) (off : Nat) (s : State) : Prop where
  pc : s.pc = base + BitVec.ofNat 32 off
  base4 : base.toNat % 4 = 0
  even : off % 2 = 0
  bytes : CodeAt s.mem base code
  space : Space s.sp
  disj : Disj base code.length (workSp s.sp) span

structure Complete (s t : State) : Prop where
  sp : t.sp = s.sp
  x2 : feVal t.mem (addr s.sp sX2) = feVal s.mem (addr s.sp sX2)
  inv : ModP (feVal t.mem (addr s.sp sZ2)) ((feVal s.mem (addr s.sp sZ2) : Int) ^ (2^255-21))
  outside : WritesOnly s.mem t.mem (workSp s.sp) span

def trace (l : LinkedInversion.Layout) (base sp : Word) (off : Nat) : List Event :=
  traceAll before (stackState (base+BitVec.ofNat 32 off) sp) ++
    (⟨base+BitVec.ofNat 32 (callSite off),callTo (callSite off) (l.first+l.start),[]⟩ ::
      l.trace base (workSp sp) (addr sp sZ2) (addr sp sZ2)) ++
    traceAll after (stackState (base+BitVec.ofNat 32 (afterSite off)) (workSp sp))

/-- Instruction addresses and writes of the shared part of the wrapper. -/
def CoreEvents (l : LinkedInversion.Layout) (base sp : Word) : Prop :=
  ∀ e ∈ l.trace base (workSp sp) (addr sp sZ2) (addr sp sZ2),
    Region (base + BitVec.ofNat 32 l.first) l.length e.pc ∧
      ∀ y, Writes e.accesses y → Region (workSp sp) frameBytes y

private theorem copy_in_span {m m' : Mem} {sp : Word} {o : Nat} (ho : borrowed+o+32 ≤ span)
    (h : WritesOnly m m' (addr sp o) 32) : WritesOnly m m' (workSp sp) span := by
  rw [rebase] at h
  exact restrict_frame ho h

private theorem keep_code {code : List (BitVec 8)} {base : Word} {s t : State} {off : Nat}
    (h : Pre code base off s) (hw : WritesOnly s.mem t.mem (workSp s.sp) span) : CodeAt t.mem base code := by
  intro i hi
  exact (hw _ (fun k hk => ne_of_disj h.disj.1 h.disj.2.1 h.disj.2.2 hi hk)).trans (h.bytes i hi)

theorem call_pre {l : LinkedInversion.Layout} {code : List (BitVec 8)} {base old : Word} {off : Nat}
    {s : State} (hBase : base.toNat % 4 = 0) (hSpace : Space old)
    (hDisj : Disj base code.length (workSp old) span) (hCode : CodeAt s.mem base code)
    (hSp : s.sp = workSp old) (hOut : s.regs 0 = addr old sZ2) (hSrc : s.regs 1 = addr old sZ2) :
    LinkedInversion.Pre (entered base off (l.first+l.start) s) base code l := by
  let e := entered base off (l.first+l.start) s
  have es : e.sp = workSp old := (entered_sp _ _ _ _).trans hSp
  have e0 : e.regs 0 = addr old sZ2 := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hOut
  have e1 : e.regs 1 = addr old sZ2 := (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hSrc
  have em : e.mem = s.mem := entered_mem _ _ _ _
  refine ⟨entered_pc _ _ _ _,hBase,?_,?_,?_,?_,source_ok hSpace es e1,?_,?_⟩
  · rwa [em]
  · rw [es]
    simpa [addr] using cut (o := 0) hDisj (by decide : 0 < frameBytes) (by decide)
  · rw [e0,rebase]
    exact cut hDisj (by decide) (by decide)
  · rw [es]
    exact frame_ok hSpace
  · rw [es,e0]
    exact output_ok hSpace
  · rw [show e.regs 14 = _ from entered_lr _ _ _ _]
    exact linkedRet_odd _ _

/-- During the inversion `Z2` may alias a dead bank. Its result and every write
    of the callee stay in the borrowed frame, away from parked `X2`. -/
private theorem call_frame {s a b : State} (hA : Saved s a)
    (h : RunFinal.WritesFrameAndOut a.mem b.mem a.sp (addr s.sp sZ2)) :
    WritesOnly a.mem b.mem a.sp frameBytes := by
  intro y hy
  apply h y hy
  intro i hi he
  have hb : borrowed+sZ2+32 ≤ frameBytes := by decide
  apply hy (borrowed+sZ2+i) (by omega)
  rw [he, rebase s.sp sZ2, ← hA.sp]
  simp only [addr,ofNat_add_assoc]

private theorem aligned_block (s : State) (is : List Instr) (hSp : s.sp.toNat % 4 = 0)
    (hf : is.all Instr.falls = true) (hc : alignChk [(13,4)] is = true) :
    alignedAll is s = true := by
  apply alignChk_sound [(13,4)] is (sound_all hf) s ?_ hc
  intro p hp
  rw [List.mem_singleton] at hp
  subst p
  exact hSp

theorem run {l : LinkedInversion.Layout} {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (link : LinkedInversion.Checked l code) (linked : Linked code off (l.first+l.start))
    (hSmall : code.length < 2^23) (h : Pre code base off s) :
    ∃ t, runH code base (trace l base s.sp off).length s = .ok (t,trace l base s.sp off) ∧
      t.pc = base + BitVec.ofNat 32 (afterSite off + seqSize after) ∧ Complete s t ∧ CoreEvents l base s.sp := by
  have hEven : base.toNat % 2 = 0 := by have := h.base4; omega
  let a := execAll before s
  have hA : Saved s a := save s h.space
  have ha4 : a.sp.toNat % 4 = 0 := by rw [hA.sp]; exact (frame_ok h.space).1
  have ⟨hARun,hAPc⟩ := execute_pre hEven link.length h.pc h.even linked.pre (by decide)
    (aligned_block s before h.space.1 (by decide) (by decide +kernel))
  let c := callSite off
  let d := l.first+l.start
  let u := entered base c d a
  have hc : c % 2 = 0 := by
    have ho := h.even
    have hl := seqSize_mod_two before
    dsimp only [c,callSite]
    omega
  have hcBound : c+4 < 2^23 := by
    have hd := (seqAt_size _ _ _ linked.call).resolve_right (by simp)
    change c+4 ≤ code.length at hd
    omega
  have hdBound : d < 2^23 := by
    have hp := (seqAt_size _ _ _ link.place.init.save).resolve_right (by decide)
    have hw : (l.window code).length ≤ l.length := by
      simp only [LinkedInversion.Layout.window,List.length_take]
      exact Nat.min_le_left _ _
    have hl := link.bounds
    dsimp only [d]
    omega
  have hu : LinkedInversion.Pre u base code l :=
    call_pre h.base4 h.space h.disj (keep_code h (copy_in_span (by decide) hA.outside)) hA.sp hA.out hA.src
  obtain ⟨b,hB,hInv,_,hWrites,hPCs⟩ := LinkedInversion.run link hu
  have huSp : u.sp = a.sp := entered_sp _ _ _ _
  have hu0 : u.regs 0 = addr s.sp sZ2 :=
    (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hA.out
  have hu1 : u.regs 1 = addr s.sp sZ2 :=
    (entered_regs _ _ _ _ _ (by decide) (by decide)).trans hA.src
  have huM : u.mem = a.mem := entered_mem _ _ _ _
  have hbSp : b.sp = workSp s.sp := hInv.sp.trans (huSp.trans hA.sp)
  have hbPc : b.pc = base + BitVec.ofNat 32 (afterSite off) := by
    rw [hInv.pc,show u.regs 14 = _ from entered_lr _ _ _ _,linkedRet_clear hEven hc]
    rfl
  have hbRun := run_call hEven link.length hAPc hc hcBound hdBound linked.call hB
  have hbW := hInv.outside
  rw [huM,huSp,hu0] at hbW
  have hbFrame := call_frame hA hbW
  have hbKeep := keep_field (dst := 0) (off := frameBytes) (hInv.sp.trans huSp)
    (by simpa [addr] using hbFrame : WritesOnly a.mem b.mem (addr a.sp 0) frameBytes)
    (by decide) (by decide) (.inr (by omega))
  have hbPark : feVal b.mem (addr s.sp parked) = feVal s.mem (addr s.sp sX2) := by
    rw [hbSp,hA.sp] at hbKeep
    rw [rebase s.sp parked,show borrowed+parked = frameBytes by decide]
    exact hbKeep.trans (by rw [← hA.park,rebase s.sp parked,show borrowed+parked = frameBytes by decide])
  have hbInv : ModP (feVal b.mem (addr s.sp sZ2)) ((feVal s.mem (addr s.sp sZ2) : Int) ^ (2^255-21)) := by
    have hh := hInv.value
    rw [hu0,hu1,huM,hA.value,show p.toNat-2 = 2^255-21 by decide +kernel] at hh
    exact hh
  have hb4 : b.sp.toNat % 4 = 0 := by rw [hbSp,← hA.sp]; exact ha4
  have hoEven : (afterSite off) % 2 = 0 := by unfold afterSite; change c % 2 = 0 at hc; omega
  obtain ⟨htRun,htPc⟩ := execute_pre hEven link.length hbPc hoEven linked.post (by decide)
    (aligned_block b after hb4 (by decide) (by decide +kernel))
  obtain ⟨htSp,htX,htZ,htW⟩ := restore b s.sp h.space hbSp
  have hSaved := copy_in_span (o := parked) (by decide) hA.outside
  have hRestored := copy_in_span (o := sX2) (by decide) htW
  have hbSpan : WritesOnly a.mem b.mem (workSp s.sp) span := by
    rw [hA.sp] at hbFrame
    simpa [addr] using restrict_frame (by decide : 0+frameBytes ≤ span)
      (by simpa [addr] using hbFrame : WritesOnly a.mem b.mem (addr (workSp s.sp) 0) frameBytes)
  have hFoot := WritesOnly.trans (WritesOnly.trans hSaved hbSpan) hRestored
  have hTrA := stack_trace (is := before) (by decide) (by decide +kernel) s
  have hTrT := stack_trace (is := after) (by decide) (by decide +kernel) b
  have hTr := runH_compose (runH_compose hARun hbRun) htRun
  rw [hTrA,h.pc,hAPc,hu0,hu1,huSp,hA.sp,hTrT,hbPc,hbSp] at hTr
  have hLen := SafegcdTermination.CodeWindow.run_length hTr
  rw [hLen] at hTr
  refine ⟨execAll after b,?_,htPc,⟨htSp,htX.trans hbPark,?_,hFoot⟩,?_⟩
  · simpa only [trace,c,d,callSite,List.append_assoc] using hTr
  · rw [htZ]
    exact hbInv
  · have hLen : (l.window code).length = l.length := by
      simp only [LinkedInversion.Layout.window,List.length_take,List.length_drop]
      exact Nat.min_eq_left (by have h := link.bounds; omega)
    rw [hLen,hu0,hu1,huSp,hA.sp] at hPCs
    change SafegcdTermination.EndFootprint.OutWrites _ _ _ at hWrites
    rw [hu0,hu1,huSp,hA.sp] at hWrites
    intro e he
    refine ⟨hPCs e he,?_⟩
    intro y hy
    rcases hWrites e he y hy with h | h
    · exact h
    · rw [rebase] at h
      exact TraceWrites.subregion (by decide : borrowed+sZ2+32 ≤ frameBytes) h

end M0Crypto.Release.X25519SafegcdRun
