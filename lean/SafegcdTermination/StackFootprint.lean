import SafegcdTermination.LinkedInversion
import SafegcdTermination.LoopStackEffect

namespace SafegcdTermination.LinkedInversion

open SafegcdRow.BatchCode (frameBytes)
open SafegcdTermination.InitStackEffect (Above Initialized)
open SafegcdTermination.InitCode (returnAt)
open SafegcdTermination.Bank (addr)
open SafegcdTermination.TraceReads (batchBytes)
open SafegcdTermination.TraceWrites (subregion)
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb M0Crypto.Release M0Crypto.Release.StackEffect

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000

def Layout.literalRegion (l : Layout) (base : Word) :=
  Region (base + BitVec.ofNat 32 l.first + BitVec.ofNat 32 l.targets.literal) 4

def Layout.required (l : Layout) (base src : Word) (y : Word) : Prop :=
  Region src 32 y ∨ l.literalRegion base y

def Layout.footprint (l : Layout) (base sp dst src : Word) (y : Word) : Prop :=
  Region sp frameBytes y ∨ Region dst 32 y ∨ l.required base src y

/-- Every internal stack byte read was written since the inversion call began.
    The source and correction literal may have been initialized by the caller. -/
theorem stack_effect {l : Layout} {code : List (BitVec 8)} {base : Word} {s : State}
    (link : Checked l code) (h : Pre s base code l) :
    EffT 0 (l.footprint base s.sp (s.regs 0) (s.regs 1)) (l.required base (s.regs 1))
      (Region (s.regs 0) 32) s.sp (l.trace base s.sp (s.regs 0) (s.regs 1)) := by
  let sp := s.sp
  let dst := s.regs 0
  let src := s.regs 1
  let win := base + BitVec.ofNat 32 l.first
  let trI := RunInit.initTrace win sp src l.start l.canon
  let trL := Run43.loopTrace l.targets win sp l.loop l.final
  let trF := RunFinal.finalTrace l.targets win sp dst l.final l.sub l.select
  let L := l.literalRegion base
  let R := l.required base src
  let F := l.footprint base sp dst src
  let D := Region dst 32
  have hFits := h.codeFrame.1
  have hStart := link.bounds
  have hFirst := link.nonempty
  have hNum : win.toNat = base.toNat+l.first :=
    Frame.toNat_add_ofNat base l.first (by omega)
  have hEven : win.toNat % 4 = 0 := by
    rw [hNum, Nat.add_mod, h.baseAligned, link.start]
  have hSize : (l.window code).length ≤ l.length := by
    simp only [Layout.window, List.length_take]
    exact Nat.min_le_left _ _
  have hLiteral := link.place.literal.1
  have hBound : win.toNat + l.targets.literal + 4 ≤ 2^32 := by
    rw [hNum]
    omega
  have hTrace : l.trace base sp dst src = (trI ++ trL) ++ trF := by
    simp only [Layout.trace, Invert.inversionTrace, trI, trL, trF, win, List.append_assoc]
  have hStack := (trace_io link h).2.2
  rw [hTrace] at hStack ⊢
  intro sp0 n e he _ _ hU hFoot hR
  have hs : e.sp = sp := he
  rw [hs] at hU hFoot ⊢
  have hAbove : Above sp0 n sp F := hFoot
  have hi : Seg sp0 n sp R trI (Initialized sp) :=
    (InitStackEffect.init win src l.start l.canon
      (fun y hy => hAbove y (hy.elim .inl (fun h => .inr (.inr (.inl h)))))).mono
      (fun _ h => .inl h) (fun _ h => h)
  have hl : Seg sp0 n sp (fun y => Initialized sp y ∨ L y) trL (Region sp batchBytes) :=
    LoopStackEffect.loop (sp0 := sp0) (n := n) (sp := sp) link.place.literal hEven hBound h.frame
      (fun f hf => hStack f (List.mem_append_left _ (List.mem_append_right _ hf)))
      (fun y hy => hAbove y (hy.elim .inl (fun h => .inr (.inr (.inr h)))))
  have hf : Seg sp0 n sp (fun y => Region sp batchBytes y ∨ Region (addr sp returnAt) 4 y) trF D :=
    (LoopStackEffect.closed (sp0 := sp0) (n := n) (sp := sp) (TraceReads.final l.targets win sp dst l.final l.sub l.select)
      (EndFootprint.final_writes l.targets win sp dst l.final l.sub l.select)
      (fun f hf => hStack f (List.mem_append_right _ hf))
      (fun y hy => hAbove y (hy.elim
        (fun h => .inl (h.elim (fun h => Nat.lt_of_lt_of_le h (by decide : batchBytes ≤ frameBytes))
          (subregion (by decide : returnAt+4 ≤ frameBytes))))
        (fun h => h.elim .inl (fun h => .inr (.inl h)))))).mono
      (fun _ h => h) (fun _ h => TraceCoverage.final_output _ h)
  let Known := fun y => Initialized sp y ∨ Region sp batchBytes y
  have hl' : Seg sp0 n sp (fun y => R y ∨ Initialized sp y) trL (Region sp batchBytes) :=
    hl.mono (fun _ hy => hy.elim .inr (fun h => .inl (.inr h))) (fun _ h => h)
  have hIL : Seg sp0 n sp R (trI ++ trL) Known := hi.append hl'
  have hf' : Seg sp0 n sp (fun y => R y ∨ Known y) trF D :=
    hf.mono (fun _ hy => hy.elim
      (fun h => .inr (.inr h)) (fun h => .inr (.inl (.inl (.inr h))))) (fun _ h => h)
  have hall : Seg sp0 n sp R ((trI ++ trL) ++ trF) D :=
    (hIL.append hf').mono (fun _ h => h) (fun _ h => .inr h)
  exact hall e hs hU hR

end SafegcdTermination.LinkedInversion
