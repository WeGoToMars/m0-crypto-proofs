import SafegcdTermination.Verified
import SafegcdTermination.TraceReads
import SafegcdTermination.TraceCoverage
import SafegcdTermination.CodeStack

namespace SafegcdTermination.LinkedInversion

open SafegcdRow.BatchCode
open SafegcdTermination.Bank (FrameOk)
open SafegcdTermination.CodeWindow (run_in_artifact codeAt_slice)
open SafegcdTermination.EndFootprint (OutWrites writes)
open SafegcdTermination.FinalSelect (OutputOk)
open SafegcdTermination.Invert (inversionTrace)
open SafegcdTermination.RunInit (SourceOk)
open M0Crypto.Armv6M (State Word)
open M0Crypto.Thumb
open M0Crypto.Release (Region ReadsFrom)
open M0Crypto.Release.Frame (Disj ne_of_disj toNat_add_ofNat)
open M0Crypto.Release.Field25519Routines (feVal)

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-- All inversion offsets other than `first` are relative to the window. -/
structure Layout where
  first : Nat
  length : Nat
  targets : Targets
  start : Nat
  canon : Nat
  loop : Nat
  final : Nat
  sub : Nat
  select : Nat

def Layout.window (l : Layout) (code : List (BitVec 8)) : List (BitVec 8) :=
  (code.drop l.first).take l.length

def Layout.trace (l : Layout) (base sp dst src : Word) : List Event :=
  inversionTrace l.targets (base + BitVec.ofNat 32 l.first) sp dst src
    l.start l.canon l.loop l.final l.sub l.select

structure Checked (l : Layout) (code : List (BitVec 8)) : Prop where
  length : code.length < 2^32
  nonempty : 0 < l.length
  bounds : l.first + l.length ≤ code.length
  start : l.first % 4 = 0
  stack : CodeStack.check (l.window code) = true
  place : Invert.Place (l.window code) l.targets l.start l.canon l.loop l.final l.sub l.select

structure Pre (s : State) (base : Word) (code : List (BitVec 8)) (l : Layout) : Prop where
  pc : s.pc = base + BitVec.ofNat 32 (l.first+l.start)
  baseAligned : base.toNat % 4 = 0
  bytes : CodeAt s.mem base code
  codeFrame : Disj base code.length s.sp frameBytes
  codeOutput : Disj base code.length (s.regs 0) 32
  frame : FrameOk s.sp
  src : SourceOk s
  dst : OutputOk s.sp (s.regs 0)
  ret : (s.regs 14).getLsbD 0 = true

private theorem disj_window {code : List (BitVec 8)} {base a : Word} {l : Layout} {n : Nat}
    (link : Checked l code) (h : Disj base code.length a n) :
    Disj (base + BitVec.ofNat 32 l.first) (l.window code).length a n := by
  have hLen : (l.window code).length = l.length := by
    simp only [Layout.window,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by have := link.bounds; omega)
  have hb := link.bounds
  have hn := link.nonempty
  have h0 := h.1
  have h1 := h.2.1
  rw [hLen,Disj,toNat_add_ofNat _ _ (by omega)]
  refine ⟨by omega,h1,?_⟩
  rcases h.2.2 with h | h
  · left; omega
  · right; omega

private theorem window_pre {l : Layout} {code : List (BitVec 8)} {base : Word} {s : State}
    (link : Checked l code) (h : Pre s base code l) :
    Invert.Pre s (base + BitVec.ofNat 32 l.first) (l.window code) l.start := by
  have hb := link.bounds
  have hn := link.nonempty
  have hc := h.codeFrame.1
  have ht := link.start
  refine ⟨by rw [ofNat_add_assoc]; exact h.pc,?_,codeAt_slice h.bytes,disj_window link h.codeFrame,
    disj_window link h.codeOutput,h.frame,h.src,h.dst,h.ret⟩
  rw [toNat_add_ofNat _ _ (by omega),Nat.add_mod, h.baseAligned,ht]

/-- The same inversion traces and field result hold in the actual containing artifact.
    An internal return address may be located elsewhere in that artifact. -/
theorem run {l : Layout} {code : List (BitVec 8)} {base : Word} {s : State}
    (link : Checked l code) (h : Pre s base code l) :
    let tr := l.trace base s.sp (s.regs 0) (s.regs 1)
    ∃ t, runH code base tr.length s = .ok (t,tr) ∧
      RunFinal.Result s t (s.regs 0) (s.regs 14) (feVal s.mem (s.regs 1)) ∧
      CodeAt t.mem base code ∧ OutWrites s.sp (s.regs 0) tr ∧
      ∀ e ∈ tr, M0Crypto.Release.Region (base + BitVec.ofNat 32 l.first) (l.window code).length e.pc := by
  obtain ⟨t,k,hRun,hResult,_⟩ := Invert.functional link.place (window_pre link h)
  have hLength := CodeWindow.run_length hRun
  have hFull := run_in_artifact link.length hRun
  rw [hLength] at hFull
  refine ⟨t,hFull,hResult,?_,writes _ _ _ _ _ _ _ _ _ _ _,CodeWindow.fetched_inside hRun⟩
  intro i hi
  have hf := h.codeFrame
  have ho := h.codeOutput
  rw [hResult.outside _ (fun k hk => ne_of_disj hf.1 hf.2.1 hf.2.2 hi hk)
    (fun k hk => ne_of_disj ho.1 ho.2.1 ho.2.2 hi hk)]
  exact h.bytes i hi

/-- The trace reads only from the frame, source, and linked correction literal,
    writes all output bytes, and keeps SP at each instruction. -/
theorem trace_io {l : Layout} {code : List (BitVec 8)} {base : Word} {s : State}
    (link : Checked l code) (h : Pre s base code l) :
    let tr := l.trace base s.sp (s.regs 0) (s.regs 1)
    ReadsFrom (fun y => Region s.sp frameBytes y ∨ Region (s.regs 1) 32 y ∨
      Region (base + BitVec.ofNat 32 (l.first + l.targets.literal)) 4 y) tr ∧
      TraceCoverage.Covers (Region (s.regs 0) 32) tr ∧
      ∀ e ∈ tr, (!(e.instr.dsts.contains 13)) = true := by
  have hw := window_pre link h
  have hReads := TraceReads.inversion (sp := s.sp) (dst := s.regs 0) (src := s.regs 1)
    (start := l.start) (canon := l.canon) (subOff := l.sub) (selectOff := l.select)
    link.place.literal hw.baseAligned
  obtain ⟨t,n,hRun,_,_⟩ := Invert.functional link.place hw
  have hEven : (base + BitVec.ofNat 32 l.first).toNat % 2 = 0 := by
    have := hw.baseAligned
    omega
  exact ⟨by simpa only [Layout.trace, ofNat_add_assoc] using hReads,
    TraceCoverage.output, CodeStack.trace_keeps_sp link.stack hEven hRun⟩

end SafegcdTermination.LinkedInversion
