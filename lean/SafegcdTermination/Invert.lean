import SafegcdTermination.RunFinal

namespace SafegcdTermination.Invert

open SafegcdRow SafegcdRow.BatchCode
open SafegcdTermination.Bank SafegcdTermination.FrameWords
open SafegcdTermination.Literal (LiteralLinks literal_of_link)
open SafegcdTermination.FinalSelect (OutputOk)
open SafegcdTermination.RunFinal (Result)
open SafegcdTermination.RunInit (SourceOk)
open SafegcdTermination.Run43 (forty_three)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj ne_of_disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Reduce (pN)

set_option maxHeartbeats 1000000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false

structure Place (code : List (BitVec 8)) (q : Targets) (start canon entry done sub select : Nat) : Prop where
  length : code.length < 2^23
  startEven : start % 2 = 0
  entryEven : entry % 2 = 0
  doneEven : done % 2 = 0
  init : RunInit.Place code start canon
  joined : RunInit.loopSite start = entry
  loop : LoopLinks.Place code q entry done
  literal : LiteralLinks code q entry done
  final : RunFinal.Place code q done sub select

structure Pre (s : State) (base : Word) (code : List (BitVec 8)) (o : Nat) : Prop where
  pc : s.pc = base + BitVec.ofNat 32 o
  baseAligned : base.toNat % 4 = 0
  bytes : CodeAt s.mem base code
  codeFrame : Disj base code.length s.sp frameBytes
  codeOutput : Disj base code.length (s.regs 0) 32
  frame : FrameOk s.sp
  src : SourceOk s
  dst : OutputOk s.sp (s.regs 0)
  ret : (s.regs 14).getLsbD 0 = true

theorem code_after_frame {code : List (BitVec 8)} {base : Word} {s t : State}
    (hc : CodeAt s.mem base code) (hd : Disj base code.length s.sp frameBytes)
    (hw : WritesOnly s.mem t.mem s.sp frameBytes) : CodeAt t.mem base code := by
  intro i hi
  exact (hw _ (fun k hk => ne_of_disj hd.1 hd.2.1 hd.2.2 hi hk)).trans (hc i hi)

theorem code_after_result {code : List (BitVec 8)} {base : Word} {s t : State} {start : Nat}
    (h : Pre s base code start) (hF : RunFinal.WritesFrameAndOut s.mem t.mem s.sp (s.regs 0)) :
    CodeAt t.mem base code := by
  intro i hi
  have h1 := h.codeFrame
  have h2 := h.codeOutput
  exact (hF _ (fun k hk => ne_of_disj h1.1 h1.2.1 h1.2.2 hi hk)
    (fun k hk => ne_of_disj h2.1 h2.2.1 h2.2.2 hi hk)).trans (h.bytes i hi)

private theorem canonical_as_int (x : Nat) : ((x % pN : Nat) : Int) = (x : Int) % p := by
  rw [Int.natCast_emod, show (pN : Int) = p by decide +kernel]

def inversionTrace (q : Targets) (base sp dst src : Word) (start canon entry done sub select : Nat) : List Event :=
  RunInit.initTrace base sp src start canon ++ Run43.loopTrace q base sp entry done ++
    RunFinal.finalTrace q base sp dst done sub select

/-- Functional, frame and return-PC contract for the shared assembled inversion.
    The destination may alias the input, including when both are in the frame. -/
theorem functional {code : List (BitVec 8)} {q : Targets} {base : Word} {s : State}
    {start canon entry done sub select : Nat}
    (linked : Place code q start canon entry done sub select) (h : Pre s base code start) :
    ∃ t n, runH code base n s = .ok (t, inversionTrace q base s.sp (s.regs 0) (s.regs 1) start canon entry done sub select) ∧
      Result s t (s.regs 0) (s.regs 14) (feVal s.mem (s.regs 1)) ∧ CodeAt t.mem base code := by
  let x : Nat := feVal s.mem (s.regs 1)
  let z : Int := (x : Int) % p
  have hBase : base.toNat % 2 = 0 := by have := h.baseAligned; omega
  obtain ⟨a,na,hA,hAP,hInit⟩ := RunInit.run_init s hBase linked.length linked.startEven h.pc h.frame h.src linked.init
  have hz : 0 ≤ z := Int.emod_nonneg _ (Int.ne_of_gt p_pos)
  have hzp : z < p := Int.emod_lt_of_pos _ p_pos
  have hCanon : ((x % pN : Nat) : Int) = z := canonical_as_int x
  have hFrame : FrameOk a.sp := by rw [hInit.sp]; exact h.frame
  have hCode : CodeAt a.mem base code := code_after_frame h.bytes h.codeFrame hInit.outside
  have hSep : Disj base code.length a.sp frameBytes := by rw [hInit.sp]; exact h.codeFrame
  have hLoop : RunLoop.Entry code base q entry done a z :=
    ⟨hBase,linked.length,linked.entryEven,linked.loop,hFrame,hz,hzp,
      fun i => literal_of_link linked.literal h.baseAligned hCode hSep i⟩
  have hAP' : a.pc = base + BitVec.ofNat 32 entry := by rwa [linked.joined] at hAP
  have hImage := hInit.image
  change BatchMachine.Image a (phases 0) (initial ((x % pN : Nat) : Int)) at hImage
  rw [hCanon] at hImage
  obtain ⟨b,nb,hB,hBP,hLive,_⟩ := forty_three hLoop hImage hAP' hInit.counter
  have bS : b.sp = s.sp := hLive.sp.trans hInit.sp
  have hOut : OutputOk b.sp (s.regs 0) := by rw [bS]; exact h.dst
  obtain ⟨t,nt,hT,hFin⟩ := RunFinal.run_final hBase linked.length linked.doneEven hBP linked.final
    (by rw [bS]; exact h.frame) hOut h.ret hInit.output hInit.ret hz hzp hLive
  have hFinValue := hFin.value.trans ((Congruence.emod_left (x : Int) p).pow (p.toNat-2))
  have hFinFrame : RunFinal.WritesFrameAndOut s.mem t.mem s.sp (s.regs 0) := by
    intro y hy hd
    exact (hFin.outside y (by rwa [bS]) hd).trans
      ((hLive.outside y (by rwa [hInit.sp])).trans (hInit.outside y hy))
  have hZero : (x : Int) % p = 0 → feVal t.mem (s.regs 0) = 0 := by
    intro h0
    exact hFin.zero (by change ((x : Int) % p) % p = 0; rw [h0]; rfl)
  rw [hInit.sp] at hB
  rw [bS] at hT
  refine ⟨t,na+nb+nt,?_,⟨hFinValue,hZero,hFinFrame,hFin.sp.trans bS,hFin.pc⟩,code_after_result h hFinFrame⟩
  simpa only [inversionTrace,List.append_assoc] using runH_compose (runH_compose hA hB) hT

end SafegcdTermination.Invert
