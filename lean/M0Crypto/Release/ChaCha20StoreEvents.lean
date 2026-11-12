import M0Crypto.Release.ChaCha20Xor
import M0Crypto.Release.ConstantTime.OutputSelect
import M0Crypto.Release.ConstantTime.OutputPcBounds

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# Access events of a whole `m0c_chacha20_xor` call

Every call that satisfies the entry contract reaches its return address through an artifact
execution whose accesses obey `StorePolicy`: all writes lie in the frame or in the output
buffer, and a write made by one of the output-store instructions lies in the part of the
output buffer that the call may write. Reads are not bounded here.

The block loop reuses the per-block decomposition of the output proofs. The remaining parts
(prologue, key and nonce loads, epilogue, error exit and frame clearing) lie outside the
output-store instructions, so their writes need only the frame bound.
-/

namespace M0Crypto.Release.ChaCha20StoreEvents
open M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Layout (n1Off blsOff nxtOff bbackOff clrOff zOff epiOff errOff berrOff2 bpreOff
  achOff slotSaved chFrameWords chStackBytes)
open M0Crypto.Release.ChaCha20Xor (z_at err_at berr_at clr clr_at clr_end z_next err_next)

/-- Reads are unrestricted. A write lies in the frame or the output buffer, and a write made
by an output-store instruction lies in the output range of the call. -/
def StorePolicy (c : Ctx) (pc : Word) (kind : Kind) (y : Word) : Prop :=
  kind = .read ∨ (c.Wr y ∧ (OutputStorePC c.base pc → c.oidx y < c.len.toNat))

/-- The store policy, plus: loads made at caller-memory load instructions read readable bytes. -/
def RdPolicy (c : Ctx) (pc : Word) (kind : Kind) (y : Word) : Prop :=
  StorePolicy c pc kind y ∧ (kind = .read → ChaCha20Policy.SitePC c.base pc → TraceSpec.ChaCha20XorReadRegion c y)

theorem rdPolicy_of_nonSite (c : Ctx) {pc : Word} {kind : Kind} {y : Word}
    (hs : ¬ ChaCha20Policy.SitePC c.base pc) (hns : ¬ OutputStorePC c.base pc)
    (hw : writeOnlyPolicy c.Wr pc kind y) : RdPolicy c pc kind y :=
  ⟨hw.elim Or.inl (fun h => Or.inr ⟨h, fun hh => absurd hh hns⟩), fun _ hh => absurd hh hs⟩

theorem admitsRd_front (c : Ctx) :
    ChaCha20Policy.Admits (ChaCha20Policy.FrontPc c.base) c.Wr (RdPolicy c) := fun pc kind y hpc hw =>
  rdPolicy_of_nonSite c (ChaCha20Policy.not_sitePC_front hpc)
    (before_output_not_store c.base pc (ChaCha20Policy.frontPc_before hpc))
    (ChaCha20Policy.admits_writeOnly _ c.Wr pc kind y hpc hw)

theorem admitsRd_back (c : Ctx) :
    ChaCha20Policy.Admits (ChaCha20Policy.BackPc c.base) c.Wr (RdPolicy c) := fun pc kind y hpc hw =>
  rdPolicy_of_nonSite c (ChaCha20Policy.not_sitePC_back hpc) (after_output_not_store c.base pc hpc)
    (ChaCha20Policy.admits_writeOnly _ c.Wr pc kind y hpc hw)

theorem knRd_chaChaRd (c : Ctx) {y : Word} (h : ChaCha20Init.KNRd c y) : TraceSpec.ChaCha20XorReadRegion c y := by
  rcases h with ⟨o, ho, e⟩ | ⟨o, ho, e⟩
  · exact Or.inr (Or.inl (Region.mk ho e))
  · exact Or.inr (Or.inr (Or.inl (Region.mk ho e)))

theorem admitsSite_rd (c : Ctx) :
    ChaCha20Policy.AdmitsSite c.base c.Wr (ChaCha20Init.KNRd c) (RdPolicy c) := by
  intro pc kind y hpc hw hr
  cases kind with
  | read => exact ⟨Or.inl rfl, fun _ _ => knRd_chaChaRd c (hr rfl)⟩
  | write =>
    exact ⟨Or.inr ⟨hw rfl, fun hs => absurd hs (before_output_not_store c.base pc (ChaCha20Policy.knPC_before hpc))⟩,
      fun h => by cases h⟩

theorem storePolicy_of_output (c : Ctx) {pc : Word} {kind : Kind} {y : Word}
    (h : OutputAccess c pc kind y) : StorePolicy c pc kind y := by
  cases kind with
  | read => exact Or.inl rfl
  | write => exact Or.inr h

/-- Appending traces keeps an access policy. -/
theorem eventAccessesTo_append {allowed : Word → Kind → Word → Prop} {a b : List Event}
    (ha : EventAccessesTo allowed a) (hb : EventAccessesTo allowed b) :
    EventAccessesTo allowed (a ++ b) := by
  intro e he x hx k hk
  rcases List.mem_append.mp he with he | he
  · exact ha e he x hx k hk
  · exact hb e he x hx k hk

/-- One block of the output loop. -/
theorem block_events (c : Ctx) (hv : Valid c) (k : Nat) (t : State) (h : BlockInv c k t) :
    ReachEvents c.base (RdPolicy c) t fun u =>
      (c.len.toNat ≤ 64 * (k + 1) ∧ u.pc = c.base + BitVec.ofNat 32 clrOff ∧
        u.regs 13 = c.fp ∧ c.MemOk c.len.toNat u.mem) ∨
      (64 * (k + 1) < c.len.toNat ∧ BlockInv c (k + 1) u) := by
  obtain ⟨steps, finish, tr, hr, -, hph, hend⟩ := block_phases c hv k t h
  obtain ⟨post, out, np, no, nn, tp, to', tn, -, -, -, -, -, -, -, -, hpre, hpolicy, hafter, rfl⟩ := hph
  refine ⟨steps, finish, tp ++ to' ++ tn, hr, ?_, hend⟩
  refine eventAccessesTo_append (eventAccessesTo_append ?_ ?_) ?_
  · intro e he a ha q hq
    obtain ⟨hp, hw⟩ := hpre e he a ha q hq
    exact rdPolicy_of_nonSite c (ChaCha20Policy.not_sitePC_pre hp)
      (before_output_not_store c.base e.pc (ChaCha20Policy.pcBefore_of_between hp)) hw
  · intro e he a ha q hq
    have h := hpolicy e he a ha q hq
    exact ⟨storePolicy_of_output c h, fun hk _ => by rw [hk] at h; exact h⟩
  · intro e he a ha q hq
    obtain ⟨hp, hw⟩ := hafter e he a ha q hq
    exact rdPolicy_of_nonSite c (ChaCha20Policy.not_sitePC_back hp) (after_output_not_store c.base e.pc hp) hw

/-- All blocks: from a block invariant to the frame-clearing entry. -/
theorem blocks_events (c : Ctx) (hv : Valid c) :
    ∀ m k t, c.len.toNat ≤ 64 * (k + m) → BlockInv c k t →
      ReachEvents c.base (RdPolicy c) t fun u =>
        u.pc = c.base + BitVec.ofNat 32 clrOff ∧ u.regs 13 = c.fp ∧ c.MemOk c.len.toNat u.mem
  | 0, k, t, hm, h => absurd h.lt (by omega)
  | m + 1, k, t, hm, h => by
    apply ReachEvents.bind
    apply (block_events c hv k t h).mono (fun _ _ _ x => x)
    intro u hu
    rcases hu with ⟨_, a, b, d⟩ | ⟨_, hu⟩
    · exact ReachEvents.done ⟨a, b, d⟩
    · exact blocks_events c hv m (k + 1) u (by omega) hu

/-- From the zeroing of `r0` through the epilogue to the return address. -/
theorem fin0_events (c : Ctx) (hv : Valid c)
    (hlr : (c.regs0 14).getLsbD 0 = true) (t : State)
    (hpc : t.pc = c.base + BitVec.ofNat 32 zOff) (h13 : t.regs 13 = c.fp)
    (hsv : ∀ i < 9, read32 t.mem (slot c.fp (slotSaved + i)) = Frame.saved c.regs0 i) :
    ReachEvents c.base (RdPolicy c) t fun u => u.pc = c.regs0 14 &&& ~~~1#32 := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  refine ChaCha20Policy.backBlock (admitsRd_back c) hb2 [.movImm 0 0] zOff hpc (by decide) z_at (by decide)
    (by simp [alignedAll, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _) (by decide) (by decide) ?_
  generalize hs : execAll [.movImm 0 0] t = s1
  have sr : s1.regs 13 = t.regs 13 := by
    rw [← hs]
    exact execAll_regs_other [Instr.movImm 0 0] t 13 (by decide) (by simp [Instr.dsts])
  have sm : s1.mem = t.mem := by rw [← hs]; exact execAll_mem [Instr.movImm 0 0] t (by decide)
  have spc : s1.pc = c.base + BitVec.ofNat 32 epiOff := by
    rw [← hs, execAll_pc _ _ (by decide), hpc, ofNat_add_assoc, z_next]
  exact (ChaCha20Return.ret_events c hv c.Wr _ (admitsRd_back c) s1 spc (by rw [sr, h13])
    (fun i hi => by rw [sm]; exact hsv i hi) hlr).mono (fun _ _ _ x => x) (fun _ u => u.1)

/-- **A whole call.** From the entry state the artifact run reaches the return address with
every access obeying `StorePolicy`. -/
theorem xor_reach_events_rd (c : Ctx) (hv : Valid c) (s : State) (h : ChaCha20Setup.Entry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachEvents c.base (RdPolicy c) s fun u => u.pc = c.regs0 14 &&& ~~~1#32 := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have sFW := ChaCha20Layout.chFrameWords_eq
  have sSW := ChaCha20Layout.chStackWords_eq
  have sSB := ChaCha20Layout.chStackBytes_eq
  have sFB := ChaCha20Layout.chFrameBytes_eq
  apply ChaCha20Setup.checks_events c hv c.Wr (fun o ho => .inl ⟨o, ho, rfl⟩) (RdPolicy c) (admitsRd_front c) s h
  · -- empty input
    intro t pc sp mem hz
    exact fin0_events c hv hlr t pc sp (by rw [mem]; exact ChaCha20Xor.mP_saved' c hv)
  · -- counter range exceeded
    intro t pc sp mem _ hok
    refine ChaCha20Policy.backBlock (admitsRd_back c) hb2 [.movImm 0 0, .dp .mvns 0 0] errOff pc (by decide) err_at
      (by decide) (by simp [alignedAll, Instr.accesses]) (WritesTo.of_noWritesMem _ _ (by decide) _)
      (by decide) (by decide) ?_
    generalize hs : execAll [.movImm 0 0, .dp .mvns 0 0] t = s1
    have sr : s1.regs 13 = t.regs 13 := by
      rw [← hs]
      exact execAll_regs_other [Instr.movImm 0 0, Instr.dp .mvns 0 0] t 13 (by decide) (by simp [Instr.dsts])
    have sm : s1.mem = t.mem := by rw [← hs]; exact execAll_mem _ t (by decide)
    have spc : s1.pc = c.base + BitVec.ofNat 32 berrOff2 := by
      rw [← hs, execAll_pc _ _ (by decide), pc, ofNat_add_assoc, err_next]
    apply ReachEvents.b hb2 berrOff2 epiOff (brImm11 berrOff2 epiOff) spc (by decide) berr_at (by decide)
      (by decide +kernel)
    exact (ChaCha20Return.ret_events c hv c.Wr _ (admitsRd_back c) _ (ChaCha20Setup.setReg15_pc _ _)
      (by rw [ChaCha20Setup.setReg15_regs _ _ 13 (by decide), sr, sp])
      (fun i hi => by simp only [M0Crypto.Armv6M.State.setReg]; rw [sm, mem]; exact ChaCha20Xor.mP_saved' c hv i hi)
      hlr).mono (fun _ _ _ x => x) (fun _ u => u.1)
  · -- accepted call
    intro t hacc
    apply ChaCha20Init.init_events c hv (RdPolicy c) (admitsRd_front c) (admitsSite_rd c) t hacc
    intro t0 hb0
    apply ReachEvents.bind
    apply (blocks_events c hv (c.len.toNat / 64 + 1) 0 t0 (by omega) hb0).mono (fun _ _ _ x => x)
    intro u ⟨upc, usp, umem⟩
    refine ChaCha20Policy.backBlock (admitsRd_back c) hb2 clr clrOff upc (by decide) clr_at (by decide)
      (ChaCha20Xor.clear_aligned u (by rw [usp]; exact ChaCha20Setup.fp4 hv))
      (fun e he y ⟨a, ha, _, q, hq, hy⟩ => by
        have ham : a ∈ (traceAll clr u).flatMap Event.accesses := List.mem_flatMap.mpr ⟨e, he, ha⟩
        rw [ChaCha20Xor.clear_accesses] at ham
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ham
        have hi' := List.mem_range.mp hi
        apply ChaCha20Setup.wr_frame (c := c) (n := chFrameWords)
        · refine ⟨4 * i + q, by simp at hq; omega, ?_⟩
          rw [hy, usp]
          simp [slot, ofNat_add_assoc]
        · omega)
      (by decide) (by decide) ?_
    obtain ⟨-, -, -, -, -, v13, vz, vm⟩ := ChaCha20Xor.clr_effect u
    have vmem : c.MemOk c.len.toNat (execAll clr u).mem := fun y hy => by
      rw [vm y (by rw [usp]; rintro ⟨o, ho, rfl⟩; exact hy o (by omega) rfl)]; exact umem y hy
    exact fin0_events c hv hlr _ (by rw [execAll_pc _ _ (by decide), upc, ofNat_add_assoc, clr_end])
      (by rw [v13, usp]) (ChaCha20Xor.saved_memOk c hv vmem (Nat.le_refl _))

/-- The whole-call events obey the store policy. -/
theorem xor_reach_events (c : Ctx) (hv : Valid c) (s : State) (h : ChaCha20Setup.Entry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    ReachEvents c.base (StorePolicy c) s fun u => u.pc = c.regs0 14 &&& ~~~1#32 :=
  (xor_reach_events_rd c hv s h hlr).mono (fun _ _ _ x => x.1) (fun _ u => u)

/-- A run to the stop address whose accesses obey a policy is the model's `runUntil`, provided
the policy's writes miss the code. -/
theorem reachEvents_runUntil {allowed : Word → Kind → Word → Prop} {base : Word} {s : State}
    {stop : Word} (hc : CodeAt s.mem base B)
    (hwc : ∀ pc y, allowed pc .write y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i)
    (h : ReachEvents base allowed s fun s' => s'.pc = stop) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil stop fuel s = .ok (s', tr) ∧
      EventAccessesTo allowed tr := by
  obtain ⟨n, s', tr, hr, ha, hpc⟩ := h
  refine ⟨n, fun fuel hf => ⟨s', tr, ?_, ha⟩⟩
  apply runUntil_of_runH n fuel s s' tr hc hr _ _ hpc hf
  · intro e he i hi hwr
    obtain ⟨a, ham, hw, k, hk, heq⟩ := hwr
    exact hwc e.pc _ (by simpa [hw] using ha e he a ham k hk) i hi (by rw [heq])
  · intro e he heq
    obtain ⟨off, ho, hpe⟩ := runH_pcs n s s' tr hr e he
    exact hstop off ho (heq ▸ hpe)

end M0Crypto.Release.ChaCha20StoreEvents
