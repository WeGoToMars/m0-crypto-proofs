import M0Crypto.Release.ConstantTime.ChaCha20OutputAccess
import M0Crypto.Release.ChaCha20Xor

/-! Functional selection of the output implementation. -/
set_option linter.unusedSimpArgs false
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout

/-- The functional output execution retains both its output invariant and
instruction-specific access bounds. -/
theorem post_output_functional_accesses (xc : Frame.Ctx) (hv : Frame.Valid xc)
    (block : Nat) (t : State) (h : Post xc block t) :
    ReachEvents xc.base (OutputAccess xc) t (ChaCha20Output.Out xc block) := by
  apply bout_events xc hv block t h (OutputAccess xc) ?_ ?_ ?_ (ChaCha20Output.Out xc block)
  · intro u hu
    exact ReachEvents.done hu
  · intro hlen i hi u _ hsp hin hout
    intro e he a ha q hq
    cases hk : a.kind with
    | read =>
      exact aligned_chunk_reads_contract xc block i u hi hsp hin (by omega) e he _
        ⟨a, ha, hk, q, hq, rfl⟩
    | write =>
      have hw := chacha20_chunk_writes_output xc hv block i u hi hout (by omega) e he _
        ⟨a, ha, hk, q, hq, rfl⟩
      exact ⟨Or.inr hw, fun _ => hw⟩
  · intro i hi u hpc hsp
    exact byte_prepare_contract_policy xc u i hi hsp hpc
  · intro N hN hlen p hp u _ _ h0 hin hout hsp
    have hpval : (u.regs 0).toNat = p := by
      rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply byte_tail_contract_policy xc hv block u hin hsp hout
    · rw [hpval]; omega
    · rw [hpval]; omega


/-- A block trace split at the post-round and post-output invariants. -/
def OutputBlockPhases (xc : Frame.Ctx) (block : Nat) (start finish : State)
    (tr : List Event) : Prop :=
  ∃ post out npost nout nnext tpost tout tnext,
    Post xc block post ∧ ChaCha20Output.Out xc block out ∧
    runH B xc.base npost start = .ok (post, tpost) ∧
    runH B xc.base nout post = .ok (out, tout) ∧
    runH B xc.base nnext out = .ok (finish, tnext) ∧
    WritesTo xc.Wr tpost ∧ WritesTo xc.Wr tout ∧ WritesTo xc.Wr tnext ∧
    EventAccessesTo (fun pc kind y => PCBetween xc.base bpreOff achOff pc ∧ writeOnlyPolicy xc.Wr pc kind y) tpost ∧
    EventAccessesTo (OutputAccess xc) tout ∧
    EventAccessesTo (fun pc kind y => PCBetween xc.base n1Off Artifacts.Release.size pc ∧
      writeOnlyPolicy xc.Wr pc kind y) tnext ∧ tr = tpost ++ tout ++ tnext

/-- Construct the block execution while retaining its three functional phases. -/
theorem block_phases (xc : Frame.Ctx) (hv : Frame.Valid xc) (block : Nat)
    (start : State) (hblock : Frame.BlockInv xc block start) :
    ∃ steps finish tr, runH B xc.base steps start = .ok (finish, tr) ∧
      WritesTo xc.Wr tr ∧ OutputBlockPhases xc block start finish tr ∧
      ((xc.len.toNat ≤ 64 * (block + 1) ∧
          finish.pc = xc.base + BitVec.ofNat 32 clrOff ∧
          finish.regs 13 = xc.fp ∧ xc.MemOk xc.len.toNat finish.mem) ∨
        (64 * (block + 1) < xc.len.toNat ∧ Frame.BlockInv xc (block + 1) finish)) := by
  obtain ⟨np, post, tp, hp, hpre, hpost⟩ :=
    ChaCha20Policy.ofEvP (bpost_before_output (Pc := fun _ => True) xc hv (fun _ _ => trivial) block start hblock)
  have hwp : WritesTo xc.Wr tp := hpre.writesTo (fun _ _ h => by
    rcases h.2 with h | h
    · cases h
    · exact h)
  obtain ⟨no, out, to', ho, hpolicy, hout⟩ :=
    post_output_functional_accesses xc hv block post hpost
  have hwo : WritesTo xc.Wr to' := hpolicy.writesTo (fun _ _ h => h.1)
  obtain ⟨nn, finish, tn, hn, hafter, hend⟩ := ChaCha20Policy.ofEvP (ChaCha20Xor.lnext_after_output (Pc := fun _ => True) xc hv (fun _ _ => trivial) block out hout)
  have hwn : WritesTo xc.Wr tn := hafter.writesTo (fun _ _ h => by
    rcases h.2 with h | h
    · cases h
    · exact h)
  refine ⟨np + no + nn, finish, tp ++ to' ++ tn, ?_, (hwp.append hwo).append hwn,
    ⟨post, out, np, no, nn, tp, to', tn, hpost, hout, hp, ho, hn, hwp, hwo, hwn, hpre, hpolicy, hafter, rfl⟩, hend⟩
  rw [runH_add, runH_add, hp]
  simp only [ho, hn]

/-- An ordered decomposition of the block loop into complete per-block
artifact executions, ending at the cleanup entry. -/
inductive OutputBlockTrace (xc : Frame.Ctx) : Nat → State → State → List Event → Prop
  | last {block : Nat} {start finish : State} {steps : Nat} {seg : List Event} :
      Frame.BlockInv xc block start → xc.len.toNat ≤ 64 * (block + 1) →
      runH B xc.base steps start = .ok (finish, seg) → WritesTo xc.Wr seg →
      OutputBlockPhases xc block start finish seg →
      finish.pc = xc.base + BitVec.ofNat 32 clrOff →
      finish.regs 13 = xc.fp → xc.MemOk xc.len.toNat finish.mem →
      OutputBlockTrace xc block start finish seg
  | more {block : Nat} {start next finish : State} {steps : Nat} {seg rest : List Event} :
      Frame.BlockInv xc block start → 64 * (block + 1) < xc.len.toNat →
      runH B xc.base steps start = .ok (next, seg) → WritesTo xc.Wr seg →
      OutputBlockPhases xc block start next seg →
      OutputBlockTrace xc (block + 1) next finish rest →
      OutputBlockTrace xc block start finish (seg ++ rest)

/-- Construct the ordered block decomposition along with its combined
artifact execution and functional write bound. -/
theorem output_blocks_trace (xc : Frame.Ctx) (hv : Frame.Valid xc) :
    ∀ remaining block start, xc.len.toNat ≤ 64 * (block + remaining) →
      Frame.BlockInv xc block start →
      ∃ steps finish tr, runH B xc.base steps start = .ok (finish, tr) ∧
        WritesTo xc.Wr tr ∧ OutputBlockTrace xc block start finish tr
  | 0, _, _, hbound, hblock => False.elim (by have := hblock.lt; omega)
  | remaining + 1, block, start, hbound, hblock => by
    obtain ⟨n, next, seg, hr, hw, hphases, hend⟩ := block_phases xc hv block start hblock
    rcases hend with ⟨hlast, hp, hs, hm⟩ | ⟨hmore, hn⟩
    · exact ⟨n, next, seg, hr, hw, .last hblock hlast hr hw hphases hp hs hm⟩
    ·
      obtain ⟨m, finish, rest, ht, hwt, hblocks⟩ :=
        output_blocks_trace xc hv remaining (block + 1) next (by omega) hn
      refine ⟨n + m, finish, seg ++ rest, ?_, hw.append hwt, .more hblock hmore hr hw hphases hblocks⟩
      rw [runH_add, hr]
      simp only [ht]

end M0Crypto.Release.ConstantTime
