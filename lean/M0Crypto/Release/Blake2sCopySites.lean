import M0Crypto.Release.Blake2sCopyMain
import M0Crypto.Release.Blake2sStreamSites
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.SymReachW
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# `m0c_blake2s_copy`: the write bound at the store sites

`copy_reach` bounds every write by the frame and the destination. The constant-time certificate
needs more at the six stores through `r0`: they write the destination, never the frame. The loops
of the functional proof write only the destination, so they are reused with that smaller window;
the prologue is the only part that writes the frame.
-/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Blake2sPro (regs_push mem_push)
open M0Crypto.Release.Blake2sStreamCode (copySites copySites_ge copySites_lt)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

open M0Crypto.Release.Blake2sCode (SiteAt allSites not_siteAt_range)

/-- The destination bytes. -/
def DstR (s : State) : Word → Prop := fun y => ∃ o < (s.regs 2).toNat, y = s.regs 0 + BitVec.ofNat 32 o

/-- The write bound: the frame or the destination, and the destination alone at a store site. -/
def WC (base : Word) (s : State) (pc y : Word) : Prop :=
  WrC s y ∧ (SiteAt base pc → DstR s y)

theorem copy_pro_nosite : ∀ off ∈ allSites, off < cStart ∨ cStart + seqSize proL ≤ off := by
  decide +kernel

theorem copy_reachSR {base : Word} {s : State} (e : CopyEntry base s) :
    ReachS base (PNR kLd (WC base s) (SrcR s)) s (CopyPost s) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hn : (s.regs 2).toNat < 2 ^ 31 := by have := e.n64; omega
  have hbase : base.toNat + Artifacts.Release.size ≤ 2 ^ 32 := e.codeD.1
  refine ReachS.symBlockWNR hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 - 20#32), 20)] [] proL cStart e.pc
    (by decide) pro_at (by decide) ?_ ?_ (by simp) (by decide +kernel) (by decide +kernel) ?_
  · intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact e.sp4
  · intro p hp o ho j hj
    simp only [List.mem_singleton] at hp
    subst hp
    have hj' : j < seqSize proL := hj
    refine ⟨Or.inl ⟨o, ho, by unfold fr; bv_omega⟩, fun hsite => absurd hsite ?_⟩
    exact not_siteAt_range (by decide +kernel) copy_pro_nosite hj'

  obtain ⟨p13, p4, po, pm⟩ := pro_eff s
  have hpc1 : (execAll proL s).pc = base + BitVec.ofNat 32 oTst := by
    rw [execAll_pc _ _ (by decide), e.pc, ofNat_add_assoc]; rfl
  have hci : CI (execAll proL s).regs (execAll proL s).mem (s.regs 0) (s.regs 1) (s.regs 2).toNat 0
      (execAll proL s) := by
    refine ⟨?_, ?_, ?_, cp_zero _ _ _, fun r _ _ => rfl, Nat.zero_le _⟩
    · rw [po 0 (by decide) (by decide) (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [po 1 (by decide) (by decide) (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [po 2 (by decide) (by decide) (by decide)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.sub_zero]
      exact (Nat.mod_eq_of_lt (s.regs 2).isLt).symm
  have hal := align_loop (Wr := DstR s) (Rd := SrcR s) (R := (execAll proL s).regs) (m0 := (execAll proL s).mem)
    (d := s.regs 0) (s := s.regs 1) (n := (s.regs 2).toNat) hb2 e.dj hn
    (fun i hi => ⟨i, hi, rfl⟩) (fun i hi => ⟨i, hi, rfl⟩) 0 _ hpc1 hci (by have := e.n1; omega) p4
  have hal' := ReachS.mono hal (P' := PNR kLd (WC base s) (SrcR s))
    (fun _ _ h => ⟨⟨fun y hy => ⟨Or.inr (h.1.1 y hy), fun _ => h.1.1 y hy⟩, h.1.2⟩, h.2⟩) (fun _ h => h)
  refine ReachS.bind (ReachS.mono hal' (fun _ _ h => h) (fun u hu => ?_))
  obtain ⟨hpcU, hciU⟩ := hu
  have U13 : u.regs 13 = fr s := by
    rw [hciU.hi 13 (by decide) (by decide)]; exact p13
  have key : ∀ i (hi : i < 5), read32 u.mem (fr s + BitVec.ofNat 32 (4 * i)) =
      [s.regs 4, s.regs 5, s.regs 6, s.regs 7, s.regs 14][i]'(by simpa using hi) := by
    intro i hi
    have h1 : read32 u.mem (fr s + BitVec.ofNat 32 (4 * i)) =
        read32 (execAll proL s).mem (fr s + BitVec.ofNat 32 (4 * i)) := by
      apply read32_congr
      intro k hk
      exact hciU.cp.2 _ (fun j hj => (ne_frame e.dstF hj hi hk).symm)
    rw [h1, pm]
    exact M0Crypto.Release.Frame.read32_storeWords_same _ (fr s) _ i (by simpa using hi) (by simp)
  have k0 : read32 u.mem (fr s) = s.regs 4 := by
    have := key 0 (by decide); rwa [show fr s + BitVec.ofNat 32 (4 * 0) = fr s by bv_omega] at this
  have k1 : read32 u.mem (fr s + 4#32) = s.regs 5 := by
    have := key 1 (by decide); rwa [show BitVec.ofNat 32 (4 * 1) = 4#32 from rfl] at this
  have k2 : read32 u.mem (fr s + 8#32) = s.regs 6 := by
    have := key 2 (by decide); rwa [show BitVec.ofNat 32 (4 * 2) = 8#32 from rfl] at this
  have k3 : read32 u.mem (fr s + 12#32) = s.regs 7 := by
    have := key 3 (by decide); rwa [show BitVec.ofNat 32 (4 * 3) = 12#32 from rfl] at this
  have k4 : read32 u.mem (fr s + 16#32) = s.regs 14 := by
    have := key 4 (by decide); rwa [show BitVec.ofNat 32 (4 * 4) = 16#32 from rfl] at this
  have hbit : (read32 u.mem (u.regs 13 + 16#32)).getLsbD 0 = true := by
    rw [U13, k4]; exact e.lr
  obtain ⟨s1, hex, sm, s13', s4, s5, s6, s7, so, spc⟩ :=
    M0Crypto.Release.Blake2sCompress.pop_exec u hbit
  refine ReachS.stepNWNR hb2 oDone popL hpcU (by decide) done_at (by rw [B_len]; decide) ?_ hex ?_ ?_
  · have hb4 : bitCount (240 : BitVec 8) = 4 := b4567
    simp only [popL, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
      Access.aligned, State.sp, hb4, U13]
    rintro _ ⟨i, hi, rfl⟩
    simp only [Bool.toNat_true] at hi
    have : (fr s + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0 := by
      have := e.sp4; have := e.spLo; have := (s.regs 13).isLt
      unfold fr
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simpa using this
  · intro y ⟨a, ha, hk, _⟩
    simp only [popL, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp at hk
  · refine ReachS.done ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [spc, U13, k4]
    · rw [s13', U13]; unfold fr; bv_omega
    · rw [s4, U13, k0]
    · rw [s5, U13, k1]
    · rw [s6, U13, k2]
    · rw [s7, U13, k3]
    · rw [so 8 (Or.inr ⟨by decide, by decide⟩), hciU.hi 8 (by decide) (by decide), po 8 (by decide) (by decide) (by decide)]
    · rw [so 9 (Or.inr ⟨by decide, by decide⟩), hciU.hi 9 (by decide) (by decide), po 9 (by decide) (by decide) (by decide)]
    · rw [so 10 (Or.inr ⟨by decide, by decide⟩), hciU.hi 10 (by decide) (by decide), po 10 (by decide) (by decide) (by decide)]
    · rw [so 11 (Or.inr ⟨by decide, by decide⟩), hciU.hi 11 (by decide) (by decide), po 11 (by decide) (by decide) (by decide)]
    · intro i hi
      rw [sm, hciU.cp.1 i hi, pm]
      refine storeWords_other _ _ _ _ (fun j k hj hk eq => ?_)
      exact ne_frame e.srcF hi (by simpa using hj) hk eq
    · intro y hy1 hy2
      rw [sm, hciU.cp.2 y hy2, pm]
      refine storeWords_other _ _ _ _ (fun j k hj hk eq => ?_)
      exact hy1 (4 * j + k) (by simp at hj; omega) (by rw [eq, ofNat_add_assoc]; rfl)

theorem copy_reachS {base : Word} {s : State} (e : CopyEntry base s) :
    ReachS base (PN (WC base s)) s (CopyPost s) :=
  (copy_reachSR e).mono (fun _ _ p => p.pn) (fun _ h => h)

end M0Crypto.Release.Blake2sCopy
