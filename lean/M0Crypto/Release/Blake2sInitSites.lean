import M0Crypto.Release.Blake2sInit
import M0Crypto.Release.Blake2sStreamSites
import M0Crypto.Release.SymReachW

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# `m0c_blake2s_init`: the write bound at the store sites

`init_reach` bounds every write by the frame and the context. The constant-time certificate
needs more at the five stores through `r0`: they write the context, never the frame. The pc-aware
bound `WI` says so, and `init_reachS` proves it by splitting the straight-line part into the
`push` (which writes the frame) and the rest (which writes only the context).
-/

namespace M0Crypto.Release.Blake2sInit

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sStreamEff
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)

/-- The `init` store sites in an artifact loaded at `base`. -/
def InitSiteAt (base pc : Word) : Prop := ∃ off ∈ initSites, pc = base + BitVec.ofNat 32 off

/-- The write bound: the frame or the context, and the context alone at a store site. -/
def WI (base : Word) (s : State) (pc y : Word) : Prop :=
  WrI s y ∧ (InitSiteAt base pc → ∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o)

theorem not_initSiteAt {base : Word} (hbase : base.toNat + Artifacts.Release.size ≤ 2 ^ 32)
    {j : Nat} (h : j < iStart + 2) : ¬ InitSiteAt base (base + BitVec.ofNat 32 j) := by
  rintro ⟨off, hm, he⟩
  have h1 := initSites_ge off hm
  have h2 := initSites_lt off hm
  have h4 := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h4
  have : Artifacts.Release.size < 2 ^ 32 := by decide
  omega

def iPush : List Instr := [.push 0 true]
def iRest : List Instr := iA.drop 1

theorem iA_split : iA = iPush ++ iRest := rfl

theorem iPush_at : seqAt B iStart iPush = true := by rw [seqAt_eq_scan]; decide +kernel
theorem iRest_at : seqAt B (iStart + 2) iRest = true := by rw [seqAt_eq_scan]; decide +kernel

theorem push_state (s : State) :
    (execAll iPush s).regs 0 = s.regs 0 ∧ (execAll iPush s).pc = s.pc + 2#32 := by
  have h : execAll iPush s = (Instr.push 0 true).next s := rfl
  rw [h]
  obtain ⟨-, -, h3⟩ := push_eff s
  exact ⟨h3 0 (by decide) (by decide), pc_next _ (by simp [Instr.falls]) s⟩

/-- **`init` writes the context at its store sites.** -/
theorem init_reachS {base : Word} {s : State} (e : InitEntry base s) :
    ReachS base (PcWr (WI base s)) s (InitPost s) := by
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hbase : base.toNat + Artifacts.Release.size ≤ 2 ^ 32 := e.codeC.1
  obtain ⟨b13, bo, bpc, bm⟩ := block_eff e
  obtain ⟨p0, ppc⟩ := push_state s
  have hs : execAll iA s = execAll iRest (execAll iPush s) := by
    rw [iA_split, execAll_append]
  refine ReachS.symBlockW hb2 [((13 : Reg), 4)] [((13 : Reg), (0#32 - 4#32), 4)]
    iPush iStart e.pc (by decide) iPush_at (by decide) ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact e.sp4
  · intro p hp o ho j hj
    simp only [List.mem_singleton] at hp
    subst hp
    have hj' : j < 2 := by
      have : seqSize iPush = 2 := by decide
      omega
    refine ⟨Or.inl ⟨o, ho, by bv_omega⟩, fun hsite => absurd hsite ?_⟩
    exact not_initSiteAt hbase (by omega)
  · refine ReachS.symBlockW hb2 [((0 : Reg), 4)] [((0 : Reg), 0#32, 40), ((0 : Reg), 104#32, 4)]
      iRest (iStart + 2) (by rw [ppc, e.pc, ofNat_add_assoc]) (by decide) iRest_at (by decide) ?_ ?_
      (by decide +kernel) (by decide +kernel) ?_
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      simpa [p0] using e.c4
    · intro p hp o ho j hj
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨Or.inr ⟨o, by simp at ho; omega, ?_⟩, fun _ => ⟨o, by simp at ho; omega, ?_⟩⟩ <;>
          simp [p0]
      · refine ⟨Or.inr ⟨104 + o, by simp at ho; omega, ?_⟩, fun _ => ⟨104 + o, by simp at ho; omega, ?_⟩⟩ <;>
          simp [p0, ofNat_add_assoc]
    · rw [← hs]
      have hbit : (read32 (execAll iA s).mem ((execAll iA s).regs 13)).getLsbD 0 = true := by
        rw [b13, bm]
        rw [rd_frame e]; exact e.lr
      have hsp4 : (s.regs 13 - 4#32).toNat % 4 = 0 := by
        have := e.sp4; have := e.spLo; have := (s.regs 13).isLt
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      obtain ⟨s1, hex, sm, s13', so, spc⟩ := pop_pc_exec _ hbit
      refine ReachS.stepNW hb2 oIPop iPop (by rw [bpc]; rfl) (by decide) iPop_at (by rw [B_len]; decide) ?_ hex ?_ ?_
      · have hb0 : bitCount (0#8) = 0 := by decide
        simp only [iPop, Instr.accesses, wordAccesses, List.all_eq_true, List.mem_map, List.mem_range,
          Access.aligned, State.sp, hb0, b13]
        rintro _ ⟨i, hi, rfl⟩
        simp only [Bool.toNat_true] at hi
        have hz : bitCount (0 : BitVec 8) = 0 := by decide
        simp only [hz] at hi
        have : i = 0 := by omega
        subst this
        simpa using hsp4
      · intro y ⟨a, ha, hk, _⟩
        simp only [iPop, Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
        obtain ⟨i, _, rfl⟩ := ha
        simp at hk
      · refine ReachS.done ?_
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [spc, b13, bm, rd_frame e]
        · rw [s13', b13]; bv_omega
        · intro r h4 h11
          rw [so r (by omega) (by omega), bo r h4 (by omega) (by omega)]
        · rw [sm, bm]; exact ctx_memB e
        · intro y h1 h2
          rw [sm, bm]; exact memB_other y h1 h2

end M0Crypto.Release.Blake2sInit
