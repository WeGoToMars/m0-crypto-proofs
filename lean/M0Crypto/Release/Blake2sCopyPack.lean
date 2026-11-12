import M0Crypto.Release.Blake2sCopyLoops

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_copy`: the two packed-word loops (unaligned source)

`pbB` (odd source) and `phB` (halfword-aligned source) read the source with narrow loads and
store whole words.  `r5` counts the remaining words; `r2` is constant (`(n-k0) % 4`). -/

namespace M0Crypto.Release.Blake2sCopy

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sCopyCode
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)
open M0Crypto.Release (brSize_eq)

theorem shr2 (m : Nat) (h : m < 2^32) : BitVec.ofNat 32 m >>> 2 = BitVec.ofNat 32 (m / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem and3 (m : Nat) (h : m < 2^32) : BitVec.ofNat 32 m &&& 3#32 = BitVec.ofNat 32 (m % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have e : (3 : Nat) % 2^32 = 2^2 - 1 := by decide
  rw [Nat.mod_eq_of_lt h, e, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem and3' (x : BitVec 32) : (x &&& 3#32 == 0#32) = true → x.toNat % 4 = 0 := by
  intro h
  have := congrArg BitVec.toNat (beq_iff_eq.mp h)
  simp only [BitVec.toNat_and] at this
  have e : (3#32 : BitVec 32).toNat = 2^2 - 1 := by decide
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

theorem and1 (x : BitVec 32) : (x &&& 1#32 == 0#32) = true ↔ x.toNat % 2 = 0 := by
  rw [beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and] at this
    have e : (1#32 : BitVec 32).toNat = 2^1 - 1 := by decide
    rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    have e : (1#32 : BitVec 32).toNat = 2^1 - 1 := by decide
    rw [e, Nat.and_two_pow_sub_one_eq_mod]; simpa using h

theorem dec1 (c : Nat) (h : c + 1 < 2^32) :
    (BitVec.ofNat 32 (c+1) - 1#32 == 0#32) = decide (c = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; simp at this; omega
  · intro e; subst e; decide

theorem succ_sub (c : Nat) (h : c + 1 < 2^32) : BitVec.ofNat 32 (c+1) - 1#32 = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega

theorem odd1 (x : BitVec 32) (h : x.toNat % 2 = 1) : (x + 1#32).toNat % 2 = 0 := by
  simp only [BitVec.toNat_add]; have := x.isLt; simp; omega

/-- `pbB` split after its first two instructions, so the halfword load at `r1+1` has a base
register (`r7`) of known alignment. -/
def pbA : List Instr := [.memImm .ldrb 3 1 0, .addImm3 7 1 1]
def pbC : List Instr :=
  [.memImm .ldrh 6 7 0, .lslImm 6 6 8, .dp .orrs 3 6,
   .memImm .ldrb 6 1 3, .lslImm 6 6 24, .dp .orrs 3 6, .stm 0 8, .addImm8 1 4, .subImm8 5 1]
theorem pbB_split : pbB = pbA ++ pbC := rfl
def oPB2 : Nat := oPB + seqSize pbA
theorem pbA_at : seqAt B oPB pbA = true := by rw [seqAt_eq_scan]; decide +kernel
theorem pbC_at : seqAt B oPB2 pbC = true := by rw [seqAt_eq_scan]; decide +kernel
theorem oPB2_even : oPB2 % 2 = 0 := by decide
theorem oPB_even : oPB % 2 = 0 := by decide

theorem pbA_eff (s : State) :
    (execAll pbA s).regs 7 = s.regs 1 + 1#32 ∧ (execAll pbA s).mem = s.mem ∧
    (∀ r : Reg, r.val ≠ 3 → r.val ≠ 7 → r.val ≠ 15 → (execAll pbA s).regs r = s.regs r) := by
  refine ⟨?_, ?_, fun r h3 h7 h15 => execAll_regs_other _ _ r h15
    (by simp [pbA, Instr.dsts, Fin.ext_iff, MemOp.isLoad, h3, h7] <;> omega)⟩ <;> eff_tac [pbA, MemOp.width]
  all_goals try simp (config := {decide := true}) [State.setReg, LowReg.toReg, Fin.ext_iff, MemOp.width]


/-- Pack-loop state: `k` bytes are copied, `c` words remain to pack, `r2` holds the tail count. -/
structure PK (R : Reg → Word) (m0 : Mem) (d s : Word) (n k c : Nat) (t : State) : Prop where
  r0 : t.regs 0 = d + BitVec.ofNat 32 k
  r1 : t.regs 1 = s + BitVec.ofNat 32 k
  r2 : t.regs 2 = BitVec.ofNat 32 (n - (k + 4 * c))
  r5 : t.regs 5 = BitVec.ofNat 32 c
  cp : Cp m0 t.mem d s k
  hi : ∀ r : Reg, 8 ≤ r.val → r.val ≠ 15 → t.regs r = R r
  kc : k + 4 * c ≤ n

theorem PK.setPc {R m0 d s n k c t} (h : PK R m0 d s n k c t) (v : Word) :
    PK R m0 d s n k c (t.setReg 15 v) :=
  ⟨by rw [sr_ne _ _ _ _ (by decide)]; exact h.r0, by rw [sr_ne _ _ _ _ (by decide)]; exact h.r1,
   by rw [sr_ne _ _ _ _ (by decide)]; exact h.r2, by rw [sr_ne _ _ _ _ (by decide)]; exact h.r5,
   by rw [show (t.setReg 15 v).mem = t.mem from rfl]; exact h.cp,
   fun r h8 h15 => by rw [sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl)]; exact h.hi r h8 h15, h.kc⟩

theorem PK.toCI {R m0 d s n k t} (h : PK R m0 d s n k 0 t) : CI R m0 d s n k t :=
  ⟨h.r0, h.r1, by simpa using h.r2, h.cp, h.hi, by have := h.kc; omega⟩

theorem pbB_PK {R m0 d s n k c t} (h : PK R m0 d s n k (c + 1) t) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) : PK R m0 d s n (k + 4) c (execAll pbB t) := by
  obtain ⟨e0, e1, e5, ez, em, er⟩ := pbB_eff t
  have hkc := h.kc
  have hk : k + 4 ≤ n := by omega
  have hkn : k ≤ n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [e0, h.r0, addr4]
  · rw [e1, h.r1, addr4]
  · rw [er 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r2,
      show k + 4 + 4 * c = k + 4 * (c + 1) by omega]
  · rw [e5, h.r5]; exact succ_sub c (by omega)
  · rw [em, h.r0, h.r1, pack_byte_read]
    exact cp_w32_s h.cp (fun j hj => cp_src h.cp hDj hkn hj) hk hn
  · intro r h8 h15
    rw [er r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h15]; exact h.hi r h8 h15

theorem phB_PK {R m0 d s n k c t} (h : PK R m0 d s n k (c + 1) t) (hDj : Disj d n s n)
    (hn : n < 2 ^ 31) : PK R m0 d s n (k + 4) c (execAll phB t) := by
  obtain ⟨e0, e1, e5, ez, em, er⟩ := phB_eff t
  have hkc := h.kc
  have hk : k + 4 ≤ n := by omega
  have hkn : k ≤ n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [e0, h.r0, addr4]
  · rw [e1, h.r1, addr4]
  · rw [er 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r2,
      show k + 4 + 4 * c = k + 4 * (c + 1) by omega]
  · rw [e5, h.r5]; exact succ_sub c (by omega)
  · rw [em, h.r0, h.r1, pack_half_read]
    exact cp_w32_s h.cp (fun j hj => cp_src h.cp hDj hkn hj) hk hn
  · intro r h8 h15
    rw [er r (by omega) (by omega) (by omega) (by omega) (by omega) h15]; exact h.hi r h8 h15

theorem odd_add4 (x : Word) (h : x.toNat % 2 = 1) : (x + 4#32).toNat % 2 = 1 := by
  simp only [BitVec.toNat_add]; have := x.isLt; simp; omega

theorem even_add4 (x : Word) (h : x.toNat % 2 = 0) : (x + 4#32).toNat % 2 = 0 := by
  simp only [BitVec.toNat_add]; have := x.isLt; simp; omega

section loops
variable {base : Word} {Wr Rd : Word → Prop} {R : Reg → Word} {m0 : Mem} {d s : Word} {n : Nat}

theorem ph_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ c k : Nat, ∀ t : State, t.pc = base + BitVec.ofNat 32 oPH → PK R m0 d s n k (c + 1) t →
      (t.regs 0).toNat % 4 = 0 → (t.regs 1).toNat % 2 = 0 → ReachNR base Wr Rd t (G base R m0 d s n)
  | c, k, t, hpc, hpi, hal0, hal1 => by
    refine ReachNR.symBlock hb2 [((1 : Reg), 2), ((0 : Reg), 4)] [((0 : Reg), (0#32 : Word), 4)] [((1 : Reg), (0#32 : Word), 4)] phB oPH hpc
      (by decide +kernel) ph_at (by decide) ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hal1
      · exact hal0
    · apply Reach.region_one
      intro o ho
      have := hpi.kc
      rw [hpi.r0, BitVec.add_zero, ofNat_add_assoc]; exact hW _ (by omega)
    · apply rr_one
      intro o ho
      have := hpi.kc
      rw [hpi.r1, BitVec.add_zero, ofNat_add_assoc]; exact hR _ (by omega)
    obtain ⟨e0, e1, e5, ez, em, er⟩ := phB_eff t
    have hpi' := phB_PK hpi hDj hn
    have hz : (execAll phB t).z = decide (c = 0) := by
      have := hpi.kc
      rw [ez, hpi.r5]; exact dec1 c (by omega)
    have hp : (execAll phB t).pc = base + BitVec.ofNat 32 oPHBne := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oPHBne oPH 1 (brImm8 oPHBne oPH) hp (by decide +kernel) phBne_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      have hz' : (execAll phB t).z = false := by rw [cp1] at hc; simpa using hc
      have hne : c ≠ 0 := by rw [hz] at hz'; simpa using hz'
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      refine ph_loop hb2 hDj hn hW hR c' (k + 4) _ (by rw [sr_pc]) (hpi'.setPc _) ?_ ?_
      · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), e0]; exact al_add _ 4 rfl hal0
      · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), e1]; exact even_add4 _ hal1
    · intro hc
      have hz' : (execAll phB t).z = true := by rw [cp1] at hc; simpa using hc
      have h0 : c = 0 := by rw [hz] at hz'; simpa using hz'
      subst h0
      exact bytes_entry hb2 hDj hn hW hR _ (by rw [sr_pc, show oPHBne + 2 = oBytes by decide])
        (hpi'.setPc _).toCI
  termination_by c => c
  decreasing_by omega

theorem pb_loop (hb2 : base.toNat % 2 = 0) (hDj : Disj d n s n) (hn : n < 2 ^ 31)
    (hW : ∀ i < n, Wr (d + BitVec.ofNat 32 i))
    (hR : ∀ i < n, Rd (s + BitVec.ofNat 32 i)) :
    ∀ c k : Nat, ∀ t : State, t.pc = base + BitVec.ofNat 32 oPB → PK R m0 d s n k (c + 1) t →
      (t.regs 0).toNat % 4 = 0 → (t.regs 1).toNat % 2 = 1 → ReachNR base Wr Rd t (G base R m0 d s n)
  | c, k, t, hpc, hpi, hal0, hal1 => by
    refine ReachNR.symBlock hb2 [((1 : Reg), 1)] [] [((1 : Reg), (0#32 : Word), 1)] pbA oPB hpc oPB_even pbA_at (by decide) ?_ (by simp)
      ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp; simp only [List.mem_singleton] at hp
      subst hp; exact Nat.mod_one _
    · apply rr_one
      intro o ho
      have := hpi.kc
      rw [hpi.r1, BitVec.add_zero, ofNat_add_assoc]; exact hR _ (by omega)
    obtain ⟨a7, am, ar⟩ := pbA_eff t
    have hpc2 : (execAll pbA t).pc = base + BitVec.ofNat 32 oPB2 := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    refine ReachNR.symBlock hb2 [((7 : Reg), 2), ((1 : Reg), 1), ((0 : Reg), 4)]
      [((0 : Reg), (0#32 : Word), 4)] [((7 : Reg), (0#32 : Word), 2), ((1 : Reg), (3#32 : Word), 1)] pbC oPB2 hpc2 oPB2_even pbC_at (by decide) ?_ ?_
      ?_ (by decide +kernel) (by decide +kernel) ?_
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · show ((execAll pbA t).regs 7).toNat % 2 = 0
        rw [a7]; exact odd1 _ hal1
      · exact Nat.mod_one _
      · show ((execAll pbA t).regs 0).toNat % 4 = 0
        rw [ar 0 (by decide) (by decide) (by decide)]; exact hal0
    · apply Reach.region_one
      intro o ho
      have := hpi.kc
      rw [ar 0 (by decide) (by decide) (by decide), hpi.r0, BitVec.add_zero, ofNat_add_assoc]
      exact hW _ (by omega)
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      have := hpi.kc
      rcases hp with rfl | rfl
      · intro o ho
        have ho : o < 2 := ho
        show Rd ((execAll pbA t).regs 7 + 0#32 + BitVec.ofNat 32 o)
        have e : (execAll pbA t).regs 7 + 0#32 + BitVec.ofNat 32 o = s + BitVec.ofNat 32 (k + 1 + o) := by
          rw [a7, hpi.r1]; bv_omega
        rw [e]; exact hR _ (by omega)
      · intro o ho
        have ho : o < 1 := ho
        show Rd ((execAll pbA t).regs 1 + 3#32 + BitVec.ofNat 32 o)
        have e : (execAll pbA t).regs 1 + 3#32 + BitVec.ofNat 32 o = s + BitVec.ofNat 32 (k + 3 + o) := by
          rw [ar 1 (by decide) (by decide) (by decide), hpi.r1]; bv_omega
        rw [e]; exact hR _ (by omega)
    rw [show execAll pbC (execAll pbA t) = execAll pbB t from (execAll_append pbA pbC t).symm]
    obtain ⟨e0, e1, e5, ez, em, er⟩ := pbB_eff t
    have hpi' := pbB_PK hpi hDj hn
    have hz : (execAll pbB t).z = decide (c = 0) := by
      have := hpi.kc
      rw [ez, hpi.r5]; exact dec1 c (by omega)
    have hp : (execAll pbB t).pc = base + BitVec.ofNat 32 oPBBne := by
      rw [execAll_pc _ _ (by decide), hpc, ofNat_add_assoc]; rfl
    apply ReachNR.bcond hb2 oPBBne oPB 1 (brImm8 oPBBne oPB) hp (by decide +kernel) pbBne_at
      (by decide +kernel) (by decide +kernel)
    · intro hc
      have hz' : (execAll pbB t).z = false := by rw [cp1] at hc; simpa using hc
      have hne : c ≠ 0 := by rw [hz] at hz'; simpa using hz'
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      refine pb_loop hb2 hDj hn hW hR c' (k + 4) _ (by rw [sr_pc]) (hpi'.setPc _) ?_ ?_
      · rw [sr_ne _ _ _ _ (show (0 : Reg) ≠ 15 by decide), e0]; exact al_add _ 4 rfl hal0
      · rw [sr_ne _ _ _ _ (show (1 : Reg) ≠ 15 by decide), e1]; exact odd_add4 _ hal1
    · intro hc
      have hz' : (execAll pbB t).z = true := by rw [cp1] at hc; simpa using hc
      have h0 : c = 0 := by rw [hz] at hz'; simpa using hz'
      subst h0
      have hp2 : ((execAll pbB t).setReg 15 (base + BitVec.ofNat 32 (oPBBne + 2))).pc =
          base + BitVec.ofNat 32 oPBBack := by
        rw [sr_pc, show oPBBne + 2 = oPBBack by decide]
      apply ReachNR.b hb2 oPBBack oBytes (brImm11 oPBBack oBytes) hp2 (by decide +kernel) pbBack_at
        (by decide +kernel) (by decide +kernel)
      exact bytes_entry hb2 hDj hn hW hR _ (by rw [sr_pc]) ((hpi'.setPc _).setPc _).toCI
  termination_by c => c
  decreasing_by omega

end loops

end M0Crypto.Release.Blake2sCopy
