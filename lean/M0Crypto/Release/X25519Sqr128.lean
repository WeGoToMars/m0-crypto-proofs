import M0Crypto.Release.X25519Mul128
import M0Crypto.Release.X25519CombSq
import M0Crypto.Release.X25519Sqr64

set_option linter.unusedSimpArgs false

/-!
Macro `sqr128` of `m0c_fe_sqr` (plan `x25519-proofs.md`, phase 8): one level of Karatsuba
squaring of the 4-word operand at `r1`. As `mul128`, a `Runs` composition of its pieces.
`L = aL^2` and `H = aH^2` are kept half in memory and half in `r8`, `r10`, `r11`, `r12`
(`combine128sq`'s layout); the middle product is `(aL - aH)^2`, always subtracted.
-/

namespace M0Crypto.Release.X25519Sqr128
open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion WritesTo)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Macros (combine128sq sqr128 sl)
open M0Crypto.Release.X25519Mul (sqr64 sqr64_exec Dist8)
open M0Crypto.Release.X25519Absd (absd64)
open M0Crypto.Release.X25519Comb (cw coff cregs)
open M0Crypto.Release.X25519CombSq
open M0Crypto.Release.X25519Slot
open M0Crypto.Release.X25519Mul128 (hi_ne absd64_runs listRegs_50 listRegs_65 opv lt64 lt128)
open M0Crypto.Release.InstrNext (toReg_ne15 regs_movHi)

/-- `add d, sp, #4k; stm d!, l`: the registers of `l` to slot `k`. -/
theorem sst_run {Wr : Word → Prop} (s : State) (d : LowReg) (k : Nat) (l : BitVec 8)
    (hd : ∀ r ∈ listRegs l, r.toReg ≠ d.toReg) (hsp : s.sp.toNat % 4 = 0)
    (hW : ∀ j < 4 * bitCount l, Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + j))) :
    Runs (AccOk Wr) [.addRdSp d (sl k), .stm d l] s fun t =>
      t.mem = storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4))
        ((listRegs l).map s.reg) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ d.toReg → t.regs r = s.regs r := by
  refine ⟨accAll_cons (fun a ha => by simp [Instr.accesses] at ha)
    (accAll_cons ?_ (accAll_nil _ _)), ?_, ?_⟩
  · intro a ha
    simp only [Instr.accesses, State.reg, regs_addRdSp _ _ _ _ (toReg_ne15 d), ite_true] at ha
    refine wordAccesses_ok (word_add_aligned hsp (by omega)) (fun _ i hi q hq => ?_) a ha
    rw [ofNat_add_assoc, ofNat_add_assoc]
    exact hW _ (by omega)
  · simp only [execAll, mem_stm, mem_addRdSp]
    have e : ((Instr.addRdSp d (sl k)).next s).reg d = s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) := by
      simp only [State.reg, regs_addRdSp _ _ _ _ (toReg_ne15 d), ite_true, State.sp]
    rw [e]
    congr 1
    apply List.map_congr_left
    intro r hr
    simp only [State.reg, regs_addRdSp _ _ _ _ (toReg_ne15 r), hd r hr, ite_false]
  · intro r h15 hr
    simp only [execAll, regs_stm _ _ _ _ h15, regs_addRdSp _ _ _ _ h15, hr, ite_false]

def q1 : List Instr := [.movHi 12 1, .ldm 1 0x50]

theorem q1_run {Wr : Word → Prop} (s : State) (ha : (s.regs 1).toNat % 4 = 0) :
    Runs (AccOk Wr) q1 s fun t => t.regs 12 = s.regs 1 ∧
      t.regs 4 = ld s.mem (s.regs 1) 0 ∧ t.regs 6 = ld s.mem (s.regs 1) 1 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 12 → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [q1, alignedAll, Instr.accesses, List.all_nil,
      Bool.true_and, Bool.and_true, regs_movHi, State.reg, toReg1, ite_true, ite_false,
      next_mem, Bool.and_eq_true]
    exact wordAccesses_aligned ha
  · refine ⟨?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 h12 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp (config := {decide := true}) only [q1, execAll, regs_ldm, regs_movHi, listRegs_50,
        List.map, List.mem_cons, State.reg, toReg1, toReg4, toReg6, h15, h12, n 1 (by decide),
        n 4 (by decide), n 6 (by decide), ne_eq, not_false_eq_true, ite_false, or_self,
        List.not_mem_nil]
    all_goals
      simp (config := {decide := true}) only [q1, execAll, regs_ldm, regs_movHi, listRegs_50,
        List.map, List.mem_cons, State.reg, toReg1, toReg4, toReg6, ite_true, ite_false,
        next_mem, mem_ldm, List.idxOf, ld, List.findIdx_cons, List.findIdx_nil]
      try rfl

def q2r : List Instr :=
  [.movHi 8 6, .movHi 10 7, .movHi 1 12, .memImm .ldr 4 1 2, .memImm .ldr 6 1 3]

theorem q2r_run {Wr : Word → Prop} (s : State) (ha : (s.regs 12).toNat % 4 = 0) :
    Runs (AccOk Wr) q2r s fun t =>
      t.regs 8 = s.regs 6 ∧ t.regs 10 = s.regs 7 ∧
      t.regs 4 = ld s.mem (s.regs 12) 2 ∧ t.regs 6 = ld s.mem (s.regs 12) 3 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [q2r, alignedAll, Instr.accesses, List.all_cons,
      List.all_nil, Bool.true_and, Bool.and_true, regs_movHi, regs_ldrImm, State.reg, toReg1,
      toReg4, ite_true, ite_false, Bool.and_eq_true]
    refine ⟨?_, ?_⟩ <;> simp only [MemOp.width] <;>
      exact aligned_word (word_add_aligned ha (by decide))
  · refine ⟨?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 n8 n10 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp only [q2r, execAll, regs_ldrImm _ _ _ _ _ h15, regs_movHi _ _ _ _ h15, toReg1,
        toReg4, toReg6, n 1 (by decide), n 4 (by decide), n 6 (by decide), n8, n10, ite_false]
    all_goals
      simp (config := {decide := true}) only [q2r, execAll, regs_ldrImm, regs_movHi, State.reg,
        toReg1, toReg4, toReg6, ite_true, ite_false, next_mem, mem_ldrImm, ld]
      try rfl

def q3r : List Instr := [.movHi 7 12, .movHi 11 4, .movHi 12 5, .ldm 7 0x65]

theorem q3r_run {Wr : Word → Prop} (s : State) (ha : (s.regs 12).toNat % 4 = 0) :
    Runs (AccOk Wr) q3r s fun t =>
      t.regs 11 = s.regs 4 ∧ t.regs 12 = s.regs 5 ∧
      t.regs 0 = ld s.mem (s.regs 12) 0 ∧ t.regs 2 = ld s.mem (s.regs 12) 1 ∧
      t.regs 5 = ld s.mem (s.regs 12) 2 ∧ t.regs 6 = ld s.mem (s.regs 12) 3 ∧ t.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 11 → r ≠ 12 → t.regs r = s.regs r := by
  refine ⟨accAll_of ?_ (WritesTo.of_noWritesMem _ _ (by decide) _), ?_⟩
  · simp (config := {decide := true}) only [q3r, alignedAll, Instr.accesses, List.all_nil,
      Bool.true_and, Bool.and_true, regs_movHi, State.reg, toReg7, ite_true, ite_false]
    exact wordAccesses_aligned ha
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, execAll_mem _ _ (by decide), fun r h15 h8 h11 h12 => ?_⟩
    rotate_right
    · have n : ∀ k : Reg, k.val < 8 → r ≠ k := fun k hk e => by subst e; omega
      simp (config := {decide := true}) only [q3r, execAll, regs_ldm, regs_movHi, listRegs_65,
        List.map, List.mem_cons, State.reg, toReg0, toReg2, toReg5, toReg6, toReg7, h15, h11, h12,
        n 0 (by decide), n 2 (by decide), n 5 (by decide), n 6 (by decide), n 7 (by decide), ne_eq,
        not_false_eq_true, ite_false, or_self, List.not_mem_nil]
    all_goals
      simp (config := {decide := true}) only [q3r, execAll, regs_ldm, regs_movHi, listRegs_65,
        List.map, List.mem_cons, State.reg, toReg0, toReg2, toReg5, toReg6, toReg7, ite_true,
        ite_false, next_mem, List.idxOf, ld, List.findIdx_cons, List.findIdx_nil]
      try rfl

/-- `sqr64` with every low register in use. -/
theorem sqr64_runs {Wr : Word → Prop} (s : State) (a0 a1 o1 o3 t1 t2 t3 t4 : LowReg)
    (hd : Dist8 a0 a1 o1 o3 t1 t2 t3 t4) :
    Runs (AccOk Wr) (sqr64 a0 a1 o1 o3 t1 t2 t3 t4) s fun t =>
      (t.reg a0).toNat + 2 ^ 32 * (t.reg o1).toNat + 2 ^ 64 * (t.reg a1).toNat +
          2 ^ 96 * (t.reg o3).toNat =
        ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) *
          ((s.reg a0).toNat + 2 ^ 32 * (s.reg a1).toNat) ∧
      t.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  obtain ⟨e1, e2, e3⟩ := sqr64_exec s a0 a1 o1 o3 t1 t2 t3 t4 hd
  exact Runs.reg
    (X25519Mul.sqr64_regOnly ..)
    (X25519Mul.sqr64_noW ..)
    ⟨e1, e2, fun r h15 h8 => e3 r h15 (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _)
      (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _)⟩

theorem sqr128_split (k : Nat) (direct : Bool) :
    sqr128 k direct = q1 ++ (sqr64 4 6 5 7 0 1 2 3 ++ ([.addRdSp 0 (sl k), .stm 0 0x30] ++
      (q2r ++ (sqr64 4 6 5 7 0 1 2 3 ++ ([.addRdSp 0 (sl (k + 6)), .stm 0 0xc0] ++ (q3r ++
      (absd64 0 2 5 6 5 ++ (sqr64 0 2 1 3 4 5 6 7 ++ combine128sq k direct)))))))) := by
  simp only [sqr128, q1, q2r, q3r, absd64, List.append_assoc, List.cons_append, List.nil_append]

theorem disjAt {p a : Word} (h : Frame.Disj p 16 a 32) (o n : Nat) (hon : o + n ≤ 32) :
    Frame.Disj p 16 (a + BitVec.ofNat 32 o) n := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩ <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem disjAt0 {p a : Word} (h : Frame.Disj p 16 a 32) (n : Nat) (hn : n ≤ 32) :
    Frame.Disj p 16 a n := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, by omega, by omega⟩

theorem ld_past' {m : M0Crypto.Armv6M.Mem} {p b : Word} {ws : List Word}
    (h : Frame.Disj p 16 b (4 * ws.length)) (i : Nat) (hi : i < 4) :
    ld (storeWords m b ws) p i = ld m p i := by
  unfold ld; exact read32_storeWords_disj m p b ws h i (by omega)

theorem sl_add6 {k : Nat} (hk : k + 6 < 256) : (sl (k + 6)).toNat * 4 = (sl k).toNat * 4 + 24 := by
  simp only [sl, BitVec.toNat_ofNat]; omega

/-- The arithmetic of `sqr128`. -/
theorem sqr128_nat (AL AH R L H P : Nat) (hAL : AL < 2 ^ 64) (hAH : AH < 2 ^ 64)
    (hL : L = AL * AL) (hH : H = AH * AH) (hP : P = R * R)
    (hA : (AL : Int) - AH = if AL < AH then -(R : Int) else R) :
    AL * AH + AH * AL + P = L + H ∧ AL * AH + AH * AL < 2 ^ 160 ∧
    L + 2 ^ 64 * (AL * AH + AH * AL) + 2 ^ 128 * H = (AL + 2 ^ 64 * AH) * (AL + 2 ^ 64 * AH) ∧
    (AL + 2 ^ 64 * AH) * (AL + 2 ^ 64 * AH) < 2 ^ 256 := by
  have b1 := lt64 hAL hAH; have b2 := lt64 hAH hAL
  have ks := X25519Kara.kara_split (2 ^ 64) AL AH AL AH
  have c := X25519Kara.cross_sq AL AH R (if AL < AH then 1 else 0)
    (by by_cases h : AL < AH <;> simp [h] at hA ⊢ <;> exact hA) (by split <;> omega)
  subst hL hH hP
  exact ⟨by omega, by omega, by omega, lt128 (by omega) (by omega)⟩

theorem sqr128_runs {Wr : Word → Prop} (s : State) (k : Nat) (direct : Bool) (hk : k + 6 < 256)
    (hsp : s.sp.toNat % 4 = 0) (ha : (s.regs 1).toNat % 4 = 0)
    (hda : Frame.Disj (s.regs 1) 16 (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 32)
    (hW : ∀ j < 32, Wr (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + j))) :
    Runs (AccOk Wr) (sqr128 k direct) s fun t =>
      ∃ l0 l1 : Word,
        SlotOut s.mem t.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) direct l0 l1 t ∧
        l0.toNat + 2 ^ 32 * l1.toNat + 2 ^ 64 * w4 (t.regs 0) (t.regs 1) (t.regs 2) (t.regs 3) +
            2 ^ 192 * (t.regs 4).toNat + 2 ^ 224 * (t.regs 5).toNat =
          opv s.mem (s.regs 1) * opv s.mem (s.regs 1) ∧
        ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
          t.regs r = s.regs r := by
  have d8 : Dist8 4 6 5 7 0 1 2 3 := by simp only [Dist8]; decide
  have b30 : bitCount 0x30 = 2 := by decide
  have bc0 : bitCount 0xc0 = 2 := by decide
  rw [sqr128_split]
  -- `L`
  refine Runs.append (q1_run s ha) fun s1 ⟨p12, p4, p6, pm, pf⟩ => ?_
  refine Runs.append (sqr64_runs s1 4 6 5 7 0 1 2 3 d8) fun s2 ⟨qv, qm, qf⟩ => ?_
  have sp2 : s2.sp = s.sp := by
    show s2.regs 13 = s.regs 13
    rw [qf 13 (by decide) (by decide), pf 13 (by decide) (by decide) (by decide)]
  have a2 : s2.regs 12 = s.regs 1 := by rw [qf 12 (by decide) (by decide), p12]
  simp only [State.reg, toReg4, toReg5, toReg6, toReg7, p4, p6] at qv
  refine Runs.append (sst_run s2 0 k 0x30 (by decide) (by rw [sp2]; exact hsp)
    (fun j hj => by rw [sp2]; exact hW j (by omega))) fun s3 ⟨sm3, sf3⟩ => ?_
  simp only [(by decide : listRegs 0x30 = [4, 5]), List.map, State.reg, toReg4, toReg5, qm, pm,
    sp2] at sm3
  have g3 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s3.regs r = s2.regs r := fun r h h8 => sf3 r h (hi_ne h8 0)
  have a3 : s3.regs 12 = s.regs 1 := by rw [g3 12 (by decide) (by decide), a2]
  -- `H`
  refine Runs.append (q2r_run s3 (by rw [a3]; exact ha)) fun s4 ⟨u8, u10, u4, u6, um, uf⟩ => ?_
  rw [a3, sm3, ld_past' (disjAt0 hda 8 (by omega)) _ (by decide)] at u4 u6
  refine Runs.append (sqr64_runs s4 4 6 5 7 0 1 2 3 d8) fun s5 ⟨qv5, qm5, qf5⟩ => ?_
  simp only [State.reg, toReg4, toReg5, toReg6, toReg7, u4, u6] at qv5
  have f5 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → s5.regs r = s3.regs r :=
    fun r a b c d => by rw [qf5 r a b, uf r a b c d]
  have sp5 : s5.sp = s.sp := by
    show s5.regs 13 = s.regs 13
    rw [f5 13 (by decide) (by decide) (by decide) (by decide), g3 13 (by decide) (by decide)]
    exact sp2
  have a5 : s5.regs 12 = s.regs 1 := by rw [f5 12 (by decide) (by decide) (by decide) (by decide), a3]
  refine Runs.append (sst_run s5 0 (k + 6) 0xc0 (by decide) (by rw [sp5]; exact hsp)
    (fun j hj => by rw [sp5, sl_add6 hk, Nat.add_assoc]; exact hW (24 + j) (by omega)))
    fun s6 ⟨sm6, sf6⟩ => ?_
  simp only [(by decide : listRegs 0xc0 = [6, 7]), List.map, State.reg, toReg6, toReg7, qm5, um,
    sm3, sp5, sl_add6 hk, ← ofNat_add_assoc] at sm6
  have g6 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s6.regs r = s5.regs r := fun r h h8 => sf6 r h (hi_ne h8 0)
  -- `aL - aH`
  refine Runs.append (q3r_run s6 (by rw [g6 12 (by decide) (by decide), a5]; exact ha))
    fun s7 ⟨w11, w12, w0, w2, w5, w6, wm, wf⟩ => ?_
  rw [g6 12 (by decide) (by decide), a5, sm6, ld_past' (disjAt hda 24 8 (by omega)) _ (by decide),
    ld_past' (disjAt0 hda 8 (by omega)) _ (by decide)] at w0 w2 w5 w6
  refine Runs.append (absd64_runs s7 0 2 5 6 5 (by decide) (by decide) (by decide) (by decide))
    fun s8 ⟨_, vd, vm, vf⟩ => ?_
  simp only [State.reg, toReg0, toReg2, toReg5, toReg6, w0, w2, w5, w6] at vd
  refine Runs.append (sqr64_runs s8 0 2 1 3 4 5 6 7 (by simp only [Dist8]; decide))
    fun s9 ⟨pv, pm9, pf9⟩ => ?_
  simp only [State.reg, toReg0, toReg1, toReg2, toReg3] at pv
  -- the state before `combine128sq`
  have h8 : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → s9.regs r = s7.regs r :=
    fun r h h8 => by rw [pf9 r h h8, vf r h (hi_ne h8 _) (hi_ne h8 _) (hi_ne h8 _)]
  have F : ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
      s9.regs r = s.regs r := by
    intro r a b c d e f
    rw [h8 r a b, wf r a b e f, g6 r a b, f5 r a b c d, g3 r a b, qf r a b, pf r a b f]
  have sp9 : s9.sp = s.sp := F 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have r8 : s9.regs 8 = s2.regs 6 := by
    rw [h8 8 (by decide) (by decide), wf 8 (by decide) (by decide) (by decide) (by decide),
      g6 8 (by decide) (by decide), qf5 8 (by decide) (by decide), u8, sf3 6 (by decide) (by decide)]
  have r10 : s9.regs 10 = s2.regs 7 := by
    rw [h8 10 (by decide) (by decide), wf 10 (by decide) (by decide) (by decide) (by decide),
      g6 10 (by decide) (by decide), qf5 10 (by decide) (by decide), u10, sf3 7 (by decide) (by decide)]
  have r11 : s9.regs 11 = s5.regs 4 := by
    rw [h8 11 (by decide) (by decide), w11, sf6 4 (by decide) (by decide)]
  have r12 : s9.regs 12 = s5.regs 5 := by
    rw [h8 12 (by decide) (by decide), w12, sf6 5 (by decide) (by decide)]
  have mem9 : s9.mem = storeWords (storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4))
      [s2.regs 4, s2.regs 5]) (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) + BitVec.ofNat 32 24)
      [s5.regs 6, s5.regs 7] := by
    rw [pm9, vm, wm, sm6]
  have dlo : Frame.Disj (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 8
      (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) + BitVec.ofNat 32 24) (4 * [s5.regs 6, s5.regs 7].length) := by
    have := hda.2.1
    generalize s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) = a at this ⊢
    refine ⟨by omega, ?_, ?_⟩ <;> simp only [List.length_cons, List.length_nil,
      BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  have lo : ∀ j < 2, ld s9.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) j =
      ld (storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) [s2.regs 4, s2.regs 5])
        (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) j := by
    intro j hj
    rw [mem9]; unfold ld
    rw [read32_storeWords_disj _ _ _ _ dlo j (by omega)]
  have lo0 : ld s9.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 0 = s2.regs 4 := by
    rw [lo 0 (by decide)]; exact ld_store_same _ _ _ 0 (by simp) (by simp)
  have lo1 : ld s9.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 1 = s2.regs 5 := by
    rw [lo 1 (by decide)]; exact ld_store_same _ _ _ 1 (by simp) (by simp)
  have addr : ∀ o j : Nat, s.sp + BitVec.ofNat 32 ((sl k).toNat * 4 + (o + 4 * j)) =
      s.sp + BitVec.ofNat 32 ((sl k).toNat * 4) + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j) := by
    intro o j; simp only [ofNat_add_assoc, Nat.add_assoc]
  have c0 : cw s9 k 0 = s2.regs 4 := by
    unfold ld at lo0; unfold cw; rw [sp9, ← ofNat_add_assoc]; exact lo0
  have c1 : cw s9 k 1 = s2.regs 5 := by
    unfold ld at lo1; unfold cw; rw [sp9, ← ofNat_add_assoc]; exact lo1
  have c6 : cw s9 k 6 = s5.regs 6 := by
    unfold cw; rw [sp9, show (sl k).toNat * 4 + 4 * 6 = (sl k).toNat * 4 + (24 + 4 * 0) by omega,
      addr, mem9]
    exact Frame.read32_storeWords_same _ _ _ 0 (by simp) (by simp)
  have c7 : cw s9 k 7 = s5.regs 7 := by
    unfold cw; rw [sp9, show (sl k).toNat * 4 + 4 * 7 = (sl k).toNat * 4 + (24 + 4 * 1) by omega,
      addr, mem9]
    exact Frame.read32_storeWords_same _ _ _ 1 (by simp) (by simp)
  have hx : ∀ w : Word, w.toNat < 2 ^ 32 := fun w => w.isLt
  have qv' : w4 (s2.regs 4) (s2.regs 5) (s2.regs 6) (s2.regs 7) = _ := qv
  have qv5' : w4 (s5.regs 4) (s5.regs 5) (s5.regs 6) (s5.regs 7) = _ := qv5
  have pv' : w4 (s9.regs 0) (s9.regs 1) (s9.regs 2) (s9.regs 3) = _ := pv
  obtain ⟨hmid, hM, hval, hlt⟩ := sqr128_nat _ _ _ _ _ _
    (by have := hx (ld s.mem (s.regs 1) 0); have := hx (ld s.mem (s.regs 1) 1); omega)
    (by have := hx (ld s.mem (s.regs 1) 2); have := hx (ld s.mem (s.regs 1) 3); omega)
    qv' qv5' pv' vd
  have pre : SqPre s9 k _ := ⟨by rw [c0, c1, c6, c7, r8, r10, r11, r12]; exact hmid, hM,
    by rw [c0, c1, c6, c7, r8, r10, r11, r12, hval]; exact hlt⟩
  refine ⟨combine128sq_acc s9 k direct hk (by rw [sp9]; exact hsp) (fun j hj => by
    rw [sp9, Nat.add_assoc]; exact hW _ (by cases direct <;> simp only [coff] at hj ⊢ <;> simp at hj ⊢ <;> omega)), ?_⟩
  obtain ⟨cv, cmem, cf⟩ := combine128sq_exec s9 k direct _ hk pre
  generalize execAll (combine128sq k direct) s9 = t at cv cmem cf
  refine ⟨s2.regs 4, s2.regs 5, ?_, ?_, fun r a b c d e f => by rw [cf r a b, F r a b c d e f]⟩
  · rw [cmem, sp9, ← ofNat_add_assoc]
    refine slotOut_store _ _ _ hda.2.1 _ _ _ _ lo0 lo1 fun y hy => ?_
    rw [mem9]
    have h24 := storeWords_frame (storeWords s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4))
      [s2.regs 4, s2.regs 5]) (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 24 [s5.regs 6, s5.regs 7]
      (by simp) y hy
    have h0 := storeWords_frame s.mem (s.sp + BitVec.ofNat 32 ((sl k).toNat * 4)) 0
      [s2.regs 4, s2.regs 5] (by simp) y hy
    rw [h24]; simpa using h0
  · rw [c0, c1, c6, c7, r8, r10, r11, r12] at cv
    have oA : opv s.mem (s.regs 1) = (ld s.mem (s.regs 1) 0).toNat + 2 ^ 32 * (ld s.mem (s.regs 1) 1).toNat +
        2 ^ 64 * ((ld s.mem (s.regs 1) 2).toNat + 2 ^ 32 * (ld s.mem (s.regs 1) 3).toNat) := by
      unfold opv w4; omega
    rw [cv, hval, oA]

end M0Crypto.Release.X25519Sqr128
