import M0Crypto.Release.X25519CRWord

set_option linter.unusedSimpArgs false

/-!
The reduction loop of `combineReduce` (`X25519Macros.reduceLoop`): seven `reduceWord`s and the
last word. `Inv s0 s` is what every word keeps: the registers the loop reads but does not
write (`r0` the destination, `r2` zero, `r7` the constant 38, `r8`-`r12` the parked words,
`sp`), and the frame words `L`, `H` (the destination is disjoint from them). `word_step` is
`reduceWord_exec` under `Inv`; `reduceLoop_exec` chains the seven steps and the tail.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519W4 (w4)
open M0Crypto.Release.X25519Macros (sl SH SP_ reduceWord reduceLoop)
open M0Crypto.Release.X25519Mul (regs_adds toReg_inj Dist8)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.Blake2s (toReg_ne15 regs_movHi)

theorem storeWords_snoc (m : Mem) (a : Word) (vs : List Word) (v : Word) :
    storeWords m a (vs ++ [v]) = write32 (storeWords m a vs) (a + BitVec.ofNat 32 (4 * vs.length)) v := by
  induction vs generalizing m a with
  | nil => simp [storeWords]
  | cons x vs ih =>
    simp only [List.cons_append, storeWords, ih, List.length_cons]
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
    congr 3; omega

/-- What the loop keeps from its entry state `s0`. -/
structure Inv (s0 s : State) : Prop where
  r0 : s.regs 0 = s0.regs 0
  r2 : s.regs 2 = s0.regs 2
  r7 : s.regs 7 = s0.regs 7
  hi : ∀ r : Reg, 8 ≤ r.val → r ≠ 15 → s.regs r = s0.regs r
  fr : ∀ x < SH + 8, fr s.mem s.sp x = fr s0.mem s0.sp x

theorem Inv.refl (s : State) : Inv s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem yval_inv {s0 s : State} (h : Inv s0 s) (y : Option Reg)
    (hy : ∀ r, y = some r → 8 ≤ r.val ∧ r ≠ 15) : yval s y = yval s0 y := by
  cases y with
  | none => rfl
  | some r => obtain ⟨r8, r15⟩ := hy r rfl; simp only [yval, h.hi r r8 r15]

theorem lo_ne (x : LowReg) (n : Nat) (hn : x.val ≠ n) (hn8 : n < 8) :
    (⟨n, by omega⟩ : Reg) ≠ x.toReg := by
  intro e; apply hn; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega

/-- One word of the loop under `Inv`. -/
theorem word_step (s0 s : State) (hinv : Inv s0 s) (i : Nat) (hi : i < 7) (k h l t u : LowReg)
    (y : Option Reg) (hd : Dist8 k h l t u 0 2 7) (hy : ∀ r, y = some r → 8 ≤ r.val ∧ r ≠ 15)
    (hr7 : (s0.reg 7).toNat = 38) (hr2 : (s0.reg 2).toNat = 0)
    (hD : Disj (s0.reg 0) 32 s0.sp (4 * (SH + 8)))
    (hk : (s.reg k).toNat < 2 ^ 20) (h9 : (s0.regs 9).toNat ≤ 2) :
    let s' := execAll (reduceWord i k h l t u y) s
    (s'.reg l).toNat + 2 ^ 32 * (s'.reg h).toNat =
        (fr s0.mem s0.sp (SP_ + i)).toNat + 38 * (fr s0.mem s0.sp (SH + i)).toNat + (s.reg k).toNat +
          (if i = 4 then 38 * (s0.regs 9).toNat else 0) + yval s0 y ∧
      (s'.reg h).toNat < 64 ∧
      s'.mem = write32 s.mem (s0.reg 0 + BitVec.ofNat 32 (i * 4)) (s'.reg l) ∧ Inv s0 s' := by
  have hd' := hd
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨-, -, -, -, k0, k2, k7⟩, ⟨-, -, -, h0, h2, h7⟩, ⟨-, -, l0, l2, l7⟩,
    ⟨-, t0, t2, t7⟩, ⟨u0, u2, u7⟩, -, -⟩ := hd'
  have n : ∀ x : LowReg, ∀ c : LowReg, x ≠ c → (c.toReg ≠ x.toReg) := fun x c h e =>
    h ((toReg_inj x c).mp e.symm)
  have h9' : s.regs 9 = s0.regs 9 := hinv.hi 9 (by decide) (by decide)
  have W := reduceWord_exec s i (by omega) k h l t u y hd hy
    (by show (s.regs 7).toNat = 38; rw [hinv.r7]; exact hr7)
    (by show (s.regs 2).toNat = 0; rw [hinv.r2]; exact hr2) (by rw [h9']; omega)
  intro s'
  obtain ⟨w1, w2, w3, w4'⟩ := W
  have hsp : s.sp = s0.sp := hinv.hi 13 (by decide) (by decide)
  have e0 : s.reg 0 = s0.reg 0 := hinv.r0
  have keep : ∀ c : LowReg, c ≠ k → c ≠ h → c ≠ l → c ≠ t → c ≠ u → s'.reg c = s.reg c :=
    fun c ck ch cl ct cu => w4' _ (toReg_ne15 _) (n _ _ (Ne.symm ck)) (n _ _ (Ne.symm ch))
      (n _ _ (Ne.symm cl)) (n _ _ (Ne.symm ct)) (n _ _ (Ne.symm cu))
  have hik : ∀ r : Reg, 8 ≤ r.val → ∀ x : LowReg, r ≠ x.toReg := fun r h8 x => by
    rw [ne_eq, hi_ne r h8]; trivial
  have hspan : s'.sp = s.sp := w4' 13 (by decide) (hik _ (by decide) _) (hik _ (by decide) _)
    (hik _ (by decide) _) (hik _ (by decide) _) (hik _ (by decide) _)
  refine ⟨?_, w2, ?_, ?_⟩
  · rw [w1, hinv.fr _ (by simp only [SP_, SH] at *; omega), hinv.fr _ (by omega), h9',
      yval_inv hinv y hy]
  · rw [w3, e0]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show s'.reg 0 = s0.reg 0
      rw [keep 0 (Ne.symm k0) (Ne.symm h0) (Ne.symm l0) (Ne.symm t0) (Ne.symm u0)]; exact e0
    · show s'.reg 2 = s0.reg 2
      rw [keep 2 (Ne.symm k2) (Ne.symm h2) (Ne.symm l2) (Ne.symm t2) (Ne.symm u2)]; exact hinv.r2
    · show s'.reg 7 = s0.reg 7
      rw [keep 7 (Ne.symm k7) (Ne.symm h7) (Ne.symm l7) (Ne.symm t7) (Ne.symm u7)]; exact hinv.r7
    · intro r h8 h15
      rw [w4' r h15 (hik r h8 _) (hik r h8 _) (hik r h8 _) (hik r h8 _) (hik r h8 _), hinv.hi r h8 h15]
    · intro x hx
      rw [w3, hspan, e0, fr_write_disj _ _ _ _ (by rw [hsp]; exact hD) hx (by omega), hinv.fr x hx]


def loopTail : List Instr := [.movHi 2 12, .addReg 2 2 1, .memImm .str 2 0 7]

theorem loopTail_exec (s : State) :
    let s' := execAll loopTail s
    s'.mem = write32 s.mem (s.reg 0 + BitVec.ofNat 32 (7 * 4)) (addWithCarry (s.regs 12) (s.reg 1) false).1 ∧
      ∀ r : Reg, r ≠ 15 → r ≠ 2 → s'.regs r = s.regs r := by
  intro s'
  constructor
  · simp (config := {decide := true}) only [s', loopTail, execAll, mem_strImm, mem_addReg, mem_movHi,
      State.reg, regs_adds, regs_movHi, toReg0, toReg1, toReg2, ite_true, ite_false, ne_eq]
    rfl
  · intro r h15 h2
    simp only [s', loopTail, execAll, regs_strImm _ _ _ _ _ h15, regs_adds _ _ _ _ _ h15,
      regs_movHi _ _ _ _ h15, toReg2, h2, ite_false]

theorem reduceLoop_split : reduceLoop =
    reduceWord 0 4 1 3 5 6 none ++ reduceWord 1 1 4 3 5 6 none ++ reduceWord 2 4 1 3 5 6 none ++
    reduceWord 3 1 4 3 5 6 none ++ reduceWord 4 4 1 3 5 6 (some 8) ++
    reduceWord 5 1 4 3 5 6 (some 10) ++ reduceWord 6 4 1 3 5 6 (some 11) ++ loopTail := rfl

/-- The loop: seven words `o0`-`o6` with carry `k7`, and the last word `r12 + k7`. -/
theorem reduceLoop_exec (s : State) (hr7 : (s.reg 7).toNat = 38) (hr2 : (s.reg 2).toNat = 0)
    (hD : Disj (s.reg 0) 32 s.sp (4 * (SH + 8))) (hk : (s.reg 4).toNat < 2 ^ 20)
    (h9 : (s.regs 9).toNat ≤ 2) :
    let t := execAll reduceLoop s
    let F := fun j => (fr s.mem s.sp j).toNat
    ∃ o0 o1 o2 o3 o4 o5 o6 o7 : Word, ∃ k7 : Nat,
      t.mem = storeWords s.mem (s.reg 0) [o0, o1, o2, o3, o4, o5, o6, o7] ∧
      w4 o0 o1 o2 o3 + 2 ^ 128 * (o4.toNat + 2 ^ 32 * o5.toNat + 2 ^ 64 * o6.toNat) + 2 ^ 224 * k7 =
        (F (SP_ + 0) + 38 * F (SH + 0)) + 2 ^ 32 * (F (SP_ + 1) + 38 * F (SH + 1)) +
        2 ^ 64 * (F (SP_ + 2) + 38 * F (SH + 2)) + 2 ^ 96 * (F (SP_ + 3) + 38 * F (SH + 3)) +
        2 ^ 128 * (F (SP_ + 4) + 38 * F (SH + 4)) + 2 ^ 160 * (F (SP_ + 5) + 38 * F (SH + 5)) +
        2 ^ 192 * (F (SP_ + 6) + 38 * F (SH + 6)) + (s.reg 4).toNat +
        2 ^ 128 * (38 * (s.regs 9).toNat) +
        2 ^ 128 * ((s.regs 8).toNat + 2 ^ 32 * (s.regs 10).toNat + 2 ^ 64 * (s.regs 11).toNat) ∧
      o7.toNat = ((s.regs 12).toNat + k7) % 2 ^ 32 ∧ k7 < 64 ∧
      ∀ r : Reg, r ≠ 15 → 8 ≤ r.val → t.regs r = s.regs r := by
  intro t F
  have e : t = execAll loopTail (execAll (reduceWord 6 4 1 3 5 6 (some 11))
      (execAll (reduceWord 5 1 4 3 5 6 (some 10)) (execAll (reduceWord 4 4 1 3 5 6 (some 8))
      (execAll (reduceWord 3 1 4 3 5 6 none) (execAll (reduceWord 2 4 1 3 5 6 none)
      (execAll (reduceWord 1 1 4 3 5 6 none) (execAll (reduceWord 0 4 1 3 5 6 none) s))))))) := by
    simp only [t, reduceLoop_split, execAll_append]
  have d41 : Dist8 4 1 3 5 6 0 2 7 := by unfold Dist8; decide
  have d14 : Dist8 1 4 3 5 6 0 2 7 := by unfold Dist8; decide
  have yn : ∀ r, (none : Option Reg) = some r → 8 ≤ r.val ∧ r ≠ 15 := fun r h => by cases h
  have ys : ∀ q : Reg, 8 ≤ q.val → q ≠ 15 → ∀ r, some q = some r → 8 ≤ r.val ∧ r ≠ 15 :=
    fun q h8 h15 r h => by cases h; exact ⟨h8, h15⟩
  have S0 := word_step s s (Inv.refl s) 0 (by omega) 4 1 3 5 6 none d41 yn hr7 hr2 hD hk h9
  generalize execAll (reduceWord 0 4 1 3 5 6 none) s = s1 at S0 e
  obtain ⟨v0, b0, m0, i1⟩ := S0
  have S1 := word_step s s1 i1 1 (by omega) 1 4 3 5 6 none d14 yn hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 1 1 4 3 5 6 none) s1 = s2 at S1 e
  obtain ⟨v1, b1, m1, i2⟩ := S1
  have S2 := word_step s s2 i2 2 (by omega) 4 1 3 5 6 none d41 yn hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 2 4 1 3 5 6 none) s2 = s3 at S2 e
  obtain ⟨v2, b2, m2, i3⟩ := S2
  have S3 := word_step s s3 i3 3 (by omega) 1 4 3 5 6 none d14 yn hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 3 1 4 3 5 6 none) s3 = s4 at S3 e
  obtain ⟨v3, b3, m3, i4⟩ := S3
  have S4 := word_step s s4 i4 4 (by omega) 4 1 3 5 6 (some 8) d41 (ys 8 (by decide) (by decide))
    hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 4 4 1 3 5 6 (some 8)) s4 = s5 at S4 e
  obtain ⟨v4, b4, m4, i5⟩ := S4
  have S5 := word_step s s5 i5 5 (by omega) 1 4 3 5 6 (some 10) d14 (ys 10 (by decide) (by decide))
    hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 5 1 4 3 5 6 (some 10)) s5 = s6 at S5 e
  obtain ⟨v5, b5, m5, i6⟩ := S5
  have S6 := word_step s s6 i6 6 (by omega) 4 1 3 5 6 (some 11) d41 (ys 11 (by decide) (by decide))
    hr7 hr2 hD (by omega) h9
  generalize execAll (reduceWord 6 4 1 3 5 6 (some 11)) s6 = s7 at S6 e
  obtain ⟨v6, b6, m6, i7⟩ := S6
  have T := loopTail_exec s7
  rw [← e] at T
  obtain ⟨tm, to⟩ := T
  simp only [yval, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6
  have r0' : s7.reg 0 = s.reg 0 := i7.r0
  refine ⟨s1.reg 3, s2.reg 3, s3.reg 3, s4.reg 3, s5.reg 3, s6.reg 3, s7.reg 3,
    (addWithCarry (s7.regs 12) (s7.reg 1) false).1, (s7.reg 1).toNat, ?_, ?_, ?_, b6, ?_⟩
  · rw [tm, r0', m6, m5, m4, m3, m2, m1, m0]
    rw [show [s1.reg 3, s2.reg 3, s3.reg 3, s4.reg 3, s5.reg 3, s6.reg 3, s7.reg 3,
        (addWithCarry (s7.regs 12) (s7.reg 1) false).1] = [] ++ [s1.reg 3] ++ [s2.reg 3] ++
        [s3.reg 3] ++ [s4.reg 3] ++ [s5.reg 3] ++ [s6.reg 3] ++ [s7.reg 3] ++
        [(addWithCarry (s7.regs 12) (s7.reg 1) false).1] from rfl]
    simp only [storeWords_snoc, List.length_append, List.length_nil, List.length_singleton]
    rfl
  · simp only [w4, F, Nat.add_zero]
    omega
  · rw [i7.hi 12 (by decide) (by decide)]
    simp [addWithCarry]
  · intro r h15 h8
    rw [to r h15 (fun h => by subst h; simp at h8), i7.hi r h8 h15]

end M0Crypto.Release.X25519CR
