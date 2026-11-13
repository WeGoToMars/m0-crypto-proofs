import M0Crypto.Release.X25519CRBase

set_option linter.unusedSimpArgs false

/-!
One word of the reduction loop of `combineReduce` (`X25519Macros.reduceWord`), generic in the
word index `i` and in the five rotating low registers `k h l t u` and the parked register
`y`. Word `i` reads `W = H[i]` (slot `SH + i`) and `Lw = L[i]` (slot `SP_ + i`) and computes
`l + 2^32 h = Lw + 38 W + k (+ 38 r9 at i = 4) (+ y)`; `l` is stored at `dst + 4 i`.

The macro is split into five pieces (`wLoad`, `wExtra`, `wMid`, `wY`, `wStore`, by `rfl`)
with one lemma each; `reduceWord_exec` composes them. The registers enter only through
disequality hypotheses, so the loop instantiates the lemma seven times.
-/

namespace M0Crypto.Release.X25519CR
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.X25519Mem
open M0Crypto.Release.X25519Macros (sl SH SP_ reduceWord)
open M0Crypto.Release.X25519Mul (regs_adcs regs_adds regs_lsr regs_lsl regs_muls regs_uxth
  toReg_inj High mul_small lo16 hi16 shl16 c_adds c_adcs)
open M0Crypto.Release.X25519Carry (adc_nat carry_le)
open M0Crypto.Release.Blake2s (toReg_ne15 regs_movHi)

def wLoad (i : Nat) (h l t : LowReg) : List Instr :=
  [.ldrSp h (sl (SH + i)), .ldrSp l (sl (SP_ + i)), .uxth t h, .lsrImm h h 16,
   .dp .muls t 7, .dp .muls h 7]

def wExtra (i : Nat) (k u : LowReg) : List Instr :=
  if i = 4 then [.movHi u.toReg 9, .dp .muls u 7, .addReg k k u] else []

def wMid (k h l t u : LowReg) : List Instr :=
  [.addReg t t k, .lslImm u h 16, .lsrImm h h 16, .addReg l l t, .dp .adcs h 2,
   .addReg l l u, .dp .adcs h 2]

/-- The value of the parked word `y` (zero if none). -/
def yval (s : State) : Option Reg → Nat
  | some r => (s.regs r).toNat
  | none => 0

theorem yval_lt (s : State) (y : Option Reg) : yval s y < 2 ^ 32 := by
  cases y with
  | none => simp [yval]
  | some r => exact (s.regs r).isLt

def wY (h l u : LowReg) (y : Option Reg) : List Instr :=
  match y with | some r => [.movHi u.toReg r, .addReg l l u, .dp .adcs h 2] | none => []

theorem reduceWord_split (i : Nat) (k h l t u : LowReg) (y : Option Reg) :
    reduceWord i k h l t u y =
      wLoad i h l t ++ wExtra i k u ++ wMid k h l t u ++ wY h l u y ++
        [.memImm .str l 0 (BitVec.ofNat 5 i)] := by
  cases y <;> simp only [reduceWord, wLoad, wExtra, wMid, wY, List.cons_append, List.nil_append,
    List.append_assoc]

theorem regs_ldrSp_sl (s : State) (d : LowReg) (k : Nat) (hk : k < 256) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldrSp d (sl k)).next s).regs r = if r = d.toReg then fr s.mem s.sp k else s.regs r := by
  rw [regs_ldrSp _ _ _ _ hr, sl_toNat, Nat.mod_eq_of_lt hk, Nat.mul_comm]; rfl

/-- A high register is no low register. -/
theorem hi_ne (r : Reg) (h : 8 ≤ r.val) (x : LowReg) : (r = x.toReg) = False := by
  apply eq_false; intro e; subst e; simp [LowReg.toReg] at h; omega

theorem m38_lo (R W : Word) (hR : R.toNat = 38) :
    (R * BitVec.setWidth 32 (BitVec.setWidth 16 W)).toNat = 38 * (W.toNat % 2 ^ 16) := by
  rw [mul_small _ _ (by omega) (by rw [lo16]; omega), lo16, hR]

theorem m38_hi (R W : Word) (hR : R.toNat = 38) : (R * (W >>> 16)).toNat = 38 * (W.toNat / 2 ^ 16) := by
  have := W.isLt
  rw [mul_small _ _ (by omega) (by rw [hi16]; omega), hi16, hR]

theorem t16 : (16 : BitVec 5).toNat = 16 := rfl
theorem r13_ne : (13 : Reg) ≠ 15 := by decide

theorem wLoad_exec (s : State) (i : Nat) (hi : i < 8) (h l t : LowReg) (hhl : h ≠ l) (hht : h ≠ t)
    (hlt : l ≠ t) (h7 : h ≠ 7) (t7 : t ≠ 7) (l7 : l ≠ 7) (hr7 : (s.reg 7).toNat = 38) :
    let s' := execAll (wLoad i h l t) s
    (s'.reg t).toNat = 38 * ((fr s.mem s.sp (SH + i)).toNat % 2 ^ 16) ∧
      (s'.reg h).toNat = 38 * ((fr s.mem s.sp (SH + i)).toNat / 2 ^ 16) ∧
      s'.reg l = fr s.mem s.sp (SP_ + i) ∧ s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ h.toReg → r ≠ l.toReg → r ≠ t.toReg → s'.regs r = s.regs r := by
  intro s'
  have hk1 : SH + i < 256 := by simp only [SH]; omega
  have hk2 : SP_ + i < 256 := by simp only [SP_]; omega
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [wLoad, Instr.writesMem])
  refine ⟨?_, ?_, ?_, hm, ?_⟩
  rotate_left 3
  · intro r h15 hrh hrl hrt
    simp only [s', wLoad, execAll, regs_ldrSp_sl _ _ _ hk1 _ h15, regs_ldrSp_sl _ _ _ hk2 _ h15,
      regs_uxth _ _ _ _ h15, regs_lsr _ _ _ 16 (by decide) _ h15, regs_muls _ _ _ _ h15, hrh, hrl,
      hrt, ite_false]
  all_goals
    simp only [s', wLoad, execAll, State.reg]
    simp only [regs_ldrSp_sl _ _ _ hk1, regs_ldrSp_sl _ _ _ hk2, regs_uxth,
      regs_lsr _ _ _ 16 (by decide), regs_muls, toReg_ne15, r13_ne, ne_eq, not_false_eq_true,
      State.reg, toReg_inj, hhl, hht, hlt, Ne.symm hhl, Ne.symm hht, Ne.symm hlt, t7, h7, l7,
      Ne.symm t7, Ne.symm h7, Ne.symm l7, ite_true, ite_false, mem_ldrSp, mem_uxth, mem_lsr,
      State.sp, hi_ne 13 (by decide), t16]
  · exact m38_lo _ _ hr7
  · exact m38_hi _ _ hr7

theorem wExtra_exec (s : State) (i : Nat) (k u : LowReg) (hku : k ≠ u) (u7 : u ≠ 7)
    (hr7 : (s.reg 7).toNat = 38) (hb : (s.reg k).toNat + 38 * (s.regs 9).toNat < 2 ^ 32) :
    let s' := execAll (wExtra i k u) s
    (s'.reg k).toNat = (s.reg k).toNat + (if i = 4 then 38 * (s.regs 9).toNat else 0) ∧
      s'.mem = s.mem ∧ ∀ r : Reg, r ≠ 15 → r ≠ k.toReg → r ≠ u.toReg → s'.regs r = s.regs r := by
  intro s'
  by_cases hi : i = 4
  · have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [s', wExtra, hi, Instr.writesMem])
    refine ⟨?_, hm, ?_⟩
    · simp only [s', wExtra, hi, ite_true, execAll, State.reg]
      simp only [regs_adds, regs_muls, regs_movHi, toReg_ne15, ne_eq, not_false_eq_true, State.reg,
        toReg_inj, hku, Ne.symm hku, u7, Ne.symm u7, hi_ne 9 (by decide), ite_true,
        ite_false]
      have e := adc_nat (s.regs k.toReg) (s.regs (LowReg.toReg 7) * s.regs 9) false
      have := carry_le (s.regs k.toReg) (s.regs (LowReg.toReg 7) * s.regs 9) false
      have h9 : (s.regs (LowReg.toReg 7) * s.regs 9).toNat = 38 * (s.regs 9).toNat := by
        rw [BitVec.toNat_mul]; simp only [State.reg] at hr7; rw [hr7]; exact Nat.mod_eq_of_lt (by omega)
      simp only [State.reg] at hb
      rw [h9] at e; simp only [Bool.toNat_false, Nat.add_zero] at e
      omega
    · intro r h15 hrk hru
      simp only [s', wExtra, hi, ite_true, execAll, regs_adds _ _ _ _ _ h15, regs_muls _ _ _ _ h15,
        regs_movHi _ _ _ _ h15, hrk, hru, ite_false]
  · simp [s', wExtra, hi, execAll]


theorem wMid_exec (s : State) (k h l t u : LowReg) (hhl : h ≠ l) (hht : h ≠ t) (hhu : h ≠ u) (hlt : l ≠ t) (hlu : l ≠ u)
    (htu : t ≠ u) (h2 : h ≠ 2) (l2 : l ≠ 2) (t2 : t ≠ 2) (u2 : u ≠ 2)
    (hr2 : (s.reg 2).toNat = 0) (htk : (s.reg t).toNat + (s.reg k).toNat < 2 ^ 32)
    (hh : (s.reg h).toNat < 2 ^ 24) :
    let s' := execAll (wMid k h l t u) s
    (s'.reg l).toNat + 2 ^ 32 * (s'.reg h).toNat =
        (s.reg l).toNat + (s.reg t).toNat + (s.reg k).toNat + 2 ^ 16 * (s.reg h).toNat ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ h.toReg → r ≠ l.toReg → r ≠ t.toReg → r ≠ u.toReg →
        s'.regs r = s.regs r := by
  intro s'
  have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [wMid, Instr.writesMem])
  refine ⟨?_, hm, ?_⟩
  · simp only [s', wMid, execAll, State.reg]
    simp only [regs_adds, regs_adcs, regs_lsr _ _ _ 16 (by decide), regs_lsl _ _ _ 16 (by decide),
      c_adds, toReg_ne15, ne_eq, not_false_eq_true, State.reg, toReg_inj, hhl,
      hht, hhu, hlt, hlu, htu, h2, l2, t2, u2, Ne.symm hhl, Ne.symm hht, Ne.symm hhu, Ne.symm hlt, Ne.symm hlu, Ne.symm htu, Ne.symm h2,
      Ne.symm l2, Ne.symm t2, Ne.symm u2, ite_true, ite_false, t16]
    simp only [State.reg] at hr2 htk hh
    generalize s.regs (LowReg.toReg 2) = Z at hr2 ⊢
    generalize s.regs t.toReg = T at htk ⊢
    generalize s.regs k.toReg = K at htk ⊢
    generalize s.regs h.toReg = H at hh ⊢
    generalize s.regs l.toReg = L
    have e1 := adc_nat T K false
    generalize addWithCarry T K false = A1 at e1 ⊢
    have e2 := adc_nat L A1.1 false
    generalize addWithCarry L A1.1 false = A2 at e2 ⊢
    have e3 := adc_nat (H >>> 16) Z A2.2.1
    generalize addWithCarry (H >>> 16) Z A2.2.1 = A3 at e3 ⊢
    have e4 := adc_nat A2.1 (H <<< 16) false
    generalize addWithCarry A2.1 (H <<< 16) false = A4 at e4 ⊢
    have e5 := adc_nat A3.1 Z A4.2.1
    generalize addWithCarry A3.1 Z A4.2.1 = A5 at e5 ⊢
    rw [hi16] at e3
    rw [shl16] at e4
    have := carry_le A2.1 (H <<< 16) false; have := carry_le L A1.1 false
    have := carry_le A3.1 Z A4.2.1; have := A5.1.isLt; have := A1.1.isLt
    simp only [Bool.toNat_false, Nat.add_zero] at e1 e2 e4
    omega
  · intro r h15 hrh hrl hrt hru
    simp only [s', wMid, execAll, regs_adds _ _ _ _ _ h15, regs_adcs _ _ _ _ h15,
      regs_lsr _ _ _ 16 (by decide) _ h15, regs_lsl _ _ _ 16 (by decide) _ h15, hrh, hrl, hrt, hru,
      ite_false]

theorem wY_exec (s : State) (h l u : LowReg) (y : Option Reg) (hhl : h ≠ l) (hhu : h ≠ u)
    (hlu : l ≠ u) (l2 : l ≠ 2) (u2 : u ≠ 2)
    (hy : ∀ r, y = some r → 8 ≤ r.val ∧ r ≠ 15)
    (hr2 : (s.reg 2).toNat = 0) (hh : (s.reg h).toNat < 2 ^ 31) :
    let s' := execAll (wY h l u y) s
    (s'.reg l).toNat + 2 ^ 32 * (s'.reg h).toNat =
        (s.reg l).toNat + 2 ^ 32 * (s.reg h).toNat +
          yval s y ∧
      s'.mem = s.mem ∧
      ∀ r : Reg, r ≠ 15 → r ≠ h.toReg → r ≠ l.toReg → r ≠ u.toReg → s'.regs r = s.regs r := by
  intro s'
  cases y with
  | none => exact ⟨by simp [s', wY, execAll, yval], rfl, fun _ _ _ _ _ => rfl⟩
  | some y =>
    obtain ⟨y8, y15⟩ := hy y rfl
    have hm : s'.mem = s.mem := execAll_mem _ _ (by simp [wY, Instr.writesMem])
    refine ⟨?_, hm, ?_⟩
    · simp only [s', wY, execAll, State.reg, yval]
      simp only [regs_adds, regs_adcs, regs_movHi, c_adds, toReg_ne15, ne_eq, not_false_eq_true,
        State.reg, toReg_inj, hhl, hhu, hlu, l2, u2, Ne.symm hhl, Ne.symm hhu, Ne.symm hlu,
        Ne.symm l2, Ne.symm u2, ite_true, ite_false, hi_ne y y8]
      simp only [State.reg] at hr2 hh
      have e1 := adc_nat (s.regs l.toReg) (s.regs y) false
      have e2 := adc_nat (s.regs h.toReg) (s.regs (LowReg.toReg 2))
        (addWithCarry (s.regs l.toReg) (s.regs y) false).2.1
      have := carry_le (s.regs l.toReg) (s.regs y) false
      have := (addWithCarry (s.regs h.toReg) (s.regs (LowReg.toReg 2))
        (addWithCarry (s.regs l.toReg) (s.regs y) false).2.1).1.isLt
      simp only [Bool.toNat_false, Nat.add_zero] at e1
      omega
    · intro r h15 hrh hrl hru
      simp only [s', wY, execAll, regs_adds _ _ _ _ _ h15, regs_adcs _ _ _ _ h15,
        regs_movHi _ _ _ _ h15, hrh, hrl, hru, ite_false]


theorem wStore_exec (s : State) (i : Nat) (hi : i < 32) (l : LowReg) :
    let s' := execAll [.memImm .str l 0 (BitVec.ofNat 5 i)] s
    s'.mem = write32 s.mem (s.reg 0 + BitVec.ofNat 32 (i * 4)) (s.reg l) ∧
      ∀ r : Reg, r ≠ 15 → s'.regs r = s.regs r := by
  intro s'
  refine ⟨?_, fun r h15 => regs_strImm _ _ _ _ _ h15⟩
  simp only [s', execAll, mem_strImm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

open M0Crypto.Release.X25519Mul (Dist8) in
/-- Word `i` of the reduction. `k` is the carry in; `l` the word stored at `dst + 4 i`, `h` the
carry out. -/
theorem reduceWord_exec (s : State) (i : Nat) (hi : i < 8) (k h l t u : LowReg) (y : Option Reg)
    (hd : Dist8 k h l t u 0 2 7) (hy : ∀ r, y = some r → 8 ≤ r.val ∧ r ≠ 15)
    (hr7 : (s.reg 7).toNat = 38) (hr2 : (s.reg 2).toNat = 0)
    (hk : (s.reg k).toNat + 38 * (s.regs 9).toNat < 2 ^ 24) :
    let s' := execAll (reduceWord i k h l t u y) s
    (s'.reg l).toNat + 2 ^ 32 * (s'.reg h).toNat =
        (fr s.mem s.sp (SP_ + i)).toNat + 38 * (fr s.mem s.sp (SH + i)).toNat + (s.reg k).toNat +
          (if i = 4 then 38 * (s.regs 9).toNat else 0) +
          yval s y ∧
      (s'.reg h).toNat < 64 ∧
      s'.mem = write32 s.mem (s.reg 0 + BitVec.ofNat 32 (i * 4)) (s'.reg l) ∧
      ∀ r : Reg, r ≠ 15 → r ≠ k.toReg → r ≠ h.toReg → r ≠ l.toReg → r ≠ t.toReg → r ≠ u.toReg →
        s'.regs r = s.regs r := by
  simp only [Dist8, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hd
  obtain ⟨⟨kh, kl, kt, ku, k0, k2, k7⟩, ⟨hl, ht, hu, h0, h2, h7⟩, ⟨lt, lu, l0, l2, l7⟩,
    ⟨tu, t0, t2, t7⟩, ⟨u0, u2, u7⟩, -, -⟩ := hd
  have L := fun (x y : LowReg) (h : x ≠ y) => (mt (toReg_inj x y).mp h : x.toReg ≠ y.toReg)
  intro s'
  have e : s' = execAll [.memImm .str l 0 (BitVec.ofNat 5 i)] (execAll (wY h l u y)
      (execAll (wMid k h l t u) (execAll (wExtra i k u) (execAll (wLoad i h l t) s)))) := by
    simp only [s', reduceWord_split, execAll_append]
  have A := wLoad_exec s i hi h l t hl ht lt h7 t7 l7 hr7
  generalize execAll (wLoad i h l t) s = s1 at A e
  obtain ⟨a1, a2, a3, am, ao⟩ := A
  have k1 : s1.reg k = s.reg k := ao _ (toReg_ne15 _) (L _ _ kh) (L _ _ kl) (L _ _ kt)
  have n1 : ∀ r : Reg, 8 ≤ r.val → r ≠ 15 → s1.regs r = s.regs r := fun r h8 h15 =>
    ao r h15 (by rw [ne_eq, hi_ne r h8]; trivial) (by rw [ne_eq, hi_ne r h8]; trivial)
      (by rw [ne_eq, hi_ne r h8]; trivial)
  have s7 : s1.reg 7 = s.reg 7 := ao _ (toReg_ne15 _) (L _ _ (Ne.symm h7)) (L _ _ (Ne.symm l7))
    (L _ _ (Ne.symm t7))
  have s2' : s1.reg 2 = s.reg 2 := ao _ (toReg_ne15 _) (L _ _ (Ne.symm h2)) (L _ _ (Ne.symm l2))
    (L _ _ (Ne.symm t2))
  have s0 : s1.reg 0 = s.reg 0 := ao _ (toReg_ne15 _) (L _ _ (Ne.symm h0)) (L _ _ (Ne.symm l0))
    (L _ _ (Ne.symm t0))
  have s9 := n1 9 (by decide) (by decide)
  have B := wExtra_exec s1 i k u ku u7 (by rw [s7]; exact hr7) (by rw [k1, s9]; omega)
  generalize execAll (wExtra i k u) s1 = s2 at B e
  obtain ⟨b1, bm, bo⟩ := B
  have bt : s2.reg t = s1.reg t := bo _ (toReg_ne15 _) (L _ _ (Ne.symm kt)) (L _ _ tu)
  have bh : s2.reg h = s1.reg h := bo _ (toReg_ne15 _) (L _ _ (Ne.symm kh)) (L _ _ hu)
  have bl : s2.reg l = s1.reg l := bo _ (toReg_ne15 _) (L _ _ (Ne.symm kl)) (L _ _ lu)
  have b2 : s2.reg 2 = s1.reg 2 := bo _ (toReg_ne15 _) (L _ _ (Ne.symm k2)) (L _ _ (Ne.symm u2))
  have b0 : s2.reg 0 = s1.reg 0 := bo _ (toReg_ne15 _) (L _ _ (Ne.symm k0)) (L _ _ (Ne.symm u0))
  have bn : ∀ r : Reg, 8 ≤ r.val → r ≠ 15 → s2.regs r = s1.regs r := fun r h8 h15 =>
    bo r h15 (by rw [ne_eq, hi_ne r h8]; trivial) (by rw [ne_eq, hi_ne r h8]; trivial)
  have hW := (fr s.mem s.sp (SH + i)).isLt
  have C := wMid_exec s2 k h l t u hl ht hu lt lu tu h2 l2 t2 u2 (by rw [b2, s2']; exact hr2)
    (by rw [bt, b1, a1, k1, s9]; split <;> omega) (by rw [bh, a2]; omega)
  generalize execAll (wMid k h l t u) s2 = s3 at C e
  obtain ⟨c1, cm, co⟩ := C
  have c2 : s3.reg 2 = s2.reg 2 := co _ (toReg_ne15 _) (L _ _ (Ne.symm h2)) (L _ _ (Ne.symm l2))
    (L _ _ (Ne.symm t2)) (L _ _ (Ne.symm u2))
  have c0 : s3.reg 0 = s2.reg 0 := co _ (toReg_ne15 _) (L _ _ (Ne.symm h0)) (L _ _ (Ne.symm l0))
    (L _ _ (Ne.symm t0)) (L _ _ (Ne.symm u0))
  have cn : ∀ r : Reg, 8 ≤ r.val → r ≠ 15 → s3.regs r = s2.regs r := fun r h8 h15 =>
    co r h15 (by rw [ne_eq, hi_ne r h8]; trivial) (by rw [ne_eq, hi_ne r h8]; trivial)
      (by rw [ne_eq, hi_ne r h8]; trivial) (by rw [ne_eq, hi_ne r h8]; trivial)
  have hL := (s3.reg l).isLt
  have D := wY_exec s3 h l u y hl hu lu l2 u2 hy (by rw [c2, b2, s2']; exact hr2) (by
    rw [bt, bh, bl, b1, a1, a2, a3] at c1; omega)
  generalize execAll (wY h l u y) s3 = s4 at D e
  obtain ⟨d1, dm, do'⟩ := D
  have d0 : s4.reg 0 = s3.reg 0 := do' _ (toReg_ne15 _) (L _ _ (Ne.symm h0)) (L _ _ (Ne.symm l0))
    (L _ _ (Ne.symm u0))
  have E := wStore_exec s4 i (by omega) l
  rw [← e] at E
  obtain ⟨em, eo⟩ := E
  have hl' : s'.reg l = s4.reg l := eo _ (toReg_ne15 _)
  have hh' : s'.reg h = s4.reg h := eo _ (toReg_ne15 _)
  have hy' : yval s3 y = yval s y := by
    cases y with
    | none => rfl
    | some r =>
      obtain ⟨r8, r15⟩ := hy r rfl
      simp only [yval, cn r r8 r15, bn r r8 r15, n1 r r8 r15]
  rw [hy'] at d1
  rw [bt, bh, bl, b1, a1, a2, a3, k1, s9] at c1
  have hsp : s1.sp = s.sp := n1 13 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hl', hh', d1, c1]; split <;> omega
  · have := (s4.reg l).isLt; have := yval_lt s y; have := yval_lt s3 y
    rw [hh']; split at c1 <;> omega
  · rw [em, dm, cm, bm, am, d0, c0, b0, s0, hl']
  · intro r h15 rk rh rl rt ru
    rw [eo r h15, do' r h15 rh rl ru, co r h15 rh rl rt ru, bo r h15 rk ru, ao r h15 rh rl rt]

end M0Crypto.Release.X25519CR
