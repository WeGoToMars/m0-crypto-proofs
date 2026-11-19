import M0Crypto.Release.Ed25519Sha512Exec
import M0Crypto.Release.Ed25519Sha512Rounds

set_option linter.unusedSimpArgs false

/-!
# Macro `round_body`, generic in the slot map

`round_run`: for any slot map `σ` into the eight frame pairs and any word `j` of the schedule
half at `r6`, `round_body` stores `roundS σ k w V` into the frame (`V` the pairs before, `k` the
pair at `r7`, `w` word `j` at `r6`) and advances `r7` by 8. `roundS (slot r)` is
`Ed25519Sha512Rounds.codeRound r` by definition, so the eight rounds of a group are instances.
The proof is three `simp` passes over the instruction lists (`roundT1`, `roundD`, `roundA`)
with the query-form rules of `Ed25519Sha512Exec`; no register or slot is named per round.
-/

namespace M0Crypto.Release.Ed25519Sha512Round

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Exec
open M0Crypto.Proofs (toReg_0 toReg_1 toReg_2 toReg_3 toReg_4 toReg_5 toReg_6 toReg_7)
open M0Crypto.Spec.Sha512 (Sigma0 Sigma1 Ch Maj)

/-! ## Pairs of words -/

/-- The high and low words of a 64-bit pair. -/
def hiW (x : BitVec 64) : Word := x.extractLsb' 32 32
def loW (x : BitVec 64) : Word := x.extractLsb' 0 32

@[simp] theorem hiW_app (h l : Word) : hiW (h ++ l) = h := BitVec.extractLsb'_append_eq_left
@[simp] theorem loW_app (h l : Word) : loW (h ++ l) = l := BitVec.extractLsb'_append_eq_right
@[simp] theorem hiW_loW (x : BitVec 64) : hiW x ++ loW x = x :=
  BitVec.extractLsb'_append_extractLsb' (w := 32) (len := 32)

/-! ## `adds dl, xl; adcs dh, xh` -/

/-- Macro `addP` on pairs: `dh:dl += xh:xl`. -/
theorem addP_regs (s : State) (dl dh xl xh : LowReg) (h1 : dh.toReg ≠ dl.toReg)
    (h2 : xh.toReg ≠ dl.toReg) (r : Reg) (hr : r ≠ 15) :
    (execAll (addP dl dh xl xh) s).regs r =
      let p := (s.regs dh.toReg ++ s.regs dl.toReg) + (s.regs xh.toReg ++ s.regs xl.toReg)
      if r = dh.toReg then hiW p else if r = dl.toReg then loW p else s.regs r := by
  simp only [addP, execAll, nx_adcs _ _ hr, nx_adds _ _ hr, nx_adds_c, nx_adds _ _ (toReg_ne_15 dh),
    nx_adds _ _ (toReg_ne_15 xh), h1, h2, ite_false, Ed25519Sha512Exec.pair_add, hiW_app, loW_app]

theorem addP_mem (s : State) (dl dh xl xh : LowReg) : (execAll (addP dl dh xl xh) s).mem = s.mem :=
  execAll_mem _ _ rfl

/-! ## Slots -/

theorem sp_vw (σ : Nat → Nat) (hσ : ∀ x, σ x < 8) (sp : Word) (x : Nat) (hi : Bool) :
    sp + BitVec.ofNat 32 ((BitVec.ofNat 8 (vw (σ x) hi)).toNat * 4) = slot sp (vw (σ x) hi) :=
  sp_imm sp _ (by have := vw_lt (hσ x) hi; simp only [VOFF, VB] at this; omega)

theorem vp_eq (m : Mem) (sp : Word) (i : Nat) :
    vp m sp i = read32 m (slot sp (vw i true)) ++ read32 m (slot sp (vw i false)) := rfl

/-- The two stores of pair `i`: low word, then high word. -/
def vset (m : Mem) (sp : Word) (i : Nat) (x : BitVec 64) : Mem :=
  write32 (write32 m (slot sp (vw i false)) (loW x)) (slot sp (vw i true)) (hiW x)

theorem vp_vset (m : Mem) (sp : Word) {i j : Nat} (hi : i < 8) (hj : j < 8) (x : BitVec 64) :
    vp (vset m sp j x) sp i = if i = j then x else vp m sp i := by
  rw [vset, vp_write m sp hi hj, hiW_loW]

/-- Word `j` of the schedule half at `b`. -/
def wAt (m : Mem) (b : Word) (j : Nat) : BitVec 64 :=
  read32 m (b + BitVec.ofNat 32 ((2 * j + 1) * 4)) ++ read32 m (b + BitVec.ofNat 32 (2 * j * 4))

theorem imm5 {k : Nat} (hk : k < 32) : (BitVec.ofNat 5 k).toNat = k := by
  simp [BitVec.toNat_ofNat]; omega

/-- The rules of a straight-line pass. -/
macro "rsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp (config := {decide := true})
  (disch := first | rfl | decide | assumption) only [execAll_append, execAll, nx_lsr, nx_lsl, nx_eors, nx_ands,
  nx_adds, nx_adcs, nx_movHi, nx_ldrSp, nx_ldrImm, addP_regs, addP_mem, mem_lsl, mem_lsr, mem_dp,
  mem_addReg, mem_movHi, mem_movImm, mem_addImm8, mem_ldrSp, mem_ldrImm, mem_ldrReg, mem_ldm, mem_rev,
  mem_addRdSp, mem_cmpImm, nx_strSp, nx_strSp_mem, nx_movImm, nx_addImm8, nx_ldrReg, nx_strReg,
  nx_cmpImm, mem_strReg, toReg_0, toReg_1,
  toReg_2, toReg_3, toReg_4, toReg_5, toReg_6, toReg_7, ↓reduceIte, ne_eq, reduceCtorEq,
  Fin.reduceEq, Fin.isValue, not_false_eq_true, hiW_loW, ldV, stV, $ts,*])

/-! ## `T1` -/

theorem t1_run (σ : Nat → Nat) (hσ : ∀ x, σ x < 8) {j : Nat} (hj : j < 8) (s : State) :
    let s' := execAll (roundT1 σ j) s
    let V := vp s.mem (s.regs 13)
    s'.mem = s.mem ∧
    s'.regs 3 ++ s'.regs 2 = Sigma1 (V (σ 4)) + Ch (V (σ 4)) (V (σ 5)) (V (σ 6)) + V (σ 7) +
      pairAt s.mem (s.regs 7) + wAt s.mem (s.regs 6) j ∧
    s'.regs 7 = s.regs 7 + 8#32 ∧
    ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 15 →
      s'.regs r = s.regs r := by
  have o1 : sOk [14, 18, 41] none = true := by decide
  have e0 := imm5 (show 2 * j < 32 by omega)
  have e1 := imm5 (show 2 * j + 1 < 32 by omega)
  have l7 := nx_ldm2 (a := 4) (b := 5) (n := 7) (l := 48) (hl := by decide) (hn := by decide)
  intro s' V
  refine ⟨?_, ?_, ?_, fun r h0 h1 h2 h3 h4 h5 h7 h15 => ?_⟩
  · simp only [s', roundT1, execAll_append, sigma_mem _ _ o1, addP_mem]
    exact execAll_mem _ _ rfl
  · simp only [s', V, roundT1, ldV]
    rsimp [l7, e0, e1, sp_vw σ hσ, sigma_regs _ _ o1, sigma_mem _ _ o1]
    simp only [vp_eq, pairAt, wAt, Sigma1_sig, Ed25519Sha512Pairs.Ch_pair]
  · simp only [s', roundT1]
    rsimp [l7, sigma_regs _ _ o1]
  · simp only [s', roundT1]
    rsimp [l7, sigma_regs _ _ o1, h0, h1, h2, h3, h4, h5, h7]

/-! ## `e' = d + T1`, `a' = T2 + T1` -/

theorem d_run (σ : Nat → Nat) (hσ : ∀ x, σ x < 8) (s : State) :
    let s' := execAll (roundD σ) s
    let T := s.regs 3 ++ s.regs 2
    s'.mem = vset s.mem (s.regs 13) (σ 3) (vp s.mem (s.regs 13) (σ 3) + T) ∧
    s'.regs 9 ++ s'.regs 8 = T ∧
    ∀ r : Reg, r ≠ 4 → r ≠ 5 → r ≠ 8 → r ≠ 9 → r ≠ 15 → s'.regs r = s.regs r := by
  intro s' T
  refine ⟨?_, ?_, fun r h4 h5 h8 h9 h15 => ?_⟩
  · simp only [s', T, roundD]
    rsimp [sp_vw σ hσ]
    rfl
  · simp only [s', T, roundD]
    rsimp []
  · simp only [s', roundD]
    rsimp [h4, h5, h8, h9]

theorem a_run (σ : Nat → Nat) (hσ : ∀ x, σ x < 8) (s : State) :
    let s' := execAll (roundA σ) s
    let V := vp s.mem (s.regs 13)
    s'.mem = vset s.mem (s.regs 13) (σ 7)
      (Sigma0 (V (σ 0)) + Maj (V (σ 0)) (V (σ 1)) (V (σ 2)) + (s.regs 9 ++ s.regs 8)) ∧
    ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 15 → s'.regs r = s.regs r := by
  have o1 : sOk [28, 34, 39] none = true := by decide
  intro s' V
  refine ⟨?_, fun r h0 h1 h2 h3 h4 h5 h15 => ?_⟩
  · simp only [s', V, roundA]
    rsimp [sp_vw σ hσ, sigma_regs _ _ o1, sigma_mem _ _ o1]
    simp only [vset, vp_eq, Sigma0_sig, Ed25519Sha512Pairs.Maj_pair]
  · simp only [s', roundA]
    rsimp [sigma_regs _ _ o1, h0, h1, h2, h3, h4, h5]

/-! ## The round -/

open M0Crypto.Release.Ed25519Sha512Rounds (upd slot codeRound) in
/-- `codeRound` with the slot map `σ`. -/
def roundS (σ : Nat → Nat) (k w : BitVec 64) (S : Nat → BitVec 64) : Nat → BitVec 64 :=
  let e := S (σ 4)
  let t1 := Sigma1 e + Ch e (S (σ 5)) (S (σ 6)) + S (σ 7) + k + w
  let S := upd S (σ 3) (S (σ 3) + t1)
  let a := S (σ 0)
  upd S (σ 7) (Sigma0 a + Maj a (S (σ 1)) (S (σ 2)) + t1)

theorem roundS_slot (r : Nat) (k w : BitVec 64) (S : Nat → BitVec 64) :
    roundS (rslot r) k w S = Ed25519Sha512Rounds.codeRound r k w S := rfl

/-- **Macro `round_body`** for any slot map into the eight pairs and any schedule word `j < 8`:
the pairs become `roundS σ K W` of the pairs before (`K` at `r7`, `W` word `j` at `r6`), by two
pair stores; `r7` advances by 8. -/
theorem round_run (σ : Nat → Nat) (hσ : ∀ x, σ x < 8) {j : Nat} (hj : j < 8) (s : State) :
    let s' := execAll (roundBody σ j) s
    let sp := s.regs 13
    (∀ i, i < 8 → vp s'.mem sp i =
      roundS σ (pairAt s.mem (s.regs 7)) (wAt s.mem (s.regs 6) j) (vp s.mem sp) i) ∧
    (∃ X Y, s'.mem = vset (vset s.mem sp (σ 3) X) sp (σ 7) Y) ∧
    s'.regs 7 = s.regs 7 + 8#32 ∧
    ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 15 →
      s'.regs r = s.regs r := by
  dsimp only
  rw [roundBody, execAll_append, execAll_append]
  obtain ⟨m1, v1, r7, k1⟩ := t1_run σ hσ hj s
  generalize execAll (roundT1 σ j) s = s1 at *
  obtain ⟨m2, v2, k2⟩ := d_run σ hσ s1
  generalize execAll (roundD σ) s1 = s2 at *
  obtain ⟨m3, k3⟩ := a_run σ hσ s2
  generalize execAll (roundA σ) s2 = s3 at *
  have q1 := k1 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have q2 := k2 13 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [q1, q2, v2, v1, m2, m1] at m3
  refine ⟨fun i hi => ?_, ⟨_, _, m3⟩, ?_, fun r h0 h1 h2 h3 h4 h5 h7 h8 h9 h15 => ?_⟩
  · rw [m3]
    simp (disch := first | exact hσ _ | assumption) only [vp_vset, roundS,
      Ed25519Sha512Rounds.upd]
  · rw [k3 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k2 7 (by decide) (by decide) (by decide) (by decide) (by decide), r7]
  · rw [k3 r h0 h1 h2 h3 h4 h5 h15, k2 r h4 h5 h8 h9 h15, k1 r h0 h1 h2 h3 h4 h5 h7 h15]

end M0Crypto.Release.Ed25519Sha512Round
