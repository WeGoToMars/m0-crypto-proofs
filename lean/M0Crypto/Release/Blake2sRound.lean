import M0Crypto.Release.Blake2sG
import M0Crypto.Release.Frame
import M0Crypto.Release.Blake2sCompressCode

set_option linter.unusedSimpArgs false

/-!
# One `B2_G` as a step of the working vector

`Inv s sp v m c`: the machine state `s` holds the 16-word vector `v` and the message `m` in
the layout of `src/blake2s_compress.S`. The word `v[c]` (if any) is in r0 and its frame slot
is stale. `step` is the one lemma for the `B2_G` macro in this vector view.
-/

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (read32_write32_slot')
open M0Crypto.Spec.Blake2s (G)
open M0Crypto.Proofs (toReg_2 toReg_5 toReg_6 toReg_7)

/-- `G` applied to the vector entries `a b ic id`. Indices are pairwise distinct. -/
def mixF (v : Nat → Word) (a b ic id : Nat) (x y : Word) : Nat → Word := fun k =>
  let q := G (v a) (v b) (v ic) (v id) x y
  if k = id then q.2.2.2 else if k = ic then q.2.2.1 else if k = b then q.2.1
  else if k = a then q.1 else v k

theorem mixF_id (v : Nat → Word) (a b ic id : Nat) (x y : Word) :
    mixF v a b ic id x y id = (G (v a) (v b) (v ic) (v id) x y).2.2.2 := by simp [mixF]
theorem mixF_ic (v : Nat → Word) (a b ic id : Nat) (x y : Word) (h : ic ≠ id) :
    mixF v a b ic id x y ic = (G (v a) (v b) (v ic) (v id) x y).2.2.1 := by simp [mixF, h]
theorem mixF_b (v : Nat → Word) (a b ic id : Nat) (x y : Word) (h1 : b ≠ id) (h2 : b ≠ ic) :
    mixF v a b ic id x y b = (G (v a) (v b) (v ic) (v id) x y).2.1 := by simp [mixF, h1, h2]
theorem mixF_a (v : Nat → Word) (a b ic id : Nat) (x y : Word) (h1 : a ≠ id) (h2 : a ≠ ic) (h3 : a ≠ b) :
    mixF v a b ic id x y a = (G (v a) (v b) (v ic) (v id) x y).1 := by simp [mixF, h1, h2, h3]
theorem mixF_o (v : Nat → Word) (a b ic id : Nat) (x y : Word) (k : Nat) (h1 : k ≠ id) (h2 : k ≠ ic)
    (h3 : k ≠ b) (h4 : k ≠ a) : mixF v a b ic id x y k = v k := by simp [mixF, h1, h2, h3, h4]

structure Inv (s : State) (sp : Word) (v m : Nat → Word) (c : Option Nat) : Prop where
  spR : s.regs 13 = sp
  r8 : s.regs 8 = v 0
  memV : ∀ i, 1 ≤ i → i < 8 → c ≠ some i → read32 s.mem (slot sp i) = v i
  r0 : ∀ i, c = some i → s.regs 0 = v i
  r2 : s.regs 2 = v 8
  r5 : s.regs 5 = v 9
  r6 : s.regs 6 = v 10
  r7 : s.regs 7 = v 11
  r9 : s.regs 9 = v 12
  r10 : s.regs 10 = v 13
  r11 : s.regs 11 = v 14
  r12 : s.regs 12 = v 15
  memM : ∀ i, i < 16 → read32 s.mem (slot sp (8 + i)) = m i

/-- `m'` differs from `m` by stores to frame slots `1..7` only. -/
inductive MW (sp : Word) : Mem → Mem → Prop
  | refl (m : Mem) : MW sp m m
  | store {m m' : Mem} (i : Nat) (w : Word) : 1 ≤ i → i < 8 → MW sp m m' →
      MW sp m (write32 m' (slot sp i) w)

theorem MW_trans {sp : Word} {m1 m2 m3 : Mem} (h1 : MW sp m1 m2) (h2 : MW sp m2 m3) : MW sp m1 m3 := by
  induction h2 with
  | refl => exact h1
  | store i w hi hj _ ih => exact MW.store i w hi hj ih

/-- The register assignment of a `B2_G`: row-c register and the index it holds. -/
def CIdx (creg : LowReg) (ic : Nat) : Prop :=
  (creg = 2 ∧ ic = 8) ∨ (creg = 5 ∧ ic = 9) ∨ (creg = 6 ∧ ic = 10) ∨ (creg = 7 ∧ ic = 11)

theorem step (s : State) (sp : Word) (v m : Nat → Word) (c : Option Nat)
    (a b ic id x y : Nat) (creg : LowReg) (dreg : Reg) (haveA keepA : Bool)
    (hI : Inv s sp v m c)
    (ha : a < 8) (hb1 : 1 ≤ b) (hb : b < 8) (hab : a ≠ b) (hx : x < 16) (hy : y < 16)
    (hC : CIdx creg ic) (hd : DReg dreg) (hdi : id = dreg.val + 3)
    (hcA : haveA = true → c = some a) (hcN : haveA = false → c = none)
    (hcb : c ≠ some b) (hk : keepA = true → a ≠ 0) :
    let s' := execAll (b2g a b creg dreg x y haveA keepA) s
    Inv s' sp (mixF v a b ic id (m x) (m y)) m (if keepA then some a else none) ∧
    MW sp s.mem s'.mem ∧ s'.regs 14 = s.regs 14 := by
  intro s'
  have hcv : creg.val = 2 ∨ creg.val = 5 ∨ creg.val = 6 ∨ creg.val = 7 := by
    rcases hC with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide
  have hic : ic = 8 ∨ ic = 9 ∨ ic = 10 ∨ ic = 11 := by
    rcases hC with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hCR : Scr rB rT creg := by
    refine ⟨by decide, by decide, by decide, by decide, by omega, by omega, by decide, ?_, ?_⟩ <;>
      rcases hcv with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨hd9, hd12⟩ := hd
  obtain ⟨e0, ec, ed, e8, emem, ef⟩ := b2g_effect s a b x y creg dreg haveA keepA ha hb hx hy hCR ⟨hd9, hd12⟩
  have spv : s.regs 13 = sp := hI.spR
  -- operands
  have hA : (if haveA then s.regs 0 else if a = 0 then s.regs 8 else read32 s.mem (slot (s.regs 13) a)) = v a := by
    cases hh : haveA
    · have := hcN hh
      by_cases h0 : a = 0
      · subst h0; simpa using hI.r8
      · simp only [h0, ite_false, spv]
        exact hI.memV a (by omega) ha (by rw [this]; simp)
    · exact hI.r0 a (hcA hh) |> fun h => by simpa using h
  have hB : read32 s.mem (slot (s.regs 13) b) = v b := by rw [spv]; exact hI.memV b hb1 hb hcb
  have hX : read32 s.mem (slot (s.regs 13) (8 + x)) = m x := by rw [spv]; exact hI.memM x hx
  have hY : read32 s.mem (slot (s.regs 13) (8 + y)) = m y := by rw [spv]; exact hI.memM y hy
  have hCv : s.reg creg = v ic := by
    rcases hC with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h <;> subst h' <;>
      simp [State.reg, toReg_2, toReg_5, toReg_6, toReg_7, hI.r2, hI.r5, hI.r6, hI.r7]
  have hDv : s.regs dreg = v id := by
    obtain ⟨dv, hdv⟩ := dreg
    simp only at hd9 hd12 hdi
    have : dv = 9 ∨ dv = 10 ∨ dv = 11 ∨ dv = 12 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> subst hdi <;> first | exact hI.r9 | exact hI.r10 | exact hI.r11 | exact hI.r12
  -- the new values
  have hq : G (if haveA then s.regs 0 else if a = 0 then s.regs 8 else read32 s.mem (slot (s.regs 13) a))
      (read32 s.mem (slot (s.regs 13) b)) (s.reg creg) (s.regs dreg)
      (read32 s.mem (slot (s.regs 13) (8 + x))) (read32 s.mem (slot (s.regs 13) (8 + y))) =
      G (v a) (v b) (v ic) (v id) (m x) (m y) := by rw [hA, hB, hCv, hDv, hX, hY]
  rw [hq] at e0 ec ed e8 emem
  have hdv : dreg.val = id - 3 := by omega
  have hne : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rB.val → r.val ≠ rT.val → r.val ≠ 4 → r.val ≠ 8 →
      r.val ≠ creg.val → r.val ≠ dreg.val → s'.regs r = s.regs r := fun r h15 h0 h1 h3 h4 h8 hc hdr =>
    ef r h15 h0 h1 h3 h4 h8 hc (fun h => hdr (by rw [h]))
  have hreg : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rB.val → r.val ≠ rT.val → r.val ≠ 4 → r.val ≠ 8 →
      s'.regs r = if r.val = creg.val then (G (v a) (v b) (v ic) (v id) (m x) (m y)).2.2.1
        else if r.val = dreg.val then (G (v a) (v b) (v ic) (v id) (m x) (m y)).2.2.2 else s.regs r := by
    intro r h15 h0 h1 h3 h4 h8
    by_cases h1' : r.val = creg.val
    · have : r = creg.toReg := Fin.ext h1'
      rw [if_pos h1', this]; simpa [State.reg] using ec
    · rw [if_neg h1']
      by_cases h2 : r.val = dreg.val
      · have : r = dreg := Fin.ext h2
        rw [if_pos h2, this]; exact ed
      · rw [if_neg h2]; exact hne r h15 h0 h1 h3 h4 h8 h1' h2
  have hm : s'.mem = write32 (if keepA = true ∨ a = 0 then s.mem else write32 s.mem (slot sp a)
      (G (v a) (v b) (v ic) (v id) (m x) (m y)).1) (slot sp b) (G (v a) (v b) (v ic) (v id) (m x) (m y)).2.1 := by
    rw [emem, spv]
  have hcc : c = none ∨ c = some a := by
    cases hh : haveA
    · exact Or.inl (hcN hh)
    · exact Or.inr (hcA hh)
  have hdne : id ≠ ic := by omega
  have hq14 : s'.regs 14 = s.regs 14 := hne 14 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by omega)
  have hcic : (creg.val = 2 ∧ ic = 8) ∨ (creg.val = 5 ∧ ic = 9) ∨ (creg.val = 6 ∧ ic = 10) ∨
      (creg.val = 7 ∧ ic = 11) := by
    rcases hC with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> subst h <;> subst h' <;> decide
  have regField : ∀ (k : Nat) (hk : k < 16), k ≠ 15 → k ≠ 0 → k ≠ rB.val → k ≠ rT.val → k ≠ 4 → k ≠ 8 →
      ∀ (j : Nat), ((k = 2 ∧ j = 8) ∨ (k = 5 ∧ j = 9) ∨ (k = 6 ∧ j = 10) ∨ (k = 7 ∧ j = 11) ∨
        (k = 9 ∧ j = 12) ∨ (k = 10 ∧ j = 13) ∨ (k = 11 ∧ j = 14) ∨ (k = 12 ∧ j = 15)) →
      s.regs ⟨k, hk⟩ = v j →
      s'.regs ⟨k, hk⟩ = mixF v a b ic id (m x) (m y) j := by
    intro k hk h15 h0 h1 h3 h4 h8 j hj hv
    rw [hreg ⟨k, hk⟩ h15 h0 h1 h3 h4 h8, hv]
    unfold mixF
    dsimp only
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hq14⟩
  · rw [hne 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)]
    exact spv
  · by_cases h0 : a = 0
    · have hkf : keepA = false := by
        cases hh : keepA
        · rfl
        · exact absurd h0 (hk hh)
      have hm0 := mixF_a v a b ic id (m x) (m y) (by omega) (by omega) (by omega)
      rw [h0] at hm0 ⊢
      rw [hm0]
      subst hkf
      subst h0
      simpa using e8
    · rw [mixF_o _ _ _ _ _ _ _ 0 (by omega) (by omega) (by omega) (by omega)]
      have : ¬(¬keepA = true ∧ a = 0) := fun h => h0 h.2
      simp only [this, ite_false] at e8
      rw [e8]; exact hI.r8
  · -- memV
    intro i h1 h8 hci
    rw [hm, read32_write32_slot' _ _ _ b i (by omega) (by omega)]
    by_cases hbi : b = i
    · rw [if_pos hbi, ← hbi, mixF_b _ _ _ _ _ _ _ (by omega) (by omega)]
    · rw [if_neg hbi]
      by_cases hka : keepA = true ∨ a = 0
      · rw [if_pos hka]
        have hia : i ≠ a := by
          intro h
          rcases hka with hk' | h0
          · simp [hk', h] at hci
          · omega
        have hcne : c ≠ some i := by
          rcases hcc with h | h <;> rw [h]
          · simp
          · simp; omega
        rw [hI.memV i h1 h8 hcne, mixF_o _ _ _ _ _ _ _ i (by omega) (by omega) (by omega) hia]
      · rw [if_neg hka, read32_write32_slot' _ _ _ a i (by omega) (by omega)]
        by_cases hai : a = i
        · rw [if_pos hai, ← hai, mixF_a _ _ _ _ _ _ _ (by omega) (by omega) (by omega)]
        · rw [if_neg hai]
          have hcne : c ≠ some i := by
            rcases hcc with h | h <;> rw [h]
            · simp
            · simp; omega
          rw [hI.memV i h1 h8 hcne, mixF_o _ _ _ _ _ _ _ i (by omega) (by omega) (by omega) (by omega)]
  · -- r0
    intro i hi
    cases hkk : keepA
    · simp [hkk] at hi
    · simp [hkk] at hi
      subst hi
      rw [mixF_a _ _ _ _ _ _ _ (by omega) (by omega) (by omega)]
      simpa using e0
  · exact regField 2 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 8 (by omega) hI.r2
  · exact regField 5 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 9 (by omega) hI.r5
  · exact regField 6 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 10 (by omega) hI.r6
  · exact regField 7 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 11 (by omega) hI.r7
  · exact regField 9 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 12 (by omega) hI.r9
  · exact regField 10 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 13 (by omega) hI.r10
  · exact regField 11 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 14 (by omega) hI.r11
  · exact regField 12 (by omega) (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) 15 (by omega) hI.r12
  · -- memM
    intro i hi
    rw [hm, read32_write32_slot' _ _ _ b (8 + i) (by omega) (by omega), if_neg (by omega)]
    by_cases hka : keepA = true ∨ a = 0
    · rw [if_pos hka]; exact hI.memM i hi
    · rw [if_neg hka, read32_write32_slot' _ _ _ a (8 + i) (by omega) (by omega), if_neg (by omega)]
      exact hI.memM i hi
  · -- MW
    rw [hm]
    refine MW.store b _ hb1 hb ?_
    by_cases hka : keepA = true ∨ a = 0
    · rw [if_pos hka]; exact MW.refl _
    · rw [if_neg hka]
      exact MW.store a _ (by omega) ha (MW.refl _)


theorem step' (s s' : State) (sp : Word) (v m : Nat → Word) (c : Option Nat)
    (a b ic id x y : Nat) (creg : LowReg) (dreg : Reg) (haveA keepA : Bool)
    (hI : Inv s sp v m c)
    (ha : a < 8) (hb1 : 1 ≤ b) (hb : b < 8) (hab : a ≠ b) (hx : x < 16) (hy : y < 16)
    (hC : CIdx creg ic) (hd : DReg dreg) (hdi : id = dreg.val + 3)
    (hcA : haveA = true → c = some a) (hcN : haveA = false → c = none)
    (hcb : c ≠ some b) (hk : keepA = true → a ≠ 0)
    (hs : s' = execAll (b2g a b creg dreg x y haveA keepA) s) :
    Inv s' sp (mixF v a b ic id (m x) (m y)) m (if keepA then some a else none) ∧
    MW sp s.mem s'.mem ∧ s'.regs 14 = s.regs 14 := by
  subst hs; exact step s sp v m c a b ic id x y creg dreg haveA keepA hI ha hb1 hb hab hx hy hC hd hdi
    hcA hcN hcb hk

/-! ## One round -/

open M0Crypto.Release.Blake2sCode (roundS gListS)

/-- The vector after one `B2_ROUND`, in the assembly's order of the eight `G`s. -/
def roundF (v m : Nat → Word) (sch : Nat → Nat) : Nat → Word :=
  let v1 := mixF v 2 6 10 14 (m (sch 4)) (m (sch 5))
  let v2 := mixF v1 0 4 8 12 (m (sch 0)) (m (sch 1))
  let v3 := mixF v2 1 5 9 13 (m (sch 2)) (m (sch 3))
  let v4 := mixF v3 3 7 11 15 (m (sch 6)) (m (sch 7))
  let v5 := mixF v4 3 4 9 14 (m (sch 14)) (m (sch 15))
  let v6 := mixF v5 0 5 10 15 (m (sch 8)) (m (sch 9))
  let v7 := mixF v6 1 6 11 12 (m (sch 10)) (m (sch 11))
  mixF v7 2 7 8 13 (m (sch 12)) (m (sch 13))

theorem roundS_eq (sch : Nat → Nat) (first : Bool) : roundS sch first =
    gListS sch first 0 ++ gListS sch first 1 ++ gListS sch first 2 ++ gListS sch first 3 ++
    gListS sch first 4 ++ gListS sch first 5 ++ gListS sch first 6 ++ gListS sch first 7 := by
  simp [roundS, List.range_succ]

theorem round_effect (s : State) (sp : Word) (v m : Nat → Word) (sch : Nat → Nat) (first : Bool)
    (hsch : ∀ i, i < 16 → sch i < 16)
    (hI : Inv s sp v m (if first then none else some 2)) :
    let s' := execAll (roundS sch first) s
    Inv s' sp (roundF v m sch) m (some 2) ∧ MW sp s.mem s'.mem ∧ s'.regs 14 = s.regs 14 := by
  intro s'
  have h4 := hsch 4 (by omega); have h5 := hsch 5 (by omega); have h0 := hsch 0 (by omega)
  have h1 := hsch 1 (by omega); have h2 := hsch 2 (by omega); have h3 := hsch 3 (by omega)
  have h6 := hsch 6 (by omega); have h7 := hsch 7 (by omega); have h8 := hsch 8 (by omega)
  have h9 := hsch 9 (by omega); have h10 := hsch 10 (by omega); have h11 := hsch 11 (by omega)
  have h12 := hsch 12 (by omega); have h13 := hsch 13 (by omega); have h14 := hsch 14 (by omega)
  have h15 := hsch 15 (by omega)
  have hD : ∀ d : Reg, 9 ≤ d.val → d.val ≤ 12 → DReg d := fun d a b => ⟨a, b⟩
  obtain ⟨s1, hs1⟩ : ∃ t, t = execAll (gListS sch first 0) s := ⟨_, rfl⟩
  obtain ⟨I1, W1, R1⟩ := step' s s1 sp _ m _ 2 6 10 14 (sch 4) (sch 5) 6 11 (!first) false hI
    (by omega) (by omega) (by omega) (by omega) h4 h5 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (hD 11 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs1
  obtain ⟨s2, hs2⟩ : ∃ t, t = execAll (gListS sch first 1) s1 := ⟨_, rfl⟩
  obtain ⟨I2, W2, R2⟩ := step' s1 s2 sp _ m _ 0 4 8 12 (sch 0) (sch 1) 2 9 false false I1
    (by omega) (by omega) (by omega) (by omega) h0 h1 (Or.inl ⟨rfl, rfl⟩) (hD 9 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs2
  obtain ⟨s3, hs3⟩ : ∃ t, t = execAll (gListS sch first 2) s2 := ⟨_, rfl⟩
  obtain ⟨I3, W3, R3⟩ := step' s2 s3 sp _ m _ 1 5 9 13 (sch 2) (sch 3) 5 10 false false I2
    (by omega) (by omega) (by omega) (by omega) h2 h3 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (hD 10 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs3
  obtain ⟨s4, hs4⟩ : ∃ t, t = execAll (gListS sch first 3) s3 := ⟨_, rfl⟩
  obtain ⟨I4, W4, R4⟩ := step' s3 s4 sp _ m _ 3 7 11 15 (sch 6) (sch 7) 7 12 false true I3
    (by omega) (by omega) (by omega) (by omega) h6 h7 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (hD 12 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs4
  obtain ⟨s5, hs5⟩ : ∃ t, t = execAll (gListS sch first 4) s4 := ⟨_, rfl⟩
  obtain ⟨I5, W5, R5⟩ := step' s4 s5 sp _ m _ 3 4 9 14 (sch 14) (sch 15) 5 11 true false I4
    (by omega) (by omega) (by omega) (by omega) h14 h15 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (hD 11 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs5
  obtain ⟨s6, hs6⟩ : ∃ t, t = execAll (gListS sch first 5) s5 := ⟨_, rfl⟩
  obtain ⟨I6, W6, R6⟩ := step' s5 s6 sp _ m _ 0 5 10 15 (sch 8) (sch 9) 6 12 false false I5
    (by omega) (by omega) (by omega) (by omega) h8 h9 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (hD 12 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs6
  obtain ⟨s7, hs7⟩ : ∃ t, t = execAll (gListS sch first 6) s6 := ⟨_, rfl⟩
  obtain ⟨I7, W7, R7⟩ := step' s6 s7 sp _ m _ 1 6 11 12 (sch 10) (sch 11) 7 9 false false I6
    (by omega) (by omega) (by omega) (by omega) h10 h11 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (hD 9 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs7
  obtain ⟨s8, hs8⟩ : ∃ t, t = execAll (gListS sch first 7) s7 := ⟨_, rfl⟩
  obtain ⟨I8, W8, R8⟩ := step' s7 s8 sp _ m _ 2 7 8 13 (sch 12) (sch 13) 2 10 false true I7
    (by omega) (by omega) (by omega) (by omega) h12 h13 (Or.inl ⟨rfl, rfl⟩) (hD 10 (by decide) (by decide)) rfl
    (by cases first <;> simp_all) (by cases first <;> simp_all) (by cases first <;> simp_all) (by simp_all) hs8
  have hs' : s' = s8 := by
    simp only [s', roundS_eq, execAll_append, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
  rw [hs']
  exact ⟨I8, MW_trans W1 (MW_trans W2 (MW_trans W3 (MW_trans W4 (MW_trans W5 (MW_trans W6 (MW_trans W7 W8)))))),
    by rw [R8, R7, R6, R5, R4, R3, R2, R1]⟩


/-! ## Agreement with the RFC round -/

/-- The 16 entries of a function vector. -/
def arr16 (f : Nat → Word) : Array Word :=
  #[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15]

open M0Crypto.Release.Blake2sCode (sg)

end M0Crypto.Release.Blake2s
