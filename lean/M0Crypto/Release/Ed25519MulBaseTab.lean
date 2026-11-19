import M0Crypto.Release.Ed25519MulBaseVal

/-!
# `m0c_ge_mul_base`'s tables

The lookups and `odd_b[0]` read the comb table and the odd-multiples table from the code. With
the code at `base` and the build's tables the specification's (`TablesOk`), `look_ok` gives the
lookup's entry for every nonzero digit `|δ| ≤ 8` of comb `cr` as the Niels form of
`combTerm nc cr δ • B` (by `TableLink.tab_eq2` and `Comb.lookup_eq`), and `odd_ok` gives
`odd_b[0]` as `B` (by `TableLink.odd_b`).
-/

namespace M0Crypto.Release.Ed25519MulBaseTab

open M0Crypto.Armv6M (Word Mem read32)
open M0Crypto.Thumb (CodeAt ofNat_add_assoc)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519MulBaseProg (mbQ mbP maS mbS)
open M0Crypto.Release.Ed25519MulBaseVal
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Release.Ed25519Bridge (Bpt toF)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519Formulas (Niels d2)
open M0Crypto.Release.Ed25519Tables (leVal leVals TablesOk)
open M0Crypto.Release.Ed25519TableLink (tabEntry nielsF)
open M0Crypto.Release.Ed25519LookupTE (gE gS gS' gT wv lookV)
open M0Crypto.Release.Ed25519Lookup (dIdx ent)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Artifacts.Ed25519Compact (ed_comb ed_odd_b)
open Lean.Grind

/-! ## Table values from the code -/

theorem leVal_eq : ∀ (n : Nat) (bs : List (BitVec 8)), leVal n bs = decodeInt (bs.take n)
  | 0, _ => rfl
  | n + 1, [] => by simp only [leVal, List.headD_nil, List.tail_nil, leVal_eq n [], List.take_nil, decodeInt]; rfl
  | n + 1, b :: bs => by simp only [leVal, leVal_eq n bs, List.take_succ_cons, decodeInt, List.headD_cons, List.tail_cons]

theorem leVals_getD : ∀ (w k : Nat) (bs : List (BitVec 8)) (i : Nat), i < k →
    (leVals w k bs).getD i 0 = leVal w (bs.drop (w * i))
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | w, k + 1, bs, 0, _ => by simp [leVals]
  | w, k + 1, bs, i + 1, h => by
    simp only [leVals, List.getD_cons_succ]
    rw [leVals_getD w k _ i (by omega), List.drop_drop, Nat.mul_succ, Nat.add_comm]

theorem leVals_length : ∀ (w k : Nat) (bs : List (BitVec 8)), (leVals w k bs).length = k
  | _, 0, _ => rfl
  | w, k + 1, bs => by simp only [leVals, List.length_cons, leVals_length w k]

theorem tab_three {vals : List Nat} {k : Nat} (h : 3 * k + 3 ≤ vals.length) :
    tabEntry vals k = ⟨toF (vals.getD (3 * k) 0), toF (vals.getD (3 * k + 1) 0), toF (vals.getD (3 * k + 2) 0)⟩ := by
  unfold tabEntry
  obtain ⟨l, hl⟩ : ∃ l, vals.drop (3 * k) = vals.getD (3 * k) 0 :: vals.getD (3 * k + 1) 0 :: vals.getD (3 * k + 2) 0 :: l := by
    refine ⟨vals.drop (3 * k + 3), ?_⟩
    simp only [List.getD_eq_getElem?_getD]
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega)]
    simp only [List.getElem?_eq_getElem (show 3 * k < vals.length by omega),
      List.getElem?_eq_getElem (show 3 * k + 1 < vals.length by omega),
      List.getElem?_eq_getElem (show 3 * k + 2 < vals.length by omega), Option.getD_some]
  rw [hl]; rfl

/-- **A table value read from the code**: value `i` of a table of `32`-byte values at `o`. -/
theorem fe_tab {m : Mem} {base : Word} {B : List (BitVec 8)} (hc : CodeAt m base B) {o N i : Nat}
    (hi : i < N) (hl : o + 32 * N ≤ B.length) :
    feVal m (base + BitVec.ofNat 32 (o + 32 * i)) = (leVals 32 N (B.drop o)).getD i 0 := by
  rw [← Ed25519GeCompressProg.dec_fe, Ed25519ScReduceProg.code_bytes hc (by
      have : 32 * i + 32 ≤ 32 * N := by omega
      omega), leVals_getD 32 N _ i hi, leVal_eq, List.drop_drop]

/-! ## `odd_b[0]` -/

/-- **`odd_b[0]` is `B`** in Niels form. -/
theorem odd_ok {m0 : Mem} {base : Word} {c : Ctx} (b : Build) (hc : CodeAt m0 base b.bytes) (ht : TablesOk b)
    (h3 : c.ptr 3 = base + BitVec.ofNat 32 ed_odd_b) : NielsV (oddV c m0) Bpt := by
  have hl : ed_odd_b + 32 * 24 ≤ b.bytes.length := by
    rw [Build.bytes_length, ← ht.comb_end]; cases b <;> decide
  have hob : oB c m0 = (b.bytes.drop ed_odd_b).take 96 := by
    rw [oB, h3, BitVec.add_zero, Ed25519ScReduceProg.code_bytes hc (o := ed_odd_b) (n := 96) (Nat.le_trans (Nat.add_le_add_left (by decide) _) hl)]
  have hb : ∀ j, j < 3 → decodeInt (((oB c m0).drop (32 * j)).take 32) =
      (leVals 32 24 (b.bytes.drop ed_odd_b)).getD j 0 := fun j hj => by
    rw [hob, List.drop_take, List.take_take, show min 32 (96 - 32 * j) = 32 by omega,
      leVals_getD 32 24 _ j (by omega), leVal_eq]
  have e0 := hb 0 (by decide)
  have e1 := hb 1 (by decide)
  have e2 := hb 2 (by decide)
  simp only [Nat.mul_zero, List.drop_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2
  rw [List.take_of_length_le (by simp [oB, Footprint.bytesAt_length])] at e2
  have ho := Ed25519TableLink.odd_b ht 0 (by decide)
  rw [tab_three (by rw [leVals_length]; decide), show (2 * ((0 : Nat) : Int) + 1) = 1 from rfl,
    IntModule.one_zsmul] at ho
  simp only [Nat.mul_zero, Nat.zero_add] at ho
  refine ⟨_, _, _, rfl, ?_⟩
  rw [e0, e1, e2, fI_nat, fI_nat, fI_nat, ho]

/-! ## The comb rows -/

open M0Crypto.Release.Ed25519ScReduceProg (dW)

/-- The tables' `combVal` is the comb's, which is nonnegative. -/
theorem combVal_eq (b : Build) : ∀ c < b.combs, ∀ j < 8,
    ((Ed25519Tables.combVal b.combs c j).toNat : Int) = Ed25519Comb.combVal b.combs c j := by
  cases b <;> decide

/-- The entries of `m0c_ed_comb`. -/
def combEnt (b : Build) (c j : Nat) : Niels Fp := tabEntry (leVals 32 (24 * b.combs) (b.bytes.drop ed_comb)) (8 * c + j)

theorem comb_table {b : Build} (ht : TablesOk b) : Ed25519Comb.CombTable b.combs (combEnt b) := by
  intro c hc j hj
  rw [combEnt, Ed25519TableLink.tab_eq2 (fun c j => (Ed25519Tables.combVal b.combs c j).toNat) ht.comb c hc j hj,
    combVal_eq b c hc j hj]

theorem dig_facts : ∀ n : Nat, n < 17 → ((dwordI ((n : Int) - 8)) + 8#32).toNat ≤ 16 ∧
    dIdx (dwordI ((n : Int) - 8)) = ((n : Int) - 8).natAbs ∧ (dwordI ((n : Int) - 8)).msb = decide ((n : Int) - 8 < 0) := by
  decide

/-- Element `e` of the selected entry, read from the row. -/
theorem wv_gE {m0 : Mem} {row d : Word} (hd : (d + 8#32).toNat ≤ 16) (ha : dIdx d ≠ 0) {e : Nat} (he : e < 3)
    {g : Nat → Nat} (hg : ∀ i < 8, g i = 8 * e + i) :
    wv (fun i => gE (dW (bytesAt m0 row 768)) d (g i)) = feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * e)) := by
  rw [Ed25519LookupTE.feVal_wv]
  apply Ed25519LookupTE.wv_congr; intro i hi
  rw [hg i hi, Ed25519LookupTE.gE_congr (w' := Ed25519LookupTE.rw m0 row)
      (fun k hk => (Ed25519ScReduceProg.word_dW m0 row (n := 192) (j := 24 * k + (8 * e + i)) (by omega)).symm),
    Ed25519LookupTE.gE_ent hd]
  simp only [ent, ha, ↓reduceIte]
  rw [ofNat_add_assoc, show 96 * (dIdx d - 1) + 32 * e + 4 * i = 96 * (dIdx d - 1) + 4 * (8 * e + i) by omega]

/-- **The lookup's values** for a nonzero digit word: the entry's elements, swapped and negated for
a negative digit. -/
theorem look_vals {m0 : Mem} {row d : Word} (hd : (d + 8#32).toNat ≤ 16) (ha : dIdx d ≠ 0) :
    lookV [.b (bytesAt m0 row 768), .w d] =
      if d.msb then
        [.f (feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 1))),
         .f (feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 0))),
         .f (-(feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 2)) : Int))]
      else
        [.f (feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 0))),
         .f (feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 1))),
         .f (feVal m0 (row + BitVec.ofNat 32 (96 * (dIdx d - 1) + 32 * 2)))] := by
  simp only [lookV, gT]
  rw [show gS (dW (bytesAt m0 row 768)) d = fun n => gE (dW (bytesAt m0 row 768)) d (if d.msb then n + 8 else n)
      from rfl, show gS' (dW (bytesAt m0 row 768)) d =
      fun n => gE (dW (bytesAt m0 row 768)) d (if d.msb then n else n + 8) from rfl]
  cases hm : d.msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [wv_gE hd ha (e := 0) (by decide) (g := fun i => i) (fun i _ => by omega),
      wv_gE hd ha (e := 1) (by decide) (g := fun i => i + 8) (fun i _ => by omega),
      wv_gE hd ha (e := 2) (by decide) (g := fun i => 16 + i) (fun i _ => by omega)]
  · simp only [↓reduceIte]
    rw [wv_gE hd ha (e := 1) (by decide) (g := fun i => i + 8) (fun i _ => by omega),
      wv_gE hd ha (e := 0) (by decide) (g := fun i => i) (fun i _ => by omega),
      wv_gE hd ha (e := 2) (by decide) (g := fun i => 16 + i) (fun i _ => by omega)]

theorem fI_neg (x : Int) : fI (-x) = 0 - fI x := by
  rw [show -x = 0 - x by omega, fI_sub, show fI 0 = 0 from Ring.intCast_zero]

/-- **The lookups** in a build whose comb table is the specification's. -/
theorem look_ok {m0 : Mem} {base : Word} {c : Ctx} (b : Build) (hc : CodeAt m0 base b.bytes) (ht : TablesOk b)
    (h2 : c.ptr 2 = base + BitVec.ofNat 32 ed_comb) : LookOk b.combs c m0 := by
  intro cr hcr δ h1 h2' h0
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 17 ∧ δ = (n : Int) - 8 := ⟨(δ + 8).toNat, by omega, by omega⟩
  obtain ⟨hdd, hidx, hmsb⟩ := dig_facts n hn
  have ha : dIdx (dwordI ((n : Int) - 8)) ≠ 0 := by rw [hidx]; omega
  have hl : ed_comb + 32 * (24 * b.combs) ≤ b.bytes.length := by
    rw [Build.bytes_length, ht.comb_end]; exact Nat.le_refl _
  have hrow : rowAt b.combs c m0 cr = .b (bytesAt m0 (base + BitVec.ofNat 32 (ed_comb + 768 * cr)) 768) := by
    simp only [rowAt, Src.val, Loc.addr, XLen.v, h2, ofNat_add_assoc]
  have hf : ∀ e < 3, feVal m0 (base + BitVec.ofNat 32 (ed_comb + 768 * cr) +
      BitVec.ofNat 32 (96 * (dIdx (dwordI ((n : Int) - 8)) - 1) + 32 * e)) =
      (leVals 32 (24 * b.combs) (b.bytes.drop ed_comb)).getD
        (3 * (8 * cr + (dIdx (dwordI ((n : Int) - 8)) - 1)) + e) 0 := fun e he => by
    have hi : dIdx (dwordI ((n : Int) - 8)) ≤ 8 := by rw [hidx]; omega
    rw [ofNat_add_assoc, ← fe_tab hc (by omega) hl]
    congr 3; omega
  have hk : 3 * (8 * cr + (dIdx (dwordI ((n : Int) - 8)) - 1)) + 3 ≤
      (leVals 32 (24 * b.combs) (b.bytes.drop ed_comb)).length := by
    rw [leVals_length, hidx]; omega
  rw [hrow, look_vals hdd ha, hf 0 (by decide), hf 1 (by decide), hf 2 (by decide)]
  by_cases hp : 0 < (n : Int) - 8
  · have hm : (dwordI ((n : Int) - 8)).msb = false := by rw [hmsb]; exact decide_eq_false (by omega)
    have hj : ((n : Int) - 8).toNat - 1 = dIdx (dwordI ((n : Int) - 8)) - 1 := by rw [hidx]; omega
    simp only [hm, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, _, _, rfl, ?_⟩
    rw [← Ed25519Comb.lookup_eq (comb_table ht) hcr h1 h2']
    unfold Ed25519Comb.lookupNiels
    simp only [hp, ↓reduceIte, hj, combEnt, tab_three hk, fI_nat, Nat.add_zero]
  · have hm : (dwordI ((n : Int) - 8)).msb = true := by rw [hmsb]; exact decide_eq_true (by omega)
    have hng : (n : Int) - 8 < 0 := by omega
    have hj : (-((n : Int) - 8)).toNat - 1 = dIdx (dwordI ((n : Int) - 8)) - 1 := by rw [hidx]; omega
    simp only [hm, ↓reduceIte]
    refine ⟨_, _, _, rfl, ?_⟩
    rw [← Ed25519Comb.lookup_eq (comb_table ht) hcr h1 h2']
    unfold Ed25519Comb.lookupNiels
    simp only [hp, hng, ↓reduceIte, hj, combEnt, tab_three hk, Niels.neg, fI_neg, fI_nat, Nat.add_zero]

/-! ## The program's value -/

/-- **`m0c_ge_mul_base`'s call program computes `[k]B`** for a scalar below `2^255` in a build whose
tables are the specification's: its output point represents `[k]B`. -/
theorem mb_val {m0 : Mem} {base : Word} {c : Ctx} (b : Build) (hc : CodeAt m0 base b.bytes) (ht : TablesOk b)
    (h2 : c.ptr 2 = base + BitVec.ofNat 32 ed_comb) (h3 : c.ptr 3 = base + BitVec.ofNat 32 ed_odd_b)
    (hk : decodeInt (kB c m0) < 2 ^ 255) :
    ∃ x y z t, (mbQ b.combs).outVals (Prog.ev maS mbS (mbQ b.combs).geo (mbV b.combs) mbBV c m0 (mbP b.combs)
        (mbQ b.combs).st0 fun _ => .none) = [.p ⟨nm x, nm y, nm z, nm t⟩] ∧
      RepV [.f x, .f y, .f z, .f t] ((decodeInt (kB c m0) : Int) • Bpt) :=
  mb_out b (look_ok b hc ht h2) (odd_ok b hc ht h3) hk

end M0Crypto.Release.Ed25519MulBaseTab
