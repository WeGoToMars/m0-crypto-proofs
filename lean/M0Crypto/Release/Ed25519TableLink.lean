import M0Crypto.Release.Ed25519Comb
import M0Crypto.Release.Ed25519TablesCompact
import M0Crypto.Release.Ed25519TablesFast

/-!
# The flash tables as points

A table of the unit is a list of values, three per entry (`Ed25519Tables`: `entry m` is `[m]B` in
Niels form over `Nat`). `tabEntry vals k` reads entry `k` as a Niels triple in `F_p`.

* `entry_niels`: `entry m` is `Niels.of d2 ([m]B)`, by the bridge from the specification;
* `chunk_eq`: entry `k` of a table made by `flatMap` over `List.range n`, any width;
* `tab_eq`, `tab_eq2`: a table of entries `f k`, or of rows of eight entries `f c j`, holds
  `Niels.of d2 ([f k]B)` at entry `k`, or `8 c + j`;
* `odd_b`: `m0c_ed_odd_b` in a build with `TablesOk` gives `OddBTable`.
-/

namespace M0Crypto.Release.Ed25519TableLink

open Lean.Grind M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Group
open M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519Tables (entry niels oddTable TablesOk leVals)
open M0Crypto.Release.Ed25519 (Build)

/-- Three table values as a Niels triple in `F_p`. -/
def nielsF : List Nat → Niels Fp
  | [a, b, c] => ⟨toF a, toF b, toF c⟩
  | _ => ⟨0, 0, 0⟩

/-- Entry `k` of a table of values. -/
def tabEntry (vals : List Nat) (k : Nat) : Niels Fp := nielsF ((vals.drop (3 * k)).take 3)

/-- **An expected entry is the point's Niels form**: `entry m` is `[m]B`. -/
theorem entry_niels (m : Nat) : nielsF (entry m) = Niels.of d2 (((m : Nat) : Int) • Bpt).pt := by
  have h := xy_eq (specRep_scalarMul m specRep_B)
  simp only [entry, niels, h, nielsF, Niels.of, d2, toF_mod, toF_add, toF_fsub, toF_mul, toF_val, toF_two, toF_d]

/-- The table made by `flatMap` over `List.range n` of blocks of width `w`. -/
theorem flat_length {α : Type} (g : Nat → List α) (w : Nat) (hg : ∀ i, (g i).length = w) :
    ∀ n, ((List.range n).flatMap g).length = w * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flat_length g w hg n, List.flatMap_singleton,
      hg]; rw [Nat.mul_succ]

/-- **Block `k` of a `flatMap` table** of width `w`. -/
theorem chunk_eq {α : Type} (g : Nat → List α) (w : Nat) (hg : ∀ i, (g i).length = w) :
    ∀ n k, k < n → (((List.range n).flatMap g).drop (w * k)).take w = g k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl := flat_length g w hg n
    by_cases hk : k < n
    · have h1 : w * k ≤ ((List.range n).flatMap g).length := by rw [hl]; exact Nat.mul_le_mul_left _ (by omega)
      rw [List.drop_append_of_le_length h1, List.take_append_of_le_length (by
        rw [List.length_drop, hl, ← Nat.mul_sub]; exact Nat.le_mul_of_pos_right _ (by omega))]
      exact chunk_eq g w hg n k hk
    · obtain rfl : k = n := by omega
      rw [List.drop_append_of_le_length (by rw [hl]; exact Nat.le_refl _), show w * k = ((List.range k).flatMap g).length by rw [hl],
        List.drop_length, List.nil_append, List.take_of_length_le (by rw [hg]; exact Nat.le_refl _)]

theorem entry_length (m : Nat) : (entry m).length = 3 := rfl

/-- **A table of entries `f k`** holds `[f k]B` at entry `k`. -/
theorem tab_eq {vals : List Nat} {n : Nat} (f : Nat → Nat) (h : vals = (List.range n).flatMap fun k => entry (f k)) :
    ∀ k < n, tabEntry vals k = Niels.of d2 (((f k : Nat) : Int) • Bpt).pt := by
  intro k hk; subst h
  rw [tabEntry, chunk_eq (fun k => entry (f k)) 3 (fun _ => entry_length _) n k hk, entry_niels]

/-- **A table of rows of eight entries `f c j`** holds `[f c j]B` at entry `8 c + j`. -/
theorem tab_eq2 {vals : List Nat} {n : Nat} (f : Nat → Nat → Nat)
    (h : vals = (List.range n).flatMap fun c => (List.range 8).flatMap fun j => entry (f c j)) :
    ∀ c < n, ∀ j < 8, tabEntry vals (8 * c + j) = Niels.of d2 (((f c j : Nat) : Int) • Bpt).pt := by
  intro c hc j hj; subst h
  have hr : ∀ c, ((List.range 8).flatMap fun j => entry (f c j)).length = 24 :=
    fun c => flat_length _ 3 (fun _ => entry_length _) 8
  generalize hL : (List.range n).flatMap (fun c => (List.range 8).flatMap fun j => entry (f c j)) = L
  have hrow := chunk_eq _ 24 hr n c hc
  rw [hL] at hrow
  rw [tabEntry, show 3 * (8 * c + j) = 24 * c + 3 * j by omega, ← List.drop_drop,
    ← List.take_append_drop 24 (L.drop (24 * c)), hrow,
    List.drop_append_of_le_length (by rw [hr]; omega), List.take_append_of_le_length (by
      rw [List.length_drop, hr]; omega),
    chunk_eq (fun j => entry (f c j)) 3 (fun _ => entry_length _) 8 j hj, entry_niels]

/-- **`m0c_ed_odd_b` holds `[2k + 1]B`** at entry `k`, in a build whose tables are the
specification's. -/
theorem odd_b {b : Build} (ht : TablesOk b) :
    Ed25519Comb.OddBTable (tabEntry (leVals 32 24 (b.bytes.drop M0Crypto.Artifacts.Ed25519Compact.ed_odd_b))) := by
  intro k hk
  rw [tab_eq (fun k => 2 * k + 1) ht.odd k hk, show ((2 * k + 1 : Nat) : Int) = 2 * (k : Int) + 1 by omega]

theorem odd_b_builds : ∀ b : Build,
    Ed25519Comb.OddBTable (tabEntry (leVals 32 24 (b.bytes.drop M0Crypto.Artifacts.Ed25519Compact.ed_odd_b)))
  | .compact => odd_b Ed25519TablesCompact.tables_ok
  | .fast => odd_b Ed25519TablesFast.tables_ok

end M0Crypto.Release.Ed25519TableLink
