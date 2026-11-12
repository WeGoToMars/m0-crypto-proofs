import M0Crypto.Release.Blake2sRound

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word)
open M0Crypto.Spec.Blake2s (G)

theorem get_set! (a : Array Word) (i j : Nat) (x : Word) (hj : j < a.size) :
    (a.set! i x)[j]! = if i = j then x else a[j]! := by
  by_cases hij : i = j
  · subst hij
    simp [Array.set!_eq_setIfInBounds, getElem!_pos, hj]
  · simp [Array.set!_eq_setIfInBounds, getElem!_pos, hj, hij]


theorem arr16_size (f : Nat → Word) : (arr16 f).size = 16 := rfl

theorem arr16_get (f : Nat → Word) (k : Nat) (hk : k < 16) : (arr16 f)[k]! = f k := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mix_arr16 (f : Nat → Word) (ia ib ic id : Nat) (x y : Word)
    (ha : ia < 16) (hb : ib < 16) (hc : ic < 16) (hd : id < 16) :
    M0Crypto.Spec.Blake2s.mix (arr16 f) ia ib ic id x y = arr16 (mixF f ia ib ic id x y) := by
  have hsz := arr16_size f
  have hget := arr16_get f
  have hget' := arr16_get (mixF f ia ib ic id x y)
  have hszr := arr16_size (mixF f ia ib ic id x y)
  generalize arr16 f = a at hsz hget ⊢
  generalize arr16 (mixF f ia ib ic id x y) = r at hget' hszr ⊢
  unfold M0Crypto.Spec.Blake2s.mix
  rw [hget ia ha, hget ib hb, hget ic hc, hget id hd]
  simp only [mixF] at hget'
  generalize G (f ia) (f ib) (f ic) (f id) x y = q at hget' ⊢
  obtain ⟨A, B, C, D⟩ := q
  simp only at hget' ⊢
  apply Array.ext
  · simp [Array.size_set!, hsz, hszr]
  · intro k hk1 hk2
    have hk : k < 16 := by simpa [Array.size_set!, hsz] using hk1
    have s0 : k < a.size := by omega
    have s1 : k < (a.set! ia A).size := by simp [Array.size_set!, hsz, hk]
    have s2 : k < ((a.set! ia A).set! ib B).size := by simp [Array.size_set!, hsz, hk]
    have s3 : k < (((a.set! ia A).set! ib B).set! ic C).size := by simp [Array.size_set!, hsz, hk]
    rw [← getElem!_pos, ← getElem!_pos, hget' k hk, get_set! _ _ _ _ s3, get_set! _ _ _ _ s2,
      get_set! _ _ _ _ s1, get_set! _ _ _ _ s0, hget k hk]
    repeat' split
    all_goals first | rfl | (exfalso; omega)

theorem case8 (k a1 b1 c1 d1 a2 b2 c2 d2 : Nat) : k = a1 ∨ k = b1 ∨ k = c1 ∨ k = d1 ∨ k = a2 ∨ k = b2 ∨ k = c2 ∨ k = d2 ∨
      (k ≠ a1 ∧ k ≠ b1 ∧ k ≠ c1 ∧ k ≠ d1 ∧ k ≠ a2 ∧ k ≠ b2 ∧ k ≠ c2 ∧ k ≠ d2) := by
  by_cases e0 : k = a1
  · exact Or.inl e0
  by_cases e1 : k = b1
  · exact Or.inr (Or.inl e1)
  by_cases e2 : k = c1
  · exact Or.inr (Or.inr (Or.inl e2))
  by_cases e3 : k = d1
  · exact Or.inr (Or.inr (Or.inr (Or.inl e3)))
  by_cases e4 : k = a2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e4))))
  by_cases e5 : k = b2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e5)))))
  by_cases e6 : k = c2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e6))))))
  by_cases e7 : k = d2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7)))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨e0, e1, e2, e3, e4, e5, e6, e7⟩))))))))

theorem mixF_comm (v : Nat → Word) (a1 b1 c1 d1 a2 b2 c2 d2 : Nat) (x1 y1 x2 y2 : Word)
    (hd : a1 ≠ b1 ∧ a1 ≠ c1 ∧ a1 ≠ d1 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ a1 ≠ c2 ∧ a1 ≠ d2 ∧ b1 ≠ c1 ∧ b1 ≠ d1 ∧ b1 ≠ a2 ∧ b1 ≠ b2 ∧ b1 ≠ c2 ∧ b1 ≠ d2 ∧ c1 ≠ d1 ∧ c1 ≠ a2 ∧ c1 ≠ b2 ∧ c1 ≠ c2 ∧ c1 ≠ d2 ∧ d1 ≠ a2 ∧ d1 ≠ b2 ∧ d1 ≠ c2 ∧ d1 ≠ d2 ∧ a2 ≠ b2 ∧ a2 ≠ c2 ∧ a2 ≠ d2 ∧ b2 ≠ c2 ∧ b2 ≠ d2 ∧ c2 ≠ d2) :
    mixF (mixF v a1 b1 c1 d1 x1 y1) a2 b2 c2 d2 x2 y2 =
    mixF (mixF v a2 b2 c2 d2 x2 y2) a1 b1 c1 d1 x1 y1 := by
  funext k
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hd
  rcases case8 k a1 b1 c1 d1 a2 b2 c2 d2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩
  all_goals simp (disch := first | assumption | (apply Ne.symm; assumption)) only [mixF_id, mixF_ic, mixF_b, mixF_a, mixF_o]
  
/-- The RFC order of the eight `G`s of a round. -/
def roundSpecF (v m : Nat → Word) (sch : Nat → Nat) : Nat → Word :=
  let w1 := mixF v 0 4 8 12 (m (sch 0)) (m (sch 1))
  let w2 := mixF w1 1 5 9 13 (m (sch 2)) (m (sch 3))
  let w3 := mixF w2 2 6 10 14 (m (sch 4)) (m (sch 5))
  let w4 := mixF w3 3 7 11 15 (m (sch 6)) (m (sch 7))
  let w5 := mixF w4 0 5 10 15 (m (sch 8)) (m (sch 9))
  let w6 := mixF w5 1 6 11 12 (m (sch 10)) (m (sch 11))
  let w7 := mixF w6 2 7 8 13 (m (sch 12)) (m (sch 13))
  mixF w7 3 4 9 14 (m (sch 14)) (m (sch 15))

/-- The assembly's order of the `G`s gives the RFC result: disjoint `G`s commute. -/
theorem roundF_eq (v m : Nat → Word) (sch : Nat → Nat) : roundF v m sch = roundSpecF v m sch := by
  simp only [roundF, roundSpecF]
  -- first half: C A B D = A B C D
  rw [mixF_comm v 2 6 10 14 0 4 8 12 _ _ _ _ (by decide)]
  rw [mixF_comm (mixF v 0 4 8 12 _ _) 2 6 10 14 1 5 9 13 _ _ _ _ (by decide)]
  -- second half: H E F G = E F G H
  rw [mixF_comm _ 3 4 9 14 0 5 10 15 _ _ _ _ (by decide)]
  rw [mixF_comm _ 3 4 9 14 1 6 11 12 _ _ _ _ (by decide)]
  rw [mixF_comm _ 3 4 9 14 2 7 8 13 _ _ _ _ (by decide)]

open M0Crypto.Release.Blake2sCode (sg sg_eq)

theorem sg_lt : ∀ r : Fin 10, ∀ i : Fin 16, sg r i < 16 := by decide

theorem round_arr16 (v m : Nat → Word) (r : Fin 10) :
    M0Crypto.Spec.Blake2s.round (arr16 v) (arr16 m) r = arr16 (roundSpecF v m (sg r)) := by
  have hrow : ∀ i : Fin 16, (M0Crypto.Spec.Blake2s.SIGMA[(r : Nat) % 10]!)[(i : Nat)]! = sg r i := by
    intro i; rw [Nat.mod_eq_of_lt r.isLt]; exact (sg_eq r i).symm
  have hm : ∀ i : Nat, i < 16 → (arr16 m)[sg r i]! = m (sg r i) := fun i hi => arr16_get m _ (sg_lt r ⟨i, hi⟩)
  unfold M0Crypto.Spec.Blake2s.round
  simp only [hrow ⟨0, by omega⟩, hrow ⟨1, by omega⟩, hrow ⟨2, by omega⟩, hrow ⟨3, by omega⟩,
    hrow ⟨4, by omega⟩, hrow ⟨5, by omega⟩, hrow ⟨6, by omega⟩, hrow ⟨7, by omega⟩,
    hrow ⟨8, by omega⟩, hrow ⟨9, by omega⟩, hrow ⟨10, by omega⟩, hrow ⟨11, by omega⟩,
    hrow ⟨12, by omega⟩, hrow ⟨13, by omega⟩, hrow ⟨14, by omega⟩, hrow ⟨15, by omega⟩,
    hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega), hm 4 (by omega),
    hm 5 (by omega), hm 6 (by omega), hm 7 (by omega), hm 8 (by omega), hm 9 (by omega),
    hm 10 (by omega), hm 11 (by omega), hm 12 (by omega), hm 13 (by omega), hm 14 (by omega),
    hm 15 (by omega)]
  simp (config := {decide := true}) only [mix_arr16, roundSpecF]

theorem round_spec (v m : Nat → Word) (r : Fin 10) :
    arr16 (roundF v m (sg r)) = M0Crypto.Spec.Blake2s.round (arr16 v) (arr16 m) r := by
  rw [round_arr16, roundF_eq]

end M0Crypto.Release.Blake2s
