/-!
Primality by Lucas certificates (Pratt), and Fermat's little theorem for certified primes.

`lucas`: if `a ^ (n - 1) ≡ 1 (mod n)`, `n - 1` is the product of the primes `fs`, and
`a ^ ((n - 1) / r) ≢ 1 (mod n)` for each `r` in `fs`, then `n` is prime and
`x ^ (n - 1) ≡ 1 (mod n)` for every `x ≢ 0`. The proof needs no general Fermat theorem:
the order of `a` is `n - 1`, so `a ^ 0, …, a ^ (n - 2)` are `n - 1` distinct residues
coprime to `n`. By counting (`List.Nodup.length_le_of_subset`) they are all of
`1, …, n - 1`, so every nonzero residue is a power of `a` and coprime to `n`.

`check` evaluates a list of Lucas steps, each allowed to cite the primes of earlier steps,
with `Nat.powMod`; `check_sound` turns a `true` result into primality and Fermat's
theorem for every step. Certificates are checked by kernel evaluation (`decide +kernel`).
-/

namespace M0Crypto.Release.Ed25519Prime

/-- `n` is prime. -/
def Prime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- Fermat's little theorem at `n`. -/
def Fermat (n : Nat) : Prop := ∀ x, x % n ≠ 0 → x ^ (n - 1) % n = 1

theorem prime_two : Prime 2 := by
  refine ⟨Nat.le_refl 2, fun m hm => ?_⟩
  have h2 := Nat.le_of_dvd (by decide) hm
  have h0 : m ≠ 0 := by rintro rfl; simp at hm
  omega

theorem Prime.dvd_mul {q m k : Nat} (hq : Prime q) (h : q ∣ m * k) : q ∣ m ∨ q ∣ k := by
  rcases hq.2 (Nat.gcd q m) (Nat.gcd_dvd_left q m) with h1 | h1
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · exact Or.inl (h1 ▸ Nat.gcd_dvd_right q m)

/-- A prime dividing a product of primes is one of them. -/
theorem mem_of_dvd_prod {q : Nat} (hq : Prime q) :
    ∀ {l : List Nat}, (∀ r ∈ l, Prime r) → q ∣ l.prod → q ∈ l
  | [], _, h => by
    have := hq.1
    simp at h
    omega
  | r :: l, hl, h => by
    rw [List.prod_cons] at h
    rcases hq.dvd_mul h with h | h
    · rcases (hl r List.mem_cons_self).2 q h with h1 | h1
      · have := hq.1
        omega
      · exact h1 ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (mem_of_dvd_prod hq (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) h)

/-- Every `m ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd (m : Nat) : 2 ≤ m → ∃ q, Prime q ∧ q ∣ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm
    by_cases h : ∀ k, k ∣ m → k = 1 ∨ k = m
    · exact ⟨m, ⟨hm, h⟩, Nat.dvd_refl m⟩
    · have : ∃ k, k ∣ m ∧ k ≠ 1 ∧ k ≠ m := by
        apply Classical.byContradiction
        intro hne
        apply h
        intro k hk
        apply Classical.byContradiction
        intro hor
        exact hne ⟨k, hk, fun e => hor (Or.inl e), fun e => hor (Or.inr e)⟩
      obtain ⟨k, hk, hk1, hkm⟩ := this
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
      have hklt : k < m := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hk) hkm
      obtain ⟨q, hq, hqk⟩ := ih k hklt (by omega)
      exact ⟨q, hq, Nat.dvd_trans hqk hk⟩

section Powers

variable {a n : Nat}

theorem pow_mul_mod_one (hn : 2 ≤ n) {x : Nat} (h : a ^ x % n = 1) (k : Nat) :
    a ^ (x * k) % n = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod, h, Nat.one_pow]
  exact Nat.mod_eq_of_lt (by omega)

theorem mul_mod_of_mod_one {u : Nat} (h : u % n = 1) (v : Nat) : u * v % n = v % n := by
  rw [Nat.mul_mod, h, Nat.one_mul, Nat.mod_mod]

/-- `a ^ x ≡ 1` and `a ^ y ≡ 1` give `a ^ gcd x y ≡ 1`. -/
theorem pow_gcd_mod (hn : 2 ≤ n) (x y : Nat) :
    a ^ x % n = 1 → a ^ y % n = 1 → a ^ Nat.gcd x y % n = 1 := by
  induction x, y using Nat.gcd.induction with
  | H0 y => intro _ hy; rwa [Nat.gcd_zero_left]
  | H1 x y _ ih =>
    intro hx hy
    rw [Nat.gcd_rec]
    apply ih _ hx
    have e : a ^ y = a ^ (x * (y / x)) * a ^ (y % x) := by
      rw [← Nat.pow_add, Nat.div_add_mod]
    rwa [e, mul_mod_of_mod_one (pow_mul_mod_one hn hx _)] at hy

/-- Cancelling a power of a unit. -/
theorem pow_sub_mod_one (hn : 2 ≤ n) (hcop : Nat.Coprime a n) {i j : Nat} (hij : i ≤ j)
    (h : a ^ i % n = a ^ j % n) : a ^ (j - i) % n = 1 := by
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp [Nat.Coprime] at hcop
    omega
  have hj : a ^ j = a ^ i * a ^ (j - i) := by rw [← Nat.pow_add]; congr 1; omega
  have hdvd : n ∣ a ^ i * (a ^ (j - i) - 1) := by
    rw [Nat.mul_sub_one, ← hj]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  obtain ⟨c, hc⟩ := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left i hcop).symm hdvd
  have hpos : 1 ≤ a ^ (j - i) := Nat.one_le_pow _ _ ha
  have e : a ^ (j - i) = n * c + 1 := by omega
  rw [e, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem coprime_of_pow_mod (hn : 2 ≤ n) (h : a ^ (n - 1) % n = 1) : Nat.Coprime a n := by
  have hg : Nat.gcd a n ∣ a ^ (n - 1) % n :=
    (Nat.dvd_mod_iff (Nat.gcd_dvd_right a n)).mpr
      (Nat.dvd_trans (Nat.gcd_dvd_left a n)
        (by have := Nat.pow_dvd_pow a (by omega : 1 ≤ n - 1); rwa [Nat.pow_one] at this))
  rw [h] at hg
  exact Nat.dvd_one.mp hg

theorem coprime_pow_mod (hcop : Nat.Coprime a n) (i : Nat) : Nat.Coprime (a ^ i % n) n := by
  have := Nat.Coprime.pow_left i hcop
  unfold Nat.Coprime at *
  rw [← Nat.gcd_rec n (a ^ i), Nat.gcd_comm]
  exact this

end Powers

/-- Lucas's test. -/
theorem lucas {n a : Nat} (fs : List Nat) (hn : 2 ≤ n) (hfs : ∀ r ∈ fs, Prime r)
    (hprod : fs.prod = n - 1) (h1 : a ^ (n - 1) % n = 1)
    (hr : ∀ r ∈ fs, a ^ ((n - 1) / r) % n ≠ 1) : Prime n ∧ Fermat n := by
  have hcop := coprime_of_pow_mod hn h1
  -- No exponent `0 < t < n - 1` has `a ^ t ≡ 1`.
  have order {t : Nat} (ht0 : 0 < t) (ht : t < n - 1) (h : a ^ t % n = 1) : False := by
    have hg := pow_gcd_mod hn t (n - 1) h h1
    have hgN : Nat.gcd t (n - 1) ∣ n - 1 := Nat.gcd_dvd_right t (n - 1)
    have hgpos : 0 < Nat.gcd t (n - 1) := Nat.gcd_pos_of_pos_left _ ht0
    have hgt : Nat.gcd t (n - 1) ≤ t := Nat.le_of_dvd ht0 (Nat.gcd_dvd_left t (n - 1))
    generalize Nat.gcd t (n - 1) = g at hg hgN hgpos hgt
    obtain ⟨k, hk⟩ := hgN
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    obtain ⟨q, hq, hqk⟩ := exists_prime_dvd k hk2
    obtain ⟨k', hk'⟩ := hqk
    have hqN : n - 1 = q * (g * k') := by
      rw [hk, hk', Nat.mul_left_comm]
    have hmem : q ∈ fs := mem_of_dvd_prod hq hfs (hprod ▸ ⟨_, hqN⟩)
    apply hr q hmem
    rw [hqN, Nat.mul_div_cancel_left _ (by have := hq.1; omega)]
    exact pow_mul_mod_one hn hg k'
  -- The powers `a ^ i % n`, `i < n - 1`, are distinct.
  let L := (List.range (n - 1)).map fun i => a ^ i % n
  have hinj {i j : Nat} (hi : i < n - 1) (hj : j < n - 1) (h : a ^ i % n = a ^ j % n) :
      i = j := by
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact (order (by omega) (by omega) (pow_sub_mod_one hn hcop (Nat.le_of_lt hij) h)).elim
    · exact hij
    · exact (order (by omega) (by omega) (pow_sub_mod_one hn hcop (Nat.le_of_lt hij) h.symm)).elim
  have hnodup : L.Nodup := by
    refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem ?_ List.nodup_range)
    intro i j hi hj hne h
    exact hne (hinj (List.mem_range.mp hi) (List.mem_range.mp hj) h)
  -- They lie in `1, …, n - 1`, and so they are all of it.
  let M := (List.range n).erase 0
  have hM : M.length = n - 1 := by
    simp only [M]
    rw [List.length_erase_of_mem (List.mem_range.mpr (by omega)), List.length_range]
  have hcopL {x : Nat} (hx : x ∈ L) : Nat.Coprime x n := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact coprime_pow_mod hcop i
  have hsub : L ⊆ M := by
    intro x hx
    have hc := hcopL hx
    have hx0 : x ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact (List.mem_erase_of_ne hx0).mpr (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
  have hall {y : Nat} (hy : y ∈ M) : y ∈ L := by
    apply Classical.byContradiction
    intro hyL
    have hsub' : L ⊆ M.erase y := by
      intro x hx
      have hxy : x ≠ y := fun e => hyL (e ▸ hx)
      exact (List.mem_erase_of_ne hxy).mpr (hsub hx)
    have hlen := hnodup.length_le_of_subset hsub'
    rw [List.length_erase_of_mem hy, hM] at hlen
    simp only [L, List.length_map, List.length_range] at hlen
    omega
  have hmemM {y : Nat} (h0 : y ≠ 0) (hlt : y < n) : y ∈ M :=
    (List.mem_erase_of_ne h0).mpr (List.mem_range.mpr hlt)
  refine ⟨⟨hn, fun m hm => ?_⟩, fun x hx => ?_⟩
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
    have hle := Nat.le_of_dvd (by omega) hm
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hc := hcopL (hall (hmemM hm0 hlt))
      unfold Nat.Coprime at hc
      rw [Nat.gcd_eq_left hm] at hc
      exact Or.inl hc
    · exact Or.inr heq
  · obtain ⟨i, _, hi⟩ := List.mem_map.mp (hall (hmemM hx (Nat.mod_lt _ (by omega))))
    rw [Nat.pow_mod, ← hi, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm]
    exact pow_mul_mod_one hn h1 i

/-! ### Certificates checked by evaluation -/

/-- One Lucas step: `n`, the witness `a`, and the prime factors of `n - 1` with
multiplicity. -/
structure Step where
  n : Nat
  a : Nat
  fs : List Nat

/-- The step's conditions, with the factors drawn from `known`. -/
def Step.check (known : List Nat) (s : Step) : Bool :=
  decide (2 ≤ s.n) && s.fs.prod == s.n - 1 && s.fs.all (fun r => known.contains r) &&
    Nat.powMod s.a (s.n - 1) s.n == 1 &&
    s.fs.all (fun r => Nat.powMod s.a ((s.n - 1) / r) s.n != 1)

/-- Check the steps in order; each may cite `known` and the earlier steps. -/
def check : List Nat → List Step → Bool
  | _, [] => true
  | known, s :: ss => s.check known && check (s.n :: known) ss

theorem Step.check_sound {known : List Nat} {s : Step} (hk : ∀ r ∈ known, Prime r)
    (h : s.check known = true) : Prime s.n ∧ Fermat s.n := by
  simp only [Step.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hn, hprod⟩, hfs⟩, h1⟩, hr⟩ := h
  rw [Nat.powMod_def] at h1
  exact lucas s.fs hn (fun r hr' => hk r (hfs r hr')) hprod h1
    (fun r hr' => by have := hr r hr'; rwa [Nat.powMod_def] at this)

theorem check_sound : ∀ {known : List Nat} {ss : List Step}, (∀ r ∈ known, Prime r) →
    check known ss = true → ∀ s ∈ ss, Prime s.n ∧ Fermat s.n
  | _, [], _, _, _, hs => by simp at hs
  | known, s :: ss, hk, h, t, ht => by
    simp only [check, Bool.and_eq_true] at h
    have hs := Step.check_sound hk h.1
    have hk' : ∀ r ∈ s.n :: known, Prime r := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hs.1
      · exact hk r hr
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hs
    · exact check_sound hk' h.2 t ht

end M0Crypto.Release.Ed25519Prime
