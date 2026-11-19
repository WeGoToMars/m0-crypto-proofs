/-!
Multi-word values and carry chains for the Ed25519 scalar routines, over `Nat`.

A multi-word quantity is a function from word index to word value, `Nat → Nat`, read little
endian in base `2^32` by `wsum f n`. Machine proofs read words from memory into such functions;
`upd f i v` is `f` after a store of `v` at word `i`.

The lemmas are hypothesis-style, as in the X25519 arithmetic: each word step of a chain goes in
as a `Nat` equation (`r + 2^32 * c' = x + y + c` for `adds`/`adcs`, `r + y + b = x + 2^32 * b'`
for `subs`/`sbcs`), and value equations come out.

* `add_chain`, `sub_chain`: a chain of `adds`/`adcs` or `subs`/`sbcs` over `n` words
  (`sub_words` in `bench/ed25519/gen_ed25519.py`).
* `mac_acc`: one inner step of `m0c_mp_mul`, the 64-bit accumulation of `mul32` with the
  destination word and the carry word, which never overflows.
* `mp_mul_inner`, `mp_mul_row`: the loop invariants of `m0c_mp_mul` (rows `i`, inner `j`).
-/

namespace M0Crypto.Release.Ed25519Words

/-! ## Values -/

/-- The value of the words `f 0, ..., f (n - 1)`, little endian, base `2^32`. -/
def wsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wsum f n + 2 ^ (32 * n) * f n

@[simp] theorem wsum_zero (f : Nat → Nat) : wsum f 0 = 0 := rfl

theorem wsum_succ (f : Nat → Nat) (n : Nat) : wsum f (n + 1) = wsum f n + 2 ^ (32 * n) * f n :=
  rfl

/-- `f` with word `i` replaced by `v`. -/
def upd (f : Nat → Nat) (i v : Nat) : Nat → Nat := fun k => if k = i then v else f k

@[simp] theorem upd_same (f : Nat → Nat) (i v : Nat) : upd f i v i = v := by simp [upd]

theorem upd_ne (f : Nat → Nat) {i k : Nat} (v : Nat) (h : k ≠ i) : upd f i v k = f k := by
  simp [upd, h]

theorem wsum_congr {f g : Nat → Nat} {n : Nat} (h : ∀ j, j < n → f j = g j) :
    wsum f n = wsum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wsum_succ, wsum_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem pow32_succ (n : Nat) : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem wsum_lt {f : Nat → Nat} {n : Nat} (h : ∀ j, j < n → f j < 2 ^ 32) :
    wsum f n < 2 ^ (32 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wsum_succ, pow32_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 : f n + 1 ≤ 2 ^ 32 := h n (by omega)
    have h3 := Nat.mul_le_mul_left (2 ^ (32 * n)) h2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

/-- Splitting a value at word `m`. -/
theorem wsum_add (f : Nat → Nat) (m k : Nat) :
    wsum f (m + k) = wsum f m + 2 ^ (32 * m) * wsum (fun j => f (m + j)) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, wsum_succ, ih, wsum_succ, Nat.mul_add, Nat.mul_add, Nat.pow_add,
      Nat.mul_assoc]
    omega

theorem wsum_mod {f : Nat → Nat} {m k : Nat} (h : ∀ j, j < m + k → f j < 2 ^ 32) :
    wsum f (m + k) % 2 ^ (32 * m) = wsum f m := by
  rw [wsum_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wsum_lt fun j hj => h j (by omega))]

theorem wsum_div {f : Nat → Nat} {m k : Nat} (h : ∀ j, j < m + k → f j < 2 ^ 32) :
    wsum f (m + k) / 2 ^ (32 * m) = wsum (fun j => f (m + j)) k := by
  rw [wsum_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wsum_lt fun j hj => h j (by omega)), Nat.zero_add]

/-- Word `j` of a value below `2^(32 n)`. -/
theorem wsum_top_zero {f : Nat → Nat} {n : Nat} (h : wsum f (n + 1) < 2 ^ (32 * n)) :
    f n = 0 := by
  rw [wsum_succ] at h
  rcases Nat.eq_zero_or_pos (f n) with h0 | h0
  · exact h0
  · have := Nat.mul_le_mul_left (2 ^ (32 * n)) (Nat.succ_le_of_lt h0)
    omega

/-- A store at word `i < n` changes the value by `2^(32 i)` times the difference. -/
theorem wsum_upd (f : Nat → Nat) {i n : Nat} (v : Nat) (hi : i < n) :
    wsum (upd f i v) n + 2 ^ (32 * i) * f i = wsum f n + 2 ^ (32 * i) * v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [wsum_succ, wsum_succ]
    by_cases h : i = n
    · subst h
      rw [wsum_congr (g := f) (fun j hj => upd_ne f v (by omega)), upd_same]
      omega
    · rw [upd_ne f v (Ne.symm h)]
      have := ih (by omega)
      omega

/-! ## Carry chains -/

/-- `adds`/`adcs` over `n` words: word `j` gives `r j` with carry `c (j + 1)`. -/
theorem add_chain (x y r c : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → r j + 2 ^ 32 * c (j + 1) = x j + y j + c j) :
    wsum r n + 2 ^ (32 * n) * c n = wsum x n + wsum y n + c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := h n (by omega)
    have ih := ih (fun j hj => h j (by omega))
    rw [wsum_succ, wsum_succ, wsum_succ, pow32_succ]
    generalize 2 ^ (32 * n) = P at *
    grind

/-- `subs`/`sbcs` over `n` words: word `j` gives `r j` with borrow `b (j + 1)` (the borrow is
`1 - C`). -/
theorem sub_chain (x y r b : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → r j + y j + b j = x j + 2 ^ 32 * b (j + 1)) :
    wsum r n + wsum y n + b 0 = wsum x n + 2 ^ (32 * n) * b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := h n (by omega)
    have ih := ih (fun j hj => h j (by omega))
    rw [wsum_succ, wsum_succ, wsum_succ, pow32_succ]
    generalize 2 ^ (32 * n) = P at *
    grind

/-- A `subs`/`sbcs` chain whose result is known to be nonnegative and fits: the result is the
exact difference and the final borrow is zero. -/
theorem sub_exact {x y r B : Nat} (n : Nat) (hr : r < 2 ^ (32 * n))
    (hB : B ≤ 1) (h : r + y = x + 2 ^ (32 * n) * B) (hyx : y ≤ x) : r = x - y ∧ B = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with rfl | rfl <;> omega

/-! ## `m0c_mp_mul` -/

/-- One inner step: `mul32` gives `lo + 2^32 hi = x * y`, then `adds lo, d; adcs hi, #0` and
`adds lo, c; adcs hi, #0` (the carries out of `hi` are dropped). The 64-bit sum
`x * y + d + c` of four words fits, so no carry is lost. -/
theorem mac_acc {x y d c lo hi lo1 k1 hi1 lo2 k2 hi2 : Nat}
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hd : d < 2 ^ 32) (hc : c < 2 ^ 32)
    (hmul : lo + 2 ^ 32 * hi = x * y) (hlo2 : lo2 < 2 ^ 32)
    (h1 : lo1 + 2 ^ 32 * k1 = lo + d) (hh1 : hi1 = (hi + k1) % 2 ^ 32)
    (h2 : lo2 + 2 ^ 32 * k2 = lo1 + c) (hh2 : hi2 = (hi1 + k2) % 2 ^ 32) :
    lo2 + 2 ^ 32 * hi2 = x * y + d + c := by
  have hxy : x * y ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (Nat.le_sub_one_of_lt hx) (Nat.le_sub_one_of_lt hy)
  have hhi : hi + k1 < 2 ^ 32 := by omega
  rw [hh1, Nat.mod_eq_of_lt hhi] at hh2
  rw [hh2, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The inner loop invariant of row `i` after `j` steps. `D` is the destination (`2 n` words),
`c` the carry word. Row `i` adds `a i * b` at word `i`. -/
theorem mp_mul_inner {n i j : Nat} {a b D : Nat → Nat} {c c' r : Nat}
    (hinv : wsum D (2 * n) + 2 ^ (32 * (i + j)) * c =
      wsum a i * wsum b n + 2 ^ (32 * i) * (a i * wsum b j))
    (hj : j < n) (hi : i < n)
    (hstep : r + 2 ^ 32 * c' = a i * b j + D (i + j) + c) :
    wsum (upd D (i + j) r) (2 * n) + 2 ^ (32 * (i + (j + 1))) * c' =
      wsum a i * wsum b n + 2 ^ (32 * i) * (a i * wsum b (j + 1)) := by
  have hu := wsum_upd D r (i := i + j) (n := 2 * n) (by omega)
  rw [wsum_succ, ← Nat.add_assoc, pow32_succ]
  have hp : 2 ^ (32 * (i + j)) = 2 ^ (32 * i) * 2 ^ (32 * j) := by
    rw [Nat.mul_add, Nat.pow_add]
  rw [hp] at hu hinv ⊢
  generalize 2 ^ (32 * i) = P at *
  generalize 2 ^ (32 * j) = Q at *
  grind

/-- The end of row `i`: the carry is stored at word `i + n`, which was zero. -/
theorem mp_mul_row {n i : Nat} {a b D : Nat → Nat} {c : Nat}
    (hinv : wsum D (2 * n) + 2 ^ (32 * (i + n)) * c =
      wsum a i * wsum b n + 2 ^ (32 * i) * (a i * wsum b n))
    (hi : i < n) (hz : D (i + n) = 0) :
    wsum (upd D (i + n) c) (2 * n) = wsum a (i + 1) * wsum b n := by
  have hu := wsum_upd D c (i := i + n) (n := 2 * n) (by omega)
  rw [hz, Nat.mul_zero, Nat.add_zero] at hu
  rw [wsum_succ]
  generalize 2 ^ (32 * i) = P at *
  grind

theorem wsum_const_zero (m : Nat) : wsum (fun _ => 0) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [wsum_succ, ih]; simp

/-- The start of `m0c_mp_mul`: a zeroed destination. -/
theorem mp_mul_start {n : Nat} {a b D : Nat → Nat} (hz : ∀ k, k < 2 * n → D k = 0) :
    wsum D (2 * n) = wsum a 0 * wsum b n := by
  rw [wsum_congr (g := fun _ => 0) hz, wsum_zero, Nat.zero_mul]
  exact wsum_const_zero _

end M0Crypto.Release.Ed25519Words
