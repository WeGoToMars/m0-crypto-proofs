/-!
The right-to-left windowed NAF of `m0c_sc_wnaf` (verify only, variable time).

`step w k` is one iteration of the main loop of `m0c_sc_wnaf` (`emit_wnaf` in
`bench/ed25519/gen_ed25519.py`, `wnaf` in `edref.py`) on the state `(bit, carry, digits)`:

* if bit `bit` of `k` equals `carry`, the digit is zero and only `bit` advances;
* otherwise `now = min w (256 - bit)`, `word = carry + (bits [bit, bit + now) of k)`, the new
  carry is bit `w - 1` of `word`, the digit at `bit` is `word - carry' 2^w`, and `bit`
  advances by `now`.

`window_step` is the inner loop that sums `m0c_sbit (bit + j) << j`. `Inv` is the loop
invariant: `sum_{i < bit} d_i 2^i + carry 2^bit = k mod 2^bit`, the digits at and above `bit`
are zero, every digit is zero or odd with `|d| < 2^(w-1)`, and `carry = 0` once
`bit = 256`. `step_inv` preserves it for `k < 2^255` and `2 ≤ w`.

`wnaf w k` runs the loop to its end; `wnaf_spec` gives the digit identity and bounds that the
verify equation needs, and `wnaf_spec_3`, `wnaf_spec_5` instantiate the two widths.
-/

namespace M0Crypto.Release.Ed25519WnafDigits

/-- Bit `i` of `k`. -/
def bit (k i : Nat) : Nat := k / 2 ^ i % 2

/-- `sum_{i < n} f i 2^i` over `Int`. -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n * 2 ^ n

theorem isum_succ (f : Nat → Int) (n : Nat) : isum f (n + 1) = isum f n + f n * 2 ^ n := rfl

theorem isum_congr {f g : Nat → Int} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    isum f n = isum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [isum_succ, isum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem isum_zero_tail {f : Nat → Int} {m t : Nat}
    (h : ∀ i, m ≤ i → i < m + t → f i = 0) : isum f (m + t) = isum f m := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← Nat.add_assoc, isum_succ, ih (fun i h1 h2 => h i h1 (by omega)),
      h (m + t) (by omega) (by omega)]
    simp

theorem isum_zero_tail' {f : Nat → Int} {m n : Nat} (hmn : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → f i = 0) : isum f n = isum f m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact isum_zero_tail h

/-- A digit of width `w`: zero, or odd with `|d| < 2^(w-1)`. -/
def Digit (w : Nat) (d : Int) : Prop :=
  d = 0 ∨ (d % 2 = 1 ∧ -2 ^ (w - 1) < d ∧ d < 2 ^ (w - 1))

/-- The loop state of `m0c_sc_wnaf`: the frame slots `BIT` and `CARRY` and the digit bytes. -/
structure St where
  bit : Nat
  carry : Nat
  digits : Nat → Int

/-- One iteration of the main loop (taken while `bit ≤ 255`). -/
def step (w k : Nat) (s : St) : St :=
  if bit k s.bit = s.carry then { s with bit := s.bit + 1 }
  else
    let now := min w (256 - s.bit)
    let word := s.carry + k / 2 ^ s.bit % 2 ^ now
    let c := word / 2 ^ (w - 1) % 2
    { bit := s.bit + now, carry := c,
      digits := fun i => if i = s.bit then (word : Int) - c * 2 ^ w else s.digits i }

/-- The inner loop: adding bit `b + j` of `k` at position `j` extends the window by one bit. -/
theorem window_step (k b j : Nat) :
    k / 2 ^ b % 2 ^ (j + 1) = k / 2 ^ b % 2 ^ j + 2 ^ j * bit k (b + j) := by
  rw [Nat.pow_succ, Nat.mod_mul, bit, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- The loop invariant. -/
structure Inv (w k : Nat) (s : St) : Prop where
  bit_le : s.bit ≤ 256
  carry_le : s.carry ≤ 1
  sum : isum s.digits s.bit + s.carry * 2 ^ s.bit = ((k % 2 ^ s.bit : Nat) : Int)
  zero : ∀ i, s.bit ≤ i → s.digits i = 0
  digit : ∀ i, Digit w (s.digits i)
  top : s.bit = 256 → s.carry = 0

/-- The state after `call_zero` and the two `str` of zero. -/
def init : St := ⟨0, 0, fun _ => 0⟩

theorem init_inv (w k : Nat) : Inv w k init where
  bit_le := by simp [init]
  carry_le := by simp [init]
  sum := by simp [init, isum]
  zero := by simp [init]
  digit := fun _ => Or.inl rfl
  top := by simp [init]

theorem bit_le_one (k i : Nat) : bit k i ≤ 1 := by unfold bit; omega

/-- The digit computed from an odd `word < 2^w`: the carry is `word ≥ 2^(w-1)` and the digit is
odd with `|d| < 2^(w-1)`. -/
theorem odd_digit {w word : Nat} (hw : 2 ≤ w) (hodd : word % 2 = 1) (hlt : word < 2 ^ w) :
    Digit w ((word : Int) - (word / 2 ^ (w - 1) % 2 : Nat) * 2 ^ w) := by
  unfold Digit
  right
  have e1 : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl
  have e2 : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
  have hW : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hH : 2 ≤ 2 ^ (w - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ w - 1 by omega)
    simpa using this
  have hHe : 2 ^ (w - 1) % 2 = 0 := by
    rw [show w - 1 = (w - 2) + 1 by omega, Nat.pow_succ]; simp
  rw [e1, e2, hW]
  rw [hW] at hlt
  generalize 2 ^ (w - 1) = H at *
  by_cases hc : word < H
  · rw [Nat.div_eq_of_lt hc]; push_cast; omega
  · have hd : word / H = 1 := by
      rw [Nat.div_eq_iff (by omega)]; constructor <;> omega
    rw [hd]; push_cast; omega

theorem bit_top {k : Nat} (hk : k < 2 ^ 255) : bit k 255 = 0 := by
  unfold bit; rw [Nat.div_eq_of_lt hk]

/-- The window value `k / 2^b mod 2^now` at `b + now = 256` has no bit `now - 1`. -/
theorem window_top {k b now : Nat} (hk : k < 2 ^ 255) (h : b + now = 256) (hn : 1 ≤ now) :
    k / 2 ^ b % 2 ^ now < 2 ^ (now - 1) := by
  have : k / 2 ^ b < 2 ^ (now - 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show now - 1 + b = 255 by omega]; exact hk
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this

theorem pow_even {n : Nat} (h : 1 ≤ n) : 2 ^ n % 2 = 0 := by
  rw [show n = (n - 1) + 1 by omega, Nat.pow_succ]; simp

/-- One iteration preserves the invariant, for `k < 2^255` and `2 ≤ w`. -/
theorem step_inv {w k : Nat} {s : St} (hw : 2 ≤ w) (hk : k < 2 ^ 255) (hb : s.bit < 256)
    (h : Inv w k s) : Inv w k (step w k s) := by
  obtain ⟨b, c, d⟩ := s
  obtain ⟨hble, hc, hsum, hzero, hdig, htop⟩ := h
  simp only at hb hble hc hsum hzero hdig htop
  have hbit := bit_le_one k b
  unfold step
  simp only
  split
  · -- digit zero
    rename_i heq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · omega
    · exact hc
    · rw [isum_succ, hzero b (Nat.le_refl _), Nat.mod_pow_succ, ← bit, heq]
      push_cast at hsum ⊢
      rw [Int.pow_succ]
      generalize (2 : Int) ^ b = P at hsum ⊢
      grind
    · exact fun i hi => hzero i (by omega)
    · exact hdig
    · intro h1
      have : b = 255 := by omega
      subst this
      rw [bit_top hk] at heq; omega
  · -- odd window
    rename_i hne
    generalize hn : min w (256 - b) = now
    have hn1 : 1 ≤ now := by omega
    have hnw : now ≤ w := by omega
    have hcase : now = w ∨ b + now = 256 := by omega
    generalize hX : k / 2 ^ b % 2 ^ now = X
    have hXlt : X < 2 ^ now := hX ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
    have hd2 : 2 ∣ 2 ^ now := by
      have := Nat.pow_dvd_pow 2 hn1; simpa using this
    have hX2 : X % 2 = bit k b := by
      rw [← hX, Nat.mod_mod_of_dvd _ hd2]; rfl
    have hpe := pow_even hn1
    have hodd : (c + X) % 2 = 1 := by omega
    have hwlt : c + X < 2 ^ now := by omega
    have hpw : 2 ^ now ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hnw
    have hdg := odd_digit hw hodd (by omega)
    generalize hc' : (c + X) / 2 ^ (w - 1) % 2 = c' at hdg ⊢
    have hc'1 : c' ≤ 1 := by omega
    have htop' : b + now = 256 → c' = 0 := by
      intro h256
      have ht := window_top hk h256 hn1
      rw [hX] at ht
      have hpw1 : 2 ^ (now - 1) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hpe1 := pow_even (n := w - 1) (by omega)
      have : c + X < 2 ^ (w - 1) := by omega
      rw [← hc', Nat.div_eq_of_lt this]
    refine ⟨?_, hc'1, ?_, fun i hi => ?_, fun i => ?_, htop'⟩ <;> dsimp only at *
    · omega
    · -- the sum
      rw [isum_zero_tail' (m := b + 1) (by omega), isum_succ,
        isum_congr (g := d) (fun i hi => ite_eq_right (by omega)), ite_eq_left rfl,
        Nat.pow_add, Nat.mod_mul, hX]
      · push_cast at hsum ⊢
        rw [Int.pow_add]
        rcases hcase with rfl | h256
        · generalize (2 : Int) ^ b = P at hsum ⊢
          generalize (2 : Int) ^ now = Q
          grind
        · rw [htop' h256]
          generalize (2 : Int) ^ b = P at hsum ⊢
          grind
      · intro i h1 h2
        rw [ite_eq_right (by omega)]; exact hzero i (by omega)
    · rw [ite_eq_right (by omega)]; exact hzero i (by omega)
    · split
      · exact hdg
      · exact hdig i

/-- At loop exit (`bit = 256`): the digits sum to `k`, the carry is zero. -/
theorem inv_final {w k : Nat} {s : St} (hk : k < 2 ^ 255) (h : Inv w k s) (hb : s.bit = 256) :
    isum s.digits 256 = k ∧ s.carry = 0 := by
  have hc := h.top hb
  have hs := h.sum
  rw [hb, hc, Nat.mod_eq_of_lt (Nat.lt_trans hk (Nat.pow_lt_pow_right (by omega) (by omega)))]
    at hs
  exact ⟨by simpa using hs, hc⟩

theorem step_bit {w k : Nat} {s : St} (hw : 1 ≤ w) (hb : s.bit < 256) :
    s.bit + 1 ≤ (step w k s).bit := by
  unfold step
  split <;> simp only <;> omega

/-- The main loop, with fuel. -/
def loop (w k : Nat) : Nat → St → St
  | 0, s => s
  | f + 1, s => if s.bit < 256 then loop w k f (step w k s) else s

theorem loop_inv {w k : Nat} (hw : 2 ≤ w) (hk : k < 2 ^ 255) :
    ∀ (f : Nat) (s : St), Inv w k s → Inv w k (loop w k f s) ∧ min 256 (s.bit + f) ≤ (loop w k f s).bit
  | 0, s, h => ⟨h, by simp only [loop]; omega⟩
  | f + 1, s, h => by
    simp only [loop]
    split
    · rename_i hb
      have ⟨h1, h2⟩ := loop_inv hw hk f (step w k s) (step_inv hw hk hb h)
      exact ⟨h1, by have := step_bit (k := k) (by omega : 1 ≤ w) hb; omega⟩
    · exact ⟨h, by omega⟩

/-- The digits of `m0c_sc_wnaf` with width `w` for the scalar `k`. -/
def wnaf (w k : Nat) : Nat → Int := (loop w k 256 init).digits

/-- The windowed NAF: the digits sum to `k`, each is zero or odd with `|d| < 2^(w-1)`, and
those from position 256 on are zero. -/
theorem wnaf_spec (w k : Nat) (hw : 2 ≤ w) (hk : k < 2 ^ 255) :
    isum (wnaf w k) 256 = k ∧ (∀ i, Digit w (wnaf w k i)) ∧ ∀ i, 256 ≤ i → wnaf w k i = 0 := by
  have ⟨h1, h2⟩ := loop_inv hw hk 256 init (init_inv w k)
  have hb : (loop w k 256 init).bit = 256 := by
    have := h1.bit_le
    have h3 : init.bit = 0 := rfl
    rw [h3] at h2
    omega
  exact ⟨(inv_final hk h1 hb).1, h1.digit, fun i hi => h1.zero i (by omega)⟩

/-- Width 3, the digits of `h` in `m0c_ed25519_verify`. -/
theorem wnaf_spec_3 (k : Nat) (hk : k < 2 ^ 255) :
    isum (wnaf 3 k) 256 = k ∧ (∀ i, Digit 3 (wnaf 3 k i)) ∧ ∀ i, 256 ≤ i → wnaf 3 k i = 0 :=
  wnaf_spec 3 k (by omega) hk

/-- Width 5, the digits of `s` in `m0c_ed25519_verify`. -/
theorem wnaf_spec_5 (k : Nat) (hk : k < 2 ^ 255) :
    isum (wnaf 5 k) 256 = k ∧ (∀ i, Digit 5 (wnaf 5 k i)) ∧ ∀ i, 256 ≤ i → wnaf 5 k i = 0 :=
  wnaf_spec 5 k (by omega) hk

/-- A digit of width `w ≤ 8` fits a signed byte. -/
theorem Digit.byte {w : Nat} {d : Int} (hw : w ≤ 8) (h : Digit w d) : -128 ≤ d ∧ d < 128 := by
  have hp : (2 : Int) ^ (w - 1) ≤ 128 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show w - 1 ≤ 7 by omega)
    have : ((2 ^ (w - 1) : Nat) : Int) ≤ ((2 ^ 7 : Nat) : Int) := by exact_mod_cast this
    simpa using this
  rcases h with rfl | ⟨_, h1, h2⟩ <;> omega

end M0Crypto.Release.Ed25519WnafDigits
