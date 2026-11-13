/-!
Value of a little-endian list of 32-bit words, for the X25519 arithmetic.

`val ws` reads `ws` as a number in base `2^32`, least significant word first. The split
lemma `val_append` is one generic lemma for every boundary the code uses (64, 128 and 256
bits are lists of 2, 4 and 8 words). `val_not` is the value of the word-wise complement,
which the code uses to negate a product; `val_word` reads one word back.

The words are `Nat`: machine layers map a register or memory word `w` to `w.toNat`. No
machine term appears here.
-/

namespace M0Crypto.Release.X25519Val

/-- Little-endian value in base `2^32`. -/
def val : List Nat → Nat
  | [] => 0
  | w :: ws => w + 2 ^ 32 * val ws

/-- Every word is below `2^32`. -/
def Words (ws : List Nat) : Prop := ∀ w ∈ ws, w < 2 ^ 32

theorem val_nil : val [] = 0 := rfl

theorem val_cons (w : Nat) (ws : List Nat) : val (w :: ws) = w + 2 ^ 32 * val ws := rfl

theorem val_append (xs ys : List Nat) :
    val (xs ++ ys) = val xs + 2 ^ (32 * xs.length) * val ys := by
  induction xs with
  | nil => simp [val]
  | cons x xs ih =>
    simp only [List.cons_append, val, ih, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [Nat.mul_assoc (2 ^ (32 * xs.length)), Nat.mul_left_comm (2 ^ (32 * xs.length))]
    omega

theorem val_lt (ws : List Nat) (h : Words ws) : val ws < 2 ^ (32 * ws.length) := by
  induction ws with
  | nil => simp [val]
  | cons w ws ih =>
    have hw := h w (List.mem_cons_self ..)
    have ih := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [val, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have : val ws + 1 ≤ 2 ^ (32 * ws.length) := ih
    have : 2 ^ 32 * (val ws + 1) ≤ 2 ^ 32 * 2 ^ (32 * ws.length) := Nat.mul_le_mul_left _ this
    rw [Nat.mul_comm (2 ^ (32 * ws.length))]
    omega

/-- Word-wise complement: `2^32 - 1 - w` in every word. -/
def notW (ws : List Nat) : List Nat := ws.map fun w => 2 ^ 32 - 1 - w

theorem val_not (ws : List Nat) (h : Words ws) :
    val (notW ws) + val ws + 1 = 2 ^ (32 * ws.length) := by
  induction ws with
  | nil => simp [val, notW]
  | cons w ws ih =>
    have hw := h w (List.mem_cons_self ..)
    have ih := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [notW, List.map_cons, val, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add] at ih ⊢
    rw [Nat.mul_comm (2 ^ (32 * ws.length)), ← ih]
    omega

/-- Word `i` of the value. -/
theorem val_word (ws : List Nat) (h : Words ws) (i : Nat) (hi : i < ws.length) :
    val ws / 2 ^ (32 * i) % 2 ^ 32 = ws[i] := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    have hw := h w (List.mem_cons_self ..)
    cases i with
    | zero => simp [val]; omega
    | succ i =>
      have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) i (by simp at hi; omega)
      simp only [val, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one, Nat.pow_add]
      rw [Nat.mul_comm (2 ^ (32 * i)) (2 ^ 32), ← Nat.div_div_eq_div_mul]
      rw [show (w + 2 ^ 32 * val ws) / 2 ^ 32 = val ws by omega]
      exact ih

/-- The value of an 8-word list given as eight words. -/
theorem val_eight (w0 w1 w2 w3 w4 w5 w6 w7 : Nat) :
    val [w0, w1, w2, w3, w4, w5, w6, w7] =
      w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 + 2 ^ 128 * w4 + 2 ^ 160 * w5 +
        2 ^ 192 * w6 + 2 ^ 224 * w7 := by
  simp only [val]; omega

end M0Crypto.Release.X25519Val
