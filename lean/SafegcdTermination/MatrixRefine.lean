import SafegcdTermination.Inversion
import SafegcdRow.MatrixWords

namespace SafegcdTermination.MatrixRefine
open SafegcdRow.MatrixCode
open SafegcdRow (Word annotate nextPC)
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
set_option linter.unusedSimpArgs false

def w (z : Int) : Word := BitVec.ofInt 32 z

def pack (r : Row) : Word := w (r.a + 65536 * r.b)

theorem pack_plus (r s : Row) : pack (r.plus s) = pack r + pack s := by
  simp only [pack, w, ← BitVec.ofInt_add]
  congr 1
  simp only [Row.plus]
  grind only

theorem pack_minus (r s : Row) : pack (r.minus s) = pack r - pack s := by
  simp only [pack, BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, Row.minus, w]
  congr 1
  grind only

theorem pack_twice (r : Row) : pack r.twice = 2 * pack r := by
  simp only [pack, Row.twice, w]
  change BitVec.ofInt 32 (2 * r.a + 65536 * (2 * r.b)) =
    BitVec.ofInt 32 2 * BitVec.ofInt 32 (r.a + 65536 * r.b)
  rw [← BitVec.ofInt_mul]
  congr 1
  grind only

theorem pack_coeffs (r : Row) (hr : r.norm ≤ batchScale) :
    lowSigned (pack r) = w r.a ∧ highSigned (pack r) = w r.b := by
  have h₁ := magnitude_nonneg r.a
  have h₂ := magnitude_nonneg r.b
  have hab : magnitude (r.a) ≤ 16384 ∧ magnitude (r.b) ≤ 16384 := by
    unfold Row.norm at hr
    change magnitude (r.a) + magnitude (r.b) ≤ 16384 at hr
    omega
  have ha := magnitude_le_iff.mp hab.1
  have hb := magnitude_le_iff.mp hab.2
  have el : (pack r).setWidth 16 = BitVec.ofInt 16 r.a := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, pack, w, Nat.reducePow]
    omega
  have el' : lowSigned (pack r) = w r.a := by
    rw [lowSigned_eq, el]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    unfold w
    rw [BitVec.toInt_ofInt_eq_self (by decide : 0 < 16) (by omega) (by omega),
      BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) (by omega) (by omega)]
  refine ⟨el', ?_⟩
  have es : pack r - w r.a = w (65536 * r.b) := by
    unfold pack w
    rw [BitVec.ofInt_add]
    bv_omega
  rw [highSigned, el', es]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  unfold w
  rw [BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) (by omega) (by omega),
    BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) (by omega) (by omega)]
  omega

def Low (k : Nat) (a : Word) (b : Int) : Prop := a.toInt ≡ b [ZMOD (2 : Int)^k]

private theorem low_of_bmod (v : Int) (k : Nat) (hk : k ≤ 32) :
    v.bmod (2^32) ≡ v [ZMOD (2 : Int)^k] := by
  have dd : (2 : Int)^k ∣ 2^32 := Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hk)
  apply Congruence.of_dvd dd
  exact Int.bmod_emod

theorem low_of_word (k : Nat) (hk : k ≤ 32) (v : Int) : Low k (w v) v := by
  unfold Low w
  rw [BitVec.toInt_ofInt]
  exact low_of_bmod v k hk

theorem Low.fewer {k l : Nat} {x : Word} {a : Int} (h : Low k x a) (hl : l ≤ k) :
    Low l x a :=
  Congruence.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hl)) h

theorem Low.add {k : Nat} {x y : Word} {a b : Int}
    (hx : Low k x a) (hy : Low k y b) (hk : k ≤ 32) : Low k (x + y) (a + b) := by
  unfold Low
  rw [BitVec.toInt_add]
  exact (low_of_bmod _ _ hk).trans (Congruence.add hx hy)

theorem Low.sub {k : Nat} {x y : Word} {a b : Int}
    (hx : Low k x a) (hy : Low k y b) (hk : k ≤ 32) : Low k (x - y) (a - b) := by
  unfold Low
  rw [BitVec.toInt_sub]
  exact (low_of_bmod _ _ hk).trans (Congruence.sub hx hy)

theorem Low.shift {k : Nat} {x : Word} {a : Int} (h : Low (k + 1) x a) :
    Low k (x.sshiftRight 1) (a / 2) := by
  unfold Low at h ⊢
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  rw [Congruence.iff_dvd] at h ⊢
  obtain ⟨m, hm⟩ := h
  have e : a = x.toInt + 2 * ((2 : Int)^k * m) := by rw [Int.pow_succ] at hm; grind only
  change (2 : Int)^k ∣ a / 2 - x.toInt / 2
  rw [e, Int.add_mul_ediv_left _ _ (by decide : (2 : Int) ≠ 0)]
  exact ⟨m, by grind only⟩

theorem Low.parity {k : Nat} {x : Word} {a : Int} (h : Low (k+1) x a) :
    x.getLsbD 0 = decide (a % 2 = 1) := by
  have h₁ : x.toInt % 2 = a % 2 := (h.fewer (l := 1) (by omega))
  have he : x.toInt % 2 = (x.toNat : Int) % 2 := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  rw [BitVec.getLsbD, Nat.testBit_zero, ← h₁, he, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, beq_iff_eq]
  omega

def DeltaFits (d : Int) : Prop := -2147483648 < d ∧ d < 2147483648

theorem delta_sign {d : Int} (h : DeltaFits d) : (-w d).msb = decide (0 < d) := by
  have he : (-w d).toInt = -d := by
    unfold w
    rw [← BitVec.ofInt_neg]
    exact BitVec.toInt_ofInt_eq_self (by decide : 0 < 32) (by obtain ⟨_, _⟩ := h; omega)
      (by obtain ⟨_, _⟩ := h; omega)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, BitVec.msb_eq_true_iff_two_mul_ge, ← BitVec.toInt_neg_iff, he]
  omega

structure Sim (k : Nat) (x : Words) (s : DivstepState) (m : Matrix) : Prop where
  f : Low k x.f s.f
  g : Low k x.g s.g
  delta : x.delta = w s.delta
  top : x.top = pack m.f
  bot : x.bot = pack m.g

theorem Sim.advance {k : Nat} {x : Words} {s : DivstepState} {m : Matrix}
    (h : Sim (k+1) x s m) (hd : DeltaFits s.delta) (hk : k+1 ≤ 32) :
    Sim k (SafegcdRow.MatrixCode.advance x) (step s) (m.next s) := by
  have hg := h.g.parity
  have hD := h.delta ▸ delta_sign hd
  by_cases ho : s.g % 2 = 1
  · have ho' : x.g.getLsbD 0 = true := by simp [hg, ho]
    by_cases hp : 0 < s.delta
    · rw [advance_swap _ ho' (by simp [hD, hp])]
      simp only [step, Matrix.next, ho, hp, and_self, ite_true]
      exact ⟨h.g.fewer (by omega), (h.g.sub h.f hk).shift, by
        rw [h.delta]; unfold w; rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]; bv_omega,
        by rw [h.bot]; exact (pack_twice _).symm,
        by simp only [Matrix.swap, pack_minus, h.top, h.bot]⟩
    · rw [advance_odd _ ho' (by simp [hD, hp])]
      simp only [step, Matrix.next, ho, hp, and_true, ite_false, ite_true, Int.one_mul]
      exact ⟨h.f.fewer (by omega), (h.g.add h.f hk).shift, by
        rw [h.delta]; unfold w; rw [BitVec.ofInt_add]; ac_rfl,
        by simp only [Matrix.odd, pack_twice, h.top],
        by simp only [Matrix.odd, pack_plus, h.top, h.bot]⟩
  · have he : s.g % 2 = 0 := by omega
    have he' : x.g.getLsbD 0 = false := hg.trans (decide_eq_false ho)
    rw [advance_even _ he']
    simp only [step, Matrix.next, he, show ¬((0 : Int) = 1) by decide, and_false, ite_false, Int.zero_mul, Int.add_zero]
    exact ⟨h.f.fewer (by omega), h.g.shift, by
      rw [h.delta]; unfold w; rw [BitVec.ofInt_add]; ac_rfl,
      by simp only [Matrix.even, pack_twice, h.top],
      by exact h.bot⟩

/-- The counter changes by at most 2 in magnitude, including the swap. -/
theorem delta_bound (s : DivstepState) :
    magnitude ((step s).delta) ≤ magnitude (s.delta) + 2 := by
  unfold step
  split
  · change magnitude (2 - s.delta) ≤ magnitude (s.delta) + 2
    simpa only [Int.sub_eq_add_neg, magnitude_neg, show magnitude 2 = 2 by decide, Int.add_comm 2 (magnitude s.delta)] using magnitude_add_le (2 : Int) (-s.delta)
  · change magnitude (2 + s.delta) ≤ magnitude (s.delta) + 2
    simpa only [Int.add_comm s.delta 2, show magnitude 2 = 2 by decide] using
      magnitude_add_le s.delta 2

theorem accumulate_delta_bound (s : DivstepState) (n : Nat) :
    magnitude ((accumulate s n).1.delta) ≤ magnitude (s.delta) + 2*n := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih =>
    change magnitude ((step (accumulate s n).1).delta) ≤ magnitude (s.delta) + 2 * (↑(n+1) : Int)
    have he := delta_bound (accumulate s n).1
    simp only [Int.natCast_succ]
    omega

theorem run_sim (s : DivstepState) (x : Words)
    (h : Sim 32 x s Matrix.identity) (hd : magnitude (s.delta) ≤ 1205)
    (n : Nat) (hn : n ≤ 14) :
    Sim (32-n) (run x n) (accumulate s n).1 (accumulate s n).2 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have he : 32-n = (32-(n+1))+1 := by omega
    have ih := ih (by omega)
    rw [he] at ih
    have hb := accumulate_delta_bound s n
    have hs := magnitude_le_iff.mp (show magnitude ((accumulate s n).1.delta) ≤ 1233 by omega)
    exact ih.advance ⟨by omega, by omega⟩ (by omega)

theorem word_matrix (s : DivstepState) (ho : s.f % 2 = 1) (hd : magnitude (s.delta) ≤ 1205) :
    let (t, m) := accumulate s batchSteps
    unpackWords (run (init (w s.f) (w s.g) (w s.delta)) rounds) =
      (w t.delta, w m.f.a, w m.f.b, w m.g.a, w m.g.b) := by
  have h : Sim 32 (init (w s.f) (w s.g) (w s.delta)) s Matrix.identity :=
    ⟨low_of_word _ (by omega) _, low_of_word _ (by omega) _, rfl, rfl, rfl⟩
  have hs := run_sim s _ h hd rounds (by decide)
  rw [show rounds = batchSteps from rfl] at hs
  rw [show rounds = batchSteps from rfl]
  have hb := (one_matrix s ho).2.2.1
  change (accumulate s batchSteps).2.Bounds batchScale at hb
  have hf := pack_coeffs _ hb.1
  have hg := pack_coeffs _ hb.2
  dsimp only [unpackWords]
  simp only [hs.delta, hs.top, hs.bot, hf.1, hf.2, hg.1, hg.2]

theorem matrix_at {bytes : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : bytes.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt bytes off (body ++ [.bx 14]) = true)
    (hr : (s.regs 14).getLsbD 0 = true)
    (v : DivstepState) (hv : v.f % 2 = 1) (hd : magnitude (v.delta) ≤ 1205)
    (hf : s.regs 0 = w v.f) (hg : s.regs 1 = w v.g) (hδ : s.regs 2 = w v.delta) :
    let (u, m) := accumulate v batchSteps
    ∃ t, runH bytes base (body.length + 1) s =
      .ok (t, annotate s.pc body [] ++ [⟨nextPC s.pc body, .bx 14, []⟩]) ∧
      output t = (w u.delta, w m.f.a, w m.f.b, w m.g.a, w m.g.b) ∧
      t.mem = s.mem ∧ t.sp = s.sp ∧ t.pc = (s.regs 14 &&& ~~~1#32) := by
  obtain ⟨t, ht, hval, hmem, hsp, hret⟩ := run_matrix hb hlen hpc ho hat hr
  rw [hf, hg, hδ, word_matrix v hv hd] at hval
  exact ⟨t, ht, hval, hmem, hsp, hret⟩

end SafegcdTermination.MatrixRefine
