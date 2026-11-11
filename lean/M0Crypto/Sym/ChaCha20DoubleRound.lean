import M0Crypto.Sym.MemBridge
import M0Crypto.Sym.ChaCha20Core
import M0Crypto.Release.ChaCha20RoundDefs
import M0Crypto.Proofs.ChaCha20DoubleRound

/-!
# Symbolic check of the ChaCha20 double round

`dround_view_sym` has exactly the statement of `Release.ChaCha20Round.dround_view`. Its
proof does not step through the instructions. The specification side is written as
syntax: `innerS` is the RFC 8439 inner block on symbolic words, built from `qrS`, with
the input words `inS` (word 2 in r0, words 0..11 in stack slots, words 12..15 in
r8..r11). For each output word `k < 16` the kernel runs the symbolic executor and the
normaliser on `dround` (with r4-r7 known) and on `innerS`, and checks that the two
normal forms agree. Denotation lemmas then connect `innerS` to `innerBlockF`.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State read32 slot)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (quarterRound rotl)
open M0Crypto.Release
open M0Crypto.Proofs.ChaCha20DoubleRound (upd qroundF innerBlockF)

/-- Symbolic address of state word `k` in the frame at SP. -/
def slotS (k : Nat) : SExpr := .add (.reg0 13) (.const (BitVec.ofNat 32 (4 * k)))

/-- Symbolic input state word `k`, in the convention of `ChaCha20Round.view (some 2)`. -/
def inS (k : Nat) : SExpr :=
  if k = 2 then .reg0 0
  else if k < 12 then .ld32 .mem0 (slotS k)
  else if k < 16 then .reg0 (ChaCha20Round.dregOf k)
  else .const 0

/-- Functional update on symbolic word functions. -/
def upS (f : Nat → SExpr) (i : Nat) (v : SExpr) : Nat → SExpr :=
  fun j => if i = j then v else f j

/-- `QUARTERROUND(a, b, c, d)` on symbolic word functions, as `qroundF`. -/
def qroundS (f : Nat → SExpr) (a b c d : Nat) : Nat → SExpr :=
  let q := qrS (f a) (f b) (f c) (f d)
  upS (upS (upS (upS f a q.1) b q.2.1) c q.2.2.1) d q.2.2.2

/-- The RFC 8439 inner block on symbolic words, in the order of `innerBlockF`. -/
def innerS (f : Nat → SExpr) : Nat → SExpr :=
  let f := qroundS f 0 4 8 12
  let f := qroundS f 1 5 9 13
  let f := qroundS f 2 6 10 14
  let f := qroundS f 3 7 11 15
  let f := qroundS f 0 5 10 15
  let f := qroundS f 1 6 11 12
  let f := qroundS f 2 7 8 13
  let f := qroundS f 3 4 9 14
  f

/-! ## Denotation of the symbolic word functions -/

theorem upS_denote (s : State) (f : Nat → SExpr) (i : Nat) (v : SExpr) (j : Nat) :
    (upS f i v j).denote s = upd (fun j => (f j).denote s) i (v.denote s) j := by
  unfold upS upd
  by_cases h : i = j <;> simp [h]

theorem denote_qroundS (s : State) (f : Nat → SExpr) (a b c d j : Nat) :
    (qroundS f a b c d j).denote s = qroundF (fun i => (f i).denote s) a b c d j := by
  simp only [qroundS, qroundF, upS_denote]
  rfl

theorem denote_innerS (s : State) (f : Nat → SExpr) (k : Nat) :
    (innerS f k).denote s = innerBlockF (fun i => (f i).denote s) k := by
  simp only [innerS, innerBlockF, denote_qroundS]

/-! ## Input words against the view -/

theorem view_two (t : State) : ChaCha20Round.view (some 2) t 2 = t.regs 0 := by
  simp [ChaCha20Round.view]

theorem view_lo (t : State) (k : Nat) (h2 : k ≠ 2) (hk : k < 12) :
    ChaCha20Round.view (some 2) t k = read32 t.mem (slot (t.regs 13) k) := by
  simp [ChaCha20Round.view, hk, Ne.symm h2]

theorem view_mid (t : State) (k : Nat) (h12 : 12 ≤ k) (hk : k < 16) :
    ChaCha20Round.view (some 2) t k = t.regs (ChaCha20Round.dregOf k) := by
  simp [ChaCha20Round.view, hk, Nat.not_lt.mpr h12]

theorem view_top (t : State) (k : Nat) (h : 16 ≤ k) : ChaCha20Round.view (some 2) t k = 0 := by
  simp [ChaCha20Round.view, Nat.not_lt.mpr (show 12 ≤ k by omega), Nat.not_lt.mpr h]

theorem denote_inS (s : State) (k : Nat) :
    (inS k).denote s = ChaCha20Round.view (some 2) s k := by
  by_cases h2 : k = 2
  · subst h2
    rw [view_two]
    simp [inS, SExpr.denote]
  by_cases h12 : k < 12
  · rw [view_lo s k h2 h12]
    simp [inS, slotS, slot, SExpr.denote, SMem.denote, h2, h12]
  by_cases h16 : k < 16
  · rw [view_mid s k (by omega) h16]
    simp [inS, SExpr.denote, h2, h12, h16]
  · rw [view_top s k (by omega)]
    simp [inS, SExpr.denote, h2, h12, h16]

/-- The inner block on the input words is the inner block on the view. -/
theorem inner_view (s : State) (k : Nat) :
    (innerS inS k).denote s = innerBlockF (ChaCha20Round.view (some 2) s) k := by
  have hfun : (fun i => (inS i).denote s) = ChaCha20Round.view (some 2) s :=
    funext (denote_inS s)
  rw [denote_innerS, hfun]

theorem upd_hi (f : Nat → Word) (i : Nat) (v : Word) (k : Nat) (h : i ≠ k) :
    upd f i v k = f k := by
  show (if i = k then v else f k) = f k
  simp [h]

theorem qroundF_hi (f : Nat → Word) (a b c d k : Nat) (ha : a ≠ k) (hb : b ≠ k)
    (hc : c ≠ k) (hd : d ≠ k) : qroundF f a b c d k = f k := by
  unfold qroundF
  rw [upd_hi _ _ _ _ hd, upd_hi _ _ _ _ hc, upd_hi _ _ _ _ hb, upd_hi _ _ _ _ ha]

/-- Above word 16 the inner block is the identity on the view. -/
theorem innerBlockF_hi (g : Nat → Word) (k : Nat) (hk : 16 ≤ k) :
    innerBlockF g k = g k := by
  unfold innerBlockF
  rw [qroundF_hi _ 3 4 9 14 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 2 7 8 13 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 1 6 11 12 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 0 5 10 15 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 3 7 11 15 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 2 6 10 14 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 1 5 9 13 k (by omega) (by omega) (by omega) (by omega),
    qroundF_hi _ 0 4 8 12 k (by omega) (by omega) (by omega) (by omega)]

/-! ## Symbolic double round and its output words -/

abbrev dS : SState := symExec ChaCha20Round.dround (SState.initK rotK)

/-- Symbolic output word `k` of the double round, in the convention of the view. -/
def wordS (k : Nat) : SExpr :=
  if k = 2 then dS.regs 0
  else if k < 12 then .ld32 dS.mem (slotS k)
  else dS.regs (ChaCha20Round.dregOf k)

theorem view_wordS (s : State) (h : ChaCha20Round.RotRegs s) (k : Nat) (hk : k < 16) :
    ChaCha20Round.view (some 2) (execAll ChaCha20Round.dround s) k = (norm (wordS k)).denote s := by
  have hk' : ∀ p ∈ rotK, s.regs p.1 = p.2 := by
    obtain ⟨h4, h5, h6, h7⟩ := h
    simp [rotK, h4, h5, h6, h7]
  have hsp : (execAll ChaCha20Round.dround s).regs 13 = s.regs 13 := by
    rw [execAll_regs_normK ChaCha20Round.dround ChaCha20Round.dround_falls rotK s hk' 13]
    rw [show norm (dS.regs 13) = SExpr.reg0 13 by decide +kernel]
    rfl
  by_cases h2 : k = 2
  · subst h2
    rw [view_two, execAll_regs_normK ChaCha20Round.dround ChaCha20Round.dround_falls rotK s hk' 0]
    simp only [wordS, ↓reduceIte]
  by_cases h12 : k < 12
  · rw [view_lo (execAll ChaCha20Round.dround s) k h2 h12, hsp]
    simp only [wordS, h2, h12, ↓reduceIte]
    exact read32_execAll_normK ChaCha20Round.dround ChaCha20Round.dround_falls rotK s hk' (slotS k)
  · rw [view_mid (execAll ChaCha20Round.dround s) k (by omega) hk]
    simp only [wordS, h2, h12, ↓reduceIte]
    exact execAll_regs_normK ChaCha20Round.dround ChaCha20Round.dround_falls rotK s hk' _

/-! ## One kernel check per output word -/

theorem dword_0 : norm (wordS 0) = norm (innerS inS 0) := by decide +kernel
theorem dword_1 : norm (wordS 1) = norm (innerS inS 1) := by decide +kernel
theorem dword_2 : norm (wordS 2) = norm (innerS inS 2) := by decide +kernel
theorem dword_3 : norm (wordS 3) = norm (innerS inS 3) := by decide +kernel
theorem dword_4 : norm (wordS 4) = norm (innerS inS 4) := by decide +kernel
theorem dword_5 : norm (wordS 5) = norm (innerS inS 5) := by decide +kernel
theorem dword_6 : norm (wordS 6) = norm (innerS inS 6) := by decide +kernel
theorem dword_7 : norm (wordS 7) = norm (innerS inS 7) := by decide +kernel
theorem dword_8 : norm (wordS 8) = norm (innerS inS 8) := by decide +kernel
theorem dword_9 : norm (wordS 9) = norm (innerS inS 9) := by decide +kernel
theorem dword_10 : norm (wordS 10) = norm (innerS inS 10) := by decide +kernel
theorem dword_11 : norm (wordS 11) = norm (innerS inS 11) := by decide +kernel
theorem dword_12 : norm (wordS 12) = norm (innerS inS 12) := by decide +kernel
theorem dword_13 : norm (wordS 13) = norm (innerS inS 13) := by decide +kernel
theorem dword_14 : norm (wordS 14) = norm (innerS inS 14) := by decide +kernel
theorem dword_15 : norm (wordS 15) = norm (innerS inS 15) := by decide +kernel

/-- Per-word check for every `k < 16`, by case split on `k` (`omega` supplies the cases). -/
theorem dround_word (k : Nat) (hk : k < 16) : norm (wordS k) = norm (innerS inS k) := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact dword_0
  · exact dword_1
  · exact dword_2
  · exact dword_3
  · exact dword_4
  · exact dword_5
  · exact dword_6
  · exact dword_7
  · exact dword_8
  · exact dword_9
  · exact dword_10
  · exact dword_11
  · exact dword_12
  · exact dword_13
  · exact dword_14
  · exact dword_15

/-- The double round's view after `dround`, from the RFC 8439 inner block on the view
before it. The statement of `Release.ChaCha20Round.dround_view`. -/
theorem dround_view_sym (s : State) (hrot : ChaCha20Round.RotRegs s) :
    ChaCha20Round.view (some 2) (execAll ChaCha20Round.dround s) = innerBlockF (ChaCha20Round.view (some 2) s) := by
  funext k
  by_cases hk : k < 16
  · rw [view_wordS s hrot k hk, dround_word k hk, norm_sound s, inner_view]
  · rw [view_top _ k (by omega), innerBlockF_hi _ k (by omega), view_top s k (by omega)]

end M0Crypto.Sym
