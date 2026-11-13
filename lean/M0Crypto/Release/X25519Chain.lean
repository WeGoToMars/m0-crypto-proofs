import M0Crypto.Release.X25519Congr

/-!
The Fermat inversion chain of `m0c_x25519`, as data, and its exponent.

`invChain` mirrors `INV_CHAIN` of the generator (`tools/gen_x25519.py`) step for step:
`sqr d a n` sets slot `d` to slot `a` squared `n` times (one call, or a call followed by a
counted loop of `n - 1` calls), `mul d a b` sets `d` to the product. Slot `z` holds the
input, `dst` the output. The machine proof of the chain is a fold over this list, so the
eleven segments are not written out by hand.

`invChain_exp` evaluates the exponent the chain computes in `dst`: `p - 2`. `run_pow`
shows that running the chain on values congruent to powers of `x` leaves `x ^ exp` in each
slot it defines, so the output is congruent to `x ^ (p - 2)`, which is how RFC 7748 writes
the inverse.
-/

namespace M0Crypto.Release.X25519Chain

open M0Crypto.Release.X25519Congr

/-- Slots named in `INV_CHAIN`: four temporaries, the input and the output. -/
inductive CSlot where
  | t0 | t1 | t2 | t3 | z | dst
  deriving DecidableEq, Repr

inductive CStep where
  | sqr (d a : CSlot) (n : Nat)
  | mul (d a b : CSlot)
  deriving DecidableEq, Repr

open CSlot CStep in
/-- `INV_CHAIN` of the generator. -/
def invChain : List CStep :=
  [sqr t0 z 1, sqr t1 t0 2, mul t1 z t1, mul t0 t0 t1, sqr t2 t0 1, mul t1 t1 t2,
   sqr t2 t1 5, mul t1 t2 t1, sqr t2 t1 10, mul t2 t2 t1, sqr t3 t2 20, mul t2 t3 t2,
   sqr t2 t2 10, mul t1 t2 t1, sqr t2 t1 50, mul t2 t2 t1, sqr t3 t2 100, mul t2 t3 t2,
   sqr t2 t2 50, mul t1 t2 t1, sqr t1 t1 5, mul dst t1 t0]

def upd {α : Type} (f : CSlot → α) (d : CSlot) (v : α) : CSlot → α :=
  fun s => if s = d then v else f s

/-- One step on exponents. -/
def CStep.exp (e : CSlot → Nat) : CStep → CSlot → Nat
  | .sqr d a n => upd e d (e a * 2 ^ n)
  | .mul d a b => upd e d (e a + e b)

/-- Exponent in every slot after the chain, starting from `z = 1`. -/
def chainExp (steps : List CStep) : CSlot → Nat :=
  steps.foldl CStep.exp (fun s => if s = .z then 1 else 0)

theorem invChain_exp : chainExp invChain .dst = 2 ^ 255 - 21 := by decide

theorem invChain_exp_p : (chainExp invChain .dst : Int) = p - 2 := by
  rw [invChain_exp]; decide

/-- Squarings and multiplications of the chain (the generator asserts 254 and 11). -/
def sqrCount : List CStep → Nat
  | [] => 0
  | .sqr _ _ n :: r => n + sqrCount r
  | .mul .. :: r => sqrCount r

theorem invChain_counts :
    sqrCount invChain = 254 ∧ (invChain.filter fun s => s matches .mul ..).length = 11 := by
  decide

/-! ### Values -/

/-- One step on values, each operation only up to congruence: `R d v w` relates the
value `w` written to slot `d` with the exact result `v`. -/
def CStep.Rel (f g : CSlot → Int) : CStep → Prop
  | .sqr d a n => g d ≡p f a ^ (2 ^ n) ∧ ∀ s, s ≠ d → g s = f s
  | .mul d a b => g d ≡p f a * f b ∧ ∀ s, s ≠ d → g s = f s

/-- A run of the chain: a list of value maps, one per step boundary. -/
inductive Run : List CStep → (CSlot → Int) → (CSlot → Int) → Prop
  | nil (f) : Run [] f f
  | cons {st steps f g h} : CStep.Rel f g st → Run steps g h → Run (st :: steps) f h

theorem pow_pow_two (x : Int) (e n : Nat) : (x ^ e) ^ (2 ^ n) = x ^ (e * 2 ^ n) := by
  rw [Int.pow_mul]

/-- Slots defined after a step: the destination joins the defined set. -/
def CStep.defs (D : CSlot → Bool) : CStep → CSlot → Bool
  | .sqr d .. => upd D d true
  | .mul d .. => upd D d true

/-- Every step reads only defined slots. -/
def readsDefined : List CStep → (CSlot → Bool) → Bool
  | [], _ => true
  | .sqr d a n :: r, D => D a && readsDefined r (CStep.defs D (.sqr d a n))
  | .mul d a b :: r, D => D a && D b && readsDefined r (CStep.defs D (.mul d a b))

/-- Defined slots after the whole list. -/
def definedAfter (steps : List CStep) (D : CSlot → Bool) : CSlot → Bool :=
  steps.foldl CStep.defs D

theorem run_pow (x : Int) :
    ∀ (steps : List CStep) (D : CSlot → Bool) (e : CSlot → Nat) (f h : CSlot → Int),
      readsDefined steps D = true → (∀ s, D s = true → f s ≡p x ^ e s) → Run steps f h →
      ∀ s, definedAfter steps D s = true → h s ≡p x ^ steps.foldl CStep.exp e s
  | [], D, e, f, h, _, hf, hr => by cases hr; simpa [definedAfter] using hf
  | st :: steps, D, e, f, h, hw, hf, .cons (g := g) hs hr => by
    intro s hs'
    cases st with
    | sqr d a n =>
      simp only [readsDefined, Bool.and_eq_true] at hw
      obtain ⟨hD, ho⟩ := hs
      refine run_pow x steps _ _ g h hw.2 ?_ hr s hs'
      intro t ht
      by_cases h' : t = d
      · subst h'
        simp only [CStep.exp, upd, if_pos rfl]
        exact hD.trans ((ModP.pow (hf a hw.1) _).trans (ModP.of_eq (pow_pow_two x _ _)))
      · simp only [CStep.defs, upd, if_neg h'] at ht
        simp only [CStep.exp, upd, if_neg h', ho t h']
        exact hf t ht
    | mul d a b =>
      simp only [readsDefined, Bool.and_eq_true] at hw
      obtain ⟨hD, ho⟩ := hs
      refine run_pow x steps _ _ g h hw.2 ?_ hr s hs'
      intro t ht
      by_cases h' : t = d
      · subst h'
        simp only [CStep.exp, upd, if_pos rfl]
        exact hD.trans ((ModP.mul (hf a hw.1.1) (hf b hw.1.2)).trans
          (ModP.of_eq (Int.pow_add x _ _).symm))
      · simp only [CStep.defs, upd, if_neg h'] at ht
        simp only [CStep.exp, upd, if_neg h', ho t h']
        exact hf t ht

/-- Only the input slot is read before it is written, and the output is written. -/
theorem invChain_reads : readsDefined invChain (fun s => decide (s = .z)) = true ∧
    definedAfter invChain (fun s => decide (s = .z)) .dst = true := by decide

/-- The chain inverts: whatever the temporaries and the output slot hold at the start, a
run from `z ≡ x` ends with the output congruent to `x ^ (p - 2)`. -/
theorem invChain_correct (x : Int) (f h : CSlot → Int) (hz : f .z ≡p x)
    (hr : Run invChain f h) : h .dst ≡p x ^ (2 ^ 255 - 21) := by
  have := run_pow x invChain (fun s => decide (s = .z)) (fun s => if s = .z then 1 else 0)
    f h invChain_reads.1 ?_ hr .dst invChain_reads.2
  · exact this.trans (ModP.of_eq (by rw [← invChain_exp]; rfl))
  · intro s hs
    simp only [decide_eq_true_eq] at hs
    subst hs
    simpa [Int.pow_one] using hz

end M0Crypto.Release.X25519Chain
