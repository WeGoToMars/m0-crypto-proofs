import M0Crypto.Release.Ed25519Build
import M0Crypto.Release.RoutineBranch
import M0Crypto.Release.Field25519Facts
import M0Crypto.Release.Field25519Congr

/-!
# Contracts of the Ed25519 internal routines (not audited)

Each internal routine is a `Routine` (`docs/ROUTINES.md`): entry offset, code, stack, `Pre`, write
and read footprints, `Post`, and the high registers it changes (`clob`; none of them follows the
AAPCS except `m0c_zero`). The routines are proved generic in their offsets: a contract takes the
offsets as parameters, and each build instantiates them from its symbol table. A routine's call
lemma is `Routine.TSpec (fun _ : Unit => R) pub`: its trace is a function of the code base and the
public values `pub`.

* `fieldR`: `m0c_fe_add`, `m0c_fe_sub`, `m0c_fe_mul`, `m0c_fe_sqr`: `dst ≡ fn a b` modulo `p`.
  `dst` equals each input or lies apart from it. Public: `r0`, `r1`, `r2` (if read), `sp`.
* `wordR` (`Ed25519WordLoop`): `m0c_copy`, `m0c_zero`, `m0c_cmov`, a loop over `n` words, `n` even
  and nonzero. Public: `r0`, `r1`, the counter and `sp`; the mask of `m0c_cmov` is secret.
* `lookupR` (`Ed25519Lookup`): the niels entry of a row selected by a secret digit.
-/

namespace M0Crypto.Release.Ed25519Routines

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)

/-- `r4`-`r11`: the high registers a non-AAPCS routine may change. -/
def hiRegs : List Reg := [4, 5, 6, 7, 8, 9, 10, 11]

theorem mem_hiRegs {r : Reg} (h4 : 4 ≤ r.val) (h11 : r.val ≤ 11) : r ∈ hiRegs := by
  revert r; decide

/-- A region of `f` is apart from `g`. -/
theorem sep_of_mem {r : Rgn} {f g : List Rgn} (hr : r ∈ f) (h : Sep f g) : Sep [r] g :=
  fun q hq => by rw [List.mem_singleton.mp hq]; exact h r hr

/-- The word `push {lr}` saves is the window of a routine 4 bytes deep. -/
theorem saved0_eq {f : Routine} {s : State} (h : f.stack = 4) : saved 0 s = f.win s := by
  simp only [saved, Routine.win, h]; rfl

/-- `p` equals `q` or the `n` bytes from each lie apart. -/
def EqOrDisj (p q : Word) (n : Nat) : Prop := p = q ∨ Disj p n q n

/-- **A field routine** at offset `o`, `size` bytes, `stack` bytes deep: `r0 = dst`, `r1 = a`,
`r2 = b` (read when `useB`), 8 words each, word-aligned. -/
def fieldR (o size stack : Nat) (useB : Bool) (fn : Int → Int → Int) : Routine where
  entry := o
  code := [(o, o + size)]
  stack := stack
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧
    (useB = true → (s.regs 2).toNat % 4 = 0) ∧ EqOrDisj (s.regs 0) (s.regs 1) 32 ∧
    (useB = true → EqOrDisj (s.regs 0) (s.regs 2) 32)
  wr := fun s => [⟨s.regs 0, 32⟩]
  rd := fun s => if useB then [⟨s.regs 1, 32⟩, ⟨s.regs 2, 32⟩] else [⟨s.regs 1, 32⟩]
  Post := fun s m _ => ModP (feVal m (s.regs 0)) (fn (feVal s.mem (s.regs 1)) (feVal s.mem (s.regs 2)))
  clob := hiRegs

/-- The public values of a field routine call: its pointers and `sp`. -/
def fieldPub (useB : Bool) (_ : Word) (s : State) : Nat → Word :=
  pubOf (if useB then [s.regs 0, s.regs 1, s.regs 2, s.regs 13] else [s.regs 0, s.regs 1, s.regs 13])

end M0Crypto.Release.Ed25519Routines
