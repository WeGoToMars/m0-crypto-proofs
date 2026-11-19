import M0Crypto.Release.Field25519Canon
import M0Crypto.Release.Ed25519Leaf
import M0Crypto.Release.Ed25519FieldRoutines
import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.Ed25519CallProgAdapt

namespace M0Crypto.Release.Ed25519FeCanon

open M0Crypto.Armv6M (Word Reg State Mem read32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.BlockEffect
open M0Crypto.Release.Field25519Facts (psum psum_congr feVal_psum)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Sym (SExpr SBool SMem)

open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint (Rgn Has)
open M0Crypto.Release.StackEffect (InR)
open M0Crypto.Release.Ed25519Leaf
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Artifacts

export M0Crypto.Release.Field25519Canon (body body_val body_r0 cw ldW ldW_denote)

theorem feVal_congr {m m' : Mem} {a : Word} (h : ∀ y, Has [⟨a, 32⟩] y → m' y = m y) :
    feVal m' a = feVal m a := by
  unfold feVal; congr 1; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  rw [Frame.read32_congr fun k hk =>
    h _ ⟨_, List.mem_singleton_self _, 4 * i + k, show 4 * i + k < 32 by omega, by rw [ofNat_add_assoc]⟩]

/-- The 32 bytes at `r0`. -/
def rg0 : List (SExpr × Nat) := [(.reg0 0, 32)]

/-- **`m0c_fe_canon`**: the element at the word-aligned `r0` becomes its canonical representative. -/
def canonR : Routine := leafR Ed25519Compact.fe_canon body rg0 rg0
  (fun s => (s.regs 0).toNat % 4 = 0)
  (fun s m _ => feVal m (s.regs 0) = feVal s.mem (s.regs 0) % pN ∧ feVal m (s.regs 0) < pN)

/-- Its effect: it reads the 32 bytes at `r0`, then writes them. -/
abbrev canonE : Word → (Nat → Word) → TrP := leafE Ed25519Compact.fe_canon [0] rg0 rg0 rg0

theorem canon_ok : leafOk body [0] [(.reg0 0, 4)] rg0 rg0 rg0 rg0 rg0 = true := by decide +kernel

/-- `m0c_fe_canon`'s call lemma with its effect, in each build. -/
noncomputable def canon_te (b : Build) : letI := b.codeBytes; canonR.TE (leafPub [0]) canonE :=
  letI := b.codeBytes
  leaf_te canon_ok (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)
    (fun s h r hr => by rw [List.mem_singleton.mp hr]; exact h) fun s t _ _ tr hm => by
      have := body_val t
      rw [tr 0 (by decide) (by decide), feVal_congr (a := s.regs 0) (m := s.mem) hm] at this
      exact this

/-! ## As a callee

The element at `r0` in, its canonical value out. -/

def ioCanon : Iface :=
  { ins := [(0, 0, .view .fe)], outs := [(0, 0, .fc)], wr := [⟨0, 0, .k 32⟩], rd := [⟨0, 0, .k 32⟩],
    al := [0] }

def canonS : CalleeS := calleeAt Ed25519Compact.fe_canon ioCanon [0]

theorem canon_pub : canonS.pub = leafPub [0] := rfl
/-- The leaf effect is the callee's. -/
theorem canon_eff (base : Word) (p : Nat → Word) (tr : List Event) (h : canonE base p tr) :
    canonS.Eff p base tr :=
  leaf_eff h (by decide +kernel) (by decide) (by decide)

end M0Crypto.Release.Ed25519FeCanon
