import M0Crypto.Release.Ed25519Recode
import M0Crypto.Release.Ed25519CallProgAdapt

/-!
# `m0c_sc_recode_comb` as a callee

`recAd b Rs` is the adapter of the callee `rcS` (`Ed25519Recode`): the scalar at `r1` is a
`.cl` view, the 64 digit bytes at `r0` its output, with values `recV`: byte `q` is the comb digit
`digitAt n e q` plus 8 (`recBytes`), for the build's `n` combs. The call lemma is `recode_te`,
whose trace is a function of `r0`, `r1` and `sp` (`rcPub`), not of the scalar's bytes.
-/

namespace M0Crypto.Release.Ed25519RecodeAd

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (Rgn Has bytesAt)
open M0Crypto.Release.Routine (codeR)
open M0Crypto.Release.StackEffect (EffT)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519Recode
open M0Crypto.Release.Ed25519RecodeCode (O)
open M0Crypto.Release.Ed25519CombDigits (digitAt)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519 (Build)

/-- The 64 digit bytes of the scalar `e` for `n` combs: comb digit `q` plus 8. -/
def recBytes (n e : Nat) : List (BitVec 8) :=
  (List.range 64).map fun q => BitVec.ofNat 8 (digitAt n e q + 8).toNat

/-- The callee's value: the digit bytes of the scalar's bytes `l`. -/
def recV (n : Nat) : List V → List V
  | [.b l] => [.b (recBytes n (decodeInt l))]
  | _ => [.none]

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The routine's effect is the callee's, in any code bytes. -/
theorem rec_eff (base : Word) (p : Nat → Word) (tr : List Event) (h : rcE base p tr) : rcS.Eff p base tr := by
  refine EffT.mono h (by decide +kernel) (fun y ⟨r, hr, hy⟩ => ⟨r, ?_, hy⟩)
    (fun y ⟨r, hr, hy⟩ => .inr ⟨_, .head _, ?_⟩) (fun y ⟨x, hx, hy⟩ => ⟨_, .head _, ?_⟩)
  · show r ∈ [codeR base, ⟨p 1 + BitVec.ofNat 32 0, 32⟩, ⟨p 0 + BitVec.ofNat 32 0, 64⟩]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  · simp only [List.mem_singleton] at hr; subst hr
    show Region (p 1 + BitVec.ofNat 32 0) 32 y; rw [BitVec.add_zero]; obtain ⟨_, ho, e⟩ := hy; exact Region.mk ho e
  · simp only [rcS, calleeAt, io1, List.mem_singleton] at hx; subst hx
    have hy : Region (p 0 + BitVec.ofNat 32 0) 64 y := hy
    rw [BitVec.add_zero] at hy; exact Rgn.of_region hy
end

/-- **`m0c_sc_recode_comb`'s adapter** in build `b`: the digit bytes of the scalar, its trace a
function of `r0`, `r1` and `sp`. -/
noncomputable def recAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) rcS :=
  letI := b.codeBytes
  Ad.ofTSpec { rcR b.combs with code := footprint O } rfl rfl (by show 44 = stackOf O; decide +kernel)
    ((recode_te b).code _ (by cases b <;> decide +kernel)) (fun _ _ _ h => rec_eff _ _ _ h) (recV b.combs)
    (fun _ _ _ st vs _ _ hi => by
      rcases vs with _ | ⟨l | _ | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, rcS, calleeAt, io1, Rel, In.kd, and_true, and_false] at hi
      obtain ⟨h1, h2⟩ := hi
      show decodeInt (bytesAt st.mem (st.regs 1) 32) < 2 ^ 255
      simp only [BitVec.add_zero] at h1
      rw [h1]
      exact h2)
    (fun st => by
      show ([⟨st.regs 0, 64⟩] : List Rgn) = [⟨st.regs 0 + 0#32, 64⟩]; rw [BitVec.add_zero])
    (fun st => by
      show ([⟨st.regs 1, 32⟩] : List Rgn) = [⟨st.regs 1 + 0#32, 32⟩]; rw [BitVec.add_zero])
    fun _ _ st m _ vs _ hi hp => by
      rcases vs with _ | ⟨l | _ | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, rcS, calleeAt, io1, Rel, In.kd, and_true, and_false] at hi
      simp only [BitVec.add_zero] at hi
      obtain ⟨rfl, -⟩ := hi
      simp only [OutsRel, All2, rcS, calleeAt, io1, recV, Rel, BitVec.add_zero, and_true]
      rw [show bytesAt m (st.regs 0) 64 = (List.range 64).map fun i => m (st.regs 0 + BitVec.ofNat 32 i) from rfl]
      unfold recBytes
      refine List.map_congr_left fun q hq => BitVec.eq_of_toNat_eq ?_
      rw [hp q (List.mem_range.mp hq), BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      rw [← hp q (List.mem_range.mp hq)]; exact (m _).isLt

end M0Crypto.Release.Ed25519RecodeAd
