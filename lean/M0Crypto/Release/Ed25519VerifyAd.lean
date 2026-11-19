import M0Crypto.Release.Ed25519VerifyStitch
import M0Crypto.Release.Ed25519FeEqZ

/-!
# The adapters of verify's tests

`ltD`, `ltZ`: the block `lt` and its carry test, the value at `r1` below that at `r2`; with `L`
at `r2`, `r1` then holds a scalar. `fe_eq`'s adapter is `Ed25519FeEqZ`'s.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb (execAll)
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_congr)
open M0Crypto.Release.Ed25519CallProg
open Spec.Ed25519 (decodeInt L)

variable (Rs : Rels)

/-! ## `lt` -/

/-- `lt`'s difference is scratch: no values. -/
def ltD : Bd Rs (vbS .lt) :=
  ⟨fun _ => [], fun _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, vbS, ioLt],
    fun _ _ _ _ _ _ _ _ _ h => by simp [vbS, ioLt] at h⟩

/-- The test: the value at `r1` below that at `r2`. -/
def ltOk : List V → Bool
  | [.b a, .b b] => decide (decodeInt a < decodeInt b)
  | _ => false

/-- The premise: `r2` holds `L`. -/
def ltPre : List V → Prop
  | [_, .b b] => decodeInt b = L
  | _ => False

/-- The scalar at `r1`. -/
def ltSem : List V → List V
  | [.b a, _] => [.b a]
  | _ => []

theorem lt_in {c : Ctx} {sp : Word} {t : State} {vs : List V} (h : InsRel Rs c sp ioLt t vs) :
    ∃ a b, vs = [.b a, .b b] ∧ bytesAt t.mem (t.regs 1) 32 = a ∧ bytesAt t.mem (t.regs 2) 32 = b := by
  rcases vs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;>
    simp only [InsRel, All2, ioLt, and_true, and_false, In.kd, ALen.val] at h
  obtain ⟨a, rfl, ha⟩ := Ed25519DecompressProg.rel_bytes Rs h.1
  obtain ⟨b, rfl, hb⟩ := Ed25519DecompressProg.rel_bytes Rs h.2
  rw [BitVec.add_zero] at ha hb
  exact ⟨a, b, rfl, ha, hb⟩

theorem lt_sep {c : Ctx} {sp : Word} {t : State} (hpv : PreV ioLt c sp t.regs) :
    ∀ o < 32, ∀ q < 32, t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 1 + BitVec.ofNat 32 q ∧
      t.regs 3 + BitVec.ofNat 32 o ≠ t.regs 2 + BitVec.ofNat 32 q := by
  have h1 := hpv.2.2 _ List.mem_cons_self
  have h2 := hpv.2.2 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [rgnsC, SRgn.rgnC, ALen.val, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    show (32 = 0) = False from by decide, ite_false, BitVec.add_zero] at h1 h2
  intro o ho q hq
  exact ⟨fun he => h1.not_has ⟨_, List.mem_singleton_self _, o, ho, rfl⟩ ⟨_, List.mem_singleton_self _, q, hq, he⟩,
    fun he => h2.not_has ⟨_, List.mem_singleton_self _, o, ho, rfl⟩ ⟨_, List.mem_singleton_self _, q, hq, he⟩⟩

/-- **`lt`'s test**: carry set (`bhs`) exactly when the value at `r1` is not below that at
`r2`; with `L` at `r2`, `r1` holds a scalar after the block. -/
def ltZ : ZB Rs (ltD Rs) where
  cc := 2
  ok := ltOk
  okf := fun _ _ t _ _ _ hpv hin => by
    obtain ⟨a, b, rfl, ha, hb⟩ := lt_in Rs hin
    show (execAll ltG t).c = _
    rw [(Ed25519VerifyBlocks.lt_run t (lt_sep hpv)).1, ha, hb]
    simp only [ltOk, ← decide_not, Nat.not_lt]
  co := ltCo
  csem := ltSem
  vpre := ltPre
  cpost := fun _ _ t _ _ _ hpv hin hv hok => by
    obtain ⟨a, b, rfl, ha, hb⟩ := lt_in Rs hin
    simp only [ltPre] at hv
    simp only [ltOk, decide_eq_true_eq, hv] at hok
    have hm := (Ed25519VerifyBlocks.lt_run t (lt_sep hpv)).2.1
    simp only [OutsRel, All2, ltCo, ltSem, Rel, BitVec.add_zero, and_true, vbS]
    refine ⟨?_, hok⟩
    rw [← ha]
    exact bytesAt_congr fun i hi => hm _ fun o ho e => (lt_sep hpv o ho i hi).1 e.symm

end M0Crypto.Release.Ed25519VerifyProg
