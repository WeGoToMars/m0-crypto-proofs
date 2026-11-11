import M0Crypto.Release.ConstantTime.SemArithmetic
import M0Crypto.Release.ConstantTime.Transfer

/-! Relational arithmetic and NZCV soundness for `addRes`. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word addWithCarry)

/-- In the non-exact case, `addRes`'s fallback result is sound provided its
caller-supplied abstract result describes both concrete `AddWithCarry` results.
The fallback flags are sound for public and secret operands and carry labels. -/
theorem addRes_fallback_sound {p : Params} {va vb exactV : AbsVal} {cin : AbsFlags}
    {x₁ x₂ y₁ y₂ : Word} {c₁ c₂ : Bool}
    (ha : AbsVal.Sem p va x₁ x₂) (hb : AbsVal.Sem p vb y₁ y₂)
    (hc : AbsFlags.Sem cin c₁ c₂)
    (hfallback : addRes va vb cin exactV =
      (exactV, AFl.all (AbsFlags.ofPub (va.pub && vb.pub && cin.pub))))
    (hr : AbsVal.Sem p exactV (addWithCarry x₁ y₁ c₁).1 (addWithCarry x₂ y₂ c₂).1) :
    AbsVal.Sem p (addRes va vb cin exactV).1
        (addWithCarry x₁ y₁ c₁).1 (addWithCarry x₂ y₂ c₂).1 ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.n (addWithCarry x₁ y₁ c₁).1.msb
      (addWithCarry x₂ y₂ c₂).1.msb ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.z ((addWithCarry x₁ y₁ c₁).1 == 0#32)
      ((addWithCarry x₂ y₂ c₂).1 == 0#32) ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.c (addWithCarry x₁ y₁ c₁).2.1
      (addWithCarry x₂ y₂ c₂).2.1 ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.v (addWithCarry x₁ y₁ c₁).2.2
      (addWithCarry x₂ y₂ c₂).2.2 := by
  rw [hfallback]
  refine ⟨hr, ?_⟩
  have hflags :
      AbsFlags.Sem (AbsFlags.ofPub (va.pub && vb.pub && cin.pub))
        (addWithCarry x₁ y₁ c₁).1.msb (addWithCarry x₂ y₂ c₂).1.msb ∧
      AbsFlags.Sem (AbsFlags.ofPub (va.pub && vb.pub && cin.pub))
        ((addWithCarry x₁ y₁ c₁).1 == 0#32) ((addWithCarry x₂ y₂ c₂).1 == 0#32) ∧
      AbsFlags.Sem (AbsFlags.ofPub (va.pub && vb.pub && cin.pub))
        (addWithCarry x₁ y₁ c₁).2.1 (addWithCarry x₂ y₂ c₂).2.1 ∧
      AbsFlags.Sem (AbsFlags.ofPub (va.pub && vb.pub && cin.pub))
        (addWithCarry x₁ y₁ c₁).2.2 (addWithCarry x₂ y₂ c₂).2.2 := by
    by_cases hp : va.pub && vb.pub && cin.pub
    · have hp' := hp
      simp only [Bool.and_eq_true] at hp'
      rcases hp' with ⟨⟨hav, hbv⟩, hcv⟩
      have hx := AbsVal.sem_public ha hav
      have hy := AbsVal.sem_public hb hbv
      have hcin : c₁ = c₂ := by
        cases cin <;> simp_all [AbsFlags.Sem, AbsFlags.pub]
      subst x₂; subst y₂; subst c₂
      simp [AbsFlags.Sem, AbsFlags.ofPub, hav, hbv, hcv]
    · simp [AbsFlags.Sem, AbsFlags.ofPub, hp]
  simpa [AFl.all] using hflags

end M0Crypto.Release.ConstantTime

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word addWithCarry)

/-- Every abstract exact value denotes its corresponding 32-bit constant. -/
theorem AbsVal.exact_sem {p : Params} {v : AbsVal} {a : Nat} {x y : Word}
    (he : v.exact? = some a) (h : AbsVal.Sem p v x y) :
    a < AbsVal.word ∧ x = BitVec.ofNat 32 a ∧ y = BitVec.ofNat 32 a := by
  cases v <;> simp_all [AbsVal.exact?, AbsVal.Sem, AbsVal.word]
  case num lo hi =>
    have hn : x.toNat = a := by omega
    have hlt : a < 2 ^ 32 := by rw [← hn]; exact x.isLt
    constructor
    · exact hlt
    · apply BitVec.eq_of_toNat_eq
      simp_all [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]

/-- `addRes` soundness with the result abstraction supplied by its caller.
The caller proves the result interval; this theorem handles both the exact
constant and fallback paths and all four flags. -/
theorem addRes_sound {p : Params} {va vb exactV : AbsVal} {cin : AbsFlags}
    {x₁ x₂ y₁ y₂ : Word} {c₁ c₂ : Bool}
    (ha : AbsVal.Sem p va x₁ x₂) (hb : AbsVal.Sem p vb y₁ y₂)
    (hc : AbsFlags.Sem cin c₁ c₂)
    (hr : AbsVal.Sem p exactV (addWithCarry x₁ y₁ c₁).1 (addWithCarry x₂ y₂ c₂).1) :
    AbsVal.Sem p (addRes va vb cin exactV).1
        (addWithCarry x₁ y₁ c₁).1 (addWithCarry x₂ y₂ c₂).1 ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.n (addWithCarry x₁ y₁ c₁).1.msb
      (addWithCarry x₂ y₂ c₂).1.msb ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.z ((addWithCarry x₁ y₁ c₁).1 == 0#32)
      ((addWithCarry x₂ y₂ c₂).1 == 0#32) ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.c (addWithCarry x₁ y₁ c₁).2.1
      (addWithCarry x₂ y₂ c₂).2.1 ∧
    AbsFlags.Sem (addRes va vb cin exactV).2.v (addWithCarry x₁ y₁ c₁).2.2
      (addWithCarry x₂ y₂ c₂).2.2 := by
  cases hea : va.exact? with
  | none =>
    apply addRes_fallback_sound ha hb hc _ hr
    simp [addRes, hea]
  | some a =>
    cases heb : vb.exact? with
    | none =>
      apply addRes_fallback_sound ha hb hc _ hr
      simp [addRes, hea, heb]
    | some b =>
      cases cin with
      | hi =>
        apply addRes_fallback_sound ha hb hc _ hr
        simp [addRes, hea, heb]
      | lo =>
        apply addRes_fallback_sound ha hb hc _ hr
        simp [addRes, hea, heb]
      | known c =>
        obtain ⟨hbounda, rfl, rfl⟩ := AbsVal.exact_sem hea ha
        obtain ⟨hboundb, rfl, rfl⟩ := AbsVal.exact_sem heb hb
        simp only [AbsFlags.Sem] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp [addRes, hea, heb, hbounda, hboundb, AbsVal.Sem, AbsFlags.Sem, AbsVal.cst]

/-- Register addition supplies the result premise of `addRes_sound`. -/
theorem addRes_add_sound {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : Word}
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) :
    let res := addRes a b (.known false) (a.add b)
    let v₁ := addWithCarry x₁ y₁ false
    let v₂ := addWithCarry x₂ y₂ false
    AbsVal.Sem p res.1 v₁.1 v₂.1 ∧
    AbsFlags.Sem res.2.n v₁.1.msb v₂.1.msb ∧
    AbsFlags.Sem res.2.z (v₁.1 == 0#32) (v₂.1 == 0#32) ∧
    AbsFlags.Sem res.2.c v₁.2.1 v₂.2.1 ∧ AbsFlags.Sem res.2.v v₁.2.2 v₂.2.2 := by
  apply addRes_sound ha hb (by simp [AbsFlags.Sem])
  have h := AbsVal.add_sound ha hb
  simpa [addWithCarry, BitVec.add_def] using h

end M0Crypto.Release.ConstantTime
