import M0Crypto.Release.ConstantTime.StateSem
import M0Crypto.Release.ConstantTime.Transfer

/-! Relational soundness of flag-label updates. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State Word)

/-- Updating N and Z from a word preserves their labels, leaving C and V alone. -/
theorem setNZ_sound {p : Params} {v : AbsVal} {x y : Word} {f : AFl} {s₁ s₂ : State}
    (hv : AbsVal.Sem p v x y) (hf : FlagSem f s₁ s₂) :
    FlagSem (setNZ f v.pub) (s₁.setNZ x) (s₂.setNZ y) := by
  cases hp : v.pub with
  | false => simpa [FlagSem, setNZ, AbsFlags.ofPub, AbsFlags.Sem, State.setNZ, hp] using ⟨hf.2.2.1, hf.2.2.2⟩
  | true =>
    have heq := AbsVal.sem_public hv hp
    subst y
    simpa [FlagSem, setNZ, AbsFlags.ofPub, AbsFlags.Sem, State.setNZ, hp] using ⟨hf.2.2.1, hf.2.2.2⟩

/-- Overwriting N and Z discards a prior comparison regardless of register touches. -/
theorem setNZ_touch (f : AFl) (r : Nat) (p : Bool) :
    setNZ (f.touch r) p = setNZ f p := by
  cases h : f.cmp with
  | none => simp [AFl.touch, h, setNZ]
  | some c => cases hu : c.uses r <;> simp [AFl.touch, h, hu, setNZ]

/-- Setting N and Z in both concrete states preserves the full relation with the
corresponding abstract flag update. -/
theorem LowEq.withNZ {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} {v : AbsVal} {x y : Word}
    (h : LowEq p bytes off st s₁ s₂) (hv : AbsVal.Sem p v x y) :
    LowEq p bytes off { st with fl := setNZ st.fl v.pub }
      (s₁.setNZ x) (s₂.setNZ y) := by
  rcases h with ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, hflags, _, hstk, hrel,
    hlnk, hsize, hcode₁, hcode₂⟩
  refine ⟨hpc₁, hpc₂, hsp₁, hsp₂, hregs, setNZ_sound hv hflags, ?_,
    hstk, hrel, hlnk, hsize, hcode₁, hcode₂⟩
  intro c hc
  simp [setNZ] at hc

end M0Crypto.Release.ConstantTime
