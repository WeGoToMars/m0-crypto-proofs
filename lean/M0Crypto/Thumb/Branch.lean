import M0Crypto.Thumb.Seq

namespace M0Crypto.Thumb

theorem bl_target (q t : Nat) (hq : q + 4 < 2 ^ 23) (ht : t < 2 ^ 23) :
    BitVec.ofNat 32 q + 4#32 + (BitVec.ofInt 25 ((t : Int) - (q + 4))).signExtend 32 =
      BitVec.ofNat 32 t := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_add, BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt,
    BitVec.toInt_ofNat', BitVec.toInt_ofNat', BitVec.toInt_ofNat']
  have e1 : ((q : Int)).bmod (2 ^ 32) = q := Int.bmod_eq_of_le (by omega) (by omega)
  have e2 : ((t : Int) - (q + 4)).bmod (2 ^ 25) = (t : Int) - (q + 4) :=
    Int.bmod_eq_of_le (by omega) (by omega)
  have e3 : ((t : Int)).bmod (2 ^ 32) = t := Int.bmod_eq_of_le (by omega) (by omega)
  have e4 : ((q : Int) + 4).bmod (2 ^ 32) = q + 4 := Int.bmod_eq_of_le (by omega) (by omega)
  have e5 : (((4 : Nat) : Int)).bmod (2 ^ 32) = 4 := by decide
  rw [e1, e5, e4, e2, show (q : Int) + 4 + ((t : Int) - (q + 4)) = t by omega, e3]

open M0Crypto.Armv6M (Word State)

/-- Setting and then clearing the Thumb bit recovers an aligned address. -/
theorem clear_thumb_return_bit (x : Word) (h : x.getLsbD 0 = false) :
    (x ||| 1#32) &&& ~~~1#32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_one]
  by_cases hz : i = 0
  · subst i
    have h' : x[0] = false := by simpa [BitVec.getLsbD_eq_getElem] using h
    simp [h']
  · simp [hz, hi]

theorem seqSize_mod_two (is : List Instr) : seqSize is % 2 = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have h := instr_size_even i
    change (i.size + seqSize is) % 2 = 0
    omega

theorem runH_compose {code : List (BitVec 8)} {base : Word} {s t u : State}
    {m n : Nat} {x y : List Event}
    (hx : runH code base m s = .ok (t, x)) (hy : runH code base n t = .ok (u, y)) :
    runH code base (m+n) s = .ok (u, x ++ y) := by
  rw [runH_add, hx]
  change (match runH code base n t with
    | .error e => Except.error e
    | .ok (t', tr) => .ok (t', x ++ tr)) = _
  rw [hy]

end M0Crypto.Thumb
