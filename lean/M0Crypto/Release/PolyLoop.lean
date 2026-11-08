import M0Crypto.Release.PolyOne
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace M0Crypto.Release.PolyBlocks
open M0Crypto.Armv6M (Word Reg State Mem read32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.AEAD (p)
attribute [local irreducible] body loadState oneBlock loopState

theorem hval_pc (s : State) (pc : Word) : hval (s.setReg 15 pc) = hval s := by
  simp [hval, M0Crypto.Armv6M.State.setReg]
theorem mp_pc (s : State) (pc : Word) : mp (s.setReg 15 pc) = mp s := by
  simp [mp, M0Crypto.Armv6M.State.setReg]
theorem cw_pc (s : State) (pc : Word) (j : Nat) : cw (s.setReg 15 pc) j = cw s j := by
  simp [cw, M0Crypto.Armv6M.State.setReg]

theorem bytes_congr (m m' : Mem) : ∀ n a, (∀ o < n, m' (a + BitVec.ofNat 32 o) = m (a + BitVec.ofNat 32 o)) →
    Ctx.bytesAt m' a n = Ctx.bytesAt m a n
  | 0, a, _ => rfl
  | n+1, a, h => by
    rw [bytesAt_succ, bytesAt_succ]
    congr 1
    · simpa using h 0 (by omega)
    · apply bytes_congr m m' n
      intro o ho
      rw [show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_assoc]
      exact h (1+o) (by omega)

theorem disj_tail (a sp : Word) (n : Nat) (hn : 0 < n) (h : Disj a (16*(n+1)) sp frameBytes) :
    Disj (a + 16#32) (16*n) sp frameBytes := by
  obtain ⟨ha, hs, hd⟩ := h
  have he : (a + 16#32).toNat = a.toNat + 16 := by
    change (a + BitVec.ofNat 32 16).toNat = _
    apply toNat_add_ofNat; omega
  simp only [Disj, he]
  omega

/-- Lift the exact block step to RFC's fold over an arbitrary positive number of
full blocks; both aligned and unaligned loads are covered by `one_correct`. -/
theorem loop_correct (base : Word) : ∀ n, 0 < n → ∀ s : State,
    Sep s → KeyOK s → (s.regs 14).toNat ≤ 4 → (s.regs 12).toNat ≤ 1 →
    Disj (mp s) (16*n) (s.regs 13) frameBytes →
    hval (loopState base n s) % p = PolySpec.polyBlocks (rval s) (s.regs 12).toNat (hval s % p)
      (Ctx.bytesAt s.mem (mp s) (16*n)) ∧ hval (loopState base n s) < 5*2^128
    := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn0 s hs hk hh hp hm
    obtain ⟨u, hu, step⟩ := step_result s hs hk hh hp
    have hc := step.value
    have hb := step.bound
    by_cases hn : n = 0
    · subst n
      rw [loopState, ite_eq_left (rfl : (0 : Nat) = 0), hu, hval_pc]
      have hlen : (Ctx.bytesAt s.mem (mp s) 16).length = 16 := bytesAt_length _ _ _
      rw [show 16*(0+1) = 16 from rfl, PolySpec.polyBlocks_block _ _ _ _ hlen,
        PolySpec.step_mod]
      exact ⟨hc, hb⟩
    · let t := u.setReg 15 (base + BitVec.ofNat 32 testAt)
      have ts : t.regs 13 = s.regs 13 := by
        rw [show t.regs 13 = u.regs 13 from setReg_regs_ne _ _ _ _ (by decide)]
        exact step.sp
      have tp : t.regs 12 = s.regs 12 := by
        rw [show t.regs 12 = u.regs 12 from setReg_regs_ne _ _ _ _ (by decide)]
        exact step.pad
      have tm : mp t = mp s + 16#32 := by rw [mp_pc, step.ptr]
      have tS : Sep t := by
        change Sep (u.setReg 15 (base + BitVec.ofNat 32 testAt))
        simpa only [Sep, setReg_regs_ne _ 15 7 _ (by decide),
          setReg_regs_ne _ 15 13 _ (by decide)] using step.sep
      have tK : KeyOK t := by
        change KeyOK (u.setReg 15 (base + BitVec.ofNat 32 testAt))
        simp only [KeyOK, cw_pc]
        exact step.key
      have th : (t.regs 14).toNat ≤ 4 := by
        have h := hb
        rw [hval, PolyArith.val5] at h
        change (u.regs 14).toNat ≤ 4
        omega
      have tr : rval t = rval s := by
        change rval (u.setReg 15 (base + BitVec.ofNat 32 testAt)) = rval s
        simp only [rval, cw_pc]
        rw [step.words 5 (by decide), step.words 6 (by decide),
          step.words 7 (by decide), step.words 8 (by decide)]
      have hd := disj_tail (mp s) (s.regs 13) n (by omega) hm
      have hrec := ih (by omega) t tS tK th (by rw [tp]; exact hp)
        (by rw [tm, ts]; exact hd)
      have hbytes : Ctx.bytesAt t.mem (mp t) (16*n) = Ctx.bytesAt s.mem (mp s + 16#32) (16*n) := by
        rw [tm]
        apply bytes_congr
        intro o ho
        apply step.mem
        rintro ⟨q, hq, heq⟩
        -- `q` lies in the one-block frame (`4 * slotPad` bytes, `PolyOne`), which fits in `frameBytes`.
        have hq' : q < PolyBlocks.frameBytes := Nat.lt_of_lt_of_le hq (by decide)
        apply ne_of_disj hm.1 hm.2.1 hm.2.2 (i := 16+o) (j := q) (by omega) hq'
        rw [show (16#32 : Word) = BitVec.ofNat 32 16 from rfl, ofNat_add_assoc] at heq
        exact heq
      rw [tr, tp, hbytes, hval_pc, hc] at hrec
      rw [loopState, ite_eq_right hn, hu]
      rw [show 16*(n+1) = 16 + 16*n by omega, PolySpec.bytesAt_add,
        PolySpec.polyBlocks_append _ _ _ 1 _ _ (by simp [bytesAt_length]),
        PolySpec.polyBlocks_block _ _ _ _ (bytesAt_length _ _ _), PolySpec.step_mod]
      exact hrec

end M0Crypto.Release.PolyBlocks
