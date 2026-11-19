import M0Crypto.Thumb.Harvard
import M0Crypto.Thumb.SeqScan
import M0Crypto.Release.FrameBase

namespace SafegcdTermination.CodeWindow

open M0Crypto.Armv6M (Mem State Word)
open M0Crypto.Thumb
open M0Crypto.Release (Region)

/-- Proofs of an internal call use only that call's contiguous code window;
    every byte still comes from the enclosing linked artifact. -/
theorem codeAt_slice {m : Mem} {base : Word} {bytes : List (BitVec 8)} {o n : Nat}
    (h : CodeAt m base bytes) :
    CodeAt m (base + BitVec.ofNat 32 o) ((bytes.drop o).take n) := by
  intro i hi
  have hI : o+i < bytes.length := by simp at hi; omega
  rw [ofNat_add_assoc,h _ hI]
  simp only [List.getElem_take,List.getElem_drop]

private theorem hwAt_slice (bytes : List (BitVec 8)) (first n o : Nat) (h : o+2 ≤ n) :
    hwAt ((bytes.drop first).take n) o = hwAt bytes (first+o) := by
  unfold hwAt
  rw [show first+o+1 = first+(o+1) by omega]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    ite_eq_left (show o+1 < n by omega), ite_eq_left (show o < n by omega)]

private theorem instrAt_slice {bytes : List (BitVec 8)} {first n o : Nat} {i : Instr}
    (h : instrAt ((bytes.drop first).take n) o = some i) (hl : o+i.size ≤ n) :
    instrAt bytes (first+o) = some i := by
  have h2 : 2 ≤ i.size := by cases i <;> simp [Instr.size]
  unfold instrAt at h ⊢
  rw [hwAt_slice _ _ _ _ (by omega)] at h
  cases h32 : is32 (hwAt bytes (first+o))
  · rwa [decode_of_not_is32 _ _ (hwAt bytes (first+o+2)) h32] at h
  · have hBL : decodeBL (hwAt bytes (first+o)) (hwAt ((bytes.drop first).take n) (o+2)) = some i := by
      simpa only [decode,h32,ite_true] using h
    have h4 := decodeBL_size hBL
    rwa [hwAt_slice _ _ _ _ (by omega), ← Nat.add_assoc] at h

theorem step_in_artifact {bytes : List (BitVec 8)} {base : Word} {first n : Nat} {s t : State} {e : Event}
    (hSize : bytes.length < 2^32)
    (h : stepH ((bytes.drop first).take n) (base+BitVec.ofNat 32 first) s = .ok (t,e)) :
    stepH bytes base s = .ok (t,e) := by
  let o := (s.pc - (base+BitVec.ofNat 32 first)).toNat
  unfold stepH at h
  simp only at h
  split at h
  · cases h
  · rename_i hOdd
    split at h
    · cases h
    · rename_i i hAt
      split at h
      · rename_i hb
        change o+i.size ≤ ((bytes.drop first).take n).length at hb
        have h2 := instr_size_pos i
        have hFit : first+o+i.size ≤ bytes.length := by
          rw [List.length_take,List.length_drop] at hb
          omega
        have ho : (s.pc-base).toNat = first+o := by
          have hP := base_add_sub (base := base+BitVec.ofNat 32 first) s.pc
          rw [ofNat_add_assoc] at hP
          have ha : s.pc-base = BitVec.ofNat 32 (first+o) := by
            have he : base + BitVec.ofNat 32 (first+o) = s.pc := hP
            bv_omega
          rw [ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hn : o+i.size ≤ n := by simp only [List.length_take] at hb; omega
        have hInst : instrAt bytes (first+o) = some i := instrAt_slice hAt hn
        simp only [stepH,hOdd,Bool.false_eq_true,ite_false,ho,hInst,ite_eq_left hFit]
        exact h
      · cases h

theorem run_in_artifact {bytes : List (BitVec 8)} {base : Word} {first n k : Nat}
    {s t : State} {tr : List Event} (hSize : bytes.length < 2^32)
    (h : runH ((bytes.drop first).take n) (base+BitVec.ofNat 32 first) k s = .ok (t,tr)) :
    runH bytes base k s = .ok (t,tr) := by
  induction k generalizing s t tr with
  | zero => exact h
  | succ k ih =>
    simp only [runH] at h
    split at h
    · cases h
    · rename_i u e hU
      split at h
      · cases h
      · rename_i v ts hV
        cases h
        simp only [runH,step_in_artifact hSize hU, ih hV]

theorem fetched_inside {code : List (BitVec 8)} {base : Word} {s t : State} {n : Nat} {tr : List Event}
    (h : runH code base n s = .ok (t,tr)) : ∀ e ∈ tr, Region base code.length e.pc := by
  intro e he
  obtain ⟨o,ho,eq⟩ := M0Crypto.Release.runH_pcs n s t tr h e he
  exact Region.mk ho eq

theorem run_length {code : List (BitVec 8)} {base : Word} {s t : State} {n : Nat} {tr : List Event}
    (h : runH code base n s = .ok (t,tr)) : n = tr.length := by
  induction n generalizing s t tr with
  | zero => cases h; rfl
  | succ n ih =>
    simp only [runH] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i u ts hs
        cases h
        exact congrArg Nat.succ (ih hs)

end SafegcdTermination.CodeWindow
