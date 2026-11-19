import M0Crypto.Release.Ed25519Sha512Round
import M0Crypto.Release.FrameBase

set_option linter.unusedSimpArgs false

/-!
# The eight rounds of a group

`group_run`: `groupI` (the eight unrolled `round_body`s) turns pairs `S` into `codeRuns k w 8 S`
when the eight `K` pairs at `r7` are `k` and the eight schedule words at `r6` are `w`, and these
lie outside the 64 bytes of the variables at `sp`. Memory outside those bytes is unchanged. The
proof is an induction over the rounds, each an instance of `round_run` with slot map `rslot r`.
-/

namespace M0Crypto.Release.Ed25519Sha512Group

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Exec
open M0Crypto.Release.Ed25519Sha512Round
open M0Crypto.Release.Ed25519Sha512Rounds (upd codeRuns)

/-- `a` is not one of the `VB` bytes of the variables at `sp + VOFF`. -/
def OutV (sp a : Word) : Prop := ∀ k < VB, a ≠ sp + BitVec.ofNat 32 (VOFF + k)

theorem add_ofNat (a : Word) (x y : Nat) :
    a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem vset_out (m : Mem) (sp : Word) {i : Nat} (hi : i < 8) (x : BitVec 64) {a : Word}
    (h : OutV sp a) : vset m sp i x a = m a := by
  have w : ∀ b : Bool, ∀ k < 4, a ≠ slot sp (vw i b) + BitVec.ofNat 32 k := fun b k hk e =>
    h (4 * vw i b + k - VOFF) (by cases b <;> simp [vw, VOFF, VB] <;> omega)
      (by rw [e, slot, add_ofNat]; congr 2; cases b <;> simp [vw, VOFF] <;> omega)
  rw [vset, M0Crypto.Armv6M.write32_other _ _ _ _ (w true),
    M0Crypto.Armv6M.write32_other _ _ _ _ (w false)]

/-- Eight bytes from `a` agree. -/
def Agree8 (m' m : Mem) (a : Word) : Prop := ∀ q < 8, m' (a + BitVec.ofNat 32 q) = m (a + BitVec.ofNat 32 q)

theorem read32_agree {m' m : Mem} {a : Word} (n : Nat) (hn : n + 4 ≤ 8)
    (h : Agree8 m' m a) : read32 m' (a + BitVec.ofNat 32 n) = read32 m (a + BitVec.ofNat 32 n) :=
  M0Crypto.Release.Frame.read32_congr fun k hk => by rw [add_ofNat]; exact h _ (by omega)

theorem pairAt_agree {m' m : Mem} {a : Word} (h : Agree8 m' m a) : pairAt m' a = pairAt m a := by
  have h0 := read32_agree 0 (by omega) h
  have h4 := read32_agree 4 (by omega) h
  simp only [BitVec.add_zero] at h0
  simp only [pairAt, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, h0, h4]

theorem wAt_agree {m' m : Mem} {b : Word} {j : Nat} (h : Agree8 m' m (b + BitVec.ofNat 32 (8 * j))) :
    wAt m' b j = wAt m b j := by
  have h0 := read32_agree 0 (by omega) h
  have h4 := read32_agree 4 (by omega) h
  simp only [BitVec.add_zero, add_ofNat] at h0 h4
  simp only [wAt, show (2 * j + 1) * 4 = 8 * j + 4 by omega, show 2 * j * 4 = 8 * j by omega, h0, h4]

/-- `roundS` reads and writes only pairs below 8. -/
theorem roundS_congr {σ : Nat → Nat} (hσ : ∀ x, σ x < 8) (k w : BitVec 64) {S S' : Nat → BitVec 64}
    (h : ∀ i < 8, S i = S' i) : ∀ i < 8, roundS σ k w S i = roundS σ k w S' i := by
  intro i hi
  simp only [roundS, upd, h i hi, h _ (hσ _)]

theorem codeRuns_succ (k w : Nat → BitVec 64) (m : Nat) (S : Nat → BitVec 64) :
    codeRuns k w (m + 1) S = roundS (rslot m) (k m) (w m) (codeRuns k w m S) := rfl

theorem rslot_lt (r x : Nat) : rslot r x < 8 := by unfold rslot; omega

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (m : Nat) :
    (List.range (m + 1)).flatMap f = (List.range m).flatMap f ++ f m := by
  simp [List.range_succ, List.flatMap_append]

/-- **The eight rounds of a group.** -/
theorem group_run (s : State) (k w : Nat → BitVec 64) (S : Nat → BitVec 64)
    (hS : ∀ i < 8, vp s.mem (s.regs 13) i = S i)
    (hk : ∀ r < 8, pairAt s.mem (s.regs 7 + BitVec.ofNat 32 (8 * r)) = k r)
    (hw : ∀ r < 8, wAt s.mem (s.regs 6) r = w r)
    (hK : ∀ q < 64, OutV (s.regs 13) (s.regs 7 + BitVec.ofNat 32 q))
    (hW : ∀ q < 64, OutV (s.regs 13) (s.regs 6 + BitVec.ofNat 32 q)) :
    let s' := execAll groupI s
    (∀ i < 8, vp s'.mem (s.regs 13) i = codeRuns k w 8 S i) ∧
    (∀ a, OutV (s.regs 13) a → s'.mem a = s.mem a) ∧
    s'.regs 7 = s.regs 7 + BitVec.ofNat 32 (8 * 8) ∧
    ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 15 →
      s'.regs r = s.regs r := by
  have key : ∀ m ≤ 8, let t := execAll ((List.range m).flatMap fun r => roundBody (rslot r) r) s
      (∀ i < 8, vp t.mem (s.regs 13) i = codeRuns k w m S i) ∧
      (∀ a, OutV (s.regs 13) a → t.mem a = s.mem a) ∧
      t.regs 7 = s.regs 7 + BitVec.ofNat 32 (8 * m) ∧
      ∀ r : Reg, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 15 →
        t.regs r = s.regs r := by
    intro m
    induction m with
    | zero => intro _; exact ⟨hS, fun _ _ => rfl, by simp [execAll], fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨v, o, r7, kp⟩ := ih (by omega)
      dsimp only at v o r7 kp ⊢
      rw [flatMap_range_succ, execAll_append]
      generalize execAll ((List.range m).flatMap fun r => roundBody (rslot r) r) s = t at v o r7 kp
      have t13 := kp 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      have t6 := kp 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      obtain ⟨v', ⟨X, Y, me⟩, r7', kp'⟩ := round_run (rslot m) (rslot_lt m) (show m < 8 by omega) t
      have ag : ∀ b n, n + 8 ≤ 64 → (∀ q < 64, OutV (s.regs 13) (b + BitVec.ofNat 32 q)) →
          Agree8 t.mem s.mem (b + BitVec.ofNat 32 n) := fun b n hn hb q hq => by
        rw [add_ofNat]; exact o _ (hb _ (by omega))
      have ek : pairAt t.mem (t.regs 7) = k m := by
        rw [r7, pairAt_agree (ag _ _ (by omega) hK), hk m (by omega)]
      have ew : wAt t.mem (t.regs 6) m = w m := by
        rw [t6, wAt_agree (ag _ _ (by omega) hW), hw m (by omega)]
      rw [t13, ek, ew] at v'
      rw [t13] at me
      refine ⟨fun i hi => ?_, fun a ha => ?_, ?_, fun r h0 h1 h2 h3 h4 h5 h7 h8 h9 h15 => ?_⟩
      · rw [v' i hi, codeRuns_succ]; exact roundS_congr (rslot_lt m) _ _ v i hi
      · rw [me, vset_out _ _ (rslot_lt _ _) _ ha, vset_out _ _ (rslot_lt _ _) _ ha, o a ha]
      · rw [r7', r7, show (8#32 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat,
          show 8 * m + 8 = 8 * (m + 1) by omega]
      · exact (kp' r h0 h1 h2 h3 h4 h5 h7 h8 h9 h15).trans (kp r h0 h1 h2 h3 h4 h5 h7 h8 h9 h15)
  unfold groupI
  exact key 8 (Nat.le_refl _)

end M0Crypto.Release.Ed25519Sha512Group
