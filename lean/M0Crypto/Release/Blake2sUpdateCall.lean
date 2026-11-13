import M0Crypto.Release.Blake2sUpdateNf
import M0Crypto.Release.Blake2sCopyMain
import M0Crypto.Release.Blake2sCopySites
import M0Crypto.Release.ReachPcN
import M0Crypto.Release.ReachPcR2
import M0Crypto.Release.Blake2sLd

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # The copy call of `update`

`bl_copy` is the generic `bl` to `m0c_blake2s_copy`, stated on the state just before the `bl`. -/

namespace M0Crypto.Release.Blake2sUpdate

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sCopy (CopyEntry CopyPost copy_reach copy_reachS copy_reachSR SrcR WrC fr sr_ne sr_pc)
open M0Crypto.Release.Blake2sLd (ldAll)
open M0Crypto.Release.Blake2sCode (SiteAt)
open M0Crypto.Release.Frame (Disj read32_congr toNat_add_ofNat)

/-- What the call to copy leaves, stated on the state `u` just before the `bl`. -/
structure BcPost (base : Word) (off : Nat) (u v : State) : Prop where
  pc : v.pc = base + BitVec.ofNat 32 (off + 4)
  sp : v.regs 13 = u.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → v.regs r = u.regs r
  copy : ∀ i < (u.regs 2).toNat, v.mem (u.regs 0 + BitVec.ofNat 32 i) = u.mem (u.regs 1 + BitVec.ofNat 32 i)
  mem : ∀ y, (∀ o < 20, y ≠ u.regs 13 - 20#32 + BitVec.ofNat 32 o) →
    (∀ o < (u.regs 2).toNat, y ≠ u.regs 0 + BitVec.ofNat 32 o) → v.mem y = u.mem y

/-- The writes of a call to copy, seen from the state `u` before the `bl`: its frame and the
destination, and only the destination at its store sites. -/
def WCu (base : Word) (u : State) (pc y : Word) : Prop :=
  ((∃ o < 20, y = u.regs 13 - 20#32 + BitVec.ofNat 32 o) ∨
    (∃ o < (u.regs 2).toNat, y = u.regs 0 + BitVec.ofNat 32 o)) ∧
  (SiteAt base pc → ∃ o < (u.regs 2).toNat, y = u.regs 0 + BitVec.ofNat 32 o)

theorem bl_copyS {base : Word} {W : Word → Word → Prop} {R : Word → Prop} {u : State} (off : Nat)
    (hb4 : base.toNat % 4 = 0) (hpc : u.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hbl : instrAt B off = some (.bl (blImm off copyStart))) (hsz : off + 4 < Artifacts.Release.size)
    (ht : Release.blTarget off (blImm off copyStart) = BitVec.ofNat 32 copyStart)
    (hcode : CodeAt u.mem base B) (hsp4 : (u.regs 13).toNat % 4 = 0) (hspLo : 20 ≤ (u.regs 13).toNat)
    (n1 : 1 ≤ (u.regs 2).toNat) (n64 : (u.regs 2).toNat ≤ 64)
    (dj : Disj (u.regs 0) (u.regs 2).toNat (u.regs 1) (u.regs 2).toNat)
    (codeD : Disj base Artifacts.Release.size (u.regs 0) (u.regs 2).toNat)
    (codeF : Disj base Artifacts.Release.size (u.regs 13 - 20#32) 20)
    (dstF : Disj (u.regs 0) (u.regs 2).toNat (u.regs 13 - 20#32) 20)
    (srcF : Disj (u.regs 1) (u.regs 2).toNat (u.regs 13 - 20#32) 20)
    (hW : ∀ pc y, WCu base u pc y → W pc y) (hRc : ∀ y, SrcR u y → R y) :
    ReachS base (PNR ldAll W R) u (BcPost base off u) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  apply ReachS.blPcNR hb2 off copyStart _ hpc ho hbl (by omega) ht
  obtain ⟨sc, hsc⟩ : ∃ x, x = (u.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 copyStart) := ⟨_, rfl⟩
  rw [← hsc]
  have sr : ∀ r : Reg, r ≠ 14 → r.val ≠ 15 → sc.regs r = u.regs r := by
    intro r h14 h15
    rw [hsc, sr_ne _ _ _ _ (by rintro rfl; exact h15 rfl), sr_ne _ _ _ _ h14]
  have scm : sc.mem = u.mem := by rw [hsc]; rfl
  have scpc : sc.pc = base + BitVec.ofNat 32 copyStart := by rw [hsc, sr_pc]
  have s13 : sc.regs 13 = u.regs 13 := sr 13 (by decide) (by decide)
  have s0 : sc.regs 0 = u.regs 0 := sr 0 (by decide) (by decide)
  have s1 : sc.regs 1 = u.regs 1 := sr 1 (by decide) (by decide)
  have s2 : sc.regs 2 = u.regs 2 := sr 2 (by decide) (by decide)
  have h14' : sc.regs 14 = (base + BitVec.ofNat 32 (off + 4)) ||| 1#32 := by
    rw [hsc, sr_ne _ _ _ _ (by decide)]; simp [State.setReg]
  have e : CopyEntry base sc := by
    refine ⟨hb4, scpc, by rw [scm]; exact hcode, by rw [s13]; exact hsp4, by rw [s13]; exact hspLo,
      by rw [h14']; exact M0Crypto.Release.lr_odd _, by rw [s2]; exact n1, by rw [s2]; exact n64,
      by rw [s0, s1, s2]; exact dj, by rw [s0, s2]; exact codeD,
      by unfold fr; rw [s13]; exact codeF, by unfold fr; rw [s0, s2, s13]; exact dstF,
      by unfold fr; rw [s1, s2, s13]; exact srcF⟩
  have hq : ∀ v, CopyPost sc v → BcPost base off u v := by
    intro v hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hbs := codeD.1
      rw [hp.pc, h14', M0Crypto.Release.lr_mask]
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    · rw [hp.sp, s13]
    · intro r h4 h11
      have hn14 : r ≠ 14 := fun h => by rw [h] at h11; exact absurd h11 (by decide)
      have hn15 : r.val ≠ 15 := by omega
      have hcases : ∀ q : Reg, 4 ≤ q.val → q.val ≤ 11 → q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 := by
        decide
      have : v.regs r = sc.regs r := by
        rcases hcases r h4 h11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hp.r4
        · exact hp.r5
        · exact hp.r6
        · exact hp.r7
        · exact hp.r8
        · exact hp.r9
        · exact hp.r10
        · exact hp.r11
      rw [this, sr r hn14 hn15]
    · intro i hi
      have := hp.copy i (by rw [s2]; exact hi)
      rw [s0, s1, scm] at this
      exact this
    · intro y hy1 hy2
      have := hp.mem y (by intro o ho; unfold fr; rw [s13]; exact hy1 o ho)
        (by intro o ho; rw [s0]; exact hy2 o (by rw [s2] at ho; exact ho))
      rw [this, scm]
  refine (copy_reachSR e).mono
    (fun _ ev hp => ⟨⟨fun y hy => hW _ _ ?_, hp.1.2⟩, fun hld y hy => hRc y ?_⟩) hq
  · obtain ⟨hw, hs⟩ := hp.1.1 y hy
    refine ⟨?_, fun hsite => ?_⟩
    · rcases hw with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · exact Or.inl ⟨o, ho, by unfold fr; rw [s13]⟩
      · exact Or.inr ⟨o, by rw [s2] at ho; exact ho, by rw [s0]⟩
    · obtain ⟨o, ho, rfl⟩ := hs hsite
      exact ⟨o, by rw [s2] at ho; exact ho, by rw [s0]⟩
  · obtain ⟨o, ho, h⟩ := hp.2 hld y hy
    exact ⟨o, by rw [s2] at ho; exact ho, by rw [h, s1]⟩

end M0Crypto.Release.Blake2sUpdate
