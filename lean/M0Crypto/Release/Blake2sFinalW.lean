import M0Crypto.Release.Blake2sFinal
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.Blake2sCompress
import M0Crypto.Release.Blake2sStreamSites

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! # `m0c_blake2s_final`: the pc-dependent write bound

At a store site the run writes only the region the store addresses: the context for the two pad
stores (and the chain-window stores of `compress`), the output for the three digest stores.
Elsewhere it writes anywhere `final` may write. -/

namespace M0Crypto.Release.Blake2sFinal

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode
open M0Crypto.Release.Blake2sCode (SiteAt allSites)
open M0Crypto.Release.Blake2sCompress (off_eq)

/-- The three stores that write the digest to `out`. -/
def finalOutSites : List Nat := [siteOf oOutW outW 1, siteOf oOutW outW 3, siteOf oOutB outB 1]

theorem finalOutSites_sub : ∀ off ∈ finalOutSites, off ∈ finalSites := by decide +kernel
theorem finalOutSites_lt : ∀ off ∈ finalOutSites, off < Artifacts.Release.size := by decide +kernel

/-- Program counters of the output stores. -/
def SiteOut (base pc : Word) : Prop := ∃ off ∈ finalOutSites, pc = base + BitVec.ofNat 32 off

def OutR (s : State) : Word → Prop := fun y => ∃ o < 32, y = s.regs 1 + BitVec.ofNat 32 o
def CtxRF (s : State) : Word → Prop := fun y => ∃ o < 112, y = s.regs 0 + BitVec.ofNat 32 o

/-- The write bound of `final` by program counter. -/
def WF (base : Word) (s : State) (pc y : Word) : Prop :=
  WrF s y ∧ (SiteAt base pc → (SiteOut base pc → OutR s y) ∧ (¬ SiteOut base pc → CtxRF s y))

theorem WrF_of_out {s : State} {y : Word} (h : OutR s y) : WrF s y := Or.inr (Or.inr h)
theorem WrF_of_ctx {s : State} {y : Word} (h : CtxRF s y) : WrF s y := Or.inr (Or.inl h)

/-- A pc with no site may write anything `final` may. -/
theorem WF_nosite {base : Word} {s : State} {pc y : Word} (hn : ¬ SiteAt base pc) (hy : WrF s y) :
    WF base s pc y := ⟨hy, fun h => absurd h hn⟩

/-- A code range whose only sites are output stores: its pcs may write `out`. -/
theorem WF_out {base : Word} {s : State} {a n j : Nat} {y : Word} (hj : j < n)
    (ha : a + n ≤ Artifacts.Release.size)
    (hr : ∀ off ∈ allSites, off < a ∨ a + n ≤ off ∨ off ∈ finalOutSites) (hy : OutR s y) :
    WF base s (base + BitVec.ofNat 32 (a + j)) y := by
  refine ⟨WrF_of_out hy, ?_⟩
  rintro ⟨off, hm, he⟩
  have hlt := Blake2sCode.allSites_lt off hm
  have hoff := off_eq (by omega) hlt he
  have hsite : off ∈ finalOutSites := by
    rcases hr off hm with h | h | h <;> first | omega | exact h
  exact ⟨fun _ => hy, fun hn => absurd ⟨off, hsite, he.symm ▸ rfl⟩ hn⟩

/-- A code range with no output store: its pcs may write the context at its sites. -/
theorem WF_ctx {base : Word} {s : State} {a n j : Nat} {y : Word} (hj : j < n)
    (ha : a + n ≤ Artifacts.Release.size)
    (hr : ∀ off ∈ allSites, off < a ∨ a + n ≤ off ∨ off ∉ finalOutSites) (hy : CtxRF s y) :
    WF base s (base + BitVec.ofNat 32 (a + j)) y := by
  refine ⟨WrF_of_ctx hy, ?_⟩
  rintro ⟨off, hm, he⟩
  have hlt := Blake2sCode.allSites_lt off hm
  have hoff := off_eq (by omega) hlt he
  have hsite : off ∉ finalOutSites := by
    rcases hr off hm with h | h | h <;> first | omega | exact h
  refine ⟨fun ⟨o3, h3, he3⟩ => ?_, fun _ => hy⟩
  have := off_eq (by omega) (finalOutSites_lt o3 h3) (he.symm.trans he3)
  exact absurd (this ▸ h3) hsite

end M0Crypto.Release.Blake2sFinal
