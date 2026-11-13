import M0Crypto.Release.ConstantTime.Reach
import M0Crypto.Release.ConstantTime.Entries

/-! Relational interpretation of public entry arguments. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State read32)
open M0Crypto.Artifacts
open M0Crypto.Thumb (CodeAt)

/-- Equal public stack arguments establish the entry stack interpretation; all
other words are unconstrained. -/
theorem entryStack_sound (p : Params) (args : Nat) (s₁ s₂ : State)
    (hargs : ∀ k < args, read32 s₁.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)) =
      read32 s₂.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat))) :
    StkSem p (entryState args).stk s₁.mem s₂.mem := by
  intro o
  unfold stkGet
  cases hl : (entryState args).stk.lookup o with
  | none => simp [AbsVal.Sem]
  | some v =>
    obtain ⟨before, after, hlist, _⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : (o, v) ∈ (entryState args).stk := by rw [hlist]; simp
    simp only [entryState, entryStateP, List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
    obtain ⟨k, hk, ho, hv⟩ := hmem
    subst v
    subst o
    simpa [hl, AbsVal.Sem] using hargs k hk

/-- The entry abstract state describes any two machines agreeing on public
register and stack arguments, SP, LR, and the loaded artifact. -/
theorem entryStateP_sound {p : Params} {bytes : List (BitVec 8)} {off np args : Nat}
    {s₁ s₂ : State} (hnp : np ≤ 4)
    (hpc₁ : s₁.pc = p.base + BitVec.ofNat 32 off) (hpc₂ : s₂.pc = s₁.pc)
    (hsp₁ : s₁.regs 13 = p.sp0) (hsp₂ : s₂.regs 13 = s₁.regs 13)
    (hpub : ∀ i, i < np → regAt s₁ i = regAt s₂ i)
    (hlr₁ : regAt s₁ 14 = p.lr0) (hlr₂ : regAt s₂ 14 = regAt s₁ 14)
    (hargs : ∀ k < args, read32 s₁.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)) =
      read32 s₂.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)))
    (hsize : bytes.length = p.size) (hc₁ : CodeAt s₁.mem p.base bytes)
    (hc₂ : CodeAt s₂.mem p.base bytes) :
    LowEq p bytes off (entryStateP np args) s₁ s₂ := by
  refine ⟨hpc₁, hpc₂, ?_, hsp₂, ?_, ?_, ?_, entryStack_sound p args s₁ s₂ hargs,
    ?_, ?_, hsize, hc₁, hc₂⟩
  · simpa [entryStateP] using hsp₁
  · intro i hi hne
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 14 := by
      simp only [numRegs] at hi
      omega
    by_cases hlt : i < np
    · have hp := hpub i hlt
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (exfalso; omega)
          | simp [entryStateP, AbsState.get, regGet, entryRegsP, numRegs, AbsVal.Sem, hlt, hp, hlr₁, hlr₂]
    · rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [entryStateP, AbsState.get, regGet, entryRegsP, numRegs, AbsVal.Sem, hlt, hlr₁, hlr₂]
  · simp [entryStateP, AFl.all, FlagSem, AbsFlags.Sem]
  · simp [entryStateP, AFl.all]
  · simp [entryStateP]
  · simp [entryStateP]

theorem entryState_sound {p : Params} {bytes : List (BitVec 8)} {off args : Nat}
    {s₁ s₂ : State}
    (hpc₁ : s₁.pc = p.base + BitVec.ofNat 32 off) (hpc₂ : s₂.pc = s₁.pc)
    (hsp₁ : s₁.regs 13 = p.sp0) (hsp₂ : s₂.regs 13 = s₁.regs 13)
    (hpub : ∀ i, i < 4 → regAt s₁ i = regAt s₂ i)
    (hlr₁ : regAt s₁ 14 = p.lr0) (hlr₂ : regAt s₂ 14 = regAt s₁ 14)
    (hargs : ∀ k < args, read32 s₁.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)) =
      read32 s₂.mem (p.sp0 + BitVec.ofInt 32 (4 * k : Nat)))
    (hsize : bytes.length = p.size) (hc₁ : CodeAt s₁.mem p.base bytes)
    (hc₂ : CodeAt s₂.mem p.base bytes) :
    LowEq p bytes off (entryState args) s₁ s₂ :=
  entryStateP_sound (np := 4) (Nat.le_refl 4) hpc₁ hpc₂ hsp₁ hsp₂ hpub hlr₁ hlr₂ hargs hsize hc₁ hc₂

/-- A related initial state is admitted by the checked certificate entry. -/
theorem certAt_initial {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {p : Params} {s₁ s₂ : State}
    (hc : certOk env bytes entry init cert = true)
    (hi : certIndicesFailure cert env = none) (hrel : LowEq p bytes entry init s₁ s₂) :
    CertAt env cert p bytes s₁ s₂ := by
  have hf := (certOk_iff env bytes entry init cert).mp hc
  unfold certFailure at hf
  cases hb : findBlk cert entry none with
  | none => simp [hb] at hf
  | some b =>
    simp only [hb] at hf
    split at hf
    · contradiction
    · rename_i hle
      have hle' : init.le b.st = true := by simpa using hle
      have hm : b ∈ cert := List.mem_of_find?_eq_some hb
      have hidx := certIndices_blockHead hi hm
      have hnext := AbsState.le_sound hle' hidx hrel
      exact certAt_resolved hc hb hm hnext

end M0Crypto.Release.ConstantTime
