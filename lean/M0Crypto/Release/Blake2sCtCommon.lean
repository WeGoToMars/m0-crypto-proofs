import M0Crypto.Release.ConstantTime.Blake2sStreamEntries
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.RegionStores
import M0Crypto.Release.Blake2sSites
import M0Crypto.Release.Blake2sStreamSites
import M0Crypto.Release.ReachPcN

set_option linter.unusedSimpArgs false

/-!
# Shared pieces of the `update` and `final` constant-time proofs

* the event of the second run's step at a checked position (`certPoint_step_event₂`);
* decoding a store site;
* `PubLoadOk` for the declared `ldr rt, [r4, #CTX_USED]`: both runs hold the context pointer in
  `r4` and read equal words.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State LowReg read32)
open M0Crypto.Thumb
open M0Crypto.Release.Blake2sStreamCode (isStoreSite)

/-- `certPoint_step_event` for the partner run. -/
theorem certPoint_step_event₂ {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s s₂ t : State} {e : Event} (i : Instr)
    (hc : certOk env bytes entry init cert = true)
    (ha : certAligned cert = true) (hbase : p.base.toNat % 2 = 0)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is))
    (h : LowEq p bytes off st s s₂) (hstep : step s₂ = .ok (t, e)) :
    e = ⟨s₂.pc, i, i.accesses s₂⟩ := by
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hd := decode_at h.code₂ off i hdecode hlen
  have heven := certPoint_pc_even p.base hbase ha hm hp
  have hpc : s₂.pc = p.base + BitVec.ofNat 32 off := h.pc_eq.trans h.pc
  unfold step at hstep
  simp only [hpc] at hstep
  rw [heven, hd] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · cases hex : i.exec s₂ <;> simp_all
  · simp at hstep

/-- A store site decodes to a nonempty `stm` or an immediate-offset store. -/
theorem store_decode {off : Nat} (h : isStoreSite (instrAt B off) = true) {i : Instr}
    (hi : instrAt B off = some i) :
    (∃ n l, i = .stm n l ∧ 0 < bitCount l) ∨ (∃ op t n k, i = .memImm op t n k ∧ op.isLoad = false) := by
  rw [hi] at h
  cases i with
  | stm n l => exact Or.inl ⟨n, l, rfl, by simpa [isStoreSite] using h⟩
  | memImm op t n k => exact Or.inr ⟨op, t, n, k, rfl, by simpa [isStoreSite] using h⟩
  | _ => simp [isStoreSite] at h

/-- The declared public load of `ctx.used` loads the same word in both runs. -/
theorem pubLoadOk_used (env : Env) (off : Nat) (t : LowReg) {u₁ u₂ : State} {a : Word}
    (h₁ : u₁.regs 4 = a) (h₂ : u₂.regs 4 = a)
    (hm : read32 u₁.mem (a + 104#32) = read32 u₂.mem (a + 104#32)) :
    PubLoadOk env off u₁ u₂ (.memImm .ldr t 4 26) := by
  intro _ _
  show read32 u₁.mem (u₁.regs 4 + BitVec.ofNat 32 (26 * 4)) = read32 u₂.mem (u₂.regs 4 + BitVec.ofNat 32 (26 * 4))
  rw [h₁, h₂]
  exact hm

/-- Away from the declared loads, `PubLoadOk` is vacuous. -/
theorem pubLoadOk_of_notin {env : Env} {off : Nat} {s₁ s₂ : State} {i : Instr}
    (h : env.pubLoads.contains off = false) : PubLoadOk env off s₁ s₂ i := by
  cases i <;> simp only [PubLoadOk] <;>
    (intro _ hm; rw [h] at hm; exact absurd hm (by decide))

end M0Crypto.Release.ConstantTime
