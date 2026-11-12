import M0Crypto.Sym.Block
import M0Crypto.Release.Reach

/-!
# Symbolic read-region check for a straight-line segment

`readChk Ld rg is` is the read analogue of `writeChk`: every read access of an instruction `i`
with `Ld i = true` lies inside one annotated region `(r, k, n)` = the `n` bytes from
`regs r + k` at segment entry. Reads of instructions outside `Ld` are not constrained. `Ld` is
the set of the instructions at the certificate's *load sites* (loads through a caller
pointer); every other read is bounded by the certificate's window.
-/

namespace M0Crypto.Sym

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- A read access by a constrained instruction lies inside one region. -/
def accRCovered (Ld : Instr → Bool) (i : Instr) (rg : List (Reg × Word × Nat)) (a : SAccess) : Bool :=
  a.kind != .read || !Ld i ||
  match peel (norm a.addr) with
  | some (r, k) => rg.any fun p => p.1 == r && (k - p.2.1).toNat + a.width ≤ p.2.2
  | none => false

def readChk (Ld : Instr → Bool) (rg : List (Reg × Word × Nat)) (is : List Instr) : Bool :=
  (symTrace is SState.init).all fun e => e.2.2.all (accRCovered Ld e.2.1 rg)

theorem accRCovered_sound (s0 : State) (Ld : Instr → Bool) (i : Instr)
    (rg : List (Reg × Word × Nat)) (a : SAccess) (hi : Ld i = true)
    (h : accRCovered Ld i rg a = true) (y : Word) (hy : Reads [a.denote s0] y) :
    ∃ p ∈ rg, ∃ o < p.2.2, y = s0.regs p.1 + p.2.1 + BitVec.ofNat 32 o := by
  obtain ⟨x, hx, hkind, k', hk', hyx⟩ := hy
  rw [List.mem_singleton] at hx
  subst hx
  have hk : a.kind = .read := hkind
  have hk'' : k' < a.width := hk'
  have hyx' : y = a.addr.denote s0 + BitVec.ofNat 32 k' := hyx
  unfold accRCovered at h
  generalize hpe : peel (norm a.addr) = pe at h
  cases pe with
  | none => simp [hk, hi] at h
  | some p =>
    obtain ⟨r, k⟩ := p
    have hn : a.addr.denote s0 = s0.regs r + k := by
      rw [← norm_sound s0 a.addr]; exact peel_sound s0 _ r k hpe
    simp only [hk, hi, Bool.or_eq_true, beq_iff_eq, false_or, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_true_eq_false, Bool.not_true,
      Bool.false_eq_true, or_false] at h
    obtain ⟨q, hq, hqr, hle⟩ := h
    subst hqr
    refine ⟨q, hq, (k - q.2.1).toNat + k', by omega, ?_⟩
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, hyx', hn]
    exact add_sub_rearr _ _ _ _

theorem readChk_sound (Ld : Instr → Bool) (rg : List (Reg × Word × Nat)) (is : List Instr)
    (hs : ∀ i ∈ is, Sound i) (s : State) (h : readChk Ld rg is = true) :
    ∀ e ∈ traceAll is s, Ld e.instr = true → ∀ y, Reads e.accesses y →
      ∃ p ∈ rg, ∃ o < p.2.2, y = s.regs p.1 + p.2.1 + BitVec.ofNat 32 o := by
  have hT := symTrace_sound is hs s SState.init
  rw [SState.init_denote] at hT
  intro e he hld y hy
  rw [← hT, List.mem_map] at he
  obtain ⟨⟨pc, i, acc⟩, hse, rfl⟩ := he
  unfold readChk at h
  have h2 : acc.all (accRCovered Ld i rg) = true := List.all_eq_true.mp h _ hse
  obtain ⟨x, hx, hkind, k, hk, hyx⟩ := hy
  have hx' : x ∈ acc.map (SAccess.denote s) := hx
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hx'
  exact accRCovered_sound s Ld i rg a' hld (List.all_eq_true.mp h2 a' ha') y
    ⟨a'.denote s, List.mem_singleton_self _, hkind, k, hk, hyx⟩

end M0Crypto.Sym
