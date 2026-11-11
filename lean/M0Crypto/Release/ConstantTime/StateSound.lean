import M0Crypto.Release.ConstantTime.StateOrder
import M0Crypto.Release.ConstantTime.SemEntails
import M0Crypto.Release.ConstantTime.SemLinkEntails
import M0Crypto.Release.ConstantTime.SemStackOrder

/-! Soundness of the abstract-state ordering for well-formed target records. -/
namespace M0Crypto.Release.ConstantTime

/-- Subsumption preserves the relational interpretation when the target's record
indices are valid. This condition must be established for certificate states. -/
theorem AbsState.le_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {a b : AbsState} {s₁ s₂ : M0Crypto.Armv6M.State}
    (hle : a.le b = true) (hb : b.indicesOk)
    (ha : LowEq p bytes off a s₁ s₂) : LowEq p bytes off b s₁ s₂ := by
  have hle' := hle
  simp only [AbsState.le, Bool.and_eq_true] at hle'
  rcases hle' with ⟨⟨⟨⟨⟨hsp, hfl⟩, hreg⟩, hstk⟩, hrel⟩, hlnk⟩
  have hspEq : a.spOff = b.spOff := by simpa using hsp
  have h := ha
  refine {
    pc := h.pc
    pc_eq := h.pc_eq
    sp := ?_
    sp_eq := h.sp_eq
    regs := ?_
    flags := flagSem_le hfl h.flags
    comparison := cmpSem_le hfl h.comparison
    stack := stkLe_sem hstk h.stack
    facts := ?_
    links := ?_
    size := h.size
    code₁ := h.code₁
    code₂ := h.code₂ }
  · simpa [← hspEq] using h.sp
  · exact regsLe_sem hreg h.regs
  · intro f hf
    exact AbsState.entails_sound ha (hb.2.1 f hf) ((List.all_eq_true.mp hrel) f hf)
  · intro l hl
    exact AbsState.lnkEntails_sound ha (hb.2.2 l hl) ((List.all_eq_true.mp hlnk) l hl)

end M0Crypto.Release.ConstantTime
