import M0Crypto.Release.ConstantTime.MemoryStep
import M0Crypto.Release.AeadCrypt
import M0Crypto.Release.ConstantTime.EntriesDefs

/-! Contract-based separation of writes contained in caller buffers. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Release.Frame (Disj)

/-- An access contained in the second disjoint region remains disjoint from
the first region. The positive width rules out an endpoint represented by a
wrapped machine address. -/
theorem disj_buffer_subrange {a b : Word} {n len offset width : Nat}
    (hd : Disj a n b len) (hwidth : 0 < width) (hbound : offset + width ≤ len) :
    Disj a n (b + BitVec.ofNat 32 offset) width := by
  have haddr : (b + BitVec.ofNat 32 offset).toNat = b.toNat + offset := by
    apply M0Crypto.Release.Frame.toNat_add_ofNat
    obtain ⟨_, hb, _⟩ := hd
    omega
  obtain ⟨ha, hb, hsep⟩ := hd
  unfold Disj
  rw [haddr]
  exact ⟨ha, by omega, by omega⟩

/-- Separation is symmetric. -/
theorem disj_symm {a b : Word} {n m : Nat} (h : Disj a n b m) : Disj b m a n := by
  obtain ⟨ha, hb, hs⟩ := h
  exact ⟨hb, ha, hs.symm⟩

/-- A write within a buffer disjoint from both regions is disjoint from each. -/
theorem buffer_subrange_separated {code stack buf : Word}
    {codeSize stackSize len offset width : Nat}
    (hc : Disj code codeSize buf len) (hs : Disj buf len stack stackSize)
    (hw : 0 < width) (hb : offset + width ≤ len) :
    Disj code codeSize (buf + BitVec.ofNat 32 offset) width ∧
    Disj stack stackSize (buf + BitVec.ofNat 32 offset) width :=
  ⟨disj_buffer_subrange hc hw hb, disj_buffer_subrange (disj_symm hs) hw hb⟩

/-- A ChaCha output subrange is separated from code and the analysis stack. -/
theorem chacha20_output_subrange (c : M0Crypto.Release.Frame.Ctx)
    (hv : M0Crypto.Release.Frame.Valid c) (offset width : Nat)
    (hw : 0 < width) (hb : offset + width ≤ c.len.toNat) :
    Disj c.base M0Crypto.Artifacts.Release.size (c.out + BitVec.ofNat 32 offset) width ∧
    Disj (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) (c.out + BitVec.ofNat 32 offset) width := by
  apply buffer_subrange_separated hv.codeO _ hw hb
  simpa [chacha20Env, chacha20ArgWords, M0Crypto.Release.TraceSpec.chacha20StackBytes,
    M0Crypto.Release.Frame.Ctx.fp, M0Crypto.Release.ChaCha20Layout.chStackBytes_eq] using hv.outF

/-- An AEAD output subrange is separated from code and the analysis stack. -/
theorem aead_output_subrange (c : M0Crypto.Release.Aead.ACall)
    (hb : M0Crypto.Release.Aead.ABuf c) (offset width : Nat)
    (hw : 0 < width) (hbound : offset + width ≤ c.len.toNat) :
    Disj c.base M0Crypto.Artifacts.Release.size (c.out + BitVec.ofNat 32 offset) width ∧
    Disj (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) (c.out + BitVec.ofNat 32 offset) width := by
  apply buffer_subrange_separated hb.codeO _ hw hbound
  simpa [encryptEnv, aeadArgWords, M0Crypto.Release.TraceSpec.aeadStackBytes] using hb.outS

/-- An AEAD tag subrange has the same separation. -/
theorem aead_tag_subrange (c : M0Crypto.Release.Aead.ACall)
    (hb : M0Crypto.Release.Aead.ABuf c) (offset width : Nat)
    (hw : 0 < width) (hbound : offset + width ≤ 16) :
    Disj c.base M0Crypto.Artifacts.Release.size (c.tag + BitVec.ofNat 32 offset) width ∧
    Disj (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) (c.tag + BitVec.ofNat 32 offset) width := by
  apply buffer_subrange_separated hb.codeT _ hw hbound
  simpa [encryptEnv, aeadArgWords, M0Crypto.Release.TraceSpec.aeadStackBytes] using hb.tagS

/-- Every modeled memory operation accesses at least one byte. -/
theorem memOp_width_pos (op : M0Crypto.Thumb.MemOp) : 0 < op.width := by
  cases op <;> decide

/-- First and last byte bounds imply containment of a positive-width access,
provided the permitted buffer leaves room for that width in the address space. -/
theorem buffer_range_of_endpoints (buf a : Word) (len width : Nat) (hw : 0 < width)
    (hlen : len + width ≤ 2 ^ 32)
    (hfirst : (a - buf).toNat < len)
    (hlast : (a + BitVec.ofNat 32 (width - 1) - buf).toNat < len) :
    (a - buf).toNat + width ≤ len := by
  have heq : a + BitVec.ofNat 32 (width - 1) - buf =
      (a - buf) + BitVec.ofNat 32 (width - 1) := by bv_omega
  rw [heq, BitVec.toNat_add] at hlast
  have hm : (BitVec.ofNat 32 (width - 1)).toNat = width - 1 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm] at hlast
  omega

/-- Byte-wise output bounds from a functional trace give the range separation
required by a ChaCha buffer-store step. -/
theorem chacha20_output_endpoints (c : M0Crypto.Release.Frame.Ctx)
    (hv : M0Crypto.Release.Frame.Valid c) (op : M0Crypto.Thumb.MemOp) (a : Word)
    (hfirst : c.oidx a < c.len.toNat)
    (hlast : c.oidx (a + BitVec.ofNat 32 (op.width - 1)) < c.len.toNat) :
    Disj c.base M0Crypto.Artifacts.Release.size a op.width ∧
    Disj (c.sp0 - BitVec.ofNat 32 chacha20Env.win.below)
      (chacha20Env.win.below + chacha20Env.win.above) a op.width := by
  have hw := memOp_width_pos op
  have hlen : c.len.toNat + op.width ≤ 2 ^ 32 := by
    have hc := hv.codeO.1
    have hd := hv.codeO.2.1
    have hs := hv.codeO.2.2
    cases op <;> simp [M0Crypto.Thumb.MemOp.width, M0Crypto.Artifacts.Release.size] at * <;> omega
  have hb := buffer_range_of_endpoints c.out a c.len.toNat op.width hw hlen hfirst hlast
  have hs := chacha20_output_subrange c hv (a - c.out).toNat op.width hw hb
  rw [← M0Crypto.Release.Frame.eq_add_sub c.out a] at hs
  exact hs

/-- Byte-wise output bounds give the corresponding AEAD separation. -/
theorem aead_output_endpoints (c : M0Crypto.Release.Aead.ACall)
    (hb : M0Crypto.Release.Aead.ABuf c) (op : M0Crypto.Thumb.MemOp) (a : Word)
    (hfirst : (a - c.out).toNat < c.len.toNat)
    (hlast : (a + BitVec.ofNat 32 (op.width - 1) - c.out).toNat < c.len.toNat) :
    Disj c.base M0Crypto.Artifacts.Release.size a op.width ∧
    Disj (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) a op.width := by
  have hw := memOp_width_pos op
  have hlen : c.len.toNat + op.width ≤ 2 ^ 32 := by
    have hc := hb.codeO.1
    have hd := hb.codeO.2.1
    have hs := hb.codeO.2.2
    cases op <;> simp [M0Crypto.Thumb.MemOp.width, M0Crypto.Artifacts.Release.size] at * <;> omega
  have hr := buffer_range_of_endpoints c.out a c.len.toNat op.width hw hlen hfirst hlast
  have hs := aead_output_subrange c hb (a - c.out).toNat op.width hw hr
  rw [← M0Crypto.Release.Frame.eq_add_sub c.out a] at hs
  exact hs

/-- Byte-wise tag bounds give the AEAD tag-store separation. -/
theorem aead_tag_endpoints (c : M0Crypto.Release.Aead.ACall)
    (hb : M0Crypto.Release.Aead.ABuf c) (op : M0Crypto.Thumb.MemOp) (a : Word)
    (hfirst : (a - c.tag).toNat < 16)
    (hlast : (a + BitVec.ofNat 32 (op.width - 1) - c.tag).toNat < 16) :
    Disj c.base M0Crypto.Artifacts.Release.size a op.width ∧
    Disj (c.sp0 - BitVec.ofNat 32 encryptEnv.win.below)
      (encryptEnv.win.below + encryptEnv.win.above) a op.width := by
  have hw := memOp_width_pos op
  have hlen : 16 + op.width ≤ 2 ^ 32 := by cases op <;> decide
  have hr := buffer_range_of_endpoints c.tag a 16 op.width hw hlen hfirst hlast
  have hs := aead_tag_subrange c hb (a - c.tag).toNat op.width hw hr
  rw [← M0Crypto.Release.Frame.eq_add_sub c.tag a] at hs
  exact hs

end M0Crypto.Release.ConstantTime
