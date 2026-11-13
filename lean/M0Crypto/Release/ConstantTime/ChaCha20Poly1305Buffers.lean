import M0Crypto.Release.ConstantTime.BufferSeparation
import M0Crypto.Release.ConstantTime.ChaCha20Poly1305Envs

/-!
Output and tag buffers of `m0c_chacha20_xor` and the AEAD calls as subranges of the separation model.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word)
open M0Crypto.Release.Frame (Disj)

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
