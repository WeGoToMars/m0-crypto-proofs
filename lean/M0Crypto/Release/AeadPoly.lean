import M0Crypto.Release.AeadCrypt
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
The Poly1305 context through the AEAD body. `PInv A ti msg m`: the context at `A + 8` in
memory `m` has absorbed `msg` (whole blocks, pad 1) since `init` returned with memory `ti`,
and keeps the key, the precomputed words and the pad. It holds after `init`, survives
writes outside `CTX`, and advances by `msg ++ pad16 msg` across `MAC_PADDED`.
-/

namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Blocks (BCtx BValid BEntry BResult accAt keyAt keyAtOK wordAt)
open M0Crypto.Release.Poly1305Context (padAt)
open M0Crypto.Spec.Aead (p pad16)
open M0Crypto.Spec.ChaCha20 (Byte)

structure PInv (A : Word) (ti : Mem) (msg : List Byte) (m : Mem) : Prop where
  key : keyAt m (A + 8#32) = keyAt ti (A + 8#32)
  keyOk : keyAtOK m (A + 8#32)
  pad : padAt m (A + 8#32) = padAt ti (A + 8#32)
  acc : accAt m (A + 8#32) % p = Poly1305Spec.polyBlocks (keyAt ti (A + 8#32)) 1 (accAt ti (A + 8#32) % p) msg
  bound : accAt m (A + 8#32) < 5 * 2 ^ 128
  len : msg.length % 16 = 0

theorem PInv.init (A : Word) (ic : Poly1305Init.ICtx) (ti : State) (hi : Poly1305Init.IResult ic ti)
    (hc : ic.ctx = A + 8#32) : PInv A ti.mem [] ti.mem where
  key := rfl
  keyOk := hc ▸ Poly1305Context.init_keyOk ic ti hi
  pad := rfl
  acc := (Poly1305Spec.polyBlocks_nil _ _ _).symm
  bound := by rw [← hc, Poly1305Context.init_acc ic ti hi]; decide
  len := rfl

theorem ctx_wordAt {m m' : Mem} {ctx : Word} (h : ∀ j < 64, m' (ctx + BitVec.ofNat 32 j) = m (ctx + BitVec.ofNat 32 j))
    (j : Nat) (hj : j < 16) : wordAt m' ctx j = wordAt m ctx j := by
  unfold wordAt; congr 1
  apply read32_congr
  intro k hk
  rw [slot, ofNat_add_assoc]; exact h _ (by omega)

theorem PInv.congr {A : Word} {ti m m' : Mem} {msg : List Byte} (h : PInv A ti msg m)
    (hm : ∀ j < 64, m' (A + 8#32 + BitVec.ofNat 32 j) = m (A + 8#32 + BitVec.ofNat 32 j)) :
    PInv A ti msg m' := by
  have w := ctx_wordAt hm
  have ek : keyAt m' (A + 8#32) = keyAt m (A + 8#32) := by
    unfold keyAt; rw [w 5 (by decide), w 6 (by decide), w 7 (by decide), w 8 (by decide)]
  have ea : accAt m' (A + 8#32) = accAt m (A + 8#32) := by
    unfold accAt; rw [w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide), w 4 (by decide)]
  have ep : padAt m' (A + 8#32) = padAt m (A + 8#32) := by
    unfold padAt; rw [w 12 (by decide), w 13 (by decide), w 14 (by decide), w 15 (by decide)]
  refine ⟨ek.trans h.key, ?_, ep.trans h.pad, by rw [ea]; exact h.acc, by rw [ea]; exact h.bound, h.len⟩
  have hk := h.keyOk
  unfold keyAtOK at hk ⊢
  rw [w 5 (by decide), w 6 (by decide), w 7 (by decide), w 8 (by decide), w 9 (by decide),
    w 10 (by decide), w 11 (by decide)]
  exact hk

theorem pad16_len (bs : List Byte) : (bs ++ pad16 bs).length % 16 = 0 := by
  simp only [List.length_append, pad16, List.length_replicate]; omega

/-- `MAC_PADDED` advances the invariant. -/
theorem PInv.mac {base A d n : Word} {M : Mem} {m : Nat} {s t : State} {ti : Mem} {msg : List Byte}
    (he : MacEnv base A d n M) (h : PInv A ti msg M) (ht : MacPost base A d n M m s t) :
    PInv A ti (msg ++ (Ctx.bytesAt M d n.toNat ++ pad16 (Ctx.bytesAt M d n.toNat))) t.mem := by
  have ep : padAt t.mem (A + 8#32) = padAt M (A + 8#32) := by
    unfold padAt
    rw [he.ctx_word ht.frame 12 (by decide) (by decide), he.ctx_word ht.frame 13 (by decide) (by decide),
      he.ctx_word ht.frame 14 (by decide) (by decide), he.ctx_word ht.frame 15 (by decide) (by decide)]
  refine ⟨(he.key_eq ht.frame).trans h.key, he.keyOk ht.frame h.keyOk, ep.trans h.pad, ?_, ht.bound, ?_⟩
  · rw [ht.acc, h.key, h.acc]
    exact (Poly1305Spec.polyBlocks_append _ _ _ (msg.length / 16) msg _ (by have := h.len; omega)).symm
  · rw [List.length_append]; have := h.len; have := pad16_len (Ctx.bytesAt M d n.toNat); omega

end M0Crypto.Release.Aead
