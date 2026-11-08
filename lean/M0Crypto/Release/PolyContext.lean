import M0Crypto.Release.PolyBlocksRFC
import M0Crypto.Release.PolyFinishCorrect
import M0Crypto.Release.PolyInit
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace M0Crypto.Release.PolyContext
open M0Crypto.Armv6M (Word State Mem read32 slot)
open M0Crypto.Release.Frame
open M0Crypto.Release.PolyBlocks (wordAt accAt keyAt keyAtOK)
open M0Crypto.Spec.AEAD (p clamp leNat leBytes)
open M0Crypto.Spec.ChaCha20 (Byte)

def padAt (m : Mem) (ctx : Word) : Nat := PolyArith.val4 (wordAt m ctx 12) (wordAt m ctx 13)
  (wordAt m ctx 14) (wordAt m ctx 15)

theorem mask_bound (x : Word) :
    (x &&& 0x0fffffff#32).toNat < 2^28 ∧ (x &&& 0x0ffffffc#32).toNat < 2^28 := by
  have h0 : x.toNat &&& (0x0fffffff#32).toNat ≤ (0x0fffffff#32).toNat := Nat.and_le_right
  have h1 : x.toNat &&& (0x0ffffffc#32).toNat ≤ (0x0ffffffc#32).toNat := Nat.and_le_right
  simp only [← BitVec.toNat_and] at h0 h1
  change _ ≤ 268435455 at h0
  change _ ≤ 268435452 at h1
  omega

theorem mask_four (x : Word) : (x &&& 0x0ffffffc#32).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show 4 = 2^2 from rfl, Nat.and_mod_two_pow]
  simp

theorem sfold_nat (x : Word) (hx : x.toNat < 2^28) :
    (PolyInit.sfold x).toNat = x.toNat + x.toNat/4 := by
  simp only [PolyInit.sfold, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- Init establishes the exact clamping and precomputation invariants consumed by
blocks, without adding any key restrictions to the initialization contract. -/
theorem init_keyOK (c : PolyInit.ICtx) (t : State) (ht : PolyInit.IResult c t) : keyAtOK t.mem c.ctx := by
  have w : ∀ j < 16, wordAt t.mem c.ctx j = (PolyInit.initW c j).toNat := by
    intro j hj; rw [wordAt]; exact congrArg BitVec.toNat (ht.ctx j hj)
  unfold keyAtOK
  rw [w 5 (by decide), w 6 (by decide), w 7 (by decide), w 8 (by decide),
    w 9 (by decide), w 10 (by decide), w 11 (by decide)]
  simp only [PolyInit.initW]
  exact ⟨⟨(mask_bound _).1, (mask_bound _).2, (mask_bound _).2, (mask_bound _).2⟩,
    ⟨mask_four _, mask_four _, mask_four _⟩,
    ⟨sfold_nat _ (mask_bound _).2, sfold_nat _ (mask_bound _).2, sfold_nat _ (mask_bound _).2⟩⟩

theorem init_acc (c : PolyInit.ICtx) (t : State) (ht : PolyInit.IResult c t) : accAt t.mem c.ctx = 0 := by
  unfold accAt wordAt slot
  rw [ht.ctx 0 (by decide), ht.ctx 1 (by decide), ht.ctx 2 (by decide), ht.ctx 3 (by decide), ht.ctx 4 (by decide)]
  rfl

theorem init_key (c : PolyInit.ICtx) (t : State) (ht : PolyInit.IResult c t) :
    keyAt t.mem c.ctx = clamp (leNat (Ctx.bytesAt c.m0 c.key 16)) := by
  unfold keyAt wordAt slot
  rw [ht.ctx 5 (by decide), ht.ctx 6 (by decide), ht.ctx 7 (by decide), ht.ctx 8 (by decide)]
  rw [PolySpec.leNat_bytesAt16, PolySpec.clamp_words _ _ _ _ (read32 _ _).isLt (read32 _ _).isLt (read32 _ _).isLt]
  simp only [PolyInit.initW, PolyInit.ICtx.kw, slot, BitVec.toNat_and, Nat.reduceMul, BitVec.add_zero,
    show (0x0fffffff#32).toNat = 268435455 from rfl, show (0x0ffffffc#32).toNat = 268435452 from rfl]

theorem init_pad (c : PolyInit.ICtx) (t : State) (ht : PolyInit.IResult c t) :
    padAt t.mem c.ctx = leNat (Ctx.bytesAt c.m0 (c.key + 16#32) 16) := by
  unfold padAt wordAt slot
  rw [ht.ctx 12 (by decide), ht.ctx 13 (by decide), ht.ctx 14 (by decide), ht.ctx 15 (by decide), PolySpec.leNat_bytesAt16]
  simp only [PolyInit.initW, PolyInit.ICtx.kw, slot]
  rw [show c.key + 16#32 + 4#32 = c.key + 20#32 by bv_omega,
    show c.key + 16#32 + 8#32 = c.key + 24#32 by bv_omega,
    show c.key + 16#32 + 12#32 = c.key + 28#32 by bv_omega]

/-- All key and pad words survive every blocks call, including count zero. -/
theorem blocks_words (c : PolyBlocks.BCtx) (hv : PolyBlocks.BValid c) (s t : State)
    (he : PolyBlocks.BEntry c s) (hlr : (c.regs0 14).getLsbD 0 = true) (ht : PolyBlocks.BResult c s t)
    (j : Nat) (hlo : 5 ≤ j) (hhi : j < 16) :
    wordAt t.mem c.ctx j = wordAt c.m0 c.ctx j := by
  unfold wordAt
  congr 1
  apply read32_congr
  intro k hk
  rw [slot, M0Crypto.Thumb.ofNat_add_assoc]
  exact PolyBlocks.result_key_preserved c hv s t he hlr ht (4*j+k) (by omega) (by omega)

theorem blocks_keyOK (c : PolyBlocks.BCtx) (hv : PolyBlocks.BValid c) (s t : State)
    (he : PolyBlocks.BEntry c s) (hlr : (c.regs0 14).getLsbD 0 = true) (ht : PolyBlocks.BResult c s t)
    (hk : keyAtOK c.m0 c.ctx) : keyAtOK t.mem c.ctx := by
  unfold keyAtOK
  rw [blocks_words c hv s t he hlr ht 5 (by decide) (by decide),
    blocks_words c hv s t he hlr ht 6 (by decide) (by decide), blocks_words c hv s t he hlr ht 7 (by decide) (by decide),
    blocks_words c hv s t he hlr ht 8 (by decide) (by decide), blocks_words c hv s t he hlr ht 9 (by decide) (by decide),
    blocks_words c hv s t he hlr ht 10 (by decide) (by decide), blocks_words c hv s t he hlr ht 11 (by decide) (by decide)]
  exact hk

theorem blocks_pad (c : PolyBlocks.BCtx) (hv : PolyBlocks.BValid c) (s t : State)
    (he : PolyBlocks.BEntry c s) (hlr : (c.regs0 14).getLsbD 0 = true) (ht : PolyBlocks.BResult c s t) :
    padAt t.mem c.ctx = padAt c.m0 c.ctx := by
  unfold padAt
  rw [blocks_words c hv s t he hlr ht 12 (by decide) (by decide), blocks_words c hv s t he hlr ht 13 (by decide) (by decide),
    blocks_words c hv s t he hlr ht 14 (by decide) (by decide), blocks_words c hv s t he hlr ht 15 (by decide) (by decide)]

/-- The lazy block bound is sufficient for the single conditional subtraction in finish. -/
theorem finish_bound (h : Nat) (hh : h < 5*2^128) : h < 2*p := by
  rw [PolyArith.p_eq]; omega
/-- Finish reads the same accumulator and pad as the blocks/context views. -/
theorem finish_acc (c : PolyFinish.FCtx) : c.acc = accAt c.m0 c.ctx := rfl
theorem finish_pad (c : PolyFinish.FCtx) : c.padVal = padAt c.m0 c.ctx := rfl

/-- The 32 key bytes split into the r half and the pad half. -/
theorem key_split (m : Mem) (k : Word) :
    (Ctx.bytesAt m k 32).take 16 = Ctx.bytesAt m k 16 ∧
    ((Ctx.bytesAt m k 32).drop 16).take 16 = Ctx.bytesAt m (k + 16#32) 16 := by
  have e := PolySpec.bytesAt_add m k 16 16
  have l := Frame.bytesAt_length m k 16
  have l2 := Frame.bytesAt_length m (k + BitVec.ofNat 32 16) 16
  rw [show (16 : Nat) + 16 = 32 from rfl] at e
  rw [e]
  refine ⟨List.take_left' l, ?_⟩
  rw [List.drop_left' l, List.take_of_length_le (by omega)]

/-- **Poly1305 chain.** Let `init` run from the 32 key bytes, giving memory `ti.mem`. Suppose a
later context memory `mf` keeps the pad (`blocks_pad`) and has an accumulator that refines
`polyBlocks` with pad 1 and the post-init key over the whole-block message `msg`
(`blocks_correct` per call, preserving the key by `blocks_words` and composing by
`PolySpec.polyBlocks_append`). Then the value `finish` publishes from `mf`
(`finish_correct`, read through `finish_acc` / `finish_pad`) is exactly RFC 8439 `poly1305` of
the key bytes and `msg`. This is a value-level chain; a single machine run of the whole sequence
is the AEAD's obligation. -/
theorem poly1305_chain (c : PolyInit.ICtx) (ti : State) (hi : PolyInit.IResult c ti)
    (mf : Mem) (msg : List Byte) (hm : msg.length % 16 = 0)
    (hpad : padAt mf c.ctx = padAt ti.mem c.ctx)
    (hacc : accAt mf c.ctx % p = PolySpec.polyBlocks (keyAt ti.mem c.ctx) 1 (accAt ti.mem c.ctx % p) msg) :
    leBytes 16 (accAt mf c.ctx % p + padAt mf c.ctx) =
      M0Crypto.Spec.AEAD.poly1305 (Ctx.bytesAt c.m0 c.key 32) msg := by
  obtain ⟨k1, k2⟩ := key_split c.m0 c.key
  rw [PolySpec.poly1305_eq, PolySpec.polyAcc_eq _ _ hm, hacc, hpad, init_acc c ti hi,
    init_key c ti hi, init_pad c ti hi, k1, k2]
  rfl
end M0Crypto.Release.PolyContext
