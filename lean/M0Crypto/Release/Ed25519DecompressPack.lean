import M0Crypto.Release.Ed25519DecompressGood

/-!
# `m0c_ge_decompress`'s adapter

`decAd b Rs` is `ge_decompress`'s adapter at verify's stitched sites in build `b`, and `decZ b Rs`
its status: `r0 = 0` exactly when the 32 input bytes decode, and then `out` holds the decoded
point (`decCo`, `csemX`). Its trace is the frame's around `ΨX`, a function of the public registers
and the input bytes (`xpX`). The effect holds at every public value. When the status bits of the
input bytes pass (`okpX`), it also writes `out`.
-/

namespace M0Crypto.Release.Ed25519DecompressPack

open M0Crypto.Armv6M (Word State)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DecompressProg (dec_status decTests)
open M0Crypto.Release.Ed25519DecompressStitch
open M0Crypto.Release.Ed25519DecompressW
open M0Crypto.Release.Ed25519DecompressGood (dq_ok code_okW dec_eff dec_effCo ψX_uniq ψX_ex)
open M0Crypto.Release.Ed25519VerifyProg (vxS decCo)
open M0Crypto.Release.Ed25519 (Build)

/-- The status from the input bytes among the public values. -/
def okpX (p : Nat → Word) : Bool := okB (b0 (inP p)) (b1 (inP p)) (b2 (inP p)) (bz (inP p)) (bs (inP p))

/-- **The tests pass exactly when the bytes decode.** -/
theorem okB_dec {l : List (BitVec 8)} (hl : l.length = 32) :
    okB (b0 l) (b1 l) (b2 l) (bz l) (bs l) = (Spec.Ed25519.decodePoint l).isSome := by
  rw [okB_spec]
  have h := dec_status hl (r := if decTests (yL l) (sL l) then 0#32 else 1#32) rfl
  cases e : decTests (yL l) (sL l) <;> simp [e] at h <;> simp [h]

/-- **`ge_decompress`'s call lemma** in build `b`: the frame's trace around `ΨX`. -/
noncomputable def decTE (b : Build) (Rs : Rels) :=
  letI := b.codeBytes
  CalleeP.teW (cb := b.codeBytes) (Rs := Rs) (q := dq) (bsz := bszX) (Post := PostX Rs) (xpre := xpreX)
    (pub := pubX) (Ψ := ΨX Rs b) (E := fun base p tr => dq.trW bszX base p (ΨX Rs b base p) tr)
    dq_ok (code_okW b) (fun _ _ _ h => CalleeP.reg_pubX h)
    (fun base s _ t g F hcR hat hrd => dec_body b rfl base s t g F hcR hat hrd)
    (ψX_uniq Rs b) (ψX_ex Rs b) fun _ _ _ h => h

theorem xpvX_b (l : List (BitVec 8)) : xpvX [.b l] = Ed25519WnafAd.wordsOf l 8 := rfl

/-- **`ge_decompress`'s adapter** in build `b`: no premise on the input bytes, no outputs but the
status. -/
noncomputable def decAd (b : Build) (Rs : Rels) : AdX Rs (cb := b.codeBytes) (vxS .dec) :=
  AdX.ofTE (dq.RW (PostX Rs) xpreX) rfl rfl rfl xpX xpvX
    (fun _ _ st vs hi => by rw [dec_in hi, xpvX_b, xpX, Ed25519WnafAd.wordsAt_eq])
    (decTE b Rs) (fun _ => True) (fun base p tr _ h => dec_eff Rs b base p h) (fun _ => True) (fun _ => [])
    (fun _ _ _ _ _ hg _ _ _ => ⟨⟨hg, fun _ hp => absurd hp List.not_mem_nil⟩, trivial⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, vxS, calleeAt, Ed25519VerifyProg.ioDecZ])
    (fun _ _ _ _ _ _ _ _ => trivial)

/-- **`ge_decompress`'s status**: `r0 = 0` exactly when the input bytes decode; then `out` holds the
decoded point. -/
noncomputable def decZ (b : Build) (Rs : Rels) : ZSt Rs (cb := b.codeBytes) (decAd b Rs) :=
  letI := b.codeBytes
  { ok := okX
    okr := fun c sp _ _ _ vs _ hi _ hp => (hp c sp vs hi).1
    co := decCo
    csem := csemX
    cpost := fun c sp _ _ _ vs _ hi _ hp hok => (hp c sp vs hi).2 hok
    okp := okpX
    okp_of := fun _ _ st vs _ _ hi _ => by
      show okpX (pubX 0 st) = okX vs
      rw [okpX, pub_in, okB_dec (bytesAt_length _ _ _), dec_in hi, okX_b]
    cef := fun base p _ hp => dec_effCo Rs b base p hp ((decTE b Rs).eff base p) }

end M0Crypto.Release.Ed25519DecompressPack
