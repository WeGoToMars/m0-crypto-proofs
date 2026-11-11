import M0Crypto.Release.ConstantTime.WriteBounds
import M0Crypto.Release.ChaCha20Output

/-! Output-site facts derived from the functional block invariants. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.ChaCha20Output
open M0Crypto.Release.ChaCha20Layout

/-- Every write in an aligned output chunk is in the output buffer, using the
same register and length facts as the functional chunk proof. -/
theorem chacha20_chunk_writes_output (c : Ctx) (hv : Valid c) (k i : Nat)
    (t : State) (hi : i < 16)
    (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (hbound : 64 * k + 4 * i + 4 ≤ c.len.toNat)
    (e : Event) (he : e ∈ traceAll (ach i) t) (y : Word) (hy : Writes e.accesses y) :
    c.oidx y < c.len.toNat := by
  obtain ⟨q, hq, hy⟩ := ach_writes t i hi e he y hy
  rw [hy, h3, ofNat_add_assoc, ofNat_add_assoc]
  rw [oidx_out c hv _ (by omega)]
  omega

/-- The byte-tail block writes only its current output byte. -/
theorem chacha20_tail_writes_output (c : Ctx) (hv : Valid c) (k : Nat)
    (t : State) (h3 : t.regs 3 = c.out + BitVec.ofNat 32 (64 * k))
    (hbound : 64 * k + (t.regs 0).toNat < c.len.toNat)
    (e : Event) (he : e ∈ traceAll bl t) (y : Word) (hy : Writes e.accesses y) :
    c.oidx y < c.len.toNat := by
  rw [bl_writes t e he y hy, h3]
  have hr : BitVec.ofNat 32 (t.regs 0).toNat = t.regs 0 := by simp
  rw [← hr]
  simp only [ofNat_add_assoc]
  rw [oidx_out c hv _ hbound]
  exact hbound

end M0Crypto.Release.ConstantTime
