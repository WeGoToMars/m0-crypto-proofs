import M0Crypto.Release.FrameBase
import M0Crypto.Release.ChaCha20Spec
import M0Crypto.Release.ChaCha20Layout
import M0Crypto.Release.ChaCha20Contract

set_option linter.unusedSimpArgs false

/-!
Memory bookkeeping for the whole-function proof of `m0c_chacha20_xor`.

`Ctx` fixes one call: code base, entry SP, the arguments and the entry memory and
registers. The frame after the prologue is `fp = sp0 - 176`: word slots 0..34 are
the function's frame (`X`, `J`, `LEN`, `OUTP`, `INP`), 35..43 the saved registers,
44..45 the stack arguments.
-/

namespace M0Crypto.Release.Frame

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Spec.ChaCha20 (Byte initState)
open M0Crypto.Spec.Aead (chacha20)
open M0Crypto.Release.ChaCha20Layout (chStackBytes chFrameBytes chFrameWords slotJ slotLen slotOutp slotInp)

/-! ## The call -/

namespace Ctx

variable (c : Ctx)

/-- Input state of block `k`, as a word function (0 beyond 16). -/
def J (k : Nat) (i : Nat) : Word :=
  if i < 16 then (initState c.keyB (c.ctr + BitVec.ofNat 32 k) c.nonceB)[i]! else 0

/-- Memory after the prologue: r4-r7, LR at `sp0 - 20`, r8-r11 at `sp0 - 36`. -/
def mP : Mem :=
  storeWords (storeWords c.m0 (c.sp0 - BitVec.ofNat 32 20)
    [c.regs0 4, c.regs0 5, c.regs0 6, c.regs0 7, c.regs0 14])
    (c.sp0 - BitVec.ofNat 32 20 - BitVec.ofNat 32 16) [c.regs0 8, c.regs0 9, c.regs0 10, c.regs0 11]

/-- Frame word `i`. -/
def fw (s : State) (i : Nat) : Word := read32 s.mem (slot c.fp i)

/-- `y` lies outside the 140-byte frame. -/
def OutF (y : Word) : Prop := ∀ o < chFrameBytes, y ≠ c.fp + BitVec.ofNat 32 o

/-- Memory outside the frame: the first `P` output bytes are final, the rest is `mP`. -/
def MemOk (P : Nat) (m : Mem) : Prop :=
  ∀ y, c.OutF y → m y = if c.oidx y < P then c.outB (c.oidx y) else c.mP y

/-- Writes allowed to the function: its 176 stack bytes and the output buffer. -/
def Wr (y : Word) : Prop := (∃ o < chStackBytes, y = c.fp + BitVec.ofNat 32 o) ∨ c.oidx y < c.len.toNat

end Ctx

namespace Ctx
variable (c : Ctx)

theorem memOk_write_slot {P : Nat} {m : Mem} (h : c.MemOk P m) (k : Nat) (hk : k < chFrameWords) (v : Word) :
    c.MemOk P (write32 m (slot c.fp k) v) := by
  intro y hy
  have hb : chFrameBytes = 4 * chFrameWords := rfl
  rw [M0Crypto.Armv6M.write32_other]
  · exact h y hy
  · intro q hq e; exact hy (4 * k + q) (by omega) (by rw [e]; simp only [slot]; rw [ofNat_add_assoc])

theorem fw_write {s : State} {m : Mem} (hm : s.mem = write32 m (slot c.fp k) v) (j : Nat)
    (hk : k < 2 ^ 28) (hj : j < 2 ^ 28) :
    c.fw s j = if k = j then v else read32 m (slot c.fp j) := by
  simp only [fw, hm]; exact read32_write32_slot' m c.fp v k j hk hj

end Ctx

/-! ## The input state words -/

/-- Little-endian word `i` of `n` words of memory from `a`. -/
theorem wordsOfBytes_bytesAt (m : Mem) : ∀ (n : Nat) (a : Word) (i : Nat), i < n →
    (M0Crypto.Spec.ChaCha20.wordsOfBytes (Ctx.bytesAt m a (4 * n)))[i]? =
      some (M0Crypto.Spec.ChaCha20.wordOfBytes (m (a + BitVec.ofNat 32 (4 * i)))
        (m (a + BitVec.ofNat 32 (4 * i + 1))) (m (a + BitVec.ofNat 32 (4 * i + 2)))
        (m (a + BitVec.ofNat 32 (4 * i + 3))))
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega]
    simp only [bytesAt_succ, M0Crypto.Spec.ChaCha20.wordsOfBytes]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.mul_zero, Nat.zero_add, BitVec.add_zero,
        BitVec.add_assoc, Option.some.injEq]
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ]
      rw [wordsOfBytes_bytesAt m n _ i (by omega)]
      have e4 : a + 1#32 + 1#32 + 1#32 + 1#32 = a + BitVec.ofNat 32 4 := by bv_omega
      rw [e4, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc,
        show 4 + 4 * i = 4 * (i + 1) by omega, show 4 + (4 * i + 1) = 4 * (i + 1) + 1 by omega,
        show 4 + (4 * i + 2) = 4 * (i + 1) + 2 by omega, show 4 + (4 * i + 3) = 4 * (i + 1) + 3 by omega]

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length initState constants) in
theorem J_list (c : Ctx) (k i : Nat) (hi : i < 16) :
    c.J k i = ((constants ++ wordsOfBytes c.keyB ++ [c.ctr + BitVec.ofNat 32 k] ++ wordsOfBytes c.nonceB)[i]?).getD 0 := by
  simp [Ctx.J, initState, hi]; rfl

/-- Key word `i` of the input state. -/
def keyW (c : Ctx) (i : Nat) : Word :=
  M0Crypto.Spec.ChaCha20.wordOfBytes (c.m0 (c.key + BitVec.ofNat 32 (4 * i)))
    (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 1))) (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 2)))
    (c.m0 (c.key + BitVec.ofNat 32 (4 * i + 3)))

def nonceW (c : Ctx) (i : Nat) : Word :=
  M0Crypto.Spec.ChaCha20.wordOfBytes (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i)))
    (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 1))) (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 2)))
    (c.m0 (c.nonce + BitVec.ofNat 32 (4 * i + 3)))

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_key (c : Ctx) (k i : Nat) (hi : i < 8) : c.J k (4 + i) = keyW c i := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  rw [J_list c k _ (by omega), Nat.add_comm, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp [constants]), List.getElem?_append_left (by simp [constants, hl]; omega)]
  simp only [constants, List.length_cons, List.length_nil, Nat.add_sub_cancel]
  have := wordsOfBytes_bytesAt c.m0 8 c.key i hi
  simp only [Nat.reduceMul] at this
  rw [Ctx.keyB, this]; rfl

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_nonce (c : Ctx) (k i : Nat) (hi : i < 3) : c.J k (13 + i) = nonceW c i := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  have hn : (wordsOfBytes c.nonceB).length = 3 := by simp [wordsOfBytes_length, Ctx.nonceB, bytesAt_length]
  rw [J_list c k _ (by omega), List.getElem?_append_right (by simp [constants, hl])]
  simp only [constants, List.length_append, List.length_cons, List.length_nil, hl]
  have := wordsOfBytes_bytesAt c.m0 3 c.nonce i hi
  simp only [Nat.reduceMul] at this
  rw [show 13 + i - (0 + 1 + 1 + 1 + 1 + 8 + (0 + 1)) = i by omega, Ctx.nonceB, this]; rfl

open M0Crypto.Spec.ChaCha20 (wordsOfBytes wordsOfBytes_length constants) in
theorem J_ctr (c : Ctx) (k : Nat) : c.J k 12 = c.ctr + BitVec.ofNat 32 k := by
  have hl : (wordsOfBytes c.keyB).length = 8 := by simp [wordsOfBytes_length, Ctx.keyB, bytesAt_length]
  rw [J_list c k _ (by omega), List.getElem?_append_left (by simp [constants, hl]),
    List.getElem?_append_right (by simp [constants, hl])]
  simp [constants, hl]

theorem J_const (c : Ctx) (k : Nat) :
    c.J k 0 = 0x61707865#32 ∧ c.J k 1 = 0x3320646e#32 ∧ c.J k 2 = 0x79622d32#32 ∧ c.J k 3 = 0x6b206574#32 := by
  simp [J_list, M0Crypto.Spec.ChaCha20.constants]

/-! ## Preconditions -/

/-- State at `.Lblock` (offset `bpreOff`) before block `k`. -/
structure BlockInv (c : Ctx) (k : Nat) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 M0Crypto.Release.ChaCha20Layout.bpreOff
  sp : t.regs 13 = c.fp
  j : ∀ i < 16, c.fw t (slotJ + i) = c.J k i
  len : c.fw t slotLen = c.len - BitVec.ofNat 32 (64 * k)
  outp : c.fw t slotOutp = c.out + BitVec.ofNat 32 (64 * k)
  inp : c.fw t slotInp = c.inp + BitVec.ofNat 32 (64 * k)
  mem : c.MemOk (64 * k) t.mem
  lt : 64 * k < c.len.toNat
  ok : M0Crypto.Spec.Aead.counterOk c.ctr.toNat c.len.toNat = true

end M0Crypto.Release.Frame
