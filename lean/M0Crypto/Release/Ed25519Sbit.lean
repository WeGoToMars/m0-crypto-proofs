import M0Crypto.Release.Ed25519Leaf
import M0Crypto.Release.Ed25519Bytes
import M0Crypto.Release.BlockEffect

/-!
# `m0c_sbit`

`push {lr}`, then `r0 = (byte (i >> 3) of the scalar at r0 >> (i & 7)) & 1` for `i = r1 < 256`,
`pop {pc}`: bit `i` of the scalar (`Ed25519Bytes.decodeInt_bit`). It reads the one byte it
needs and writes nothing. Its public values are the scalar's address and `i`.
-/

namespace M0Crypto.Release.Ed25519Sbit

open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.BlockEffect
open M0Crypto.Release.Ed25519Leaf
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519Bytes (decodeInt_bit)
open M0Crypto.Sym (SExpr SMem)
open M0Crypto.Artifacts

/-- `lsrs r2, r1, #3; ldrb r2, [r0, r2]; movs r3, #7; ands r1, r3; lsrs r2, r1; movs r0, #1;
ands r0, r2`. -/
def body : List Instr :=
  [.lsrImm 2 1 3, .memReg .ldrb 2 0 2, .movImm 3 7, .dp .ands 1 3, .dp .lsrs 2 1, .movImm 0 1, .dp .ands 0 2]

/-- The byte `i / 8` of the scalar. -/
def byteA : SExpr := .add (.reg0 0) (.lsr (.reg0 1) 3)
def rd : List (SExpr × Nat) := [(byteA, 1)]

theorem bytesAt_getD (m : Mem) (a : Word) {n j : Nat} (hj : j < n) :
    (bytesAt m a n).getD j 0 = m (a + BitVec.ofNat 32 j) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hj]

/-- **`m0c_sbit`**: `r0` is bit `r1 < 256` of the 32-byte scalar at `r0`. -/
def sbitR : Routine := leafR Ed25519Compact.sbit body [] rd (fun s => (s.regs 1).toNat < 256)
  (fun s _ r => r.toNat = decodeInt (bytesAt s.mem (s.regs 0) 32) / 2 ^ (s.regs 1).toNat % 2)

/-- Its effect: it reads the byte. -/
abbrev sbitE : Word → (Nat → Word) → TrP := leafE Ed25519Compact.sbit [0, 1] rd [] rd

theorem sbit_ok : leafOk body [0, 1] rd [] rd rd [] rd = true := by decide +kernel

/-- `r0 = (byte >> (i & 7)) & 1`. -/
def eB : Eff := { regs := [(0, .and (.const 1#32) (.lsrR (.ld8 .mem0 byteA) (.and (.reg0 1) (.const 7#32))
  (.lsrC (.reg0 1) 3)))], clob := [1, 2, 3] }

theorem eB_ok : effOk body eB = true := by decide +kernel

theorem bit_val (b : BitVec 8) (x : Word) (c : Bool) :
    (1#32 &&& (Thumb.lsrRegC (b.setWidth 32) ((x &&& 7#32).toNat % 256) c).1).toNat =
      b.toNat / 2 ^ (x.toNat % 8) % 2 := by
  have h7 : (x &&& 7#32).toNat = x.toNat % 8 := by
    rw [BitVec.toNat_and, show (7#32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hs : (Thumb.lsrRegC (b.setWidth 32) ((x &&& 7#32).toNat % 256) c).1 = b.setWidth 32 >>> (x.toNat % 8) := by
    rw [h7, Nat.mod_eq_of_lt (by omega)]
    unfold Thumb.lsrRegC Thumb.lsrC
    split <;> simp_all
  rw [hs, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, show (1#32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.pow_one]

/-- `m0c_sbit`'s call lemma with its effect, in each build. -/
noncomputable def sbit_te (b : Build) : letI := b.codeBytes; sbitR.TE (leafPub [0, 1]) sbitE :=
  letI := b.codeBytes
  leaf_te sbit_ok (by cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide)
    (fun _ _ _ hr => by rw [List.mem_singleton.mp hr]; exact Nat.mod_one _) fun s t hi _ tr hm => by
      have h0 := tr 0 (by decide) (by decide)
      have h1 := tr 1 (by decide) (by decide)
      have hb : t.mem (s.regs 0 + s.regs 1 >>> 3) = s.mem (s.regs 0 + s.regs 1 >>> 3) :=
        hm _ ⟨_, List.mem_singleton_self _, 0, Nat.one_pos, by simp [byteA, SExpr.denote]⟩
      have ha : s.regs 1 >>> 3 = BitVec.ofNat 32 ((s.regs 1).toNat / 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
        omega
      rw [ha] at hb
      rw [(eff_run eB_ok t).reg 0 (by decide) (by decide)]
      simp only [eB, Eff.reg, List.find?, decide_true, Option.map_some, Option.getD_some, SExpr.denote,
        SMem.denote, byteA, read8, h0, h1, hb, bit_val, decodeInt_bit, ha,
        bytesAt_getD s.mem (s.regs 0) (n := 32) (by omega : (s.regs 1).toNat / 8 < 32)]

end M0Crypto.Release.Ed25519Sbit
