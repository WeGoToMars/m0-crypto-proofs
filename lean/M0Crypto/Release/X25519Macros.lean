import M0Crypto.Release.Field25519Macros
import M0Crypto.Thumb.ReleaseCheck.X25519Cases

/-!
The X25519 field routines in the X25519 artifact. `m0c_fe_mulc_add` as an instruction list
built from the generator's macros, as in `bench/x25519/gen_x25519.py`; the lists of `m0c_fe_mul`
and `m0c_fe_sqr` are in `Field25519Macros`.

`feMul_at`, `feSqr_at`, `feMulcAdd_at` check that each routine's bytes at its symbol decode to
the list, and `*_size` that the list covers the whole routine (for `m0c_fe_mulc_add`, all but
the final literal word). So every macro lemma proved over these lists applies to the
artifact, at the offsets these lists give.
-/

namespace M0Crypto.Release.X25519Macros
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feSqr feMulSize feSqrSize feMulcAdd feMulcAddSize)
open M0Crypto.Thumb
open M0Crypto.Release (B)
open M0Crypto.Armv6M (Reg LowReg)
open M0Crypto.Release.Field25519Mul (absdiff sqr32 sqr64 mul64)
open M0Crypto.Release.Field25519Macros (feMulList feSqrList)

/-- One `word` of `m0c_fe_mulc_add`: `121666 * a[i] + b[i] (+ k)`, low word in `t`, high in
`a`. -/
def mulcWord (i : Nat) (k : Option LowReg) (a t u : LowReg) : List Instr :=
  [.memImm .ldr a 1 (BitVec.ofNat 5 i), .uxth t a, .lsrImm a a 16, .dp .muls t 7, .dp .muls a 7,
   .lslImm u a 17, .lsrImm a a 15, .addReg t t t, .dp .adcs a 6, .addReg t t u, .dp .adcs a 6,
   .memImm .ldr u 2 (BitVec.ofNat 5 i), .addReg t t u, .dp .adcs a 6] ++
  (match k with | some k => [.addReg t t k, .dp .adcs a 6] | none => [])

/-- Word `i < 7` of the chain, then the store through `r12`. -/
def mulcStep (i : Nat) (k a : LowReg) : List Instr :=
  mulcWord i (some k) a 4 5 ++ [.movHi 5 12, .memImm .str 4 5 (BitVec.ofNat 5 i)]

/-- `m0c_fe_mulc_add`; `lit` is the literal-pool index of `60833`. -/
def feMulcAddList (lit : BitVec 8) : List Instr :=
  [.push 0 true, .movHi 12 0, .ldrLit 7 lit, .movImm 6 0] ++ mulcWord 7 none 3 4 5 ++
  [.lslImm 3 3 1, .lsrImm 5 4 31, .addReg 3 3 5, .lslImm 4 4 1, .lsrImm 4 4 1, .movHi 8 4,
   .movImm 5 19, .dp .muls 3 5] ++
  mulcStep 0 3 0 ++ mulcStep 1 0 3 ++ mulcStep 2 3 0 ++ mulcStep 3 0 3 ++ mulcStep 4 3 0 ++
  mulcStep 5 0 3 ++ mulcStep 6 3 0 ++
  [.movHi 1 8, .addReg 1 1 0, .movHi 0 12, .memImm .str 1 0 7, .pop 0 true]

/-- Literal-pool index of `ldr r7, =60833`: the pool is the routine's last word, and the
load is the third instruction (offset 4). -/
def mulcLit : Nat := (feMulcAdd + feMulcAddSize - 4 - (feMulcAdd + 4 + 4) / 4 * 4) / 4

def feMulcAddList' : List Instr := feMulcAddList (BitVec.ofNat 8 mulcLit)

theorem feMul_at : seqAt B feMul feMulList = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem feSqr_at : seqAt B feSqr feSqrList = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem feMulcAdd_at : seqAt B feMulcAdd feMulcAddList' = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem feMul_size : seqSize feMulList = feMulSize := by decide +kernel

theorem feSqr_size : seqSize feSqrList = feSqrSize := by decide +kernel

theorem feMulcAdd_size : seqSize feMulcAddList' + 4 = feMulcAddSize := by decide +kernel

/-- The first `mul64` of `m0c_fe_mul`, after the routine's entry (save, frame, operand
loads). -/
theorem mul64_at_fe_mul :
    seqAt B feMul ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .strSp 2 0x23,
      .movHi 12 1, .movHi 11 2, .ldm 1 0x50, .ldm 2 0xa0] ++ mul64 4 6 5 7 0 1 2 3 8 10) = true := by
  rw [seqAt_eq_scan]; decide +kernel

/-- The first `sqr32` of `m0c_fe_sqr`, after the routine's entry and the absolute difference
that opens `sqr64`. -/
theorem sqr32_at_fe_sqr :
    seqAt B feSqr ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .movHi 12 1,
      .ldm 1 0x50] ++ absdiff 0 6 4 1 ++ sqr32 0 1 2 3) = true := by
  rw [seqAt_eq_scan]; decide +kernel

/-- The first `sqr64` of `m0c_fe_sqr`, after the routine's entry (save, frame, operand
load). -/
theorem sqr64_at_fe_sqr :
    seqAt B feSqr ([.push 0 true, .subSp 0x24, .strSp 0 0x21, .strSp 1 0x22, .movHi 12 1,
      .ldm 1 0x50] ++ sqr64 4 6 5 7 0 1 2 3) = true := by
  rw [seqAt_eq_scan]; decide +kernel

end M0Crypto.Release.X25519Macros
