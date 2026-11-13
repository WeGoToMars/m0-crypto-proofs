import M0Crypto.Release.X25519Sqr64

/-!
The three field routines of the X25519 release as instruction lists built from the
generator's macros (plan `x25519-proofs.md`, phase 8). Every macro is a function of its
registers and frame slots, as in `bench/x25519/gen_x25519.py`; `mul64`, `sqr32` and `absdiff`
come from `X25519Mul`/`X25519Mul64`/`X25519Sqr64`.

`feMul_at`, `feSqr_at`, `feMulcAdd_at` check that each routine's bytes at its symbol decode to
the list, and `*_size` that the list covers the whole routine (for `m0c_fe_mulc_add`, all but
the final literal word). So every macro lemma proved over these lists applies to the
artifact, at the offsets these lists give. Slots are the generator's frame offsets divided
by four.
-/

namespace M0Crypto.Release.X25519Macros
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feSqr feMulSize feSqrSize feMulcAdd feMulcAddSize)
open M0Crypto.Thumb
open M0Crypto.Release (B)
open M0Crypto.Armv6M (Reg LowReg)
open M0Crypto.Release.X25519Mul (absdiff sqr32 mul64 sqr64)

/-- Frame slots (word index from `sp`): the generator's `OP, OH, OPP, ODA, ODB, ON, ODST, OA,
OB` divided by four. -/
def SP_ := 0
def SH := 8
def SPP := 16
def SDA := 24
def SDB := 28
def SN := 32
def SDST := 33
def SA := 34
def SB := 35
/-- `FRAME / 4`. -/
def SFRAME := 36

abbrev sl (k : Nat) : BitVec 8 := BitVec.ofNat 8 k

/-- `combine128` of a product (`square = False`); `k` is the slot of `o`. -/
def combine128 (k : Nat) (direct : Bool) : List Instr :=
  [.dp .eors 0 4, .dp .eors 1 4, .dp .eors 2 4, .dp .eors 3 4, .addRdSp 7 (sl k), .lsrImm 5 4 1,
   .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5,
   .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5, .subImm8 7 24,
   .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6,
   .ldm 7 0x60, .dp .adcs 4 5, .movImm 5 0, .dp .adcs 5 6,
   .subImm8 7 (if direct then 16 else 24), .stm 7 (if direct then 0x3c else 0x3f)]

/-- `combine128` of a square (`square = True`). -/
def combine128sq (k : Nat) (direct : Bool) : List Instr :=
  [.dp .mvns 0 0, .dp .mvns 1 1, .dp .mvns 2 2, .dp .mvns 3 3, .addRdSp 7 (sl k), .dp .cmp 0 0,
   .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6,
   .movHi 5 8, .movHi 6 10, .dp .adcs 2 5, .dp .adcs 3 6, .dp .sbcs 4 4,
   .movHi 5 11, .movHi 6 12,
   .addReg 0 0 5, .dp .adcs 1 6,
   .addRdSp 7 (sl (k + 6)),
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5, .subImm8 7 24,
   .movHi 5 8, .movHi 6 10, .addRdSp 7 (sl (k + 6)), .addReg 0 0 5, .dp .adcs 1 6,
   .movHi 5 11, .movHi 6 12,
   .dp .adcs 2 5, .dp .adcs 3 6,
   .ldm 7 0x60, .dp .adcs 4 5, .movImm 5 0, .dp .adcs 5 6,
   .subImm8 7 (if direct then 16 else 24), .stm 7 (if direct then 0x3c else 0x3f)]

def mul128 (k : Nat) (direct : Bool) : List Instr :=
  [.movHi 12 1, .movHi 11 2, .ldm 1 0x50, .ldm 2 0xa0] ++ mul64 4 6 5 7 0 1 2 3 8 10 ++
  [.addRdSp 0 (sl k), .stm 0 0xf0, .movHi 0 12, .memImm .ldr 4 0 2, .memImm .ldr 6 0 3,
   .movHi 1 11, .memImm .ldr 5 1 2, .memImm .ldr 7 1 3] ++ mul64 4 6 5 7 0 1 2 3 8 10 ++
  [.addRdSp 0 (sl (k + 4)), .stm 0 0xf0,
   .movHi 7 12, .ldm 7 0x65, .subReg 0 0 5, .dp .sbcs 2 6, .dp .sbcs 5 5,
   .dp .eors 0 5, .dp .eors 2 5, .subReg 0 0 5, .dp .sbcs 2 5,
   .movHi 4 11, .ldm 4 0x5a, .subReg 1 1 4, .dp .sbcs 3 6, .dp .sbcs 6 6,
   .dp .eors 1 6, .dp .eors 3 6, .subReg 1 1 6, .dp .sbcs 3 6,
   .dp .eors 6 5, .dp .mvns 6 6, .movHi 12 6] ++ mul64 0 2 1 3 4 5 6 7 8 10 ++
  [.movHi 4 12] ++ combine128 k direct

def sqr128 (k : Nat) (direct : Bool) : List Instr :=
  [.movHi 12 1, .ldm 1 0x50] ++ sqr64 4 6 5 7 0 1 2 3 ++
  [.addRdSp 0 (sl k), .stm 0 0x30, .movHi 8 6, .movHi 10 7, .movHi 1 12,
   .memImm .ldr 4 1 2, .memImm .ldr 6 1 3] ++ sqr64 4 6 5 7 0 1 2 3 ++
  [.addRdSp 0 (sl (k + 6)), .stm 0 0xc0, .movHi 7 12, .movHi 11 4, .movHi 12 5, .ldm 7 0x65,
   .subReg 0 0 5, .dp .sbcs 2 6, .dp .sbcs 5 5,
   .dp .eors 0 5, .dp .eors 2 5, .subReg 0 0 5, .dp .sbcs 2 5] ++
  sqr64 0 2 1 3 4 5 6 7 ++ combine128sq k direct

/-- `|X0 - X1|` for the 8 words at the pointer in slot `p`, to slot `o`; mask in `r0`. -/
def diff256 (p o : Nat) : List Instr :=
  [.ldrSp 0 (sl p), .ldm 0 0xf0, .ldm 0 0x0f,
   .subReg 4 4 0, .dp .sbcs 5 1, .dp .sbcs 6 2, .dp .sbcs 7 3, .dp .sbcs 0 0,
   .dp .eors 4 0, .dp .eors 5 0, .dp .eors 6 0, .dp .eors 7 0,
   .subReg 4 4 0, .dp .sbcs 5 0, .dp .sbcs 6 0, .dp .sbcs 7 0,
   .addRdSp 1 (sl o), .stm 1 0xf0]

/-- `xor_n`: complement (square) or xor with `n` from slot `SN`, loaded into `nr`. -/
def xorN (sq : Bool) (nr : LowReg) : List Instr :=
  if sq then [.dp .mvns 0 0, .dp .mvns 1 1, .dp .mvns 2 2, .dp .mvns 3 3]
  else [.ldrSp nr (sl SN), .dp .eors 0 nr, .dp .eors 1 nr, .dp .eors 2 nr, .dp .eors 3 nr]

def reducePhaseA (sq : Bool) : List Instr :=
  [.movHi 3 1, .movHi 2 0, .addRdSp 7 (sl SPP), .ldm 7 0x03] ++ xorN sq 4 ++
  [if sq then .dp .cmp 0 0 else .lsrImm 4 4 1, .addRdSp 7 (sl SP_),
   .ldm 7 0x60, .dp .adcs 0 5, .dp .adcs 1 6, .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6,
   .movImm 4 0, .dp .adcs 4 4,
   .addRdSp 7 (sl SH), .ldm 7 0x60, .addReg 0 0 5, .dp .adcs 1 6,
   .ldm 7 0x60, .dp .adcs 2 5, .dp .adcs 3 6, .movImm 5 0, .dp .adcs 4 5,
   .movHi 8 0, .movHi 10 1, .movHi 11 2, .movHi 12 3]

def reducePhaseB (sq : Bool) : List Instr :=
  [.addRdSp 7 (sl (SPP + 4)), .ldm 7 0x0f] ++
  (if sq then [.dp .mvns 0 0, .dp .mvns 1 1, .dp .mvns 2 2, .dp .mvns 3 3, .movImm 6 0, .dp .mvns 6 6]
   else xorN false 6) ++
  [.movImm 5 0, .addReg 0 0 4, .dp .adcs 1 5, .dp .adcs 2 5, .dp .adcs 3 5, .dp .adcs 6 5,
   .addRdSp 7 (sl (SP_ + 4)),
   .ldm 7 0x30, .addReg 0 0 4, .dp .adcs 1 5, .ldm 7 0x30, .dp .adcs 2 4, .dp .adcs 3 5,
   .movImm 4 0, .dp .adcs 6 4,
   .addRdSp 7 (sl (SH + 4)),
   .ldm 7 0x30, .addReg 0 0 4, .dp .adcs 1 5, .ldm 7 0x30, .dp .adcs 2 4, .dp .adcs 3 5,
   .movImm 4 0, .dp .adcs 6 4]

def reducePhaseC : List Instr :=
  [.addRdSp 7 (sl SH),
   .ldm 7 0x30, .addReg 0 0 4, .dp .adcs 1 5, .ldm 7 0x30, .dp .adcs 2 4, .dp .adcs 3 5,
   .movImm 4 0, .dp .adcs 6 4, .movHi 9 6, .subImm8 7 16, .stm 7 0x0f]

def reduceTop : List Instr :=
  [.ldrSp 4 (sl (SH + 7)), .ldrSp 5 (sl (SP_ + 7)), .movImm 7 38, .movImm 2 0,
   .uxth 6 4, .lsrImm 4 4 16, .dp .muls 6 7, .dp .muls 4 7, .lslImm 3 4 16, .lsrImm 4 4 16,
   .addReg 5 5 6, .dp .adcs 4 2, .addReg 5 5 3, .dp .adcs 4 2,
   .movHi 3 12, .addReg 5 5 3, .dp .adcs 4 2,
   .lslImm 4 4 1, .lsrImm 3 5 31, .addReg 4 4 3, .lslImm 5 5 1, .lsrImm 5 5 1, .movHi 12 5,
   .movImm 3 19, .dp .muls 4 3, .ldrSp 0 (sl SDST)]

/-- Word `i` of the reduction: carry in `k`, out in `h`; `y` is the parked `Y` word added at
`i = 4, 5, 6`. -/
def reduceWord (i : Nat) (k h l t u : LowReg) (y : Option Reg) : List Instr :=
  [.ldrSp h (sl (SH + i)), .ldrSp l (sl (SP_ + i)), .uxth t h, .lsrImm h h 16,
   .dp .muls t 7, .dp .muls h 7] ++
  (if i = 4 then [.movHi u.toReg 9, .dp .muls u 7, .addReg k k u] else []) ++
  [.addReg t t k, .lslImm u h 16, .lsrImm h h 16, .addReg l l t, .dp .adcs h 2,
   .addReg l l u, .dp .adcs h 2] ++
  (match y with | some r => [.movHi u.toReg r, .addReg l l u, .dp .adcs h 2] | none => []) ++
  [.memImm .str l 0 (BitVec.ofNat 5 i)]

def reduceLoop : List Instr :=
  reduceWord 0 4 1 3 5 6 none ++ reduceWord 1 1 4 3 5 6 none ++ reduceWord 2 4 1 3 5 6 none ++
  reduceWord 3 1 4 3 5 6 none ++ reduceWord 4 4 1 3 5 6 (some 8) ++
  reduceWord 5 1 4 3 5 6 (some 10) ++ reduceWord 6 4 1 3 5 6 (some 11) ++
  [.movHi 2 12, .addReg 2 2 1, .memImm .str 2 0 7]

def combineReduce (sq : Bool) : List Instr :=
  reducePhaseA sq ++ reducePhaseB sq ++ reducePhaseC ++ reduceTop ++ reduceLoop

def feMulList : List Instr :=
  [.push 0 true, .subSp (BitVec.ofNat 7 SFRAME), .strSp 0 (sl SDST), .strSp 1 (sl SA),
   .strSp 2 (sl SB)] ++ mul128 SP_ false ++
  [.ldrSp 1 (sl SA), .addImm8 1 16, .ldrSp 2 (sl SB), .addImm8 2 16] ++ mul128 SH false ++
  diff256 SA SDA ++ [.movHi 8 0] ++ diff256 SB SDB ++
  [.movHi 1 8, .dp .eors 0 1, .dp .mvns 0 0, .strSp 0 (sl SN), .addRdSp 1 (sl SDA),
   .addRdSp 2 (sl SDB)] ++ mul128 SPP true ++ combineReduce false ++
  [.addSp (BitVec.ofNat 7 SFRAME), .pop 0 true]

def feSqrList : List Instr :=
  [.push 0 true, .subSp (BitVec.ofNat 7 SFRAME), .strSp 0 (sl SDST), .strSp 1 (sl SA)] ++
  sqr128 SP_ false ++ [.ldrSp 1 (sl SA), .addImm8 1 16] ++ sqr128 SH false ++
  diff256 SA SDA ++ [.addRdSp 1 (sl SDA)] ++ sqr128 SPP true ++ combineReduce true ++
  [.addSp (BitVec.ofNat 7 SFRAME), .pop 0 true]

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

end M0Crypto.Release.X25519Macros
