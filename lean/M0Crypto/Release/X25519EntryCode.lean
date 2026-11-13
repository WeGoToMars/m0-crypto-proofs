import M0Crypto.Release.X25519Op
import M0Crypto.Release.X25519Bytes
import M0Crypto.Release.X25519Chain
import M0Crypto.Thumb.SeqScan

set_option linter.deprecated false

/-!
The code of `m0c_x25519` as Lean lists.

The lists follow `emit_x25519` of `tools/gen_x25519.py`. Field operations are `Op` values
(`op(g, fn, d, a, b)` of the generator); `opsAt o ops` emits them from code offset `o`, so every
`bl` offset is computed from where it lands. Loops branch to offsets computed the same way. The
inversion chain is emitted from `X25519Chain.invChain`, the table the arithmetic proof uses.

`entry_at` checks the whole list against the release bytes once; every segment lemma of the
entry proof gets its `seqAt` from it by `seqAt_append`. No offset is written down: segment
offsets are `seqSize` sums (`oLadder`, `oSwap`, ...).
-/

namespace M0Crypto.Release.X25519EntryCode
open M0Crypto.Armv6M (LowReg)
open M0Crypto.Thumb
open M0Crypto.Release (B)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op (opPre blTo)
open M0Crypto.Release.X25519Bytes (loadLe32 storeLe32)
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMul feSqr feMulcAdd)
open M0Crypto.Release.X25519Chain (invChain)

/-! ## Inline bodies (`fe_add_body`, `fe_sub_body`, `select_words`, `canon_body`) -/

/-- `fe_add_body` (`neg = false`) and `fe_sub_body` (`neg = true`) share the carry chain. -/
def addSubBody (neg : Bool) : List Instr :=
  let dop : DpOp := if neg then .sbcs else .adcs
  let op3 (d n m : LowReg) : Instr := if neg then .subReg d n m else .addReg d n m
  let pair (k : Bool) : List Instr :=
    [.ldm 1 0x18, .ldm 2 0x60, if k then .dp dop 3 5 else op3 3 3 5, .dp dop 4 6]
  let fold : List Instr :=
    if neg then
      [.dp .sbcs 7 7, .lslImm 7 7 1, .dp .mvns 1 6, .lsrImm 1 1 31, .subReg 7 1 7,
        .movImm 1 1, .lslImm 1 1 31, .dp .orrs 6 1, .movImm 1 19, .dp .muls 7 1]
    else
      [.movImm 7 0, .dp .adcs 7 7, .lslImm 7 7 1, .lsrImm 1 6 31, .addReg 7 7 1,
        .lslImm 6 6 1, .lsrImm 6 6 1, .movImm 1 19, .dp .muls 7 1]
  pair false ++ [.movHi 8 3, .movHi 10 4] ++ pair true ++ [.movHi 11 3, .movHi 12 4] ++
    pair true ++ [.ldm 1 0x60, .ldm 2 0x06, .dp dop 5 1, .dp dop 6 2] ++ fold ++
    [.movHi 1 8, .movHi 2 10, op3 1 1 7, .movImm 7 0, .dp dop 2 7, .stm 0 0x06] ++
    [.movHi 1 11, .movHi 2 12, .dp dop 1 7, .dp dop 2 7, .dp dop 3 7, .dp dop 4 7,
      .dp dop 5 7, .dp dop 6 7, .stm 0 0x7e]

/-- One word pair of `select_words`. -/
def selPair : List Instr :=
  [.ldm 1 0x18, .ldm 2 0x60, .dp .eors 5 3, .dp .eors 6 4, .dp .ands 5 7, .dp .ands 6 7,
    .dp .eors 3 5, .dp .eors 4 6, .stm 0 0x18]

def selBody : List Instr := selPair ++ selPair ++ selPair ++ selPair

/-- `add_c` of `canon_body`: add `c` to the eight words at `r0`, storing them if `store`. -/
def addC (c : LowReg) (store : Bool) : List Instr :=
  let st (i : Nat) : List Instr := if store then [.memImm .str 1 0 (BitVec.ofNat 5 i)] else []
  (.memImm .ldr 1 0 0 :: .addReg 1 1 c :: st 0) ++
    (List.range' 1 7).flatMap fun i => .memImm .ldr 1 0 (BitVec.ofNat 5 i) :: .dp .adcs 1 2 :: st i

def canonBody : List Instr :=
  [.movImm 2 0, .movImm 3 19, .memImm .ldr 1 0 7, .lsrImm 4 1 31, .lslImm 1 1 1, .lsrImm 1 1 1,
    .memImm .str 1 0 7, .dp .muls 4 3] ++ addC 4 true ++ addC 3 false ++
  [.lsrImm 4 1 31, .dp .muls 4 3] ++ addC 4 true ++ [.lslImm 1 1 1, .lsrImm 1 1 1, .memImm .str 1 0 7]

/-! ## Field operations on slots -/

inductive Fn where
  | add | sub | sel | mul | sqr | mulc
  deriving DecidableEq, Repr

/-- `op(g, fn, d, a, b)`: slot offsets `d`, `a` and optionally `b`. -/
structure Op where
  fn : Fn
  d : Nat
  a : Nat
  b : Option Nat
  deriving DecidableEq, Repr

/-- Offset of the routine a call operation branches to. -/
def Fn.target : Fn → Nat
  | .mul => feMul
  | .sqr => feSqr
  | _ => feMulcAdd

/-- One operation at code offset `o`. -/
def opAt (o : Nat) (p : Op) : List Instr :=
  opPre p.d p.a p.b ++
    match p.fn with
    | .add => addSubBody false
    | .sub => addSubBody true
    | .sel => selBody
    | fn => [blTo (o + seqSize (opPre p.d p.a p.b)) fn.target]

/-- Operations from code offset `o`. -/
def opsAt : Nat → List Op → List Instr
  | _, [] => []
  | o, p :: ps => opAt o p ++ opsAt (o + seqSize (opAt o p)) ps

def add (d a b : Nat) : Op := ⟨.add, d, a, some b⟩
def sub (d a b : Nat) : Op := ⟨.sub, d, a, some b⟩
def sel (d a b : Nat) : Op := ⟨.sel, d, a, some b⟩
def mul (d a b : Nat) : Op := ⟨.mul, d, a, some b⟩
def sqr (d a : Nat) : Op := ⟨.sqr, d, a, none⟩
def mulc (d a b : Nat) : Op := ⟨.mulc, d, a, some b⟩

/-! ## Branches -/

/-- `b` at `q` to `t`. -/
def bTo (q t : Nat) : Instr := .b (BitVec.ofInt 11 (((t : Int) - (q + 4)) / 2))

/-- `b<cond>` at `q` to `t`. -/
def bcTo (cond : BitVec 4) (q t : Nat) : Instr := .bcond cond (BitVec.ofInt 8 (((t : Int) - (q + 4)) / 2))

/-- `ldr r0, [sp, #LV_T]; subs r0, #1; str r0, [sp, #LV_T]`. -/
def decT : List Instr := [.ldrSp 0 (BitVec.ofNat 8 (lvT / 4)), .subImm8 0 1, .strSp 0 (BitVec.ofNat 8 (lvT / 4))]

/-- `movs r0, #n; str r0, [sp, #LV_T]`. -/
def setT (n : Nat) : List Instr := [.movImm 0 (BitVec.ofNat 8 n), .strSp 0 (BitVec.ofNat 8 (lvT / 4))]

/-! ## Prologue -/

def saveRegs : List Instr :=
  [.push 0xf0 true, .movHi 4 8, .movHi 5 9, .movHi 6 10, .movHi 7 11, .push 0xf0 false,
    .subSp (BitVec.ofNat 7 (LFRAME / 4)), .strSp 0 (BitVec.ofNat 8 (lvOut / 4))]

/-- Word `i` of the clamped scalar into `S_K`. -/
def scalarWord (i : Nat) : List Instr :=
  loadLe32 4 3 1 (4 * i) ++
  (if i = 0 then [.lsrImm 4 4 3, .lslImm 4 4 3] else []) ++
  (if i = 7 then [.lslImm 4 4 2, .lsrImm 4 4 2, .movImm 3 1, .lslImm 3 3 30, .dp .orrs 4 3] else []) ++
  [.strSp 4 (BitVec.ofNat 8 (sK / 4 + i))]

/-- Word `i` of u, bit 255 masked, into `X1` and `X3`. -/
def pointWord (i : Nat) : List Instr :=
  loadLe32 4 3 2 (4 * i) ++
  (if i = 7 then [.lslImm 4 4 1, .lsrImm 4 4 1] else []) ++
  [.strSp 4 (BitVec.ofNat 8 (sX1 / 4 + i)), .strSp 4 (BitVec.ofNat 8 (sX3 / 4 + i))]

def words (f : Nat → List Instr) : List Instr := (List.range 8).flatMap f

/-- `X2 = 1`, `Z2 = 0`, `Z3 = 1`, `swap = 0`, `t = 254`. -/
def initState : List Instr :=
  [.addRdSp 3 (BitVec.ofNat 8 (sX2 / 4)), .movImm 4 1, .movImm 5 0, .movImm 6 0, .movImm 7 0,
    .stm 3 0xf0, .movImm 4 0, .stm 3 0xf0, .stm 3 0xf0, .stm 3 0xf0,
    .addRdSp 3 (BitVec.ofNat 8 (sZ3 / 4)), .movImm 4 1, .stm 3 0xf0, .movImm 4 0, .stm 3 0xf0,
    .strSp 4 (BitVec.ofNat 8 (lvSwap / 4))] ++ setT 254

def prologue : List Instr := saveRegs ++ words scalarWord ++ words pointWord ++ initState

/-! ## Ladder -/

def ladderOps1 : List Op := [add sA sX2 sZ2, sub sB sX2 sZ2, add sC sX3 sZ3, sub sD sX3 sZ3]

/-- `r7 = -(swap ^ k_t)`, `swap = k_t`. -/
def bitL : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 (lvT / 4)), .lsrImm 1 0 3, .movImm 2 28, .dp .ands 1 2,
    .addRdSp 2 (BitVec.ofNat 8 (sK / 4)), .memReg .ldr 1 2 1, .dp .rors 1 0, .movImm 2 1,
    .dp .ands 1 2, .ldrSp 7 (BitVec.ofNat 8 (lvSwap / 4)), .strSp 1 (BitVec.ofNat 8 (lvSwap / 4)),
    .dp .eors 7 1, .dp .rsbs 7 7]

/-- Slot aliases of the generator: `SA = X2`, `SB = Z2`, `DA = D`, `CB = C`, `AA = A`,
`BB = B`, `E = A`, `T = C`. -/
def ladderOps2 : List Op :=
  [sel sX2 sA sC, sel sZ2 sB sD, mul sD sD sA, mul sC sC sB, add sX3 sD sC, sqr sX3 sX3,
   sub sZ3 sD sC, sqr sZ3 sZ3, mul sZ3 sX1 sZ3, sqr sA sX2, sqr sB sZ2, mul sX2 sA sB,
   sub sA sA sB, mulc sC sA sB, mul sZ2 sA sC]

/-- One ladder step from `o`. -/
def stepAt (o : Nat) : List Instr :=
  let l1 := opsAt o ladderOps1 ++ bitL
  l1 ++ opsAt (o + seqSize l1) ladderOps2

/-- The ladder loop at `o`: step, `t -= 1`, exit when `t < 3`, else back to `o`. -/
def ladderAt (o : Nat) : List Instr :=
  let q := o + seqSize (stepAt o) + 6
  stepAt o ++ decT ++ [.cmpImm 0 3, bcTo 0xb (q + 2) (q + 6), bTo (q + 4) o]

/-! ## Final swap, doublings -/

def swapAt (o : Nat) : List Instr :=
  [.ldrSp 7 (BitVec.ofNat 8 (lvSwap / 4)), .dp .rsbs 7 7] ++ opsAt (o + 4) [sel sX2 sX2 sX3, sel sZ2 sZ2 sZ3] ++
    setT 3

/-- `dbl(g, X2, Z2)`. -/
def dblOps : List Op :=
  [add sA sX2 sZ2, sub sB sX2 sZ2, sqr sA sA, sqr sB sB, mul sX2 sA sB, sub sA sA sB,
   mulc sC sA sB, mul sZ2 sA sC]

def dblAt (o : Nat) : List Instr :=
  let q := o + seqSize (opsAt o dblOps) + 6
  opsAt o dblOps ++ decT ++ [bcTo 0x0 q (q + 4), bTo (q + 2) o]

/-! ## Inversion chain -/

open X25519Chain (CSlot CStep) in
/-- Frame slot of a chain slot: `T0..T3 = A..D`, `Z = DST = Z2`. -/
def cslot : X25519Chain.CSlot → Nat
  | .t0 => sA
  | .t1 => sB
  | .t2 => sC
  | .t3 => sD
  | .z => sZ2
  | .dst => sZ2

/-- `n - 1` further squarings of `d` in place, counted in `LV_T`, from `o`. -/
def sqrLoopAt (o d n : Nat) : List Instr :=
  let body := opAt (o + 4) (sqr d d)
  let q := o + 4 + seqSize body + 6
  setT (n - 1) ++ body ++ decT ++ [bcTo 0x1 q (o + 4)]

def stepChainAt (o : Nat) : X25519Chain.CStep → List Instr
  | .mul d a b => opAt o (mul (cslot d) (cslot a) (cslot b))
  | .sqr d a n =>
    let first := opAt o (sqr (cslot d) (cslot a))
    let o' := o + seqSize first
    first ++
      if n = 2 then opAt o' (sqr (cslot d) (cslot d))
      else if 2 < n then sqrLoopAt o' (cslot d) n
      else []

def chainAt : Nat → List X25519Chain.CStep → List Instr
  | _, [] => []
  | o, st :: sts => stepChainAt o st ++ chainAt (o + seqSize (stepChainAt o st)) sts

/-! ## Output, wipe, epilogue -/

def finishAt (o : Nat) : List Instr :=
  opAt o (mul sX2 sX2 sZ2) ++ [.addRdSp 0 (BitVec.ofNat 8 (sX2 / 4))] ++ canonBody

def storeOut : List Instr :=
  .ldrSp 2 (BitVec.ofNat 8 (lvOut / 4)) :: words fun i => storeLe32 1 0 2 i (4 * i)

def wipe : List Instr :=
  [.subSp (BitVec.ofNat 7 (CALLEE / 4)), .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0,
    .movImm 5 0, .addRdSp 0 0] ++ List.replicate ((LFRAME + CALLEE) / 20) (.stm 0 0x3e)

def epilogue : List Instr :=
  [.addSp (BitVec.ofNat 7 ((CALLEE + LFRAME) / 4)), .movImm 0 0, .movHi 12 0, .pop 0xf0 false,
    .movHi 8 4, .movHi 9 5, .movHi 10 6, .movHi 11 7, .pop 0xf0 true]

/-! ## Segment offsets and the whole entry -/

def oLadder : Nat := Artifacts.Release.x25519 + seqSize prologue
def oSwap : Nat := oLadder + seqSize (ladderAt oLadder)
def oDbl : Nat := oSwap + seqSize (swapAt oSwap)
def oChain : Nat := oDbl + seqSize (dblAt oDbl)
def oFinish : Nat := oChain + seqSize (chainAt oChain invChain)
def oStore : Nat := oFinish + seqSize (finishAt oFinish)
def oWipe : Nat := oStore + seqSize storeOut
def oEpi : Nat := oWipe + seqSize wipe

def entryList : List Instr :=
  prologue ++ ladderAt oLadder ++ swapAt oSwap ++ dblAt oDbl ++ chainAt oChain invChain ++
    finishAt oFinish ++ storeOut ++ wipe ++ epilogue

theorem entry_at : seqAt B Artifacts.Release.x25519 entryList = true := by
  rw [seqAt_eq_scan]; decide +kernel

theorem entry_size : Artifacts.Release.x25519 + seqSize entryList = Artifacts.Release.size := by
  decide +kernel

end M0Crypto.Release.X25519EntryCode
