import M0Crypto.Thumb.SpBlock
import SafegcdRow.Correct

/-! Caller instructions between shared leaves, with branch and literal offsets
derived from encoded instruction sizes. -/

namespace SafegcdRow.BatchCode

open M0Crypto.Armv6M (LowReg)
open M0Crypto.Thumb

def vectorBytes : Nat := 17 * 4
def bankF : Nat := 0
def bankG : Nat := vectorBytes
def bankD : Nat := 2 * vectorBytes
def bankE : Nat := 3 * vectorBytes
def temp : Nat := 4 * vectorBytes
def outputAt : Nat := 5 * vectorBytes
def deltaAt : Nat := outputAt + 4
def counterAt : Nat := deltaAt + 4
def matrixAt : Nat := counterAt + 4
def frameBytes : Nat := 376

structure Banks where
  f : Nat
  d : Nat
  free : Nat
  deriving DecidableEq

def phases : Fin 3 → Banks
  | 0 => ⟨bankF, bankD, temp⟩
  | 1 => ⟨temp, bankF, bankD⟩
  | _ => ⟨bankD, temp, bankF⟩

def Banks.next (b : Banks) : Banks := ⟨b.free, b.f, b.d⟩

def imm (offset : Nat) : BitVec 8 := BitVec.ofNat 8 (offset / 4)
def loadSp (dst : LowReg) (offset : Nat) : Instr := .ldrSp dst (imm offset)
def storeSp (src : LowReg) (offset : Nat) : Instr := .strSp src (imm offset)
def withSp (dst : LowReg) (offset : Nat) : Instr := .addRdSp dst (imm offset)

def prepareMatrix (b : Banks) : List Instr :=
  [loadSp 0 b.f, loadSp 1 bankG, loadSp 2 deltaAt, loadSp 7 (b.f + 4),
   .lslImm 7 7 16, .dp .orrs 0 7, loadSp 7 (bankG + 4), .lslImm 7 7 16, .dp .orrs 1 7]

def saveMatrix : List Instr := [storeSp 2 deltaAt, withSp 0 matrixAt, .stm 0 120]

structure RowCall where
  dst : Nat
  x : Nat
  y : Nat
  coeff : Nat
  modular : Bool

def rowCalls (b : Banks) : List RowCall :=
  [⟨b.free, b.f, bankG, 0, false⟩, ⟨bankG, b.f, bankG, 2, false⟩,
   ⟨b.f, b.d, bankE, 0, true⟩, ⟨bankE, b.d, bankE, 2, true⟩]

def prepareRow (r : RowCall) : List Instr :=
  [withSp 0 r.dst, withSp 1 r.x, withSp 2 r.y,
   loadSp 3 (matrixAt + 4 * r.coeff), loadSp 4 (matrixAt + 4 * (r.coeff + 1))]

def correctionPrefix : List Instr :=
  [.memImm .ldr 5 1 0, .memImm .ldr 6 2 0, .dp .muls 5 3, .dp .muls 6 4, .addReg 5 5 6]

def prepareCorrection (lit : BitVec 8) : List Instr :=
  correctionPrefix ++ [.ldrLit 6 lit, .dp .muls 5 6, .lslImm 5 5 18, .lsrImm 5 5 18]

def prepareFold (r : RowCall) : List Instr := [withSp 0 r.dst]

structure Targets where
  matrix : Nat
  exact : Nat
  modular : Nat
  fold : Nat
  literal : Nat

def callTo (off target : Nat) : Instr := .bl (BitVec.ofInt 25 ((target : Int) - (off + 4)))

def literalImm (off addr : Nat) : BitVec 8 := BitVec.ofNat 8 ((addr - (off + 4) / 4 * 4) / 4)

def rowCode (q : Targets) (off : Nat) (r : RowCall) : List Instr :=
  let pre := prepareRow r
  let afterPre := off + seqSize pre
  if r.modular then
    let cor := prepareCorrection (literalImm (afterPre + seqSize correctionPrefix) q.literal)
    let fold := prepareFold r
    let call := afterPre + seqSize cor
    pre ++ cor ++ [callTo call q.modular] ++ fold ++ [callTo (call + 4 + seqSize fold) q.fold]
  else
    pre ++ [callTo afterPre q.exact]

def rowsCode (q : Targets) : Nat → List RowCall → List Instr
  | _, [] => []
  | o, r :: rs =>
    let code := rowCode q o r
    code ++ rowsCode q (o + seqSize code) rs

def matrixPre (off dest : Nat) (b : Banks) : List Instr :=
  let pre := prepareMatrix b
  pre ++ [callTo (off + seqSize pre) dest]

def saveOff (q : Targets) (off : Nat) (b : Banks) : Nat :=
  off + seqSize (matrixPre off q.matrix b)

def firstRow (q : Targets) (off : Nat) (b : Banks) : Nat :=
  saveOff q off b + seqSize saveMatrix

def batchCode (q : Targets) (off : Nat) (b : Banks) : List Instr :=
  matrixPre off q.matrix b ++ saveMatrix ++ rowsCode q (firstRow q off b) (rowCalls b)

theorem phase_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (Fin.ext h))

theorem next_phase (i : Fin 3) : (phases i).next = phases (i + 1) := by
  rcases phase_cases i with rfl | rfl | rfl <;> decide +kernel

end SafegcdRow.BatchCode
