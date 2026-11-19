import M0Crypto.Release.Ed25519CallProgGeo
import M0Crypto.Sym.Core

/-!
# Call programs: public blocks

A public block is straight-line code on registers that hold public values. `pubEval` runs the
symbolic executor `Sym.symExec` on it and evaluates the resulting syntax over the known
registers `σ` and the frame words that are views of public values: each register's value as a
symbolic value `SV`, and each flag when the operands it depends on are constants. A block that
stores leaves the symbolic memory other than the entry memory and is not public. `condFl` is
`condPassed` on known flags.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State addWithCarry)
open M0Crypto.Thumb
open M0Crypto.Sym (SExpr SBool SMem SState symExec)

/-- `v + n` for a constant `n`. -/
def SV.addK : SV → Nat → Option SV
  | .k a, n => some (.k (a + n))
  | .ext i e, n => some (.ext i (e + n))
  | .sp o, n => some (.sp (o + n))
  | .prm _, _ => none

/-- The word of a constant. -/
def SV.kw : SV → Option Word
  | .k n => some (BitVec.ofNat 32 n)
  | _ => none

/-- A constant from a word. -/
def kOf (w : Word) : SV := .k w.toNat

/-- A binary operation on two constants. -/
def svK2 (f : Word → Word → Word) : Option SV → Option SV → Option SV
  | some a, some b => match a.kw, b.kw with
    | some x, some y => some (kOf (f x y))
    | _, _ => none
  | _, _ => none

/-- `addWithCarry`'s value, for a constant carry: of two constants, or of a symbolic value and a
constant without carry. -/
def awcSv (x y : Option SV) : SBool → Option SV
  | .const cin => match x, y with
    | some x, some y => match x.kw, y.kw with
      | some u, some v => some (kOf (addWithCarry u v cin).1)
      | _, some v => if cin then none else SV.addK x v.toNat
      | some u, _ => if cin then none else SV.addK y u.toNat
      | none, none => none
    | _, _ => none
  | _ => none

/-- A word load: a frame word that is a view of a public value. -/
def ld32Sv (σ : List (Reg × SV)) (Γ : List (Loc × Kd)) : SMem → SExpr → Option SV
  | .mem0, .add (.reg0 13) (.const w) => if σ.lookup 13 = some (.sp 0) then pwAt Γ w.toNat else none
  | _, _ => none

/-- **The public value of syntax**, from the registers `σ` and the word views `Γ`. -/
def exSv (σ : List (Reg × SV)) (Γ : List (Loc × Kd)) : SExpr → Option SV
  | .reg0 r => σ.lookup r
  | .const w => some (kOf w)
  | .add a b => svK2 (· + ·) (exSv σ Γ a) (exSv σ Γ b)
  | .sub a b => svK2 (· - ·) (exSv σ Γ a) (exSv σ Γ b)
  | .and a b => svK2 (· &&& ·) (exSv σ Γ a) (exSv σ Γ b)
  | .or a b => svK2 (· ||| ·) (exSv σ Γ a) (exSv σ Γ b)
  | .xor a b => svK2 (· ^^^ ·) (exSv σ Γ a) (exSv σ Γ b)
  | .not a => ((exSv σ Γ a).bind SV.kw).map fun x => kOf (~~~x)
  | .awc a b c => awcSv (exSv σ Γ a) (exSv σ Γ b) c
  | .lsl a n => ((exSv σ Γ a).bind SV.kw).map fun (x : Word) => kOf (x <<< n)
  | .lsr a n => ((exSv σ Γ a).bind SV.kw).map fun (x : Word) => kOf (x >>> n)
  | .ld32 m a => ld32Sv σ Γ m a
  | .mul _ _ | .uxth _ | .ror _ _ _ | .lslR _ _ _ | .lsrR _ _ _ | .asr _ _ | .rev _ | .ld16 _ _
  | .ld8 _ _ | .rotl _ _ => none

/-- The value of a flag, when its operands are constants. -/
def flBv (σ : List (Reg × SV)) (Γ : List (Loc × Kd)) : SBool → Option Bool
  | .const b => some b
  | .msb a => ((exSv σ Γ a).bind SV.kw).map BitVec.msb
  | .isZero a => ((exSv σ Γ a).bind SV.kw).map (· == 0)
  | .awcC a b (.const cin) => match (exSv σ Γ a).bind SV.kw, (exSv σ Γ b).bind SV.kw with
    | some x, some y => some (addWithCarry x y cin).2.1
    | _, _ => none
  | .awcV a b (.const cin) => match (exSv σ Γ a).bind SV.kw, (exSv σ Γ b).bind SV.kw with
    | some x, some y => some (addWithCarry x y cin).2.2
    | _, _ => none
  | _ => none

/-- The registers a public block reports. -/
def pubRegs : List Reg := [0, 1, 2, 3, 4, 5, 6, 7, 13]

/-- The result of a public block: the known registers and flags. -/
structure PubR where
  σ : List (Reg × SV)
  n : Option Bool
  z : Option Bool
  c : Option Bool
  v : Option Bool

/-- The memory syntax of a block that does not store. -/
def isMem0 : SMem → Bool
  | .mem0 => true
  | _ => false

/-- **A public block** from the registers `σ` and the word views `Γ`: the registers it leaves
known and its flags. -/
def pubEval (σ : List (Reg × SV)) (Γ : List (Loc × Kd)) (g : List Instr) : Option PubR :=
  let ss := symExec g SState.init
  if isMem0 ss.mem then
    some ⟨pubRegs.filterMap fun r => (exSv σ Γ (ss.regs r)).map (r, ·),
      flBv σ Γ ss.n, flBv σ Γ ss.z, flBv σ Γ ss.c, flBv σ Γ ss.v⟩
  else none

/-- `condPassed` on the flags `n z c v`. -/
def condFl (cc : BitVec 4) (n z c v : Bool) : Bool :=
  condPassed cc ⟨fun _ => 0, n, z, c, v, fun _ => 0⟩

theorem condPassed_fl (cc : BitVec 4) (t : State) : condPassed cc t = condFl cc t.n t.z t.c t.v := rfl

theorem condFl_xor1 : ∀ cc : BitVec 4, cc.toNat < 14 → ∀ n z c v : Bool,
    condFl (cc ^^^ 1) n z c v = !condFl cc n z c v := by decide

/-- The decision of a test with result `r`, when its flags are known. -/
def PubR.dec (r : PubR) (cc : BitVec 4) : Option Bool :=
  match r.n, r.z, r.c, r.v with
  | some n, some z, some c, some v => some (condFl cc n z c v)
  | _, _, _, _ => none

end M0Crypto.Release.Ed25519CallProg
