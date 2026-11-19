import M0Crypto.Release.RoutinePieces
import M0Crypto.Release.Field25519Routines
import M0Crypto.Release.Field25519Congr
import M0Crypto.Spec.Ed25519

set_option linter.unusedSimpArgs false

/-!
# Call programs: the generator's constructs as data

A routine of the Ed25519 generator is mostly operand loads and `bl`. Here its code is a value of
`Prog`, built from the generator's constructs, and `Prog.emit o` is its code at offset `o` as
`Piece`s, mirroring `tools/ed25519/asm.py` (`sp_addr`, `ldr_sp`, `const`, the operand loaders
`S`, `P`, `slot_word`, `const_len`, `jump_if`). A routine's presence is one `piecesAt` check of the
emitted pieces.

The data a program carries is static: frame offsets, registers, callee indices, the kinds of the
typed views that live in the frame. Every geometric side condition of a construct (offsets,
liveness, frame extent, which views a write kills, alignment, equal-or-apart arguments, which
external buffer an argument lies in) is a Boolean check over that data (`Ed25519CallProgGeo`),
proved sound once. Values are not data: they live in `Ed25519CallProgRun`.

Words used below. A *location* (`Loc`) is a frame offset or an offset into an external buffer
(a caller's pointer argument). A *view* is a location with a kind (`Kd`): field element, byte
string, SHA-512 context, extended point, or a public word whose value is a symbolic public value
(`SV`). A *symbolic value* is what a register holds at a call: a frame address, an external
pointer plus a constant, a public parameter, or a constant; all of them are public.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces

abbrev Byte := BitVec 8

/-! ## Emission, as `asm.py` -/

/-- `adds r, #step` with steps of at most 252, adding `n` (fuel `f`). -/
def addsN (r : LowReg) : Nat → Nat → List Instr
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else
      .addImm8 r (BitVec.ofNat 8 (min n 252)) :: addsN r f (n - min n 252)

/-- `adds` steps adding `n` to `r` (`asm.py`, `P` and `sp_addr`). -/
def adds (r : LowReg) (n : Nat) : List Instr := addsN r n n

/-- `sp_addr`: `add r, sp, #off`; above 1020, `add r, sp, #1020` and `adds` steps. -/
def spAddr (r : LowReg) (off : Nat) : List Instr :=
  if off ≤ 1020 then [.addRdSp r (BitVec.ofNat 8 (off / 4))]
  else .addRdSp r (BitVec.ofNat 8 255) :: adds r (off - 1020)

/-- `ldr_sp` with the register as its own temporary. -/
def ldrSpI (r : LowReg) (off : Nat) : List Instr :=
  if off ≤ 1020 then [.ldrSp r (BitVec.ofNat 8 (off / 4))]
  else spAddr r off ++ [.memImm .ldr r r 0]

/-- An operand loader: `S(off)`, `P(off, extra)` and `slot_word(off)` (`W`), `const_len(n)` (`K`),
`adds` steps on the register's own address (`A`), and `code_addr` (`C`): the address `e` bytes
into code buffer `i`, by `ldr r, =lit` with immediate `imm` and `add r, pc`. `A` and `C` load
only as a construct of their own (`Op.ld`). -/
inductive Ld where
  | S (off : Nat)
  | W (off extra : Nat)
  | K (n : Nat)
  | A (k : Nat)
  | C (i e imm : Nat)
  deriving DecidableEq, Repr

def Ld.emit (r : LowReg) : Ld → List Instr
  | .S off => spAddr r off
  | .W off e => ldrSpI r off ++ adds r e
  | .K n => [.movImm r (BitVec.ofNat 8 n)]
  | .A k => adds r k
  | .C _ _ imm => [.ldrLit r (BitVec.ofNat 8 imm), .addPc r]

/-- The loads of a call's arguments, in the generator's order. -/
def ldsEmit : List (LowReg × Ld) → List Instr
  | [] => []
  | (r, l) :: as => l.emit r ++ ldsEmit as

/-! ## Symbolic values, kinds, locations -/

/-- What a register holds at a call: `sp + off`; external buffer `i` plus `e`; public parameter
`i`; a constant. -/
inductive SV where
  | sp (off : Nat)
  | ext (i e : Nat)
  | prm (i : Nat)
  | k (n : Nat)
  deriving DecidableEq, Repr

/-- Bytes of the SHA-512 context (`gen_sha512.py`, `CTX_SIZE`: `N`, `H`, `BUF`). -/
def ctxSize : Nat := 196

/-- The kind of a view. -/
inductive Kd where
  | bytes (n : Nat)
  /-- 32 bytes holding a number below the group order `L`. -/
  | sc
  /-- 32 bytes holding a number below `2 ^ 255`: a clamped or a reduced scalar. -/
  | cl
  | fe
  /-- A SHA-512 context whose stream has the public length `Σ n`. -/
  | ctx (n : List SV)
  | pt
  /-- A word holding the public value `v`. -/
  | pw (v : SV)
  /-- A loop counter word (public, its value carried in the run). -/
  | cw
  /-- A register's own value: a block's register output, read by the next call. -/
  | rw
  /-- 32 bytes whose number is the field value itself, below `p` (a canonical element). -/
  | fc
  /-- 128 bytes of four field values, each modulo `p`: what a program leaves at a point output. -/
  | fe4
  deriving DecidableEq, Repr

def Kd.sz : Kd → Nat
  | .bytes n => n
  | .sc => 32
  | .cl => 32
  | .fe => 32
  | .ctx _ => ctxSize
  | .pt => 128
  | .pw _ => 4
  | .cw => 4
  | .rw => 0
  | .fc => 32
  | .fe4 => 128

/-- The kind under a refined kind (`.sc` and `.cl` are `.bytes 32` with a bound, `.pt` is four
field values that represent the point); any other kind is its own. A callee's program leaves the
kind under it at an output, and the routine proves the refinement. -/
def Kd.base : Kd → Kd
  | .sc => .bytes 32
  | .cl => .bytes 32
  | .pt => .fe4
  | k => k

/-- The refined kinds: 32 bytes with a bound on their number. -/
def Kd.isRef : Kd → Bool
  | .sc | .cl => true
  | _ => false

/-- **The kind order**: a view of kind `k` serves where kind `k'` is required. A refined kind
serves as its bytes, `.sc` as `.cl` (since `L < 2 ^ 255`), and an exact field value as one
modulo `p`. -/
def Kd.le (k k' : Kd) : Bool :=
  k == k' || (k.isRef && k' == .bytes 32) || (k == .sc && k' == .cl) || (k == .fc && k' == .fe)

theorem Kd.sz_base (k : Kd) : k.base.sz = k.sz := by cases k <;> rfl

/-- A frame offset, offset `e` into external buffer `i`, or register `r` (a block's output). -/
inductive Loc where
  | fr (o : Nat)
  | ex (i e : Nat)
  | rg (r : Reg)
  deriving DecidableEq, Repr

/-- A length: a constant, or the value of public parameter `i`. -/
inductive XLen where
  | k (n : Nat)
  | p (i : Nat)
  deriving DecidableEq, Repr

/-- A length in an interface: a constant, or the value of argument register `j`. -/
inductive ALen where
  | k (n : Nat)
  | r (j : Reg)
  deriving DecidableEq, Repr

/-- An input of an interface: a view of a kind, or raw bytes of a length. -/
inductive In where
  | view (k : Kd)
  | raw (l : ALen)
  deriving DecidableEq, Repr

/-- The bytes from argument register `r` plus `off`, of length `len`. -/
structure SRgn where
  r : Reg
  off : Nat
  len : ALen
  deriving DecidableEq, Repr

/-- **An operation interface** (static part): the inputs and outputs at argument registers plus
offsets, the symbolic write and read footprints, the registers that must be word-aligned,
argument pairs that must be equal or apart over `n` bytes, and registers that must hold a
constant. -/
structure Iface where
  ins : List (Reg × Nat × In)
  outs : List (Reg × Nat × Kd)
  wr : List SRgn
  rd : List SRgn
  al : List Reg := []
  eqd : List (Reg × Reg × Nat) := []
  kreq : List (Reg × Nat) := []
  /-- Registers that must hold a symbolic value. -/
  kreqv : List (Reg × SV) := []
  /-- Sums of public lengths that must stay below a bound. -/
  lim : List (List SV × Nat) := []
  /-- Region pairs that must lie apart. -/
  apt : List (SRgn × SRgn) := []
  /-- Registers whose `n` bytes from them do not wrap past the top of memory: frame regions. -/
  nw : List (Reg × Nat) := []
  /-- Registers a block leaves its outputs in, for the next call. -/
  ro : List Reg := []

/-- An interface with its outputs at their byte kinds. -/
def Iface.base (io : Iface) : Iface := { io with outs := io.outs.map fun x => (x.1, x.2.1, x.2.2.base) }

/-- A public value of a call: a register, or the stream-length word of the SHA-512 context at a
register. -/
inductive PubW where
  | r (r : Reg)
  | n (r : Reg)
  deriving DecidableEq, Repr

/-- A callee (static part): interface, entry, code, stack, and its public values. -/
structure CalleeS where
  io : Iface
  entry : Nat
  code : List (Nat × Nat)
  stack : Nat
  pubs : List PubW

/-- An inline block (static part): interface and instructions. `L` are the registers its pcs and
addresses read (for its trace). -/
structure BlockS where
  io : Iface
  g : List Instr
  L : List Reg

/-- An external buffer: its length, whether the program may write it, read it, and whether its
address is word-aligned. -/
structure XInfo where
  len : XLen
  w : Bool
  r : Bool
  al4 : Bool

/-- The static geometry of a program run: the caller's window `N`, the frame below `sp0 - top`,
the external buffers, the caller's code ranges. -/
structure Geo where
  N : Nat
  top : Nat
  xs : List XInfo
  cs : List (Nat × Nat)
  /-- Upper bounds of the public parameters. -/
  pm : List Nat := []
  /-- Code buffers: external buffer `i` holds the code bytes from offset `s`, for `(i, s)`. -/
  cd : List (Nat × Nat) := []
  /-- Bounded buffers: external buffer `i` holds 32 bytes of the refined kind `k` at entry, for
  `(i, k)`. -/
  xv : List (Nat × Kd) := []

/-! ## Programs -/

/-- One construct: a call with its loaders, an inline block with its loaders, a store of a
register to a frame word (`str r, [sp, #o]`), the end of the views on `n` frame bytes from
`o` (no code), or a loader. -/
inductive Op (A Bk : Type) where
  | call (a : A) (args : List (LowReg × Ld))
  | blk (b : Bk) (args : List (LowReg × Ld))
  | spill (r : LowReg) (o : Nat)
  | drop (o n : Nat)
  /-- A loader of its own: the register keeps its value for the constructs after it. -/
  | ld (r : LowReg) (l : Ld)
  /-- A public block: instructions on registers whose values `Prog.ty` evaluates, reading frame
  words that are views of public values. -/
  | pub (g : List Instr)
  /-- The views at the locations `ls`, in this order (no code): the registers other than `sp`
  end. -/
  | keep (ls : List Loc)
  /-- `ldrb rd, [rb, ri]` with `rb` a frame address and `ri` a constant, both known: a byte of a
  frame byte view at a public offset, which `rd` holds for the constructs after it (`.rg rd`). -/
  | ldb (rd rb ri : LowReg)
  /-- A literal-pool island: `b` over the padding `mov r8, r8` (when `pad`) and `n` data bytes,
  which are not code. Nothing else changes. -/
  | isl (pad : Bool) (n : Nat)

/-- A program. `loop cnt n body` is `emit_pow.steps`' counted loop: `movs r0, #n; str r0, [sp,
#cnt]`, the body, `ldr r0, [sp, #cnt]; subs r0, #1; str r0, [sp, #cnt]; jump_if bne`.
`sel w i p₀ p₁` is the dispatch of `emit_pow`: `ldr r0, [sp, #w]; cmp r0, #i; jump_if beq`
to `p₁`, `p₀` falls through; each ends in `b` to the rest. -/
inductive Prog (A Bk : Type) where
  | nil
  | op (x : Op A Bk) (k : Prog A Bk)
  | loop (cnt n : Nat) (body : Prog A Bk) (k : Prog A Bk)
  | sel (w i : Nat) (p₀ p₁ : Prog A Bk) (k : Prog A Bk)
  /-- A public test `g` with an optional store `str r, [sp, #o]`, then a branch to the exit of the
  enclosing construct `l` when `cc` holds: `b<cc>` (`sh`), or `b<!cc> +0; b`. -/
  | xit (g : List Instr) (s : Option (LowReg × Nat)) (cc : BitVec 4) (sh : Bool) (l : Nat) (k : Prog A Bk)
  /-- `b`, then (unless `h` is empty) a `b` over `h`, then `h`, and `k` at the join. The exits of
  level 0 in `b` go to `h`. -/
  | hd (b h k : Prog A Bk)
  /-- Passes of `b`, at most `n`, each followed by a `b` back to its start; the exits of level 0 in
  `b` go to `k`. -/
  | wh (n : Nat) (b k : Prog A Bk)

variable {A Bk : Type}

/-- The empty program. -/
def Prog.isNil : Prog A Bk → Bool
  | .nil => true
  | _ => false

/-- `Prog` from a list of constructs. -/
def Prog.ofList : List (Op A Bk) → Prog A Bk
  | [] => .nil
  | x :: xs => .op x (Prog.ofList xs)

/-- Two programs one after the other. -/
def Prog.seq : Prog A Bk → Prog A Bk → Prog A Bk
  | .nil, q => q
  | .op x k, q => .op x (k.seq q)
  | .loop c n b k, q => .loop c n b (k.seq q)
  | .sel w i p₀ p₁ k, q => .sel w i p₀ p₁ (k.seq q)
  | .xit g s cc sh l k, q => .xit g s cc sh l (k.seq q)
  | .hd b h k, q => .hd b h (k.seq q)
  | .wh n b k, q => .wh n b (k.seq q)

/-- `str r0, [sp, #off]` (`off ≤ 1020`). -/
def strSpI (off : Nat) : Instr := .strSp 0 (BitVec.ofNat 8 (off / 4))

/-- Loop head: `movs r0, #n; str r0, [sp, #cnt]`. -/
def loopHead (cnt n : Nat) : List Instr := [.movImm 0 (BitVec.ofNat 8 n), strSpI cnt]

/-- Loop tail before the branch: `ldr r0, [sp, #cnt]; subs r0, #1; str r0, [sp, #cnt]`. -/
def loopDec (cnt : Nat) : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 (cnt / 4)), .subImm8 0 1, strSpI cnt]

/-- Dispatch head: `ldr r0, [sp, #w]; cmp r0, #i`. -/
def selHead (w i : Nat) : List Instr := [.ldrSp 0 (BitVec.ofNat 8 (w / 4)), .cmpImm 0 (BitVec.ofNat 8 i)]

/-- Condition codes. -/
def EQ : BitVec 4 := 0
def NE : BitVec 4 := 1

/-- `str r, [sp, #o]`. -/
def strR (r : LowReg) (o : Nat) : Instr := .strSp r (BitVec.ofNat 8 (o / 4))

/-- A test's pieces: the public block, then its store. -/
def xitP (g : List Instr) : Option (LowReg × Nat) → List Piece
  | none => [.seq g]
  | some (r, o) => [.seq g, .seq [strR r o]]

/-- The size of a test's block and store. -/
def xitSz (g : List Instr) : Option (LowReg × Nat) → Nat
  | none => seqSize g
  | some _ => seqSize g + 2

/-- The branch of a test: `b<cc> T`, or `b<!cc> +0; b T`. -/
def xitBr (cc : BitVec 4) (sh : Bool) (o T : Nat) : List Piece :=
  if sh then [.bcond cc T] else [.bcond (cc ^^^ 1) (o + 4), .b T]

/-- The size of a test's branch. -/
def xbSz (sh : Bool) : Nat := if sh then 2 else 4

/-- `ldrb rd, [rb, ri]`. -/
def ldbI (rd rb ri : LowReg) : Instr := .memReg .ldrb rd rb ri

/-- An island's padding: `mov r8, r8` when `pad`. -/
def islPad (pad : Bool) : List Instr := if pad then [.movHi 8 8] else []

section emit
variable (cE : A → CalleeS) (bE : Bk → BlockS)

def Op.pieces : Op A Bk → List Piece
  | .call a as => [.seq (ldsEmit as), .call (cE a).entry]
  | .blk b as => [.seq (ldsEmit as), .seq (bE b).g]
  | .spill r o => [.seq [.strSp r (BitVec.ofNat 8 (o / 4))]]
  | .drop _ _ => []
  | .ld r l => [.seq (l.emit r)]
  | .pub g => [.seq g]
  | .keep _ => []
  | .ldb rd rb ri => [.seq [ldbI rd rb ri]]
  | .isl pad n => [.over (islPad pad) n]

def Op.size (x : Op A Bk) : Nat := piecesSize (x.pieces cE bE)

/-- Code size of a program. -/
def Prog.size : Prog A Bk → Nat
  | .nil => 0
  | .op x k => x.size cE bE + k.size
  | .loop c n b k => seqSize (loopHead c n) + b.size + seqSize (loopDec c) + 4 + k.size
  | .sel w i p₀ p₁ k => seqSize (selHead w i) + 4 + p₀.size + 2 + p₁.size + 2 + k.size
  | .xit g s _ sh _ k => xitSz g s + xbSz sh + k.size
  | .hd b h k => b.size + (if h.isNil then 0 else 2) + h.size + k.size
  | .wh _ b k => b.size + 2 + k.size

/-- **The code of a program at offset `o`**, with the exits `J` of the enclosing constructs, as
pieces. Branch and call immediates follow from `o` and the sizes, as the assembler places them. -/
def Prog.emit : List Nat → Nat → Prog A Bk → List Piece
  | _, _, .nil => []
  | J, o, .op x k => x.pieces cE bE ++ k.emit J (o + x.size cE bE)
  | J, o, .loop c n b k =>
    let ob := o + seqSize (loopHead c n)
    let oe := ob + b.size cE bE + seqSize (loopDec c)
    [.seq (loopHead c n)] ++ b.emit [] ob ++ [.seq (loopDec c), .bcond EQ (oe + 4), .b ob] ++
      k.emit J (oe + 4)
  | J, o, .sel w i p₀ p₁ k =>
    let o₀ := o + seqSize (selHead w i) + 4
    let o₁ := o₀ + p₀.size cE bE + 2
    let oo := o₁ + p₁.size cE bE + 2
    [.seq (selHead w i), .bcond NE (o + seqSize (selHead w i) + 4), .b o₁] ++ p₀.emit [] o₀ ++
      [.b oo] ++ p₁.emit [] o₁ ++ [.b oo] ++ k.emit J oo
  | J, o, .xit g s cc sh l k =>
    let ob := o + xitSz g s
    xitP g s ++ xitBr cc sh ob (J.getD l 0) ++ k.emit J (ob + xbSz sh)
  | J, o, .hd b h k =>
    let oh := o + b.size cE bE + (if h.isNil then 0 else 2)
    let oj := oh + h.size cE bE
    b.emit (oh :: J) o ++ (if h.isNil then [] else [.b oj]) ++ h.emit J oh ++ k.emit J oj
  | J, o, .wh _ b k =>
    let oe := o + b.size cE bE + 2
    b.emit (oe :: J) o ++ [.b o] ++ k.emit J oe

end emit

/-- The data ranges of the pieces from `o`: the bytes each `b` over an island skips. -/
def pieceDat : Nat → List Piece → List (Nat × Nat)
  | _, [] => []
  | o, .over g n :: ps => (o + 2 + seqSize g, o + 2 + seqSize g + n) :: pieceDat (o + 2 + seqSize g + n) ps
  | o, p :: ps => pieceDat (o + p.size) ps

end M0Crypto.Release.Ed25519CallProg
