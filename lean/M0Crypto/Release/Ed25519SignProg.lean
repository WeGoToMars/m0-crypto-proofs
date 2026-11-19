import M0Crypto.Release.Ed25519CallProgEntry
import M0Crypto.Release.Ed25519CallProgUnit
import M0Crypto.Release.Ed25519Contract

/-!
# `m0c_ed25519_sign` as a call program

The entry's body between `abi_enter` and `abi_leave` (`gen_ed25519.py`, `emit_sign`): four spills
of the arguments, three SHA-512 runs, two reductions, the base multiplication, the compression,
the multiply-add and two stores of 32 bytes to `sig`. The frame layout is `emit_sign`'s
(`Frame.alloc` order); PT shares CTX and KH shares RH, and a write kills the views it overlaps.
The callee interfaces and the two inline blocks are shared with pubkey and verify.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Artifacts.Ed25519Compact

/-! ## Callee interfaces -/

/-- The entry-level callees. A context's stream length is public: `update n ℓ` appends `ℓ` bytes
to a stream of parts `n`, and `final n` ends one. -/
inductive EA where
  | init | update (n : List SV) (ℓ : SV) | final (n : List SV) | reduce | mulBase | compress | muladd
  deriving DecidableEq

/-- A SHA-512 stream counts its bytes in one word. -/
def shaLim : Nat := 2 ^ 32

def ioInit : Iface :=
  { ins := [], outs := [(0, 0, .ctx [])], wr := [⟨0, 0, .k ctxSize⟩], rd := [], al := [0] }

/-- The context is read and written whole, apart from the input; `r2` is the part's length. -/
def ioUpdate (n : List SV) (ℓ : SV) : Iface :=
  { ins := [(0, 0, .view (.ctx n)), (1, 0, .raw (.r 2))], outs := [(0, 0, .ctx (n ++ [ℓ]))],
    wr := [⟨0, 0, .k ctxSize⟩], rd := [⟨1, 0, .r 2⟩, ⟨0, 0, .k ctxSize⟩], al := [0],
    kreqv := [(2, ℓ)], lim := [(n ++ [ℓ], shaLim)], apt := [(⟨0, 0, .k ctxSize⟩, ⟨1, 0, .r 2⟩)] }

def ioFinal (n : List SV) : Iface :=
  { ins := [(0, 0, .view (.ctx n))], outs := [(1, 0, .bytes 64)],
    wr := [⟨0, 0, .k ctxSize⟩, ⟨1, 0, .k 64⟩], rd := [⟨0, 0, .k ctxSize⟩], al := [0, 1],
    lim := [(n, shaLim)], apt := [(⟨0, 0, .k ctxSize⟩, ⟨1, 0, .k 64⟩)] }

/-- `out = f(in)` from `n` bytes at `r1` to `m` bytes of kind `k` at `r0`. -/
def io1 (n : Nat) (ki : Kd) (m : Nat) (ko : Kd) : Iface :=
  { ins := [(1, 0, .view ki)], outs := [(0, 0, ko)], wr := [⟨0, 0, .k m⟩], rd := [⟨1, 0, .k n⟩],
    al := [0, 1] }

/-- `ge_compress`: the output is stored a byte at a time (`store_bytes32`), so it may be unaligned. -/
def ioCompress : Iface := { io1 128 .pt 32 (.bytes 32) with al := [1] }

def ioMuladd : Iface :=
  { ins := [(1, 0, .view .sc), (2, 0, .view (.bytes 32)), (3, 0, .view .sc)],
    outs := [(0, 0, .bytes 32)], wr := [⟨0, 0, .k 32⟩],
    rd := [⟨1, 0, .k 32⟩, ⟨2, 0, .k 32⟩, ⟨3, 0, .k 32⟩], al := [0, 1, 2, 3] }

/-- A callee at offset `o`: entry, transitive footprint and stack depth from the call graph. -/
def calleeAt (o : Nat) (io : Iface) (pub : List Reg) (pn : List PubW := []) : CalleeS :=
  { io, entry := o, code := footprint o, stack := stackOf o,
    pubs := (pub ++ [13]).map .r ++ pn }

def eaS : EA → CalleeS
  | .init => calleeAt sha512_init ioInit [0]
  | .update n ℓ => calleeAt sha512_update (ioUpdate n ℓ) [0, 1, 2] [.n 0]
  | .final n => calleeAt sha512_final (ioFinal n) [0, 1] [.n 0]
  | .reduce => calleeAt sc_reduce (io1 64 (.bytes 64) 32 .sc) [0, 1]
  | .mulBase => calleeAt ge_mul_base (io1 32 .cl 128 .pt) [0, 1]
  | .compress => calleeAt ge_compress ioCompress [0, 1]
  | .muladd => calleeAt sc_muladd ioMuladd [0, 1, 2, 3]

/-! ## Inline blocks -/

inductive EB where
  /-- `clamp(4q)`: prune the 32-byte scalar at frame word `q`; its last word is `ldr`'s `q + 7`. -/
  | clamp (q : Fin 249)
  /-- `store_bytes32(r2, r3)`: 32 bytes from the word-aligned `r3` to `r2`. -/
  | store
  deriving DecidableEq

def clampG (q : Nat) : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 q), .lsrImm 0 0 3, .lslImm 0 0 3, .strSp 0 (BitVec.ofNat 8 q),
   .ldrSp 0 (BitVec.ofNat 8 (q + 7)), .lslImm 0 0 2, .lsrImm 0 0 2, .movImm 1 1, .lslImm 1 1 30,
   .dp .orrs 0 1, .strSp 0 (BitVec.ofNat 8 (q + 7))]

def storeG : List Instr :=
  (List.range 8).flatMap fun i =>
    [.memImm .ldr 1 3 (BitVec.ofNat 5 i), .memImm .strb 1 2 (BitVec.ofNat 5 (4 * i))] ++
    (List.range 3).flatMap fun j =>
      [.lsrImm 1 1 8, .memImm .strb 1 2 (BitVec.ofNat 5 (4 * i + j + 1))]

def ioClamp (off : Nat) : Iface :=
  { ins := [(13, off, .view (.bytes 32)), (13, off + 32, .view (.bytes 32))],
    outs := [(13, off, .cl), (13, off + 32, .bytes 32)],
    wr := [⟨13, off, .k 32⟩],
    rd := [⟨13, off, .k 32⟩], al := [13] }

def ioStore : Iface :=
  { ins := [(3, 0, .view (.bytes 32))], outs := [(2, 0, .bytes 32)], wr := [⟨2, 0, .k 32⟩],
    rd := [⟨3, 0, .k 32⟩], al := [3], eqd := [(2, 3, 32)] }

def ebS : EB → BlockS
  | .clamp q => ⟨ioClamp (4 * q.val), clampG q.val, [13]⟩
  | .store => ⟨ioStore, storeG, [2, 3]⟩

/-! ## The program -/

/-- `emit_sign`'s frame, in `Frame.alloc` order. -/
def SIG := 0
def MSG := 4
def LEN := 8
def SK := 12
def HS := 16
def RH := 80
def RR := 144
def KK := 176
def SS := 208
def RS := 240
def CTX := 272
def PT := CTX
def KH := RH

section
open Op Ld

/-- `hash_parts(out, parts)`; a part is its source, its length and the length's value. -/
def hashParts (out : Nat) (parts : List (Ld × Ld × SV)) : List (Op EA EB) :=
  call .init [(0, S CTX)] :: go [] parts
where
  go (n : List SV) : List (Ld × Ld × SV) → List (Op EA EB)
    | [] => [call (.final n) [(0, S CTX), (1, S out)]]
    | (src, len, ℓ) :: ps => call (.update n ℓ) [(1, src), (2, len), (0, S CTX)] :: go (n ++ [ℓ]) ps

/-- The body of `m0c_ed25519_sign`. The external buffers: `0` is `sig`, `1` the message, `2` `sk`;
public parameter `0` is `n`. -/
def signProg : Prog EA EB := Prog.ofList <|
  [spill 0 SIG, spill 1 MSG, spill 2 LEN, spill 3 SK] ++
  hashParts HS [(W SK 0, K 32, .k 32)] ++ [blk (.clamp ⟨HS / 4, by decide⟩) []] ++
  hashParts RH [(S (HS + 32), K 32, .k 32), (W MSG 0, W LEN 0, .prm 0)] ++
  [call .reduce [(0, S RR), (1, S RH)], call .mulBase [(0, S PT), (1, S RR)],
   call .compress [(0, S RS), (1, S PT)]] ++
  hashParts KH [(S RS, K 32, .k 32), (W SK 32, K 32, .k 32), (W MSG 0, W LEN 0, .prm 0)] ++
  [call .reduce [(0, S KK), (1, S KH)], call .muladd [(0, S SS), (1, S KK), (2, S HS), (3, S RR)],
   blk .store [(2, W SIG 0), (3, S RS)], blk .store [(2, W SIG 32), (3, S SS)]]

end

/-- The registers at the body's start: the four arguments and `sp`. -/
def signσ : List (Reg × SV) := [(0, .ext 0 0), (1, .ext 1 0), (2, .prm 0), (3, .ext 2 0), (13, .sp 0)]

def signSt : St := { Γ := [], σ := signσ, X := [] }

/-- The body's geometry: the window below the saved registers, the frame, the three buffers. -/
def signGeo : Geo :=
  { N := stackOf ed25519_sign - Ed25519.savedBytes,
    top := ((fnAt ed25519_sign).map (·.own)).getD 0 - Ed25519.savedBytes,
    xs := [⟨.k 64, true, false, false⟩, ⟨.p 0, false, true, false⟩, ⟨.k 64, false, true, false⟩],
    cs := footprint ed25519_sign, pm := [2 ^ 32 - 65] }


/-! ## The decided checks, both builds -/

section checks
open M0Crypto.Release.RoutinePieces M0Crypto.Release.Ed25519

/-- The body's start: after `abi_enter` of the frame. -/
def signBody : Nat := ed25519_sign + seqSize (abiEnter signGeo.top)

/-- `abi_leave` after the body: the frame and the deepest callee window. -/
def signLeave : List RoutinePieces.Piece :=
  abiLeave signGeo.top (signGeo.N - signGeo.top) (signBody + signProg.size eaS ebS)

theorem sign_ty : (signProg.ty eaS ebS signGeo signSt).isSome = true := by decide +kernel

theorem sign_bok (b : Build) :
    @Prog.bok _ _ b.codeBytes _ _ eaS ebS signGeo [] signProg signBody = true := by
  cases b <;> decide +kernel

theorem sign_pieces (b : Build) :
    seqAt b.bytes ed25519_sign (abiEnter signGeo.top) = true ∧
    piecesAt b.bytes signBody (Prog.emit eaS ebS [] signBody signProg ++ signLeave) = true := by
  cases b <;> exact ⟨by rw [seqAt_eq_scan]; decide +kernel, by rw [piecesAt_eq_scan]; decide +kernel⟩

end checks

end M0Crypto.Release.Ed25519CallProg
