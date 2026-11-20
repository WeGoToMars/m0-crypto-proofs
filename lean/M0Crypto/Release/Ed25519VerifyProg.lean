import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.Ed25519GeProg
import M0Crypto.Release.Ed25519FeEq
import M0Crypto.Release.X25519Bytes

/-!
# Callee interfaces and frame for Ed25519 verification

The stitched proof uses the interfaces of decompression, scalar recoding and
double-scalar multiplication. The inline blocks load the signature scalar at
any alignment and subtract the group order for the canonical scalar check.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Word Reg LowReg)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg (FA faS)
open M0Crypto.Release.Ed25519FeEq (eqS)
open M0Crypto.Release.X25519Bytes (loadLe32)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_verify ge_decompress sc_wnaf ge_dsm ed_l9)
open M0Crypto.Artifacts.Ed25519Compact (vf_body vf_done)

/-! ## Callees -/

/-- `ge_decompress(r0, r1)`: 32 bytes at `r1` (any alignment) to a point at `r0`, as four field
elements; the status is `r0`. -/
def ioDec : Iface :=
  { ins := [(1, 0, .raw (.k 32))], outs := (List.range 4).map fun j => (0, 32 * j, .fe),
    wr := [⟨0, 0, .k 128⟩], rd := [⟨1, 0, .k 32⟩], al := [0] }

/-- `sc_wnaf(r0, r1, w)`: the 256 width-`w` digits at `r0` of the scalar below `2^255` at `r1`. -/
def ioWnaf (w : Nat) : Iface :=
  { ins := [(1, 0, .view .cl)], outs := [(0, 0, .bytes 256)], wr := [⟨0, 0, .k 256⟩],
    rd := [⟨1, 0, .k 32⟩], al := [0], kreq := [(2, w)], apt := [(⟨0, 0, .k 256⟩, ⟨1, 0, .k 32⟩)] }

/-- `ge_dsm(r0, r1, r2, r3)`: `(X : Y : Z)` at `r0` from the digits at `r1` (of `B`) and `r2` (of
`−A`) and the point `A` at `r3`. -/
def ioDsm : Iface :=
  { ins := [(1, 0, .view (.bytes 256)), (2, 0, .view (.bytes 256))] ++
      (List.range 4).map (fun j => (3, 32 * j, In.view .fe)),
    outs := (List.range 3).map fun j => (0, 32 * j, .fe), wr := [⟨0, 0, .k 96⟩],
    rd := [⟨1, 0, .k 256⟩, ⟨2, 0, .k 256⟩, ⟨3, 0, .k 128⟩], al := [0, 1, 2, 3] }

/-- The entry's callees: sign's SHA-512 and reduction (`e`), and the verify-only ones. -/
inductive VA where
  | e (a : EA) | dec | wnaf (w : Nat) | dsm | f (a : FA) | eq
  deriving DecidableEq

def vaS : VA → CalleeS
  | .e a => eaS a
  | .dec => calleeAt ge_decompress ioDec [0, 1]
  | .wnaf w => calleeAt sc_wnaf (ioWnaf w) [0, 1, 2]
  | .dsm => calleeAt ge_dsm ioDsm [0, 1, 2, 3]
  | .f a => faS a
  | .eq => eqS

/-! ## The frame -/

/-- `emit_verify`'s frame, in `Frame.alloc` order, and its aliases. -/
def SIG : Nat := 0
def MSG : Nat := 4
def LEN : Nat := 8
def PK : Nat := 12
def SB : Nat := 16
def PA : Nat := 112
def ENC : Nat := 240
def DH : Nat := 368
def U : Nat := 624
def SS : Nat := SB
def HH : Nat := 48
def HD : Nat := U
def DS : Nat := U
def TMP : Nat := 656
def CTX : Nat := 688

/-! ## Inline blocks -/

/-- `load_bytes32(SS, r2)`: the eight words of `s` at any alignment into `SS`. -/
def loadSG : List Instr :=
  (List.range 8).flatMap fun i => loadLe32 4 3 2 (4 * i) ++ [.strSp 4 (BitVec.ofNat 8 ((SS + 4 * i) / 4))]

/-- Word `i` of `r1 − r2` into `r3`, with the subtraction `op`. -/
def ltW (op : Instr) (i : Nat) : List Instr :=
  [.memImm .ldr 4 1 (BitVec.ofNat 5 i), .memImm .ldr 5 2 (BitVec.ofNat 5 i), op,
   .memImm .str 4 3 (BitVec.ofNat 5 i)]

/-- `r1 − r2` over eight words into `r3`; the carry is `r1 ≥ r2`. -/
def ltG : List Instr := ltW (.subReg 4 4 5) 0 ++ (List.range 7).flatMap fun i => ltW (.dp .sbcs 4 5) (i + 1)

def ioLoadS : Iface :=
  { ins := [(2, 0, .raw (.k 32))], outs := [(13, SS, .bytes 32)], wr := [⟨13, SS, .k 32⟩],
    rd := [⟨2, 0, .k 32⟩], al := [13], apt := [(⟨13, SS, .k 32⟩, ⟨2, 0, .k 32⟩)] }

/-- The difference is scratch, written but no output: `r3` apart from both operands. -/
def ioLt : Iface :=
  { ins := [(1, 0, .view (.bytes 32)), (2, 0, .raw (.k 32))], outs := [],
    wr := [⟨3, 0, .k 32⟩], rd := [⟨1, 0, .k 32⟩, ⟨2, 0, .k 32⟩], al := [1, 2, 3],
    apt := [(⟨3, 0, .k 32⟩, ⟨1, 0, .k 32⟩), (⟨3, 0, .k 32⟩, ⟨2, 0, .k 32⟩)] }

inductive VB where
  | loadS | lt
  deriving DecidableEq

def vbS : VB → BlockS
  | .loadS => ⟨ioLoadS, loadSG, [2, 13]⟩
  | .lt => ⟨ioLt, ltG, [1, 2, 3]⟩

/-! ## The geometry -/

/-- `sig` (64 bytes), `msg` (`len` bytes), `pk` (32 bytes), all read at any alignment, and `L`
(32 bytes from `m0c_ed_l9`) a code buffer. -/
def verifyGeo : Geo :=
  { N := stackOf ed25519_verify - Ed25519.savedBytes,
    top := ((fnAt ed25519_verify).map (·.own)).getD 0 - Ed25519.savedBytes,
    xs := [⟨.k 64, false, true, false⟩, ⟨.p 0, false, true, false⟩, ⟨.k 32, false, true, false⟩,
      ⟨.k 32, false, true, true⟩],
    cs := footprint ed25519_verify, pm := [2 ^ 32 - 65], cd := [(3, ed_l9)] }

/-- The registers at the body's start: the four arguments and `sp`. -/
def verifyσ : List (Reg × SV) := [(0, .ext 0 0), (1, .ext 1 0), (2, .prm 0), (3, .ext 2 0), (13, .sp 0)]

def verifyBodyBytes : Nat := vf_done - vf_body

def stE : St := { Γ := [], σ := verifyσ, X := [] }

end M0Crypto.Release.Ed25519VerifyProg
