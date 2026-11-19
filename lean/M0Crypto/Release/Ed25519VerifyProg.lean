import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.Ed25519GeProg
import M0Crypto.Release.Ed25519FeEq
import M0Crypto.Release.X25519Bytes

/-!
# The straight-line parts of `m0c_ed25519_verify`

`m0c_ed25519_verify(r0 = sig, r1 = msg, r2 = len, r3 = pk)` (`gen_ed25519.py`, `emit_verify`)
between its tests is five straight lines:

* `seg0`: the spills and `ge_decompress(PA, pk)`;
* `seg1`: `ge_decompress(PR, sig)`;
* `seg2`: `s` from `sig + 32` into `SS` (`loadS`), then `SS − L` into `TMP` (`lt`), with `L` the
  code constant `m0c_ed_l9`;
* `seg3`: `h = SHA-512(R ‖ pk ‖ msg) mod L`, the digits of `s` (width 5) and `h` (width 3),
  `ge_dsm` into `SB = (X : Y : Z)`, then `X = x_R Z`;
* `seg4`: `Y = y_R Z`.

The tests after each line (`r0` status of `ge_decompress` and `fe_eq`, the carry of `lt`), the
verdict and the epilogue are not here. Points cross a call as four field views, as in
`ge_mul_base`. The interfaces of `ge_decompress`, `sc_wnaf` and `ge_dsm` are the ones this
program needs. `seg3` starts from `SS` refined to `.sc` (`scAt`), which the `lt` test justifies
(`Ed25519VerifyBlocks.lt_spec`). `seg_pieces` and `seg_bok` decide each line's bytes at its
offset in both builds, and `segs_ty` types the lines.
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
open M0Crypto.Artifacts.Ed25519Compact (vf_a_status vf_body vf_decode_r vf_hash vf_r_status vf_scalar vf_scalar_branch vf_x_status
  vf_y_scale vf_y_status)

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
def PR : Nat := 240
def DH : Nat := 368
def U : Nat := 624
def SS : Nat := SB
def HH : Nat := 48
def HD : Nat := U
def DS : Nat := U
def T2 : Nat := U
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

/-! ## The straight lines -/

section
open Op Ld

/-- `hash_parts(out, parts)` with the context at `CTX`. -/
def hashAt (out : Nat) (parts : List (Ld × Ld × SV)) : List (Op VA VB) :=
  call (.e .init) [(0, S CTX)] :: go [] parts
where
  go (n : List SV) : List (Ld × Ld × SV) → List (Op VA VB)
    | [] => [call (.e (.final n)) [(0, S CTX), (1, S out)]]
    | (src, len, ℓ) :: ps => call (.e (.update n ℓ)) [(1, src), (2, len), (0, S CTX)] :: go (n ++ [ℓ]) ps

/-- From the body's start to the first status test: the spills and `A` from `pk`. -/
def seg0 : Prog VA VB := Prog.ofList
  [spill 0 SIG, spill 1 MSG, spill 2 LEN, spill 3 PK, call .dec [(0, S PA), (1, W PK 0)]]

/-- `R` from `sig`. -/
def seg1 : Prog VA VB := Prog.ofList [call .dec [(0, S PR), (1, W SIG 0)]]

/-- `s` and `s − L`, whose carry the `blo` tests. -/
def seg2 : Prog VA VB := Prog.ofList
  [blk .loadS [(2, W SIG 32)], ld 1 (S SS), ld 2 (C 3 0 59), ld 3 (S TMP), blk .lt []]

/-- `h`, the digits, `[s]B − [h]A`, and the `X` comparison. -/
def seg3 : Prog VA VB := Prog.ofList <|
  hashAt HD [(W SIG 0, K 32, .k 32), (W PK 0, K 32, .k 32), (W MSG 0, W LEN 0, .prm 0)] ++
  [call (.e .reduce) [(0, S HH), (1, S HD)], call (.wnaf 5) [(0, S DS), (1, S SS), (2, K 5)],
   call (.wnaf 3) [(0, S DH), (1, S HH), (2, K 3)], call .dsm [(0, S SB), (1, S DS), (2, S DH), (3, S PA)],
   call (.f .mul) [(0, S T2), (1, S PR), (2, S (SB + 64))], call .eq [(0, S TMP), (1, S SB), (2, S T2)]]

/-- The `Y` comparison. -/
def seg4 : Prog VA VB := Prog.ofList
  [call (.f .mul) [(0, S T2), (1, S (PR + 32)), (2, S (SB + 64))], call .eq [(0, S TMP), (1, S (SB + 32)), (2, S T2)]]

end

/-- The lines at their code offsets. -/
def segs : List (Nat × Prog VA VB) :=
  [(vf_body, seg0), (vf_decode_r, seg1), (vf_scalar, seg2), (vf_hash, seg3), (vf_y_scale, seg4)]

/-- Where each line ends: a status test, or the `blo` after `lt`. -/
def segEnds : List Nat := [vf_a_status, vf_r_status, vf_scalar_branch, vf_x_status, vf_y_status]

/-! ## The decided checks, both builds -/

/-- The body's start: after `abi_enter` of the frame. -/
theorem body_at : ed25519_verify + seqSize (Ed25519CallProg.abiEnter verifyGeo.top) = vf_body := by decide +kernel

theorem enter_at (b : Build) : seqAt b.bytes ed25519_verify (Ed25519CallProg.abiEnter verifyGeo.top) = true := by
  cases b <;> (rw [seqAt_eq_scan]; decide +kernel)

theorem seg_ends : (segs.zip segEnds).all (fun p => p.1.1 + p.1.2.size vaS vbS == p.2) = true := by decide +kernel

theorem seg_pieces (b : Build) :
    segs.all (fun p => piecesAt b.bytes p.1 (Prog.emit vaS vbS [] p.1 p.2)) = true := by
  cases b <;> (simp only [segs, List.all_cons, List.all_nil, Bool.and_true, piecesAt_eq_scan]; decide +kernel)

theorem seg_bok (b : Build) :
    segs.all (fun p => @Prog.bok _ _ b.codeBytes _ _ vaS vbS verifyGeo [] p.2 p.1) = true := by
  cases b <;> decide +kernel

theorem verify_cs (b : Build) : rangesSub verifyGeo.cs [(0, b.size)] = true ∧ ed_l9 + 32 ≤ b.size := by
  cases b <;> decide +kernel

/-! ## The static states along the straight lines -/

/-- Only `sp` known: a line's start after a test. -/
def rs (st : St) : St := { st with σ := σsp }

/-- The bytes at frame offset `o` refined to a scalar below `L`: the state after the `lt` test
passes. -/
def scAt (o : Nat) (st : St) : St :=
  { st with Γ := st.Γ.map fun p => if p.1 == .fr o && p.2 == .bytes 32 then (p.1, .sc) else p }

def stE : St := { Γ := [], σ := verifyσ, X := [] }
def s0 : St := (seg0.ty vaS vbS verifyGeo stE).getD stE
def s1 : St := (seg1.ty vaS vbS verifyGeo (rs s0)).getD stE
def s2 : St := (seg2.ty vaS vbS verifyGeo (rs s1)).getD stE
def s3 : St := (seg3.ty vaS vbS verifyGeo (scAt SS (rs s2))).getD stE
def s4 : St := (seg4.ty vaS vbS verifyGeo (rs s3)).getD stE

/-- **The lines type** from the body's start, each after its test passes. -/
theorem segs_ty : seg0.ty vaS vbS verifyGeo stE = some s0 ∧ seg1.ty vaS vbS verifyGeo (rs s0) = some s1 ∧
    seg2.ty vaS vbS verifyGeo (rs s1) = some s2 ∧ seg3.ty vaS vbS verifyGeo (scAt SS (rs s2)) = some s3 ∧
    seg4.ty vaS vbS verifyGeo (rs s3) = some s4 ∧ (Loc.fr SS, Kd.bytes 32) ∈ s2.Γ := by
  decide +kernel

end M0Crypto.Release.Ed25519VerifyProg
