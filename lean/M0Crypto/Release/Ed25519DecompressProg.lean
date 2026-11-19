import M0Crypto.Release.Ed25519DecompressVal
import M0Crypto.Release.Ed25519FeEq
import M0Crypto.Release.X25519Bytes

/-!
# The straight-line parts of `m0c_ge_decompress`

`m0c_ge_decompress(r0 = out, r1 = 32 bytes)` (`gen_ed25519.py`, `emit_decompress`) between its
branches is seven straight lines (`seg0`–`seg6`): the spill of `out` and the load block (the
bytes into `Y`, bit 255 into `SIGN`); the field operations up to the first `fe_eq`; the second
candidate test; the `sqrt(−1)` fix-up; the canonical form of `x`; the negation; the output. The
field operations are `fragC` fragments, whose operands load frame slots, `out` and the code
constants of `Ed25519DecompressVal`. The branches, the tests and the `r0` status are not here.

The callee's geometry is `dcGeo`, that of any `CalleeP` `dcQ io P` (`dcQ_geo`): `out` written,
the input bytes read at any alignment, and the 160 constant bytes from `m0c_ed_zero` a code
buffer. `seg_pieces` and `seg_bok` decide each line's bytes at its offset in both builds;
`f1_terms` and `f2_terms` give the symbolic values of the field fragments.
-/

namespace M0Crypto.Release.Ed25519DecompressProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeProg
open M0Crypto.Release.Ed25519FragC
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519Curve (d)
open M0Crypto.Release.Ed25519DecompressVal (cZero cOne cD cSqrt)
open M0Crypto.Release.Ed25519FePow (powQ paS)
open M0Crypto.Release.Ed25519FeEq (eqS)
open M0Crypto.Release.Ed25519FeCanon (canonS)
open M0Crypto.Release.X25519Bytes (loadLe32)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (ge_decompress ed_zero)
open M0Crypto.Artifacts.Ed25519Compact (dc_body dc_y_test dc_first_candidate dc_first_status dc_second_candidate dc_second_status dc_sqrt_fix dc_canon_x dc_zero_test dc_negate_x dc_output dc_success)

/-! ## Callees and blocks -/

inductive DA where
  | f (a : FA) | pow | eq | canon | copy
  deriving DecidableEq

/-- The field callees, `fe_pow` (the decompression power), `fe_eq`, `fe_canon` and `copy`. -/
def daS : DA → CalleeS
  | .f a => faS a
  | .pow => powQ.s
  | .eq => eqS
  | .canon => canonS
  | .copy => paS .copyOut

theorem daS_f (a : FA) : daS (.f a) = faS a := rfl

/-- The frame (`Frame.alloc` order) and its size. -/
def OUT : Nat := 0
def SIGN : Nat := 4
def Y : Nat := 8
def YY : Nat := 40
def U : Nat := 72
def V : Nat := 104
def X2 : Nat := 136
def X : Nat := 168
def T : Nat := 200
def TMP : Nat := 232
def V3 : Nat := 264
def TOP : Nat := 296

/-- Bit 255 off `Y`'s word 7 into `SIGN`. -/
def maskG : List Instr :=
  [.ldrSp 4 (BitVec.ofNat 8 ((Y + 28) / 4)), .lsrImm 5 4 31, .strSp 5 (BitVec.ofNat 8 (SIGN / 4)),
   .lslImm 4 4 1, .lsrImm 4 4 1, .strSp 4 (BitVec.ofNat 8 ((Y + 28) / 4))]

/-- `mov r2, r1; load_bytes32(Y, r2)` and the mask. -/
def loadG : List Instr :=
  .movHi 2 1 :: ((List.range 8).flatMap fun i =>
    loadLe32 4 3 2 (4 * i) ++ [.strSp 4 (BitVec.ofNat 8 ((Y + 4 * i) / 4))]) ++ maskG

/-- The input's bytes at any alignment, apart from `Y`, which is written before the last read;
`Y` and `SIGN` written. -/
def ioLoad : Iface :=
  { ins := [(1, 0, .raw (.k 32))], outs := [(13, Y, .fe), (13, SIGN, .bytes 4)],
    wr := [⟨13, SIGN, .k 4⟩, ⟨13, Y, .k 32⟩], rd := [⟨1, 0, .k 32⟩, ⟨13, Y, .k 32⟩], al := [13],
    apt := [(⟨13, Y, .k 32⟩, ⟨1, 0, .k 32⟩)] }

inductive DB where
  | load
  deriving DecidableEq

def dbS : DB → BlockS
  | .load => ⟨ioLoad, loadG, [1, 13]⟩

/-! ## The geometry -/

/-- `out` (written, aligned), the input bytes (read, any alignment). -/
def dcXr : List (Reg × XInfo) := [(0, ⟨.k 128, true, false, true⟩), (1, ⟨.k 32, false, true, false⟩)]

/-- The callee with interface `io` and body `P`; the constants are code buffer `2`. -/
def dcQ (io : Iface) (P : Prog DA DB) : CalleeP DA DB :=
  ⟨calleeAt ge_decompress io [0, 1], P, TOP, dcXr, [], [(ed_zero, 160)], []⟩

def dcGeo : Geo :=
  { N := stackOf ge_decompress - 4, top := TOP,
    xs := [⟨.k 128, true, false, true⟩, ⟨.k 32, false, true, false⟩, ⟨.k 160, false, true, true⟩],
    cs := footprint ge_decompress, cd := [(2, ed_zero)] }

theorem dcQ_geo (io : Iface) (P : Prog DA DB) : (dcQ io P).geo = dcGeo := rfl

/-- The registers at the body's start. -/
theorem dcQ_st0 (io : Iface) (P : Prog DA DB) :
    (dcQ io P).st0 = { Γ := [], σ := [(0, .ext 0 0), (1, .ext 1 0), (13, .sp 0)], X := [] } := rfl

/-! ## The straight lines -/

section
open Op Ld

/-- The code constants: buffer `2` at `e`, by the literal at `imm`. -/
def cst (e imm : Nat) : Ld := .C 2 e imm

/-- `u = y² − 1`, `v = y² d + 1`, `v³`, `u v⁷`. -/
def F1 : List FOp :=
  [⟨.sqr, S YY, S Y, .K 0⟩, ⟨.sub, S U, S YY, cst cOne 77⟩, ⟨.mul, S V, S YY, cst cD 75⟩,
   ⟨.add, S V, S V, cst cOne 73⟩, ⟨.sqr, S V3, S V, .K 0⟩, ⟨.mul, S V3, S V3, S V⟩, ⟨.sqr, S T, S V3, .K 0⟩,
   ⟨.mul, S T, S T, S V⟩, ⟨.mul, S T, S T, S U⟩]

/-- The candidate `x = t v³ u` and `v x²`. -/
def F2 : List FOp :=
  [⟨.mul, S X, S T, S V3⟩, ⟨.mul, S X, S X, S U⟩, ⟨.sqr, S T, S X, .K 0⟩, ⟨.mul, S T, S T, S V⟩]

def F3 : List FOp := [⟨.sub, S X2, cst cZero 44, S U⟩]
def F4 : List FOp := [⟨.mul, S X, S X, cst cSqrt 38⟩]
def F5 : List FOp := [⟨.sub, S X, cst cZero 23, S X⟩]
def F6 : List FOp := [⟨.mul, W OUT 96, S X, S Y⟩]

def eqP (b : Nat) : Op DA DB := call .eq [(0, S TMP), (1, S T), (2, S b)]
def canonP : Op DA DB := call .canon [(0, S X)]

/-- From the body's start to the `y ≥ p` test. -/
def seg0 : Prog DA DB := Prog.ofList [spill 0 OUT, blk .load []]

/-- To the first `fe_eq`: `F1`, the `(p − 5)/8` power, `F2`, `v x² = u`. -/
def seg1 : Prog DA DB :=
  fragC .f F1 (.op (call .pow [(0, S T), (1, S T)]) (fragC .f F2 (.op (eqP U) .nil)))

/-- `v x² = −u`. -/
def seg2 : Prog DA DB := fragC .f F3 (.op (eqP X2) .nil)

/-- `x · sqrt(−1)`. -/
def seg3 : Prog DA DB := fragC .f F4 .nil

/-- `x` canonical. -/
def seg4 : Prog DA DB := .op canonP .nil

/-- `x = −x`, canonical. -/
def seg5 : Prog DA DB := fragC .f F5 (.op canonP .nil)

/-- The output: `x`, `y`, `1`, `x y`. -/
def seg6 : Prog DA DB := Prog.ofList
  [call .copy [(0, W OUT 0), (1, S X), (2, K 8)], call .copy [(0, W OUT 32), (1, S Y), (2, K 8)],
   ld 0 (W OUT 64), ld 1 (cst cOne 14), ld 2 (K 8), call .copy []] |>.seq (fragC .f F6 .nil)

end

/-- The lines at their code offsets. -/
def segs : List (Nat × Prog DA DB) :=
  [(dc_body, seg0), (dc_first_candidate, seg1), (dc_second_candidate, seg2), (dc_sqrt_fix, seg3), (dc_canon_x, seg4), (dc_negate_x, seg5), (dc_output, seg6)]

/-- Where each line ends: a branch, a test block or the status. -/
def segEnds : List Nat := [dc_y_test, dc_first_status, dc_second_status, dc_canon_x, dc_zero_test, dc_output, dc_success]

/-! ## The decided checks, both builds -/

theorem seg_ends : (segs.zip segEnds).all (fun p => p.1.1 + p.1.2.size daS dbS == p.2) = true := by decide +kernel

theorem seg_pieces (b : Build) :
    segs.all (fun p => piecesAt b.bytes p.1 (Prog.emit daS dbS [] p.1 p.2)) = true := by
  cases b <;> (simp only [segs, List.all_cons, List.all_nil, Bool.and_true, piecesAt_eq_scan]; decide +kernel)

theorem seg_bok (b : Build) :
    segs.all (fun p => @Prog.bok _ _ b.codeBytes _ _ daS dbS dcGeo [] p.2 p.1) = true := by
  cases b <;> decide +kernel

theorem dc_cs (b : Build) : rangesSub dcGeo.cs [(0, b.size)] = true ∧ ed_zero + 160 ≤ b.size := by
  cases b <;> decide +kernel

/-! ## The static states along the straight lines -/

/-- Only `sp` known: a line's start after a branch or a test. -/
def rs (st : St) : St := { st with σ := σsp }

def stE : St := { Γ := [], σ := [(0, .ext 0 0), (1, .ext 1 0), (13, .sp 0)], X := [] }
def s0 : St := (seg0.ty daS dbS dcGeo stE).getD stE
def s1 : St := (seg1.ty daS dbS dcGeo (rs s0)).getD stE
def s2 : St := (seg2.ty daS dbS dcGeo (rs s1)).getD stE
def s3 : St := (seg3.ty daS dbS dcGeo (rs s2)).getD stE
/-- The two candidates join before `fe_canon`. -/
def sJ : St := joinSt s1 s3
def s4 : St := (seg4.ty daS dbS dcGeo sJ).getD stE

/-- **The lines type** up to the canonical form, from the body's start through both candidates. -/
theorem segs_ty : seg0.ty daS dbS dcGeo stE = some s0 ∧ seg1.ty daS dbS dcGeo (rs s0) = some s1 ∧
    seg2.ty daS dbS dcGeo (rs s1) = some s2 ∧ seg3.ty daS dbS dcGeo (rs s2) = some s3 ∧
    seg4.ty daS dbS dcGeo sJ = some s4 ∧ (Loc.fr X, Kd.fc) ∈ s4.Γ ∧ (Loc.fr Y, Kd.fe) ∈ s4.Γ := by
  decide +kernel

/-! ## The values of the field fragments -/

/-- The leaves: the frame value at `o`, the constant at `e`. -/
def fr (o : Nat) : Tm := .v (.view (.fr o))
def cv (e : Nat) : Tm := .v (.xf ⟨.ex 2 e, .k 32⟩)

/-- `F1`'s terms at `U`, `V`, `V3`, `T`. -/
def f1T : List Tm :=
  let yy := Tm.mul (fr Y) (fr Y)
  let u := Tm.sub yy (cv cOne)
  let v := Tm.add (.mul yy (cv cD)) (cv cOne)
  let v3 := Tm.mul (.mul v v) v
  [u, v, v3, .mul (.mul (.mul v3 v3) v) u]

/-- `F2`'s terms at `X`, `T`. -/
def f2T : List Tm :=
  let x := Tm.mul (.mul (fr T) (fr V3)) (fr U)
  [x, .mul (.mul x x) (fr V)]

def L1 : FL := ((fresC dcGeo (rs s0) F1).map (·.1)).getD []

/-- The state before the power, after `F1`, and after the power. -/
def sP : St := ((fresC dcGeo (rs s0) F1).map (·.2)).getD stE
def sQ : St := ((Op.call DA.pow [(0, Ld.S T), (1, Ld.S T)] : Op DA DB).ty daS dbS dcGeo sP).getD stE

def L2 : FL := ((fresC dcGeo sQ F2).map (·.1)).getD []

theorem f1_terms : fresC dcGeo (rs s0) F1 = some (L1, sP) ∧
    [Loc.fr U, .fr V, .fr V3, .fr T].map (symL tm0 L1) = f1T := by
  decide +kernel

theorem f2_terms : (Op.call DA.pow [(0, Ld.S T), (1, Ld.S T)] : Op DA DB).ty daS dbS dcGeo sP = some sQ ∧
    (fresC dcGeo sQ F2).map (·.1) = some L2 ∧ [Loc.fr X, .fr T].map (symL tm0 L2) = f2T := by
  decide +kernel

/-- **`F1` in `F_p`**: `decodeCode`'s `u`, `v`, `v³` and `v³ v³ v u`. -/
theorem f1_evF {w : Lf → Fp} {y : Fp} (hy : w (.view (.fr Y)) = y) (h1 : w (.xf ⟨.ex 2 cOne, .k 32⟩) = 1)
    (hd : w (.xf ⟨.ex 2 cD, .k 32⟩) = d) :
    f1T.map (Tm.evF w) =
      [y * y - 1, y * y * d + 1, (y * y * d + 1) * (y * y * d + 1) * (y * y * d + 1),
       (y * y * d + 1) * (y * y * d + 1) * (y * y * d + 1) * ((y * y * d + 1) * (y * y * d + 1) * (y * y * d + 1)) *
         (y * y * d + 1) * (y * y - 1)] := by
  simp only [f1T, fr, cv, List.map, Tm.evF, hy, h1, hd]

/-- **`F2` in `F_p`**: `decodeCode`'s candidate `x = t v³ u` and `x x v`. -/
theorem f2_evF {w : Lf → Fp} {t v3 u v : Fp} (ht : w (.view (.fr T)) = t) (h3 : w (.view (.fr V3)) = v3)
    (hu : w (.view (.fr U)) = u) (hv : w (.view (.fr V)) = v) :
    f2T.map (Tm.evF w) = [t * v3 * u, t * v3 * u * (t * v3 * u) * v] := by
  simp only [f2T, fr, List.map, Tm.evF, ht, h3, hu, hv]

end M0Crypto.Release.Ed25519DecompressProg
