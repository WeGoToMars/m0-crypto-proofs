import M0Crypto.Thumb.ReleaseCheck.Ed25519Harness
import M0Crypto.Spec.Ed25519Vectors
import M0Crypto.Release.Ed25519Encode
import M0Crypto.Release.Ed25519Decode
import M0Crypto.Release.Ed25519Comb
import M0Crypto.Release.Ed25519CombDigits
import M0Crypto.Release.Ed25519WnafDigits
import M0Crypto.Release.Ed25519CallProgUnit

/-!
Executable checks of the internal routines of both Ed25519 builds against the value functions of
the mathematics modules (plan phase 5). Tests, not proofs.

Each routine is called at its symbol offset with its arguments in r0-r3 and the internal
convention of `gen_ed25519.py` (r0-r12 scratch, return to LR with SP restored). A case checks
SP, that every read lies in the routine's inputs and outputs, the code and its stack bytes (the generator's
static depth, `asm.stack_depths`), that every write lies in its outputs and those stack bytes,
and the value:

| Routine | Value function |
|---|---|
| `fe_add`, `fe_sub`, `fe_mul`, `fe_sqr` | `+`, `-`, `*`, `x * x` in `Fp` |
| `fe_inv`, `fe_pow` | `x ^ (p - 2)`, `x ^ ((p - 5) / 8)` in `Fp` |
| `fe_canon`, `fe_eq` | `Fp.val`, equality in `Fp` |
| `mp_mul`, `sc_reduce`, `sc_muladd` | `a * b`, `x % L`, `(k a + r) % L` (`Ed25519Barrett`) |
| `sha512_block` | `Spec.Sha512.compress` |
| `sha512_init`, `_update`, `_final` | `Spec.Sha512.sha512` of the whole stream |
| `ge_compress`, `ge_decompress` | `compressCode`, `decodeCode` |
| `sc_recode_comb`, `sbit`, `sc_wnaf` | `digitAt`, `decodeInt` bits, `wnaf` |
| `ge_lookup` | `lookupNiels` |
| `ge_mul_base`, `ge_dsm` | `[e]B`, `[s]B − [h]A` (`mulBase_digitAt`, `dsmRun_wnaf`) by `Spec.scalarMul` |

`ge_mul_base` and `ge_dsm` are compared through the specification, not the L1 loops
`Ed25519Comb.mulBase` and `Ed25519Wnaf.dsmRun`: `Ed25519ScalarMul.mulBase_digitAt` and
`dsmRun_wnaf` equate the loops with `[e]B` and `[s]B − [h]A`, and `Ed25519Bridge.specRep_scalarMul`
and `xy_eq` carry scalar multiples and affine coordinates to `Spec.Ed25519.scalarMul` and `Point.xy`.

Inputs stay in each routine's domain: `sc_recode_comb` and `ge_mul_base` scalars below `2^255`,
`ge_dsm` digits of scalars below `L` (verify reduces both). Aliases are the generator's: field
routines, including `fe_inv` and `fe_pow`, in place, `mp_mul` with `a = b`, `cmov`/`copy` with `src = dst`,
`sc_reduce` with `out = in`. Excluded: `mp_mul` with `dst` on an input (written row by row while
the inputs are read) and `ge_dsm` with `out` on an input (the generator forbids it); the other
routines' callers never overlap outputs and inputs.

`cmov`, `copy`, `zero` and the context of the SHA-512 stream (`N`, `H`, `BUF` between calls)
have no value function; their cases check the generator's documented effect.

Every function has the same offset in both builds (`offsets_same`), so the cases name the
`compact` offsets.
-/

namespace M0Crypto.Thumb.ReleaseCheck.Ed25519

open M0Crypto.Armv6M (Word State Mem)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg (stackOf)
open M0Crypto.Release.Ed25519Field (Fp)
open M0Crypto.Release.Ed25519Bridge (toF)
open M0Crypto.Release.Ed25519EdwardsExtended (Ext)
open M0Crypto.Spec.Ed25519 (p L B)
open M0Crypto.Artifacts.Ed25519Compact

abbrev Cases := List (String × (Unit → Option String))

/-- Call routine `off` with an `n`-byte stack on `m`, reading `ins` and `outs` and writing
`outs`; the final state when the audit holds and `ok` accepts it. -/
def routine (b : Build) (m : Mem) (off n : Nat) (args : List Nat) (ins outs : List (Nat × Nat))
    (ok : State → Bool) : Except String State :=
  match callAt b off args m (ins ++ outs) n with
  | .error e => .error e
  | .ok r =>
    match r.rd <|> (if reg r.final 13 != BitVec.ofNat 32 sp0 then some "SP not restored" else none)
        <|> writesIn r n outs with
    | some e => .error e
    | none => if ok r.final then .ok r.final else .error "value differs from the value function"

def once (e : Except String State) : Option String := match e with
  | .error e => some e
  | .ok _ => none

def fe (m : Mem) (a : Nat) : Fp := toF (valM m a 32)

def ext (m : Mem) (a : Nat) : Ext Fp := ⟨fe m a, fe m (a + 32), fe m (a + 64), fe m (a + 96)⟩

def extEq (E F : Ext Fp) : Bool := decide (E.X = F.X ∧ E.Y = F.Y ∧ E.Z = F.Z ∧ E.T = F.T)

def ra : Nat := 0x20001000
def rb : Nat := 0x20001100
def rc : Nat := 0x20001200
def rd : Nat := 0x20001300

/-! ## Field routines -/

def fieldEdges : List Nat := [0, 1, 2, 19, 38, p - 1, p, p + 1, 2 * p - 1, 2 ^ 255 - 1, 2 ^ 255,
  2 ^ 256 - 38, 2 ^ 256 - 1, 2 ^ 128 - 1]

/-- All edge pairs and 60 pseudo-random pairs, run with distinct buffers. -/
def fieldPairs : List (Nat × Nat) :=
  (fieldEdges.flatMap fun x => fieldEdges.map (x, ·)) ++
  (List.range 60).map fun i => (rndNat 32 (100 + 2 * i), rndNat 32 (101 + 2 * i))

/-- The aliased layouts `(dst, a, b)`, each run on every edge and its mirror and 6 random pairs. -/
def aliasLayouts : List (String × Nat × Nat × Nat) :=
  [("dst = a", ra, ra, rb), ("dst = b", rb, ra, rb), ("a = b", rd, ra, ra), ("all equal", ra, ra, ra),
   ("a in the code", rd, codeBase + ed_d, rb)]

def aliasPairs : List (Nat × Nat) := fieldEdges.zip fieldEdges.reverse ++ (fieldPairs.drop 196).take 6

/-- The case names show the inputs as they are in memory at entry. -/
def fieldCases (b : Build) (name : String) (off n : Nat) (useB : Bool) (f : Fp → Fp → Fp) : Cases :=
  (fieldPairs.map (("distinct", rd, ra, rb), ·) ++
    aliasLayouts.flatMap fun l => aliasPairs.map (l, ·)).zipIdx.map fun (((l, d, a, c), (x, y)), i) =>
    let m := mkMem b [(c, le 32 y), (a, le 32 x), (d, rnd 32 i)]
    (s!"{name} {l} {valM m a 32} {valM m c 32}", fun _ =>
      once <| routine b m off n [d, a, c] ((a, 32) :: if useB then [(c, 32)] else []) [(d, 32)]
        fun s => decide (fe s.mem d = f (fe m a) (fe m c)))

/-- The 14 edges and 120 random values. -/
def canonCases (b : Build) : Cases :=
  (fieldEdges ++ (fieldPairs.drop 196).flatMap fun (x, y) => [x, y]).map fun x => (s!"fe_canon {x}", fun _ =>
    let m := mkMem b [(ra, le 32 x)]
    once <| routine b m fe_canon 4 [ra] [(ra, 32)] [(ra, 32)]
      fun s => valM s.mem ra 32 == (fe m ra).val)

def eqCases (b : Build) : Cases :=
  fieldPairs.map fun (x, y) => (s!"fe_eq {x} {y}", fun _ =>
    let m := mkMem b [(ra, le 32 x), (rb, le 32 y)]
    once <| routine b m fe_eq 4 [rd, ra, rb] [(ra, 32), (rb, 32)] [(rd, 32)]
      fun s => (reg s 0 == 0) == decide (fe m ra = fe m rb))

def powCases (b : Build) : Cases :=
  (fieldEdges ++ (List.range 6).map (rndNat 32 ·)).zipIdx.flatMap fun (x, i) =>
    let d := if i % 2 = 0 then ra else rd
    let m := mkMem b [(ra, le 32 x)]
    [("fe_inv", fe_inv, p - 2), ("fe_pow", fe_pow, (p - 5) / 8)].map fun (name, off, e) =>
      (s!"{name} {x} into {d}", fun _ =>
        once <| routine b m off (stackOf off) [d, ra] [(ra, 32)] [(d, 32)]
          fun s => decide (fe s.mem d = fe m ra ^ e))

/-! ## Word routines -/

def wordCases (b : Build) : Cases :=
  [2, 8, 16, 24, 32].flatMap fun w => (List.range 6).flatMap fun i =>
    let src := rnd (4 * w) (200 + i)
    let dst := rnd (4 * w) (300 + i)
    let mask := if i % 2 = 0 then 0 else 0xffffffff
    let m := mkMem b [(ra, dst), (rb, src)]
    [(s!"cmov {w} {mask}", fun _ => once <| routine b m cmov 4 [ra, rb, w, mask]
        [(ra, 4 * w), (rb, 4 * w)] [(ra, 4 * w)]
        fun s => readM s.mem ra (4 * w) == if mask = 0 then dst else src),
     (s!"copy {w}", fun _ => once <| routine b m copy 4 [ra, rb, w] [(rb, 4 * w)] [(ra, 4 * w)]
        fun s => readM s.mem ra (4 * w) == src),
     (s!"cmov {w} {mask} src = dst", fun _ => once <| routine b m cmov 4 [ra, ra, w, mask]
        [(ra, 4 * w)] [(ra, 4 * w)] fun s => readM s.mem ra (4 * w) == dst),
     (s!"copy {w} src = dst", fun _ => once <| routine b m copy 4 [ra, ra, w] [(ra, 4 * w)] [(ra, 4 * w)]
        fun s => readM s.mem ra (4 * w) == dst),
     (s!"zero {w}", fun _ => once <| routine b m zero 4 [ra, w] [] [(ra, 4 * w)]
        fun s => readM s.mem ra (4 * w) == List.replicate (4 * w) 0)]

/-! ## SHA-512 -/

/-- The 64-byte state: eight 64-bit words, each little endian (low word first). -/
def hWords (m : Mem) (a : Nat) : Array Spec.Sha512.Word :=
  ((List.range 8).map fun j => BitVec.ofNat 64 (valM m (a + 8 * j) 8)).toArray

def hBytes (h : Array Spec.Sha512.Word) : List Byte := h.toList.flatMap fun w => le 8 w.toNat

def blockCases (b : Build) : Cases :=
  ((List.range 40).map fun i => (rnd 64 (400 + i), rnd 128 (500 + i))) ++
    [(hBytes Spec.Sha512.H0, List.replicate 128 0), (List.replicate 64 0xff, List.replicate 128 0xff)]
  |>.map fun (h, blk) => (s!"sha512_block {h} {blk}", fun _ =>
    let m := mkMem b [(ra, h), (rb, blk)]
    once <| routine b m sha512_block 208 [ra, rb] [(ra, 64), (rb, 128)] [(ra, 64)]
      fun s => readM s.mem ra 64 == hBytes (Spec.Sha512.compress (hWords m ra) (readM m rb 128)))

/-- The context after `init` and updates with the bytes `d`: `N`, `H` over the whole blocks, the
tail in `BUF`. -/
def ctxOk (s : State) (ctx : Nat) (d : List Byte) : Bool :=
  let full := d.length / 128 * 128
  valM s.mem ctx 4 == d.length &&
    hWords s.mem (ctx + 4) == Spec.Sha512.hash Spec.Sha512.H0 (d.take full) &&
    readM s.mem (ctx + 68) (d.length - full) == d.drop full

/-- `init`, `update` with each chunk, `final`; the stream's bytes at `src`. -/
def streamCase (b : Build) (chunks : List Nat) (src : Nat) (rs : List (Nat × List Byte)) :
    Option String :=
  let ctx := rc
  let m := mkMem b rs
  let total := chunks.foldl (· + ·) 0
  let d := readM m src total
  let ins := [(ctx, 196), (src, total)]
  let w := [(ctx, 196)]
  let go : Except String (State × Nat) := do
    let s ← routine b m sha512_init 4 [ctx] [] w (ctxOk · ctx [])
    chunks.foldlM (fun (s, k) c => do
      let s ← routine b s.mem sha512_update 224 [ctx, src + k, c] ins w (ctxOk · ctx (d.take (k + c)))
      pure (s, k + c)) (s, 0)
  match go with
  | .error e => some e
  | .ok (s, _) => once <| routine b s.mem sha512_final 220 [ctx, rd] ins ((rd, 64) :: w)
      fun t => readM t.mem rd 64 == Spec.Sha512.sha512 d

def streams : List (List Nat) :=
  [[0], [3], [111], [112], [127], [128], [129], [239], [240], [255], [256], [64, 64], [1, 127, 1],
   [100, 100, 100], [0, 200, 0, 56], [300], [5, 250, 130]]

def streamCases (b : Build) : Cases :=
  (streams.zipIdx.map fun (cs, i) => (s!"sha512 stream {cs}", fun _ =>
    let n := cs.foldl (· + ·) 0
    streamCase b cs (ra + i % 4) [(ra + i % 4, rnd n (600 + i))])) ++
  [("sha512 stream from the code", fun _ => streamCase b [70, 200] (codeBase + 1) [])]

/-! ## Scalars -/

def wideEdges (n : Nat) : List Nat :=
  [0, 1, 2 ^ (32 * n) - 1, 2 ^ (32 * n - 1), L - 1, L, 2 ^ 252, 2 ^ 255 - 1, 2 ^ 512 / L]

def mpCases (b : Build) : Cases :=
  [8, 9].flatMap fun n =>
    let xs := wideEdges n |>.map (· % 2 ^ (32 * n))
    ((xs.flatMap fun x => xs.map (x, ·)) ++
      (List.range 64).map fun i => (rndNat (4 * n) (700 + i), rndNat (4 * n) (800 + i))).zipIdx.map
    fun ((x, y), i) =>
      let bb := if i % 3 = 2 then codeBase + ed_l9 else rb
      let aa := ra
      let bb := if i % 3 = 1 then aa else bb
      let m := mkMem b [(ra, le (4 * n) x), (rb, le (4 * n) y)]
      (s!"mp_mul {n} {valM m aa (4 * n)} {valM m bb (4 * n)} b at {bb}", fun _ =>
        once <| routine b m mp_mul 24 [rd, aa, bb, n] [(aa, 4 * n), (bb, 4 * n)] [(rd, 8 * n)]
          fun s => valM s.mem rd (8 * n) == valM m aa (4 * n) * valM m bb (4 * n))

def scalarEdges : List Nat := [0, 1, L - 1, L, L + 1, 2 ^ 252, 2 ^ 255 - 1, 2 ^ 256 - 1]

def reduceEdges : List Nat := [0, 1, L - 1, L, L + 1, 2 * L, 3 * L - 1, 3 * L, 2 ^ 252, 2 ^ 255 - 1,
  2 ^ 256 - 1, L * L, L * 2 ^ 256 + L - 1, 2 ^ 512 - 1, 2 ^ 512 - L, 2 ^ 512 / L * L, 2 ^ 511]

/-- Into a separate buffer, and the edges with `out = in`. -/
def reduceCases (b : Build) : Cases :=
  ((reduceEdges ++ (List.range 200).map fun i => rndNat 64 (900 + i)).map (rd, ·) ++
    reduceEdges.map (ra, ·)).map fun (o, x) => (s!"sc_reduce {x}{if o = ra then " out = in" else ""}", fun _ =>
    let m := mkMem b [(ra, le 64 x)]
    once <| routine b m sc_reduce 252 [o, ra] [(ra, 64)] [(o, 32)]
      fun s => valM s.mem o 32 == x % L)

def muladdCases (b : Build) : Cases :=
  ((scalarEdges.flatMap fun k => scalarEdges.flatMap fun a => [0, L - 1, 2 ^ 256 - 1].map (k, a, ·)) ++
    (List.range 30).map fun i => (rndNat 32 (1100 + i), rndNat 32 (1200 + i), rndNat 32 (1300 + i))).map
  fun (k, a, r) => (s!"sc_muladd {k} {a} {r}", fun _ =>
    let m := mkMem b [(ra, le 32 k), (rb, le 32 a), (rc, le 32 r)]
    once <| routine b m sc_muladd 328 [rd, ra, rb, rc] [(ra, 32), (rb, 32), (rc, 32)] [(rd, 32)]
      fun s => valM s.mem rd 32 == (k * a + r) % L)

/-! ## Encoding and decoding -/

/-- `[k]B` scaled by `λ` (any projective representative). -/
def scaled (k lam : Nat) : List Byte :=
  let P := Spec.Ed25519.scalarMul k B
  [P.X, P.Y, P.Z, P.T].flatMap fun c => le 32 (c * lam % p)

def compressCases (b : Build) : Cases :=
  (((List.range 8).map fun i => scaled (rndNat 32 (1400 + i)) (rndNat 32 (1500 + i))) ++
    [scaled 0 1, le 128 0, [B.X, B.Y + p, 1 + p, B.T].flatMap (le 32), rnd 128 1600, rnd 128 1601]).zipIdx.map fun (pt, i) => (s!"ge_compress {pt}", fun _ =>
    let m := mkMem b [(rb, pt)]
    let out := ra + i % 4
    once <| routine b m ge_compress (stackOf ge_compress) [out, rb] [(rb, 128)] [(out, 32)]
      fun s => readM s.mem out 32 ==
        Spec.Ed25519.encodeInt (Release.Ed25519Encode.compressCode (ext m rb)))

def decompressCases (b : Build) : Cases :=
  let pts := (List.range 6).map fun i => Spec.Ed25519.encodePoint (Spec.Ed25519.scalarMul (rndNat 32 (1700 + i)) B)
  (pts ++ pts.map (fun e => e.set 31 (e[31]! ^^^ 0x80)) ++
    [Spec.Ed25519.identity, Spec.Ed25519.identityPlusP, Spec.Ed25519.order2,
     le 32 (2 ^ 256 - 1), le 32 p, le 32 2, le 32 (1 + 2 ^ 255), le 32 (2 ^ 255 - 1)] ++
    (List.range 4).map fun i => rnd 32 (1800 + i)).zipIdx.map fun (enc, i) =>
    (s!"ge_decompress {enc}", fun _ =>
    let src := rb + i % 4
    let m := mkMem b [(src, enc)]
    once <| routine b m ge_decompress 660 [ra, src] [(src, 32)] [(ra, 128)] fun s =>
      let n := valM m src 32
      match Release.Ed25519Decode.decodeCode (n % 2 ^ 255) (n / 2 ^ 255) with
      | none => reg s 0 == 1
      | some E => reg s 0 == 0 && extEq (ext s.mem ra) E)

/-! ## Recodings -/

def combScalars : List Nat :=
  [0, 1, 2, L - 1, L, L + 1, 2 ^ 252, 2 ^ 254, 2 ^ 255 - 1] ++ (List.range 60).map fun i => rndNat 32 (1900 + i) % 2 ^ 255

def recodeCases (b : Build) : Cases :=
  combScalars.zipIdx.map fun (e, i) => (s!"sc_recode_comb {e}", fun _ =>
    let src := rb + i % 4
    let out := ra + i % 3
    let m := mkMem b [(src, le 32 e)]
    once <| routine b m sc_recode_comb 44 [out, src] [(src, 32)] [(out, 64)] fun s =>
      readM s.mem out 64 == (List.range 64).map fun q =>
        BitVec.ofInt 8 (Release.Ed25519CombDigits.digitAt b.combs e q + 8))

def sbitCases (b : Build) : Cases :=
  [0, 1, L - 1, L, 2 ^ 252, 2 ^ 255 - 1, rndNat 32 2000].flatMap fun e => (List.range 256).map fun i => (s!"sbit {e} {i}", fun _ =>
    let m := mkMem b [(rb + 1, le 32 e)]
    once <| routine b m sbit 4 [rb + 1, i] [(rb + 1, 32)] [] fun s => (reg s 0).toNat == e / 2 ^ i % 2)

def wnafCases (b : Build) : Cases :=
  ([3, 5].flatMap fun w => combScalars.take 40 |>.map (w, ·)) ++
    ([2, 4, 6, 7, 8].flatMap fun w => [L - 1, 2 ^ 255 - 1, rndNat 32 2100 % 2 ^ 255].map (w, ·))
  |>.map fun (w, k) => (s!"sc_wnaf {w} {k}", fun _ =>
    let m := mkMem b [(rb, le 32 k)]
    once <| routine b m sc_wnaf 40 [ra, rb, w] [(rb, 32)] [(ra, 256)] fun s =>
      readM s.mem ra 256 == (List.range 256).map fun i =>
        BitVec.ofInt 8 (Release.Ed25519WnafDigits.wnaf w k i))

/-! ## Point routines -/

def nielsAt (m : Mem) (a : Nat) : Release.Ed25519Formulas.Niels Fp := ⟨fe m a, fe m (a + 32), fe m (a + 64)⟩

def lookupCases (b : Build) : Cases :=
  ((List.range b.combs).map (codeBase + ed_comb + 768 * ·) ++ [rb]).flatMap fun row =>
    ((List.range 17).map fun j => Int.ofNat j - 8).map fun δ => (s!"ge_lookup {row} {δ}", fun _ =>
    let m := mkMem b [(rb, rnd 768 2200)]
    once <| routine b m ge_lookup 64 [ra, row, (BitVec.ofInt 32 δ).toNat] [(row, 768)] [(ra, 128)]
      fun s => let N := nielsAt s.mem ra
        let E := Release.Ed25519Comb.lookupNiels (fun k => nielsAt m (row + 96 * k)) δ
        decide (N.ypx = E.ypx ∧ N.ymx = E.ymx ∧ N.xy2d = E.xy2d))

/-- `(X / Z, Y / Z)` of a point with `Z ≠ 0`, as the canonical values of `Spec.Point.xy`. -/
def affine (X Y Z : Fp) : Nat × Nat := ((X * Z ^ (p - 2)).val, (Y * Z ^ (p - 2)).val)

def mulBaseCases (b : Build) : Cases :=
  ([0, 1, 2, 8, L - 1, L, L + 1, 2 ^ 252, 2 ^ 255 - 1] ++ (List.range 2).map fun i => rndNat 32 (2300 + i) % 2 ^ 255).map
  fun e => (s!"ge_mul_base {e}", fun _ =>
    let m := mkMem b [(rb, le 32 e)]
    once <| routine b m ge_mul_base 752 [ra, rb] [(rb, 32)] [(ra, 128)] fun s =>
      let E := ext s.mem ra
      decide (E.Z ≠ 0 ∧ E.X * E.Y = E.Z * E.T) && affine E.X E.Y E.Z == (Spec.Ed25519.scalarMul e B).xy)

def dsmCases (b : Build) : Cases :=
  [(0, 0, 3), (1, 0, 5), (0, 1, 7), (L - 1, L - 1, 9), (2 ^ 252, 2 ^ 252, 11), (rndNat 32 2400 % L, rndNat 32 2401 % L, 0)].map
  fun (sc, h, k) => (s!"ge_dsm {sc} {h} [{k}]B", fun _ =>
    let A := scaled k (rndNat 32 (2500 + k))
    let dig (w x : Nat) := (List.range 256).map fun i => BitVec.ofInt 8 (Release.Ed25519WnafDigits.wnaf w x i)
    let m := mkMem b [(rb, dig 5 sc), (rc, dig 3 h), (rd, A)]
    once <| routine b m ge_dsm 840 [ra, rb, rc, rd] [(rb, 256), (rc, 256), (rd, 128)] [(ra, 96)] fun s =>
      let A' : Spec.Ed25519.Point := ⟨p - (fe m rd).val, (fe m (rd + 32)).val, (fe m (rd + 64)).val,
        p - (fe m (rd + 96)).val⟩
      let want := Spec.Ed25519.add (Spec.Ed25519.scalarMul sc B) (Spec.Ed25519.scalarMul h A')
      decide (fe s.mem (ra + 64) ≠ 0) && affine (fe s.mem ra) (fe s.mem (ra + 32)) (fe s.mem (ra + 64)) == want.xy)

/-! ## Non-vacuity: a wrong value function, a smaller stack and a narrower output are rejected -/

def routineGuards (b : Build) : Option String :=
  let m := mkMem b [(ra, rnd 32 1), (rb, rnd 32 2)]
  let mul (f : Fp → Fp → Fp) (n w : Nat) := routine b m fe_mul n [rd, ra, rb] [(ra, 32), (rb, 32)] [(rd, w)]
    fun s => decide (fe s.mem rd = f (fe m ra) (fe m rb))
  match mul (· * ·) 148 32, mul (fun x y => x * y + 1) 148 32, mul (· * ·) 144 32, mul (· * ·) 148 31 with
  | .ok _, .error _, .error _, .error _ => none
  | _, _, _, _ => some "routine check accepts a wrong run"

def routineCases (b : Build) : Cases :=
  fieldCases b "fe_add" fe_add 4 true (· + ·) ++ fieldCases b "fe_sub" fe_sub 4 true (· - ·) ++
  fieldCases b "fe_mul" fe_mul 148 true (· * ·) ++ fieldCases b "fe_sqr" fe_sqr 148 false (fun x _ => x * x) ++
  canonCases b ++ eqCases b ++ powCases b ++ wordCases b ++ blockCases b ++ streamCases b ++
  mpCases b ++ reduceCases b ++ muladdCases b ++ compressCases b ++ decompressCases b ++
  recodeCases b ++ sbitCases b ++ wnafCases b ++ lookupCases b ++ mulBaseCases b ++ dsmCases b

end M0Crypto.Thumb.ReleaseCheck.Ed25519
