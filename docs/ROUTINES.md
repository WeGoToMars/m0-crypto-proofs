# Routine and call proofs

Generic tooling for proofs of routines that call other routines, in five files of
`lean/M0Crypto/Release/`. None of it is trusted: no claim mentions it, and the kernel checks every
use. Two rules hold throughout: no hard-coded offsets (offsets come from `piecesAt`), and one
generic lemma per assembly macro.

## The files

| File | What it gives |
|---|---|
| `Footprint.lean` | Footprints: lists of regions `⟨a, n⟩`. `Sep f g` (pairwise apart, no wrap), `Sub f g` (each region of `f` inside one of `g`), `MemEq f m m'` (`m'` equals `m` outside `f`), byte lists `bytesAt`. `fp_simp`, `fp_tac` reduce them to `omega` over `toNat`. |
| `Routine.lean` | The judgments `ReachF` and `ReachFT`, the record `Routine`, its call lemma `Spec`/`SpecT`/`TSpec`, and the rules: `block`, `glue`, `site` (call), `frame` (push/sub … add/pop), counted loops. |
| `RoutinePieces.lean` | A routine's code as a list of `Piece`s (blocks, calls, branches) checked against the bytes at once (`piecesAt`), so a macro lemma takes "these pieces at any offset `o`". Also `siteT`/`site`, `cmp_bne`, `ptrOff`, `Holds`, `site_once`. |
| `RoutineBranch.lean` | Piece rules for `b<cond>` (`branch`), `b` (`jump`) and literal loads into any low register (`lit`), and the flag facts of the compares before them. |
| `ReachTrace.lean` | `ReachT`: `ReachS` with a condition `Φ : List Event → Prop` on the trace. Trace conditions `Tr.is`, `Tr.cat`, `Tr.cond`, `Tr.rep`; `Tr.Uniq`; fragment traces `Tr.HasK`; `blockTr`. |
| `RoutineBlock.lean` | `ReachFT.sglue`: `glue` for a block whose accesses lie in regions given as an expression (a register or a loaded slot) plus a constant, decided by `sglueOk`. `glue_tac` closes the side conditions of `glue` and `sglue` without running the block. `tr_block` and `traceAll_blockTrE` give a block's trace from its registers or atoms. |
| `FrameKeep.lean` | `keep_simp`: rewrites each read of a later memory to the earlier one through every `MemEq` fact in context, with `fp_tac` on the side conditions. |
| `Ed25519FieldSeq.lean` | `fops_run`: a list of field calls on frame slots (`FCall`), one entry per call site, with the slot values after the calls (`fopsVal`) and one frame for all of them; `fopsOk` decides the checks. |

## The judgments

`ReachF base Pc Rd Wr Sp s Q`: the Harvard run of the code bytes from `s` reaches a state in
`Q`, and every step runs at a pc in `Pc`, reads only in `Rd`, writes only in `Wr` and has its SP in
`Sp`. `ReachFT … Q Φ` is the same with the trace in `Φ`. Every rule is proved once in `ReachFT` form;
the `ReachF` rule is that rule with `Φ = fun _ => True`.

The code bytes are a parameter. Every judgment and rule here, and the `Field25519` proofs, take
`B` and its length `BS` from an instance of `CodeBytes B BS` (`Release/CodeBytes.lean`), whose two
arguments are output parameters: each module declares `variable {B} {BS} [CodeBytes B BS]`, and a
judgment written without them takes the instance in scope. The global instance `release` is the
workspace's `Release.B` and `Artifacts.Release.size`, so a single-build asset's proofs are written
and elaborate as before. A proof about another byte list brings its instance into scope with
`letI`, which takes precedence (`Ed25519FieldRoutines`: `letI := Build.compact.codeBytes`).

A `Routine` states what a call lemma needs beyond the common part: `entry`, `code` (its ranges and its
callees'), `stack`, its own `Pre`, its write and read footprints outside its stack window (`wr`,
`rd`), and its result `Post` on the memory and `r0` at return. `Routine.Entry base s` is the common
entry condition (code present, SP aligned with room, LR Thumb and outside `code`, footprints apart
from the code and the window, `Pre`). `Routine.Ret s t` is the common return (pc = LR, SP and
`r4`-`r11` restored, `Post`).

A routine that does not follow the AAPCS lists the registers among `r4`-`r11` it may change in
`clob` (default `[]`); `Ret` keeps the others. The rules for such routines end in `K`
(`ReachFT.push_popK`, `frameK`, `callK`, `siteK`, `RoutinePieces.siteTK`): a caller's continuation
receives `HiK f.clob R u`, `sp` and the high registers outside `f.clob`. The rules without `K` are
their instances for `clob = []` and keep their signatures.

- `f.Spec`: from every `Entry`, `ReachF` to `Ret`, running only `f.code`, writing only the window and
  `wr`, reading only the code, the window and `rd`. Memory outside `wr` is unchanged by the judgment
  itself (`ReachF.memEq`), so no `Post` states it.
- `f.SpecT Φ`: the same with trace condition `Φ base s`.
- `Routine.TSpec f pub`: there is one `T` with `(f i).SpecT fun base s => Tr.is (T base (pub base s))`
  for all `i`. The trace of a call is a function of the code base and the public values `pub`; two
  calls with equal `pub` have equal traces. `h.T` names it as a closed term, so callers never carry a
  hypothesis about a callee's trace.

## A routine spec

1. Define the `Routine`: entry, code (its own ranges and its callees'), stack, `wr`, `rd`, `Post`.
2. Define `pub`, the public values of a call (for example `r0`-`r3`, SP, LR).
3. Open the proof with `trefine Routine.tspec_by (fun _ base s e => ?_) (fun _ _ => ?_)`, which
   leaves the run (its trace condition an unassigned `?Φ base P`) and then its uniqueness.
   `generalize hP : pub base s = P` puts the public values in `P` before the state is used, so
   Lean can only assign `?Φ` from terms in `base` and `P` (a piece that mentions the state fails
   unification at once).
4. `ReachFT.frame` handles `push`/`sub sp` … `add sp`/`pop` and leaves the body; `frame_body` names
   the caller context `F` and the facts `t13`, `tl`, `hc`, `w0`.
5. The body is a chain: `ReachFT.glue` for each glue block, `ReachFT.site` for each `bl`,
   `ReachFT.lit` for literal loads, ending in `ReachT.done` with the `Ret` fields.
6. `uniq_tac` closes the uniqueness goal. `(h.spec ())` is the plain `Spec`.

## A call site

```lean
trefine ReachFT.site (callee_tspec.specT ()) F [] [] [] [] (o := oBl1) rfl bl1_at (pc_at p1)
  (Hi.self _) s1 c1 (by site_tac [t13, tl]) trivial
  (tr_glue p1 [t13, tl, q]) (tr_call [calleePub, t13, tl, q]) fun u1 p1 h1 s1 c1 m1 q1 => ?_
```

The arguments are: the callee's `SpecT`; the caller context; the glue block `g` before the `bl`
and its alignment, write and read lists; the decided piece check; the current pc, high
registers, SP and code; the side conditions `SiteSides` (footprints) and the callee's `Pre`;
the glue trace; the callee trace. The continuation names the return state `u1`, its pc `p1`, high
registers `h1`, SP `s1`, code `c1`, frame `m1` and the callee's `Post` `q1`. `MemEq.grow`/`carry`
move byte facts across calls. Fragments use `RoutinePieces.siteT` with a `siteOk` check instead, so
the site's offset comes from `piecesAt` and is never written by hand.

## Fragments and `ReachT.retrace _ rfl`

A macro that is not a routine ends in its caller's continuation. Its lemma states its public values
outside `Tr.HasK fun Θ => ∀ …`, and the rest inside. The proof is
`Tr.HasK.intro (fun … k => ReachT.retrace ?_ ?_) (fun Ψ hu => ?_)`:

1. the run, built with the rules above, with `?Θ Ψ` assigned piece by piece;
2. `rfl`: the trace condition the run produced equals `?Θ Ψ`. It closes only once every piece is
   assigned from the public values, so this `rfl` is the check that the fragment's trace does not
   depend on the state;
3. `uniq_tac`: `?Θ` keeps uniqueness.

Callers use `(h …).run` and name the trace `(h …).tr`.

## Assets with several builds (Ed25519)

The Ed25519 asset has two builds, `compact` and `fast`. Each claim is one theorem quantified
over `b : Ed25519.Build`, and it must hold for a user who links only build `b`. Three designs
were compared (2026-11-16):

| Design | Trusted lines | Cost | A user who links one build |
|---|---|---|---|
| (a) One artifact holding both units, with unit-relative entry bounds and return addresses (as the Noise asset's combined object). | `Contract.B` is the combined bytes; nothing new. | Lowest: the tooling stays fixed to `Artifacts.Release.bytes`. | Not covered: every judgment assumes `CodeAt m base B`, the bytes of both builds at the code base, which a one-build image does not hold. |
| (b) One artifact module per build; the judgments take the byte list as a parameter. | A `Build` type with the two byte lists (`Release.Ed25519Build`), later part of the contract. `Contract.B` and every released statement unchanged. | The tooling (`Reach`, `ReachSteps`, `ReachInv`, `Routine*`, `ReachTrace`, the `Field25519` family) names `B` or `Artifacts.Release.size` about 290 times in about 30 modules; each becomes a parameter. The released assets rebuild with unchanged goldens. | Covered: the claim at `b` assumes only `CodeAt m base b.bytes`. |
| (c) Two workspaces, one per build, compiling the same proofs. | As (b). | No tooling change. | Covered, but by two sets of claims with the same names that cannot share one environment: not one theorem per claim. |

Chosen: (b). In place: `Artifacts/Ed25519Compact.lean` and `Ed25519Fast.lean` (generated),
`Release.Ed25519Build` (`Build`, `combs`, `bytes`, `codeRanges`; `offsets_same`: every function,
data label and code range at the same offset in both builds), the decoding of every code range
of both builds (`Release.Ed25519CodeDecode`) and the table checks (`Release.Ed25519Tables*`), all
stated over a build's own bytes. The tooling and the `Field25519` proofs take the bytes as a
parameter (`CodeBytes`, see "The judgments"), and `Release.Ed25519FieldRoutines` proves the
`m0c_fe_mul` and `m0c_fe_sqr` contracts for each build's own bytes. The workspace's
`Artifacts.Release` is empty, so a lemma left at the global instance says nothing about Ed25519.
