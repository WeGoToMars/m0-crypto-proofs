import M0Crypto.Release.RoutineFlow
import M0Crypto.Release.Ed25519Sbit
import M0Crypto.Release.Ed25519WordLoop
import M0Crypto.Release.Ed25519WnafDigits
import M0Crypto.Release.Ed25519Bytes
import M0Crypto.Release.Ed25519Leaf

set_option linter.unusedSimpArgs false

/-!
# `m0c_sc_wnaf`

The frame holds `OUT, SCL, W, BIT, CARRY, NOW, WORD, J` (offsets `0, 4, …, 28`). The routine zeroes
the 256 digit bytes at `OUT` (`m0c_zero`), then runs the main loop of `Ed25519WnafDigits.step` while
`BIT ≤ 255`, each pass calling `m0c_sbit`; an odd pass sums `NOW` bits in the window loop (one
`m0c_sbit` each) and stores the digit at `OUT + BIT`.

The blocks are segments with decided effects (`Eff`); the branches are `cmp; b<c> +0; b tgt`
(`ReachFT.cjif`) and `b` (`ReachFT.jmp`); both loops run as `ReachT.wloop` over the public loop state
(`St` of the main loop, the window index `j`), with the trace `wnTr` a function of `base`, `r0`–`r2`,
`sp` and `k`. `Ok` holds in both builds (`ok_c`, `ok_f`). `pass_out` and `pass_in` run one pass of
each loop, `odd_run` and `run_out` the loops, and `wn_run` the body to the digits of `wnaf` (`Qw`);
`GH.wn` is the body's stack GP, and `sc_wnaf_te` the TE in each build, its public values `wnPub` with
the scalar's value. The code positions are derived from the piece sizes (`oZ`…`oN`).
-/

namespace M0Crypto.Release.Ed25519ScWnaf

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SBool SMem)
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.Ed25519WnafDigits
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Artifacts
open M0Crypto.Release.Ed25519Sbit (sbitR sbitE)
open M0Crypto.Release.Ed25519WordLoop (wordR wordPub wloopE wloop zeroPre zeroBody add_ofNat_add memEq_write32)
open M0Crypto.Release.Ed25519Leaf (leafPub)
open M0Crypto.Release.RoutineBranch (cmpImm_flags cmpReg_flags cond_eq)

/-! ## Code -/

abbrev O : Nat := Ed25519Compact.sc_wnaf
def cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)
def spA (n : Nat) : SExpr := .add (.reg0 13) (cw n)
def ldS (n : Nat) : SExpr := .ld32 .mem0 (spA n)

/-- A block on the frame: its accesses at `sp`, reading `rg`, writing `wg`. -/
def sg (g : List Instr) (rg wg : List (SExpr × Nat)) : Seg := { g, al := [(.reg0 13, 4)], wg, rg, As := [.reg0 13] }

def s0 := sg [.strSp 0 0, .strSp 1 1, .strSp 2 2, .ldrSp 0 0, .movImm 1 64] [(spA 0, 4)] [(spA 0, 12)]
def s1 := sg [.movImm 0 0, .strSp 0 3, .strSp 0 4] [] [(spA 12, 8)]
def sL := sg [.ldrSp 1 3] [(spA 12, 4)] []
def sS := sg [.ldrSp 0 1] [(spA 4, 4)] []
def sC := sg [.ldrSp 1 4] [(spA 16, 4)] []
def sE := sg [.ldrSp 0 3, .addImm8 0 1, .strSp 0 3] [(spA 12, 4)] [(spA 12, 4)]
def sO := sg [.ldrSp 0 2, .ldrSp 1 3, .movImm 2 1, .lslImm 2 2 8, .subReg 1 2 1] [(spA 8, 8)] []
def sM := sg [.movHi 0 1] [] []
def sK := sg [.strSp 0 5, .ldrSp 0 4, .strSp 0 6, .movImm 0 0, .strSp 0 7] [(spA 16, 4)] [(spA 20, 12)]
def sW := sg [.ldrSp 0 7, .ldrSp 1 5] [(spA 20, 12)] []
def sI := sg [.ldrSp 1 3, .addReg 1 1 0, .ldrSp 0 1] [(spA 4, 12)] []
def sA := sg [.ldrSp 1 7, .dp .lsls 0 1, .ldrSp 1 6, .addReg 1 1 0, .strSp 1 6, .ldrSp 0 7, .addImm8 0 1, .strSp 0 7]
  [(spA 24, 8)] [(spA 24, 8)]
/-- The digit's byte `OUT + BIT`. -/
def dA : SExpr := .add (ldS 0) (ldS 12)
def sX : Seg :=
  { g := [.ldrSp 0 6, .ldrSp 2 2, .subImm8 2 1, .lslImm 1 0 0, .dp .lsrs 1 2, .movImm 3 1, .dp .ands 1 3, .strSp 1 4,
      .addImm8 2 1, .dp .lsls 1 2, .subReg 0 0 1, .ldrSp 1 0, .ldrSp 2 3, .memReg .strb 0 1 2, .ldrSp 1 5, .addReg 2 2 1,
      .strSp 2 3], al := [(.reg0 13, 4), (dA, 1)], wg := [(dA, 1), (spA 12, 4), (spA 16, 4)], rg := [(spA 0, 28)],
    As := [.reg0 13, dA] }

def cmp01 : Instr := .dp .cmp 0 1

/-! ## Layout

Each position is the one before plus the size of what lies between; a compare with
`b<c> +0; b tgt` (`cjSize`) and a `bl` (`blSize`) or `b` (`brSize`). The frame is `lr` and the 8 slots,
`FR` bytes below the entry SP, and 4 bytes for a callee: `D` in all. -/

local notation "FR" => 36
local notation "D" => 40

def cjSize : Nat := seqSize [cmp01, .bcond 0 0, .b 0]
def oZ : Nat := seqSize [.push 0 true, .subSp 8]
def o1 : Nat := oZ + seqSize s0.g + blSize
def oL : Nat := o1 + seqSize s1.g
def oC1 : Nat := oL + seqSize sL.g
def oB1 : Nat := oC1 + cjSize
def oCa : Nat := oB1 + seqSize sS.g + blSize
def oC2 : Nat := oCa + seqSize sC.g
def oE : Nat := oC2 + cjSize
def oJ1 : Nat := oE + seqSize sE.g
def oO : Nat := oJ1 + brSize
def oC3 : Nat := oO + seqSize sO.g
def oM : Nat := oC3 + cjSize
def oK : Nat := oM + seqSize sM.g
def oW : Nat := oK + seqSize sK.g
def oC4 : Nat := oW + seqSize sW.g
def oB2 : Nat := oC4 + cjSize
def oA : Nat := oB2 + seqSize sI.g + blSize
def oJ2 : Nat := oA + seqSize sA.g
def oX : Nat := oJ2 + brSize
def oJ3 : Nat := oX + seqSize sX.g
def oP : Nat := oJ3 + brSize
def oN : Nat := oP + seqSize [.addSp 8, .pop 0 true]

def zeroR : Routine :=
  wordR Ed25519Compact.zero (seqSize (wloop zeroPre zeroBody 0xfc)) 1 false false (fun _ => True) (fun _ _ _ => 0#32) []

def cs : List (Nat × Nat) := (O, O + oN) :: sbitR.code ++ zeroR.code

/-- **`m0c_sc_wnaf`**: the 256 bytes at `r0` become the width-`r2` NAF digits of the scalar
`k < 2^255` at `r1`. -/
def wnR : Routine where
  entry := O
  code := cs
  stack := D
  Pre := fun _ s => decodeInt (bytesAt s.mem (s.regs 1) 32) < 2 ^ 255 ∧ 2 ≤ (s.regs 2).toNat ∧
    (s.regs 2).toNat ≤ 8 ∧ (s.regs 0).toNat % 4 = 0 ∧
    ((s.regs 0).toNat + 256 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat)
  wr := fun s => [⟨s.regs 0, 256⟩]
  rd := fun s => [⟨s.regs 1, 32⟩]
  Post := fun s m _ => ∀ i < 256, m (s.regs 0 + BitVec.ofNat 32 i) =
    BitVec.ofInt 8 (wnaf (s.regs 2).toNat (decodeInt (bytesAt s.mem (s.regs 1) 32)) i)
  clob := Ed25519Routines.hiRegs

section ok
variable (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS]

def segAt (B : List (BitVec 8)) (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && (sglueOk cs s.g (O + o) FR D s.al s.wg s.rg && traceOkE s.g s.As)
def siteAt (f : Routine) (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && seqAt B (O + o + seqSize s.g) [.bl (blImm (O + o + seqSize s.g) f.entry)] &&
  siteOkE (BS := BS) cs f s (O + o) FR D (blImm (O + o + seqSize s.g) f.entry)
def cjAt (o : Nat) (i : Instr) (c : BitVec 4) (tgt : Nat) : Bool :=
  seqAt B (O + o) [i, .bcond c (brImm8 (O + o + 2) (O + o + 6)), .b (brImm11 (O + o + 4) (O + tgt))] &&
  cjifOk (B := B) cs i (O + o) (O + tgt) FR D (brImm8 (O + o + 2) (O + o + 6)) (brImm11 (O + o + 4) (O + tgt))
def jmpAt (o tgt : Nat) : Bool :=
  seqAt B (O + o) [.b (brImm11 (O + o) (O + tgt))] && jmpOk (B := B) cs (O + o) (O + tgt) FR D (brImm11 (O + o) (O + tgt))

def segL : List (Nat × Seg) := [(o1, s1), (oL, sL), (oCa, sC), (oE, sE), (oO, sO), (oM, sM), (oK, sK), (oW, sW),
  (oA, sA), (oX, sX)]

/-- The decided checks of a build. -/
structure Ok : Prop where
  segs : segL.all (fun p => segAt B p.1 p.2) = true
  z : siteAt B BS zeroR oZ s0 = true
  b1 : siteAt B BS sbitR oB1 sS = true
  b2 : siteAt B BS sbitR oB2 sI = true
  c1 : cjAt B BS oC1 (.cmpImm 1 255) 9 oP = true
  c2 : cjAt B BS oC2 cmp01 0 oO = true
  c3 : cjAt B BS oC3 cmp01 12 oK = true
  c4 : cjAt B BS oC4 cmp01 11 oX = true
  j1 : jmpAt B BS oJ1 oL = true
  j2 : jmpAt B BS oJ2 oW = true
  j3 : jmpAt B BS oJ3 oL = true
  en : seqAt B wnR.entry [.push 0 true, .subSp (BitVec.ofNat 7 8)] = true
  po : seqAt B (O + oP) [.addSp (BitVec.ofNat 7 8), .pop 0 true] = true
  cd : rangesSub [(wnR.entry, wnR.entry + 4), (O + oP, O + oP + 4)] wnR.code = true
  sz : O + oN ≤ BS ∧ O % 2 = 0
end ok

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem Ok.seg (h : Ok B BS) {o : Nat} {s : Seg} (hm : (o, s) ∈ segL) :
    seqAt B (O + o) s.g = true ∧ (sglueOk cs s.g (O + o) FR D s.al s.wg s.rg && traceOkE s.g s.As) = true := by
  have := List.all_eq_true.mp h.segs _ hm; simpa [segAt] using this

omit [CodeBytes B BS] in
theorem Ok.site {f : Routine} {o : Nat} {s : Seg} (h : siteAt B BS f o s = true) : seqAt B (O + o) s.g = true ∧
    instrAt B (O + o + seqSize s.g) = some (.bl (blImm (O + o + seqSize s.g) f.entry)) ∧
    siteOkE (BS := BS) cs f s (O + o) FR D (blImm (O + o + seqSize s.g) f.entry) = true := by
  simp only [siteAt, Bool.and_eq_true] at h; exact ⟨h.1.1, instrAt_of_seqAt h.1.2, h.2⟩

/-! ## Block effects -/

def E0 : Eff := { regs := [(1, cw 64)], mem := some (.w32 (.w32 (.w32 .mem0 (spA 0) (.reg0 0)) (spA 4) (.reg0 1)) (spA 8) (.reg0 2)) }
def E1 : Eff := { regs := [(0, cw 0)], mem := some (.w32 (.w32 .mem0 (spA 12) (cw 0)) (spA 16) (cw 0)) }
def EE : Eff := { regs := [(0, .add (ldS 12) (cw 1))], mem := some (.w32 .mem0 (spA 12) (.add (ldS 12) (cw 1))) }
def EO : Eff := { regs := [(0, ldS 8), (1, .sub (.lsl (cw 1) 8) (ldS 12)), (2, .lsl (cw 1) 8)] }
def EK : Eff := { regs := [(0, cw 0)], mem := some (.w32 (.w32 (.w32 .mem0 (spA 20) (.reg0 0)) (spA 24) (ldS 16)) (spA 28) (cw 0)) }
def EI : Eff := { regs := [(0, ldS 4), (1, .add (ldS 12) (.reg0 0))] }
def bvE : SExpr := .add (ldS 24) (.lslR (.reg0 0) (ldS 28) .c0)
def EA : Eff := { regs := [(0, .add (ldS 28) (cw 1)), (1, bvE)], mem := some (.w32 (.w32 .mem0 (spA 24) bvE) (spA 28) (.add (ldS 28) (cw 1))) }
def wm1 : SExpr := .add (ldS 8) (.const (-1#32))
def cE : SExpr := .and (.lsrR (ldS 24) wm1 (.lslC (ldS 24) 0 (.awcC (ldS 8) (.const 0xfffffffe#32) (.const true)))) (cw 1)
def dE : SExpr := .sub (ldS 24) (.lslR cE (ldS 8) (.awcC (.awc (ldS 8) (.const 0xfffffffe#32) (.const true)) (cw 1) (.const false)))
def m8 : SMem := .w8 (.w32 .mem0 (spA 16) cE) dA dE
def r20 : SExpr := .ld32 m8 (spA 20)
def EX : Eff := { regs := [(0, dE), (1, r20), (2, .add (ldS 12) r20), (3, cw 1)], mem := some (.w32 m8 (spA 12) (.add (ldS 12) r20)) }

open M0Crypto.Release.Ed25519 (Build) in
theorem ok_c : @Ok _ _ Build.compact.codeBytes := by
  refine @Ok.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, segL, List.all_cons, List.all_nil, segAt, siteAt, cjAt, jmpAt, seqAt_eq_scan]) <;>
    decide +kernel

open M0Crypto.Release.Ed25519 (Build) in
theorem ok_f : @Ok _ _ Build.fast.codeBytes := by
  refine @Ok.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, segL, List.all_cons, List.all_nil, segAt, siteAt, cjAt, jmpAt, seqAt_eq_scan]) <;>
    decide +kernel

/-! ## Values -/

theorem lsl_v (x : Word) (n : Nat) (c : Bool) : (lslRegC x n c).1 = x <<< n := by
  unfold lslRegC; split <;> simp_all
theorem lsr_v (x : Word) (n : Nat) (c : Bool) : (lsrRegC x n c).1 = x >>> n := by
  unfold lsrRegC lsrC; split <;> simp_all

/-- Adding bit `t` at position `j` of the window word. -/
theorem win_add (a t j : Nat) (ht : t ≤ 1) (hj : j < 8) :
    BitVec.ofNat 32 a + (BitVec.ofNat 32 t <<< j) = BitVec.ofNat 32 (a + 2 ^ j * t) := by
  have : 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by omega) hj
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl <;> simp <;> omega

/-- Bit `n` of a word, `(x >> n) & 1`. -/
theorem bit_and (x : Word) (n : Nat) : x >>> n &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 (x.toNat / 2 ^ n % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]; omega

/-! ## The loop model -/

theorem loop_fix {w k : Nat} (hw : 1 ≤ w) : ∀ f (s : St), 256 - s.bit ≤ f → loop w k (f + 1) s = loop w k f s
  | 0, s, h => by show (if s.bit < 256 then _ else s) = s; simp only [show ¬ s.bit < 256 by omega, ↓reduceIte]
  | f + 1, s, h => by
    show (if s.bit < 256 then _ else s) = (if s.bit < 256 then _ else s); split
    · rename_i hb; exact loop_fix hw f _ (by have := step_bit (k := k) hw hb; omega)
    · rfl

theorem fin_step {w k : Nat} (hw : 1 ≤ w) {s : St} (hb : s.bit < 256) :
    loop w k 256 (step w k s) = loop w k 256 s := by
  rw [← loop_fix hw 256 s (by omega)]; show _ = (if s.bit < 256 then _ else s); simp only [hb, ↓reduceIte]

theorem fin_done {w k : Nat} {s : St} (hb : ¬ s.bit < 256) : loop w k 256 s = s := by
  show (if s.bit < 256 then _ else s) = s; simp only [hb, ↓reduceIte]

def effL : List (List Instr × Eff) := [(s0.g, E0), (s1.g, E1), (sL.g, { regs := [(1, ldS 12)] }),
  (sS.g, { regs := [(0, ldS 4)] }), (sC.g, { regs := [(1, ldS 16)] }), (sE.g, EE), (sO.g, EO),
  (sM.g, { regs := [(0, .reg0 1)] }), (sK.g, EK), (sW.g, { regs := [(0, ldS 28), (1, ldS 20)] }), (sI.g, EI),
  (sA.g, EA), (sX.g, EX)]

theorem effs : effL.all (fun p => effOk p.1 p.2) = true := by decide +kernel

theorem eff (i : Nat) {g : List Instr} {E : Eff} (hm : effL[i]? = some (g, E) := by rfl) : effOk g E = true :=
  by have := List.all_eq_true.mp effs _ (List.mem_of_getElem? hm); exact this

/-! ## Compares -/

theorem ls_of (u : State) {b : Nat} (h : u.regs 1 = BitVec.ofNat 32 b) (hb : b ≤ 256) :
    condPassed 9 ((Instr.cmpImm 1 255).next u) = decide (b < 256) := by
  obtain ⟨c, z⟩ := cmpImm_flags 1 255 u
  rw [show ∀ v : State, condPassed 9 v = (!v.c || v.z) from fun _ => rfl, c, z]; erw [h]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases e : b < 256 <;> simp [e] <;> omega

theorem eq_of (u : State) {x y : Nat} (h0 : u.regs 0 = BitVec.ofNat 32 x) (h1 : u.regs 1 = BitVec.ofNat 32 y)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : condPassed 0 (cmp01.next u) = decide (x = y) := by
  obtain ⟨-, z⟩ := cmpReg_flags 0 1 u
  rw [cond_eq, cmp01, z]; erw [h0, h1]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem lt_of (u : State) {x y : Nat} (h0 : u.regs 0 = BitVec.ofNat 32 x) (h1 : u.regs 1 = BitVec.ofNat 32 y)
    (hx : x < 2 ^ 31) (hy : y < 2 ^ 31) :
    condPassed 11 (cmp01.next u) = decide (x < y) ∧ condPassed 12 (cmp01.next u) = decide (y < x) := by
  have := cmp_signed 0 1 u (by erw [h0]; simp; omega) (by erw [h1]; simp; omega)
  erw [h0, h1] at this; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : y < 2 ^ 32)] at this; exact this

/-! ## The frame -/

/-- Slot `c ≤ vs.length` set to `x`. -/
def upd (vs : List Word) (c : Nat) (x : Word) : List Word := vs.take c ++ x :: vs.drop (c + 1)

theorem upd_get {vs : List Word} {c : Nat} {x : Word} (hc : c ≤ vs.length) (i : Nat) :
    (upd vs c x)[i]? = if i = c then some x else vs[i]? := by
  unfold upd
  rcases Nat.lt_trichotomy i c with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]; simp [h, Nat.ne_of_lt h]
  · rw [List.getElem?_append_right (by simp; omega)]; simp [Nat.min_eq_left hc]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left hc, Nat.ne_of_gt h, ↓reduceIte]
    rw [show i - c = (i - c - 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop]; congr 1; omega

/-- The width the trace uses: `w`, at least 2. -/
def wv (P : Nat → Word) : Nat := max 2 (P 2).toNat
/-- The window length at `b`. -/
def nw (P : Nat → Word) (b : Nat) : Nat := min (wv P) (256 - b)

theorem wv1 (P : Nat → Word) : 1 ≤ wv P := by simp only [wv]; omega

set_option hygiene false in
local notation "fp" => (P 3 - BitVec.ofNat 32 FR)

section
variable (P : Nat → Word) (m1 : Mem)

/-- The layout: the frame below `sp`; the digits and the scalar apart from it and each other. -/
structure Lay : Prop where
  sp : D ≤ (P 3).toNat ∧ (P 3).toNat % 4 = 0
  ab : (P 0).toNat + 256 ≤ 2 ^ 32 ∧ (P 1).toNat + 32 ≤ 2 ^ 32
  w0 : (P 0).toNat + 256 ≤ (P 3).toNat - D ∨ (P 3).toNat ≤ (P 0).toNat
  w1 : (P 1).toNat + 32 ≤ (P 3).toNat - D ∨ (P 3).toNat ≤ (P 1).toNat
  d : (P 0).toNat + 256 ≤ (P 1).toNat ∨ (P 1).toNat + 32 ≤ (P 0).toNat

def Wc : List Rgn := [⟨P 3 - BitVec.ofNat 32 D, FR⟩, ⟨P 0, 256⟩]
def Rc {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) : List Rgn :=
  codeR base :: ⟨P 3 - BitVec.ofNat 32 D, D⟩ :: [⟨P 1, 32⟩]

/-- The slots of the main loop at `s`. -/
def vo (s : St) : List Word := [P 0, P 1, P 2, BitVec.ofNat 32 s.bit, BitVec.ofNat 32 s.carry]
/-- The slots of the window loop at `s`, before pass `j`: `NOW`, `WORD`, `J`. -/
def vi (k : Nat) (s : St) (j : Nat) : List Word :=
  vo P s ++ [BitVec.ofNat 32 (nw P s.bit), BitVec.ofNat 32 (s.carry + k / 2 ^ s.bit % 2 ^ j), BitVec.ofNat 32 j]

/-- The memory: as `m1` outside `Wc`, the digit bytes `d`, the frame words `vs`. -/
structure FrM (d : Nat → Int) (vs : List Word) (m : Mem) : Prop where
  eq : MemEq (Wc P) m1 m
  dg : ∀ i < 256, m (P 0 + BitVec.ofNat 32 i) = BitVec.ofInt 8 (d i)
  sl : ∀ i v, vs[i]? = some v → read32 m (fp + BitVec.ofNat 32 (4 * i)) = v

/-- A state on the frame: `sp` at it, its memory `FrM`. -/
def Fr (d : Nat → Int) (vs : List Word) (u : State) : Prop := u.regs 13 = fp ∧ FrM P m1 d vs u.mem
end

macro "at_pc" h:term : tactic => `(tactic| (rw [$h:term]; try rfl))
macro "wn_lay" L:ident : tactic =>
  `(tactic| (have := ($L).sp; have := ($L).ab; have := ($L).w0; have := ($L).w1; have := ($L).d))
macro "wn_fp" : tactic => `(tactic| ((try simp only [Wc, Rc] at *); fp_tac))

section
variable {P : Nat → Word} {m1 : Mem} {d : Nat → Int} {vs : List Word} {m : Mem}

theorem FrM.rd (h : FrM P m1 d vs m) (n : Nat) {v : Word} (hv : vs[n / 4]? = some v := by rfl)
    (hn : n % 4 = 0 := by decide) : read32 m (fp + BitVec.ofNat 32 n) = v := by
  have := h.sl _ _ hv; rwa [show 4 * (n / 4) = n by omega] at this

theorem FrM.w32 (L : Lay P) (h : FrM P m1 d vs m) (c : Nat) (x : Word) (hc : c ≤ vs.length ∧ vs.length ≤ 8 ∧ c < 8 := by simp [vo, vi, upd]) :
    FrM P m1 d (upd vs c x) (write32 m (fp + BitVec.ofNat 32 (4 * c)) x) := by
  wn_lay L
  have hm := memEq_write32 m (fp + BitVec.ofNat 32 (4 * c)) x
  refine ⟨h.eq.grow hm (by wn_fp), fun i hi => by rw [hm.byte (by wn_fp)]; exact h.dg i hi, fun i v hv => ?_⟩
  rw [upd_get hc.1] at hv
  by_cases e : i = c
  · subst e; simp only [ite_true, Option.some.injEq] at hv; subst hv; exact M0Crypto.Armv6M.read32_write32_same _ _ _
  · simp only [e, ↓reduceIte] at hv
    have hi : i < vs.length := (List.getElem?_eq_some_iff.mp hv).1
    have : i < 8 := by omega
    rw [read32_write32_add _ _ _ _ _ (by omega) (by omega) (by omega)]; exact h.sl i v hv
end

section
variable {P : Nat → Word} {m1 : Mem} {d : Nat → Int} {vs : List Word} {m : Mem}

theorem FrM.w8 (L : Lay P) (h : FrM P m1 d vs m) {b : Nat} (hb : b < 256) (x : Word) (hl : vs.length ≤ 8 := by simp [vo, vi, upd]) :
    FrM P m1 (fun i => if i = b then (x.extractLsb' 0 8).toInt else d i) vs (Thumb.write8 m (P 0 + BitVec.ofNat 32 b) x) := by
  wn_lay L
  have hm := MemEq.write8 m (P 0 + BitVec.ofNat 32 b) x
  refine ⟨h.eq.grow hm (by wn_fp), fun i hi => ?_, fun i v hv => ?_⟩
  · by_cases e : i = b
    · subst e; simp only [Thumb.write8, ite_true, BitVec.ofInt_toInt]
    · rw [hm.byte (by wn_fp)]; simp only [e, ↓reduceIte]; exact h.dg i hi
  · have := (List.getElem?_eq_some_iff.mp hv).1
    rw [hm.read32 (by wn_fp)]; exact h.sl i v hv

theorem FrM.keep (L : Lay P) (h : FrM P m1 d vs m) {m' : Mem} (hm : MemEq [⟨fp - BitVec.ofNat 32 4, 4⟩] m m')
    (hl : vs.length ≤ 8 := by simp [vo, vi, upd]) : FrM P m1 d vs m' := by
  wn_lay L
  refine ⟨h.eq.grow hm (by wn_fp), fun i hi => by rw [hm.byte (by wn_fp)]; exact h.dg i hi, fun i v hv => ?_⟩
  have := (List.getElem?_eq_some_iff.mp hv).1
  rw [hm.read32 (by wn_fp)]; exact h.sl i v hv

theorem FrM.take (h : FrM P m1 d vs m) (n : Nat) : FrM P m1 d (vs.take n) m :=
  ⟨h.eq, h.dg, fun i v hv => h.sl i v (by rw [List.getElem?_take] at hv; split at hv <;> simp_all)⟩

theorem Fr.same {u t : State} (h : Fr P m1 d vs t) (hs : Same t u) : Fr P m1 d vs u :=
  ⟨(hs.2 13 (by decide)).trans h.1, hs.1 ▸ h.2⟩
end

/-! ## The trace -/


section
variable (Tb Tz : Word → (Nat → Word) → List Event) (base : Word) (P : Nat → Word) (k : Nat)

def bT (o : Nat) (s : Seg) (vs : List Word) : TrP := Tr.is (blockTrE s.g (base + BitVec.ofNat 32 (O + o)) s.As vs)
def cT (o : Nat) (s : Seg) (f : Routine) (T : List Event) (Ψ : TrP) : TrP :=
  Tr.cat (bT base o s [fp]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o + seqSize s.g),
    .bl (blImm (O + o + seqSize s.g) f.entry), []⟩]) (Tr.cat (Tr.is T) Ψ))
def jT (o tgt : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), .b (brImm11 (O + o) (O + tgt)), []⟩]) Ψ
def kT (o : Nat) (i : Instr) (c : BitVec 4) (tgt : Nat) (p : Bool) (ΨT ΨF : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), i, []⟩]) (Tr.cat (Tr.is (jifTr base (O + o + 2) c
    (brImm8 (O + o + 2) (O + o + 6)) (brImm11 (O + o + 4) (O + tgt)) p)) (Tr.cond p ΨT ΨF))

/-- Pass `j` of the window loop at `b`, the main loop's next pass `Ψo` after it. -/
def inTr (b : Nat) (Ψo : TrP) (j : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oW sW [fp]) (kT base oC4 cmp01 11 oX (decide (j < nw P b))
    (cT base P oB2 sI sbitR (Tb base (pubOf [P 1, BitVec.ofNat 32 (b + j), fp])) (Tr.cat (bT base oA sA [fp]) (jT base oJ2 oW Ψ)))
    (Tr.cat (bT base oX sX [fp, P 0 + BitVec.ofNat 32 b]) (jT base oJ3 oL Ψo)))

/-- The odd window at `b`. -/
def oddTr (b : Nat) (Ψ : TrP) : TrP := Tr.cat (bT base oK sK [fp]) (wTr (inTr Tb base P b Ψ) Nat.succ (nw P b + 1) 0)

/-- A pass of the main loop from `s`. -/
def outTr (s : St) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oL sL [fp]) (kT base oC1 (.cmpImm 1 255) 9 oP (decide (s.bit < 256))
    (cT base P oB1 sS sbitR (Tb base (pubOf [P 1, BitVec.ofNat 32 s.bit, fp])) (Tr.cat (bT base oCa sC [fp])
      (kT base oC2 cmp01 0 oO (decide (bit k s.bit = s.carry)) (Tr.cat (bT base oE sE [fp]) (jT base oJ1 oL Ψ))
        (Tr.cat (bT base oO sO [fp]) (kT base oC3 cmp01 12 oK (decide (256 - s.bit < wv P))
          (Tr.cat (bT base oM sM [fp]) (oddTr Tb base P s.bit Ψ)) (oddTr Tb base P s.bit Ψ))))))
    (Tr.is []))

/-- **The body's trace**: a function of `base`, `r0`-`r2`, `sp` and `k`. -/
def wnTr : TrP :=
  cT base P oZ s0 zeroR (Tz base (pubOf [P 0, BitVec.ofNat 32 64, BitVec.ofNat 32 64, fp]))
    (Tr.cat (bT base o1 s1 [fp]) (wTr (outTr Tb base P k) (step (wv P) k) 257 init))
end

/-! ## The run -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The hypotheses of the run: the caller frame, the decided checks, the layout, the code at
`m1`, `w`, the scalar `k` at `m1`, the call lemma of `m0c_sbit` with trace `Tb`. -/
structure Hy (base : Word) (P : Nat → Word) (m1 : Mem) (k : Nat) (Tb : Word → (Nat → Word) → List Event) : Prop where
  F : Caller base (P 3) D (Wc P)
  ok : Ok B BS
  L : Lay P
  cd : CodeAt m1 base B
  hw : 2 ≤ (P 2).toNat ∧ (P 2).toNat ≤ 8
  hk : decodeInt (bytesAt m1 (P 1) 32) = k
  kb : k < 2 ^ 255
  sb : sbitR.SpecT fun b s => Tr.is (Tb b (leafPub [0, 1] b s))

abbrev RF (base : Word) (P : Nat → Word) (u : State) (Q : State → Prop) (Ψ : TrP) : Prop :=
  ReachFT base (PcIn base cs) (Has (Rc P base)) (Has (Wc P)) (InStackWindow (P 3) D) u Q Ψ

variable {base : Word} {P : Nat → Word} {m1 : Mem} {k : Nat} {Tb : Word → (Nat → Word) → List Event}
  {d : Nat → Int} {vs : List Word} {t : State} {Q : State → Prop}

theorem Hy.code (H : Hy base P m1 k Tb) {u : State} (h : Fr P m1 d vs u) : CodeAt u.mem base B :=
  CodeAt.of_memEq H.cd h.2.eq H.F.codeW

theorem Hy.seg (H : Hy base P m1 k Tb) (i : Nat) {o : Nat} {s : Seg} {Ψ : TrP} {vs' : List Word}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (hf : Fr P m1 d vs t) (hs : SGlueSides t (Rc P base) (Wc P) s.al s.wg s.rg)
    (hv : s.As.map (·.denote t) = vs')
    (kk : (execAll s.g t).pc = base + BitVec.ofNat 32 (O + o + seqSize s.g) → (execAll s.g t).regs 13 = fp →
      MemEq (sregions t s.wg) t.mem (execAll s.g t).mem → RF base P (execAll s.g t) Q Ψ)
    (hm : segL[i]? = some (o, s) := by rfl) : RF base P t Q (Tr.cat (bT base o s vs') Ψ) :=
  have h := H.ok.seg (List.mem_of_getElem? hm)
  ReachFT.seg1 H.F s h.1 h.2 hpc hf.1 (H.code hf) hs hv fun hp h13 _ hm => kk hp h13 hm

theorem Hy.cj (H : Hy base P m1 k Tb) {o tgt : Nat} {i : Instr} {c : BitVec 4} (hc : cjAt B BS o i c tgt = true)
    {ΨT ΨF : TrP} (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (hf : Fr P m1 d vs t) (p : Bool)
    (hcp : condPassed c (i.next t) = p)
    (hT : p = true → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + o + 6) → RF base P u Q ΨT)
    (hF : p = false → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + tgt) → RF base P u Q ΨF)
    (hacc : i.accesses t = [] := by rfl) : RF base P t Q (kT base o i c tgt p ΨT ΨF) := by
  simp only [cjAt, Bool.and_eq_true] at hc
  exact ReachFT.cjif H.F hc.1 hc.2 hacc hpc hf.1 (H.code hf) p hcp hT hF

theorem Hy.jmp (H : Hy base P m1 k Tb) {o tgt : Nat} (hj : jmpAt B BS o tgt = true) {Ψ : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (hf : Fr P m1 d vs t)
    (kk : ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + tgt) → RF base P u Q Ψ) :
    RF base P t Q (jT base o tgt Ψ) := by
  simp only [jmpAt, Bool.and_eq_true] at hj
  exact ReachFT.jmp H.F (instrAt_of_seqAt hj.1) hj.2 hpc hf.1 kk

theorem Hy.site (H : Hy base P m1 k Tb) {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf) {o : Nat} {s : Seg}
    (hs : siteAt B BS f o s = true) {Ψ Φ : TrP} (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (hfr : Fr P m1 d vs t)
    (hsd : SiteSidesE f base s (O + o) t (Rc P base) (Wc P)) (hv : s.As.map (·.denote t) = [fp])
    (hpre : f.Pre base (atCall base f s.g (O + o) t)) (hΦ : Φf base (atCall base f s.g (O + o) t) = Φ)
    (kk : ∀ u, u.pc = base + BitVec.ofNat 32 (O + o + seqSize s.g + 4) → u.regs 13 = fp →
      MemEq (sregions t s.wg ++ f.win (atCall base f s.g (O + o) t) :: f.wr (atCall base f s.g (O + o) t)) t.mem u.mem →
      MemEq (f.win (atCall base f s.g (O + o) t) :: f.wr (atCall base f s.g (O + o) t)) (execAll s.g t).mem u.mem →
      f.Post (atCall base f s.g (O + o) t) u.mem (u.regs 0) → RF base P u Q Ψ) :
    RF base P t Q (Tr.cat (bT base o s [fp]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o + seqSize s.g),
      .bl (blImm (O + o + seqSize s.g) f.entry), []⟩]) (Tr.cat Φ Ψ))) :=
  have h := Ok.site hs
  ReachFT.siteE hf H.F s h.1 h.2.1 h.2.2 hpc (Hi.self t) hfr.1 (H.code hfr) hsd hv hpre hΦ
    fun u hu _ h13 _ hm hm' hp => kk u hu h13 hm hm' hp
end

section
variable {P : Nat → Word} {m1 : Mem} {d : Nat → Int} {vs : List Word} {u : State}

theorem Fr.ld (h : Fr P m1 d vs u) (n : Nat) {v : Word} (hv : vs[n / 4]? = some v := by rfl)
    (hn : n % 4 = 0 := by decide) : (ldS n).denote u = v := by
  show read32 u.mem (u.regs 13 + BitVec.ofNat 32 n) = v; rw [h.1]; exact h.2.rd n hv hn
end

theorem at_regs {base : Word} {f : Routine} {g : List Instr} {o : Nat} {u : State} (r : Reg)
    (h : r.val ≠ 14 ∧ r.val ≠ 15 := by decide) : (atCall base f g o u).regs r = (execAll g u).regs r :=
  blState_regs _ _ _ r h.1 h.2

theorem shr3 {b : Nat} (hb : b < 2 ^ 32) : BitVec.ofNat 32 b >>> 3 = BitVec.ofNat 32 (b / 8) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hb]; omega

section
variable (base : Word) (P : Nat → Word) (m1 : Mem) (k : Nat)

/-- Before a pass of the main loop from `s`. -/
def IO (s : St) (u : State) : Prop :=
  Fr P m1 s.digits (vo P s) u ∧ Inv (wv P) k s ∧ loop (wv P) k 256 s = loop (wv P) k 256 init
/-- The end of the body: the digit bytes of `wnaf`. -/
def Qw (u : State) : Prop := u.pc = base + BitVec.ofNat 32 (O + oP) ∧ u.regs 13 = fp ∧
  ∀ i < 256, u.mem (P 0 + BitVec.ofNat 32 i) = BitVec.ofInt 8 (wnaf (wv P) k i)
end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {P : Nat → Word} {m1 : Mem} {k : Nat}
  {Tb : Word → (Nat → Word) → List Event} {t : State}

theorem wv_eq (H : Hy base P m1 k Tb) : wv P = (P 2).toNat := by have := H.hw; simp only [wv]; omega

theorem Hy.cb (H : Hy base P m1 k Tb) : base.toNat + BS ≤ 2 ^ 32 := by
  have h := H.F.codeW; simp only [codeR, Wc] at h; fp_simp at h; omega

theorem Hy.scl (H : Hy base P m1 k Tb) {d : Nat → Int} {vs : List Word} {u : State} (h : Fr P m1 d vs u) :
    decodeInt (bytesAt u.mem (P 1) 32) = k := by
  have L := H.L; wn_lay L; rw [h.2.eq.bytes (by wn_fp)]; exact H.hk

/-- **A pass of the main loop**: its end at `bit = 256`, else `m0c_sbit` and the zero digit, or the
odd window `hodd`. -/
theorem pass_out (H : Hy base P m1 k Tb) {s : St} {Ψ : TrP} (hI : IO P m1 k s t) (hpc : t.pc = base + BitVec.ofNat 32 (O + oL))
    (hodd : s.bit < 256 → bit k s.bit ≠ s.carry → ∀ u, Fr P m1 s.digits (vo P s) u → u.regs 0 = BitVec.ofNat 32 (nw P s.bit) →
      u.pc = base + BitVec.ofNat 32 (O + oK) → RF base P u (Qw base P k) (oddTr Tb base P s.bit Ψ))
    (hn : s.bit < 256 → ∀ u, IO P m1 k (step (wv P) k s) u → u.pc = base + BitVec.ofNat 32 (O + oL) →
      RF base P u (Qw base P k) Ψ) :
    RF base P t (Qw base P k) (outTr Tb base P k s Ψ) := by
  obtain ⟨hf, hv, hfin⟩ := hI
  have hb := hv.bit_le; have hc := hv.carry_le; have L := H.L; wn_lay L; have := H.cb
  refine H.seg 1 hpc hf (by glue_tac [sg, sL, Wc, Rc, hf.1, spA, cw]) (by simp [sg, sL, SExpr.denote, hf.1]) fun hp h13 _ => ?_
  have E := eff_run (eff 2) t
  have f1 : Fr P m1 s.digits (vo P s) (execAll sL.g t) := ⟨h13, (E.mem _ rfl : _ = t.mem) ▸ hf.2⟩
  have r1 : (execAll sL.g t).regs 1 = BitVec.ofNat 32 s.bit := by rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, hf.ld 12]
  refine H.cj H.ok.c1 (by at_pc hp) f1 _ (ls_of _ r1 hb) (fun hT u hs hpu => ?_) (fun hF u hs hpu => ?_)
  case refine_2 =>
    have e : s.bit = 256 := by simp at hF; omega
    refine ReachT.done ⟨hpu, (f1.same hs).1, fun i hi => ?_⟩
    rw [(f1.same hs).2.dg i hi, ← fin_done (w := wv P) (k := k) (s := s) (by omega), hfin]; rfl
  have e : s.bit < 256 := by simpa using hT
  have f2 := f1.same hs
  have r1' : u.regs 1 = BitVec.ofNat 32 s.bit := (hs.2 1 (by decide)).trans r1
  have E := eff_run (eff 3) u
  have a0 : (atCall base sbitR sS.g (O + oB1) u).regs 0 = P 1 := by
    rw [at_regs 0, E.reg 0 (by decide) (by decide)]; simp [Eff.reg, f2.ld 4]
  have a1 : (atCall base sbitR sS.g (O + oB1) u).regs 1 = BitVec.ofNat 32 s.bit := by
    rw [at_regs 1, E.reg 1 (by decide) (by decide)]; simp [Eff.reg, SExpr.denote, r1']
  have a13 : (atCall base sbitR sS.g (O + oB1) u).regs 13 = fp := by
    rw [at_regs 13, E.reg 13 (by decide) (by decide)]; simp [Eff.reg, SExpr.denote, f2.1]
  have am : (atCall base sbitR sS.g (O + oB1) u).mem = u.mem := E.mem _ rfl
  refine H.site H.sb H.ok.b1 (by at_pc hpu) f2 ?_ (by simp [sg, sS, SExpr.denote, f2.1])
    (by show (_ : Word).toNat < 256; rw [a1]; simp [e, Nat.mod_eq_of_lt (by omega : s.bit < 2 ^ 32)])
    (by simp only [leafPub, List.cons_append, List.nil_append, List.map_cons, List.map_nil, a0, a1, a13])
    fun u2 hp2 h13' hm2 _ hpost => ?_
  · unfold SiteSidesE; generalize atCall base sbitR sS.g (O + oB1) u = a at a0 a1 a13 ⊢
    glue_tac [sg, sS, Wc, Rc, spA, cw, sbitR, Ed25519Leaf.leafR, codeR, Ed25519Sbit.rd, Ed25519Sbit.byteA,
      a0, a1, a13, shr3 (show s.bit < 2 ^ 32 by omega), f2.1]
  have hbt := bit_le_one k s.bit
  have r0 : u2.regs 0 = BitVec.ofNat 32 (bit k s.bit) := by
    apply BitVec.eq_of_toNat_eq; rw [hpost, am, a0, a1, H.scl f2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s.bit < 2 ^ 32), Nat.mod_eq_of_lt (by omega : bit k s.bit < 2 ^ 32)]; rfl
  have f3 : Fr P m1 s.digits (vo P s) u2 := ⟨h13', f2.2.keep L (by
    generalize atCall base sbitR sS.g (O + oB1) u = a at a13 hm2
    simpa [sregions, sS, sg, Routine.win, sbitR, Ed25519Leaf.leafR, a13] using hm2)⟩
  refine H.seg 2 (by at_pc hp2) f3 (by glue_tac [sg, sC, Wc, Rc, f3.1, spA, cw]) (by simp [sg, sC, SExpr.denote, f3.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 4) u2
  have f4 : Fr P m1 s.digits (vo P s) (execAll sC.g u2) := ⟨h13, (E.mem _ rfl : _ = u2.mem) ▸ f3.2⟩
  have q0 : (execAll sC.g u2).regs 0 = BitVec.ofNat 32 (bit k s.bit) := by
    rw [E.reg 0 (by decide) (by decide)]; simp [Eff.reg, SExpr.denote, r0]
  have q1 : (execAll sC.g u2).regs 1 = BitVec.ofNat 32 s.carry := by
    rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, f3.ld 16]
  refine H.cj H.ok.c2 (by at_pc hp) f4 _ (eq_of _ q0 q1 (by omega) (by omega)) (fun hT u hs hpu => ?_)
    (fun hF u hs hpu => ?_)
  · have ev : bit k s.bit = s.carry := by simpa using hT
    have st : step (wv P) k s = { s with bit := s.bit + 1 } := by simp [Ed25519WnafDigits.step, ev]
    have f5 := f4.same hs
    refine H.seg 3 (by at_pc hpu) f5 (by glue_tac [sg, sE, Wc, Rc, f5.1, spA, cw]) (by simp [sg, sE, SExpr.denote, f5.1])
      fun hp h13 _ => ?_
    have E := eff_run (eff 5) u
    have f6 : Fr P m1 (step (wv P) k s).digits (vo P (step (wv P) k s)) (execAll sE.g u) := by
      refine ⟨h13, ?_⟩
      have := f5.2.w32 L 3 (BitVec.ofNat 32 (s.bit + 1))
      rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, f5.ld 12, spA, cw, f5.1]
      rw [st]; simpa [upd, vo, BitVec.ofNat_add] using this
    refine H.jmp H.ok.j1 (by at_pc hp) f6 fun u3 hs3 hp3 => hn e u3 ⟨f6.same hs3, step_inv (Nat.le_max_left _ _) H.kb e hv,
      (fin_step (wv1 P) e).trans hfin⟩ hp3
  have od : bit k s.bit ≠ s.carry := by simpa using hF
  have f5 := f4.same hs
  refine H.seg 4 (by at_pc hpu) f5 (by glue_tac [sg, sO, Wc, Rc, f5.1, spA, cw]) (by simp [sg, sO, SExpr.denote, f5.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 6) u
  have f6 : Fr P m1 s.digits (vo P s) (execAll sO.g u) := ⟨h13, (E.mem _ rfl : _ = u.mem) ▸ f5.2⟩
  have q0 : (execAll sO.g u).regs 0 = BitVec.ofNat 32 (wv P) := by
    rw [E.reg 0 (by decide) (by decide)]; simp [Eff.reg, EO, f5.ld 8, wv_eq H]
  have q1 : (execAll sO.g u).regs 1 = BitVec.ofNat 32 (256 - s.bit) := by
    rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, EO, SExpr.denote, f5.ld 12, cw]
    apply BitVec.eq_of_toNat_eq; simp; omega
  have hw := H.hw; have := wv_eq H
  refine H.cj H.ok.c3 (by at_pc hp) f6 _ (lt_of _ q0 q1 (by omega) (by omega)).2 (fun hT u' hs' hpu' => ?_)
    (fun hF u' hs' hpu' => hodd e od u' (f6.same hs') ((hs'.2 0 (by decide)).trans (q0.trans (by
      simp at hF; simp only [nw]; congr 1; omega))) hpu')
  have f7 := f6.same hs'
  refine H.seg 5 (by at_pc hpu') f7 (by glue_tac [sg, sM, Wc, Rc, f7.1, spA, cw]) (by simp [sg, sM, SExpr.denote, f7.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 7) u'
  exact hodd e od _ ⟨h13, (E.mem _ rfl : _ = u'.mem) ▸ f7.2⟩ (by
    simp at hT; rw [show nw P s.bit = 256 - s.bit by simp only [nw]; omega, E.reg 0 (by decide) (by decide)]
    simp [Eff.reg, SExpr.denote, (hs'.2 1 (by decide)).trans q1]) (by at_pc hp)

end

/-! ## Denotations over abstract arguments

Equation lemmas, so that rewriting never unfolds the concrete carry flags of `cE` and `dE`. -/

theorem den_lsrR (a b : SExpr) (c : SBool) (u : State) :
    (SExpr.lsrR a b c).denote u = a.denote u >>> ((b.denote u).toNat % 256) := lsr_v _ _ _
theorem den_lslR (a b : SExpr) (c : SBool) (u : State) :
    (SExpr.lslR a b c).denote u = a.denote u <<< ((b.denote u).toNat % 256) := lsl_v _ _ _
theorem den_and (a b : SExpr) (u : State) : (SExpr.and a b).denote u = a.denote u &&& b.denote u := by
  simp only [SExpr.denote]
theorem den_sub (a b : SExpr) (u : State) : (SExpr.sub a b).denote u = a.denote u - b.denote u := by
  simp only [SExpr.denote]
theorem den_add (a b : SExpr) (u : State) : (SExpr.add a b).denote u = a.denote u + b.denote u := by
  simp only [SExpr.denote]
theorem den_w32 (m : SMem) (a v : SExpr) (u : State) :
    (SMem.w32 m a v).denote u = write32 (m.denote u) (a.denote u) (v.denote u) := by
  simp only [SMem.denote]
theorem den_w8 (m : SMem) (a v : SExpr) (u : State) :
    (SMem.w8 m a v).denote u = write8 (m.denote u) (a.denote u) (v.denote u) := by
  simp only [SMem.denote]
theorem den_ld32 (m : SMem) (a : SExpr) (u : State) : (SExpr.ld32 m a).denote u = read32 (m.denote u) (a.denote u) := by
  simp only [SExpr.denote]
theorem den_mem0 (u : State) : SMem.mem0.denote u = u.mem := by simp only [SMem.denote]
theorem den_reg0 (r : Reg) (u : State) : (SExpr.reg0 r).denote u = u.regs r := by simp only [SExpr.denote]
theorem rd32_zero {m : Mem} {a : Word} (h : read32 m a = 0#32) :
    m a = 0#8 ∧ m (a + 1#32) = 0#8 ∧ m (a + 2#32) = 0#8 ∧ m (a + 3#32) = 0#8 := by
  have := congrArg BitVec.toNat h
  simp only [read32, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftLeft_eq, Nat.or_eq_zero_iff,
    Nat.mul_eq_zero] at this
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  omega
theorem den_cw (n : Nat) (u : State) : (cw n).denote u = BitVec.ofNat 32 n := by
  simp only [cw, SExpr.denote]

section
variable (P : Nat → Word) (m1 : Mem) (k : Nat)
/-- Before pass `j` of the window loop at `s`. -/
theorem Fr.of {d : Nat → Int} {vs : List Word} {u : State} (h : u.regs 13 = fp) (hm : FrM P m1 d vs u.mem) :
    Fr P m1 d vs u := ⟨h, hm⟩
def II (s : St) (j : Nat) (u : State) : Prop :=
  Fr P m1 s.digits (vi P k s j) u ∧ Inv (wv P) k s ∧ loop (wv P) k 256 s = loop (wv P) k 256 init ∧
    s.bit < 256 ∧ bit k s.bit ≠ s.carry ∧ j ≤ nw P s.bit
end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {P : Nat → Word} {m1 : Mem} {k : Nat}
  {Tb : Word → (Nat → Word) → List Event} {t : State}

/-- **Pass `j` of the window loop**: add bit `BIT + j` at `j` (`m0c_sbit`), or store the digit and
leave to the main loop's next pass `Ψo`. -/
theorem pass_in (H : Hy base P m1 k Tb) {s : St} {j : Nat} {Ψo Ψ : TrP} (hI : II P m1 k s j t)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oW))
    (hn : ∀ u, IO P m1 k (step (wv P) k s) u → u.pc = base + BitVec.ofNat 32 (O + oL) → RF base P u (Qw base P k) Ψo)
    (hg : j < nw P s.bit → ∀ u, II P m1 k s (j + 1) u → u.pc = base + BitVec.ofNat 32 (O + oW) →
      RF base P u (Qw base P k) Ψ) :
    RF base P t (Qw base P k) (inTr Tb base P s.bit Ψo j Ψ) := by
  obtain ⟨hf, hv, hfin, hb, hod, hj⟩ := hI
  have hc := hv.carry_le; have hw := H.hw; have := wv_eq H; have L := H.L; wn_lay L; have := H.cb
  have hnw : nw P s.bit ≤ 8 ∧ s.bit + nw P s.bit ≤ 256 ∧ 1 ≤ nw P s.bit := by simp only [nw]; omega
  refine H.seg 7 hpc hf (by glue_tac [sg, sW, Wc, Rc, hf.1, spA, cw]) (by simp [sg, sW, SExpr.denote, hf.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 9) t
  have f1 : Fr P m1 s.digits (vi P k s j) (execAll sW.g t) := ⟨h13, (E.mem _ rfl : _ = t.mem) ▸ hf.2⟩
  have q0 : (execAll sW.g t).regs 0 = BitVec.ofNat 32 j := by rw [E.reg 0 (by decide) (by decide)]; simp [Eff.reg, hf.ld 28]
  have q1 : (execAll sW.g t).regs 1 = BitVec.ofNat 32 (nw P s.bit) := by
    rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, hf.ld 20]
  refine H.cj H.ok.c4 (by at_pc hp) f1 _ (lt_of _ q0 q1 (by omega) (by omega)).1 (fun hT u hs hpu => ?_)
    (fun hF u hs hpu => ?_)
  · have e : j < nw P s.bit := by simpa using hT
    have f2 := f1.same hs
    have r0' : u.regs 0 = BitVec.ofNat 32 j := (hs.2 0 (by decide)).trans q0
    have E := eff_run (eff 10) u
    have a0 : (atCall base sbitR sI.g (O + oB2) u).regs 0 = P 1 := by
      rw [at_regs 0, E.reg 0 (by decide) (by decide)]; simp [Eff.reg, EI, f2.ld 4]
    have a1 : (atCall base sbitR sI.g (O + oB2) u).regs 1 = BitVec.ofNat 32 (s.bit + j) := by
      rw [at_regs 1, E.reg 1 (by decide) (by decide)]; simp [Eff.reg, EI, SExpr.denote, f2.ld 12, r0', BitVec.ofNat_add]
    have a13 : (atCall base sbitR sI.g (O + oB2) u).regs 13 = fp := by
      rw [at_regs 13, E.reg 13 (by decide) (by decide)]; simp [Eff.reg, EI, SExpr.denote, f2.1]
    have am : (atCall base sbitR sI.g (O + oB2) u).mem = u.mem := E.mem _ rfl
    refine H.site H.sb H.ok.b2 (by at_pc hpu) f2 ?_ (by simp [sg, sI, SExpr.denote, f2.1])
      (by show (_ : Word).toNat < 256; rw [a1]; simp [Nat.mod_eq_of_lt (by omega : s.bit + j < 2 ^ 32)]; omega)
      (by simp only [leafPub, List.cons_append, List.nil_append, List.map_cons, List.map_nil, a0, a1, a13])
      fun u2 hp2 h13' hm2 _ hpost => ?_
    · unfold SiteSidesE; generalize atCall base sbitR sI.g (O + oB2) u = a at a0 a1 a13 ⊢
      glue_tac [sg, sI, Wc, Rc, spA, cw, sbitR, Ed25519Leaf.leafR, codeR, Ed25519Sbit.rd, Ed25519Sbit.byteA,
        a0, a1, a13, shr3 (show s.bit + j < 2 ^ 32 by omega), f2.1]
    have hbt := bit_le_one k (s.bit + j)
    have r0 : u2.regs 0 = BitVec.ofNat 32 (bit k (s.bit + j)) := by
      apply BitVec.eq_of_toNat_eq; rw [hpost, am, a0, a1, H.scl f2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : s.bit + j < 2 ^ 32), Nat.mod_eq_of_lt (by omega : bit k (s.bit + j) < 2 ^ 32)]; rfl
    have f3 : Fr P m1 s.digits (vi P k s j) u2 := ⟨h13', f2.2.keep L (by
      generalize atCall base sbitR sI.g (O + oB2) u = a at a13 hm2
      simpa [sregions, sI, sg, Routine.win, sbitR, Ed25519Leaf.leafR, a13] using hm2)⟩
    refine H.seg 8 (by at_pc hp2) f3 (by glue_tac [sg, sA, Wc, Rc, f3.1, spA, cw]) (by simp [sg, sA, SExpr.denote, f3.1])
      fun hp h13 _ => ?_
    have E := eff_run (eff 11) u2
    have hX : k / 2 ^ s.bit % 2 ^ j < 2 ^ 8 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
    have wd : BitVec.ofNat 32 (s.carry + k / 2 ^ s.bit % 2 ^ j) + (BitVec.ofNat 32 (bit k (s.bit + j)) <<< j) =
        BitVec.ofNat 32 (s.carry + k / 2 ^ s.bit % 2 ^ (j + 1)) := by
      rw [win_add _ _ _ hbt (by omega), window_step, Nat.add_assoc]
    have f4 : Fr P m1 s.digits (vi P k s (j + 1)) (execAll sA.g u2) := by
      refine ⟨h13, ?_⟩
      have := (f3.2.w32 L 6 (BitVec.ofNat 32 (s.carry + k / 2 ^ s.bit % 2 ^ (j + 1)))).w32 L 7 (BitVec.ofNat 32 (j + 1))
      rw [E.mem _ rfl]; simp only [EA, bvE, SMem.denote, SExpr.denote, f3.ld 24, f3.ld 28, spA, cw, f3.1, r0, lsl_v]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 32), Nat.mod_eq_of_lt (by omega : j < 256), wd]
      simpa [upd, vi, vo, BitVec.ofNat_add] using this
    exact H.jmp H.ok.j2 (by at_pc hp) f4 fun u3 hs3 hp3 => hg e u3 ⟨f4.same hs3, hv, hfin, hb, hod, by omega⟩ hp3
  have e : j = nw P s.bit := by simp at hF; omega
  subst e
  have f2 := f1.same hs
  have dv : dA.denote u = P 0 + BitVec.ofNat 32 s.bit := by simp [dA, SExpr.denote, f2.ld 0, f2.ld 12]
  refine H.seg 9 (by at_pc hpu) f2 (by glue_tac [sX, Wc, Rc, dv, f2.1, spA, cw]) (by simp [sX, dv, SExpr.denote, f2.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 12) u
  obtain ⟨W, hWd⟩ : ∃ W, s.carry + k / 2 ^ s.bit % 2 ^ nw P s.bit = W := ⟨_, rfl⟩
  have hW : W < 2 ^ 9 := by
    have : k / 2 ^ s.bit % 2 ^ nw P s.bit < 2 ^ 8 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) hnw.1)
    omega
  have vw : (wm1.denote u).toNat = wv P - 1 := by
    have e1 : wm1.denote u = P 2 + -1#32 := by simp only [wm1, SExpr.denote, f2.ld 8]
    rw [e1, BitVec.toNat_add, show (-1#32 : Word).toNat = 2 ^ 32 - 1 by decide]; omega
  have vc : cE.denote u = BitVec.ofNat 32 (W / 2 ^ (wv P - 1) % 2) := by
    simp only [cE, den_and, den_lsrR, f2.ld 24, vw, hWd, den_cw]
    rw [Nat.mod_eq_of_lt (by omega : wv P - 1 < 256), bit_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show W < 2 ^ 32 by omega)]
  obtain ⟨c', hcd⟩ : ∃ c', W / 2 ^ (wv P - 1) % 2 = c' := ⟨_, rfl⟩
  have hc' : c' ≤ 1 := by omega
  rw [hcd] at vc
  have vd : dE.denote u = BitVec.ofNat 32 W - (BitVec.ofNat 32 c' <<< wv P) := by
    simp only [dE, den_sub, den_lslR, f2.ld 24, f2.ld 8, vc, hWd, lsl_v]
    rw [Nat.mod_eq_of_lt (by omega : (P 2).toNat < 256), ← wv_eq H]
  have st : step (wv P) k s = ⟨s.bit + nw P s.bit, c', fun i => if i = s.bit then (W : Int) - c' * 2 ^ wv P else s.digits i⟩ := by
    rw [← hcd, ← hWd]; simp [Ed25519WnafDigits.step, hod, nw]
  have hv' : Inv (wv P) k (step (wv P) k s) := step_inv (Nat.le_max_left _ _) H.kb hb hv
  have hdg : ((BitVec.ofNat 32 W - (BitVec.ofNat 32 c' <<< wv P)).extractLsb' 0 8).toInt = (W : Int) - c' * 2 ^ wv P := by
    have h8 := Digit.byte (by omega) (hv'.digit s.bit)
    rw [st] at h8; simp only [↓reduceIte] at h8
    exact Ed25519Bytes.digit_reg W c' (wv P) (by omega) hc' (by omega) h8.1 h8.2
  have F1 := f2.2.w32 L 4 (BitVec.ofNat 32 c')
  have F2 := F1.w8 L hb (BitVec.ofNat 32 W - (BitVec.ofNat 32 c' <<< wv P))
  have r20v : read32 (Thumb.write8 (write32 u.mem (fp + BitVec.ofNat 32 (4 * 4)) (BitVec.ofNat 32 c'))
      (P 0 + BitVec.ofNat 32 s.bit) (BitVec.ofNat 32 W - (BitVec.ofNat 32 c' <<< wv P))) (fp + BitVec.ofNat 32 20) =
      BitVec.ofNat 32 (nw P s.bit) := F2.rd 20 (by simp [upd, vi, vo])
  have F3 := F2.w32 L 3 (BitVec.ofNat 32 (s.bit + nw P s.bit))
  have f3 : Fr P m1 (Ed25519WnafDigits.step (wv P) k s).digits (vo P (Ed25519WnafDigits.step (wv P) k s)) (execAll sX.g u) := by
    refine Fr.of P m1 h13 ?_
    rw [E.mem (.w32 m8 (spA 12) (.add (ldS 12) r20)) rfl]
    simp only [m8, r20, den_w32, den_w8, den_ld32, den_mem0, den_add, vc, vd, dv, spA, den_cw, f2.ld 12, f2.1]
    simp only [den_reg0, f2.1]
    simp only [Nat.reduceMul] at r20v F3
    rw [r20v, ← BitVec.ofNat_add, st]
    simp only [hdg] at F3
    simpa [upd, vi, vo] using F3.take 5
  exact H.jmp H.ok.j3 (by at_pc hp) f3 fun u3 hs3 hp3 => hn u3 ⟨f3.same hs3, hv', (fin_step (wv1 P) hb).trans hfin⟩ hp3

/-- **The odd window at `BIT`**: the slots `NOW`, `WORD`, `J`, then the window loop (`pass_in`). -/
theorem odd_run (H : Hy base P m1 k Tb) {s : St} {Ψ : TrP} (hv : Inv (wv P) k s)
    (hfin : loop (wv P) k 256 s = loop (wv P) k 256 init) (hb : s.bit < 256) (hod : bit k s.bit ≠ s.carry)
    (hf : Fr P m1 s.digits (vo P s) t) (hr0 : t.regs 0 = BitVec.ofNat 32 (nw P s.bit))
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oK))
    (hn : ∀ u, IO P m1 k (step (wv P) k s) u → u.pc = base + BitVec.ofNat 32 (O + oL) → RF base P u (Qw base P k) Ψ) :
    RF base P t (Qw base P k) (oddTr Tb base P s.bit Ψ) := by
  have L := H.L; wn_lay L; have := H.cb
  refine H.seg 6 hpc hf (by glue_tac [sg, sK, Wc, Rc, hf.1, spA, cw]) (by simp [sg, sK, SExpr.denote, hf.1])
    fun hp h13 _ => ?_
  have E := eff_run (eff 8) t
  have f1 : Fr P m1 s.digits (vi P k s 0) (execAll sK.g t) := by
    refine Fr.of P m1 h13 ?_
    have := ((hf.2.w32 L 5 (BitVec.ofNat 32 (nw P s.bit))).w32 L 6 (BitVec.ofNat 32 s.carry)).w32 L 7 (BitVec.ofNat 32 0)
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, hf.ld 16, spA, cw, hf.1, hr0]
    simpa [upd, vi, vo, Nat.mod_one] using this
  refine ReachT.wloop (I := fun j u => II P m1 k s j u ∧ u.pc = base + BitVec.ofNat 32 (O + oW))
    (go := fun j => decide (j < nw P s.bit)) (fun j => nw P s.bit - j) (fun j hj => by simp at hj; omega)
    (fun j u Ψ' hI hc => pass_in H hI.1 hI.2 hn fun hj u' hu hp' => hc (by simpa using hj) u' ⟨hu, hp'⟩)
    _ 0 _ (by omega) ⟨⟨f1, hv, hfin, hb, hod, Nat.zero_le _⟩, by at_pc hp⟩


/-- **The main loop** from `init` reaches the digit bytes of `wnaf`. -/
theorem run_out (H : Hy base P m1 k Tb) (hI : IO P m1 k init t) (hpc : t.pc = base + BitVec.ofNat 32 (O + oL)) :
    RF base P t (Qw base P k) (wTr (outTr Tb base P k) (step (wv P) k) 257 init) :=
  ReachT.wloop (I := fun s u => IO P m1 k s u ∧ u.pc = base + BitVec.ofNat 32 (O + oL))
    (go := fun s => decide (s.bit < 256)) (fun s => 256 - s.bit)
    (fun s hs => by have := step_bit (k := k) (wv1 P) (s := s); simp at hs; omega)
    (fun s u Ψ hI hc => pass_out H hI.1 hI.2
      (fun hb hod u' hf hr0 hp => odd_run H hI.1.2.1 hI.1.2.2 hb hod hf hr0 hp fun u'' hu hp' => hc (by simpa using hb) u'' ⟨hu, hp'⟩)
      fun hb u' hu hp => hc (by simpa using hb) u' ⟨hu, hp⟩)
    257 init t (by simp [init]) ⟨hI, hpc⟩

end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {P : Nat → Word} {k : Nat}
  {Tb Tz : Word → (Nat → Word) → List Event} {t : State}

/-- **The body** from the entry `sp` lowered to the frame: zero the digits, `BIT, CARRY = 0`, the main loop. -/
theorem wn_run (H : Hy base P t.mem k Tb) (h4 : (P 0).toNat % 4 = 0)
    (hz : zeroR.SpecT fun b s => Tr.is (Tz b (wordPub 1 b s)))
    (q0 : t.regs 0 = P 0) (q1 : t.regs 1 = P 1) (q2 : t.regs 2 = P 2) (q13 : t.regs 13 = fp)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oZ)) :
    RF base P t (Qw base P k) (wnTr Tb Tz base P k) := by
  have L := H.L; wn_lay L; have := H.cb
  have f0 : Fr P t.mem (fun i => (t.mem (P 0 + BitVec.ofNat 32 i)).toInt) [] t :=
    ⟨q13, fun _ _ => rfl, fun i _ => by simp, fun i v h => by simp at h⟩
  have E := eff_run (eff 0) t
  have a0 : (atCall base zeroR s0.g (O + oZ) t).regs 0 = P 0 := by
    rw [at_regs 0, E.reg 0 (by decide) (by decide)]; simp [Eff.reg, E0, SExpr.denote, q0]
  have a1 : (atCall base zeroR s0.g (O + oZ) t).regs 1 = BitVec.ofNat 32 64 := by
    rw [at_regs 1, E.reg 1 (by decide) (by decide)]; simp [Eff.reg, E0, SExpr.denote, cw]
  have a13 : (atCall base zeroR s0.g (O + oZ) t).regs 13 = fp := by
    rw [at_regs 13, E.reg 13 (by decide) (by decide)]; simp [Eff.reg, E0, SExpr.denote, q13]
  have f1 : FrM P t.mem (fun i => (t.mem (P 0 + BitVec.ofNat 32 i)).toInt) [P 0, P 1, P 2] (execAll s0.g t).mem := by
    have := ((f0.2.w32 L 0 (P 0) (by simp)).w32 L 1 (P 1) (by simp [upd])).w32 L 2 (P 2) (by simp [upd])
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, spA, cw, q13, q0, q1, q2]
    simpa [upd] using this
  refine H.site hz H.ok.z hpc f0 ?_ (by simp [sg, s0, SExpr.denote, q13])
    (by generalize atCall base zeroR s0.g (O + oZ) t = a at a0 a1; simp only [zeroR, wordR, a0, a1]; exact ⟨by unfold Ed25519WordLoop.WordsOk; decide, h4, by simp, trivial⟩) (by simp only [wordPub, a0, a1, a13])
    fun u hp h13 _ hm hpost => ?_
  · unfold SiteSidesE; generalize atCall base zeroR s0.g (O + oZ) t = a at a0 a1 a13 ⊢
    glue_tac [sg, s0, Wc, Rc, spA, cw, zeroR, wordR, a0, a1, a13, q13, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  generalize atCall base zeroR s0.g (O + oZ) t = a at a0 a1 a13 hm hpost
  simp only [zeroR, wordR, Routine.win, a0, a1, a13] at hm hpost
  have f2 : Fr P t.mem (fun _ => 0) [P 0, P 1, P 2] u := by
    refine ⟨h13, f1.eq.grow hm (by wn_fp), fun i hi => ?_, fun i v hv => ?_⟩
    · have h := rd32_zero (hpost (i / 4) (by simp; omega))
      have e : P 0 + BitVec.ofNat 32 i = P 0 + BitVec.ofNat 32 (4 * (i / 4)) + BitVec.ofNat 32 (i % 4) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
      rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h' | h' | h' | h' <;>
        simp [e, h', h]
    · have := (List.getElem?_eq_some_iff.mp hv).1; simp at this
      rw [hm.read32 (by wn_fp)]; exact f1.sl i v hv
  refine H.seg 0 (by at_pc hp) f2 (by glue_tac [sg, s1, Wc, Rc, f2.1, spA, cw]) (by simp [sg, s1, SExpr.denote, f2.1])
    fun hp1 h13' _ => ?_
  have E := eff_run (eff 1) u
  refine run_out H ⟨Fr.of P t.mem h13' ?_, init_inv _ _, rfl⟩ (by at_pc hp1)
  have := (f2.2.w32 L 3 (BitVec.ofNat 32 0)).w32 L 4 (BitVec.ofNat 32 0)
  rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, spA, cw, f2.1]
  simpa [upd, vo, init] using this
end

open M0Crypto.Release.StackEffect (EffT frame_te GP SIR pass_of sir_pass above_sub reg_in reg_sub_above inRD_of site_gp cjif_gp jmp_gp
  winsChk InRD blkChk reg_split)

/-! ## The stack effect -/

/-- The GP's hypotheses at public values `P` (as `frame_te`'s). -/
structure GH (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Prop where
  room : (sp0 - P 3).toNat + D ≤ n
  n32 : n < 2 ^ 32
  F : ∀ y, Has [⟨P 0, 256⟩, ⟨P 1, 32⟩] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (P 3) y
  R : ∀ y, Has [⟨P 1, 32⟩] y → BelowEntry sp0 n y → U y

section
variable {sp0 : Word} {n : Nat} {U : Word → Prop} {P : Nat → Word}

/-- At the entry, in the main loop (slots `OUT`–`CARRY`, the digits), in the window loop (all slots). -/
def R0 (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop := U y ∨ Region (P 3 - BitVec.ofNat 32 4) 4 y
def Rm (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop :=
  R0 U P y ∨ (Region fp 20 y ∨ Has [⟨P 0, 256⟩] y) ∧ BelowEntry sp0 n y
def Rw (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop :=
  Rm sp0 n U P y ∨ Region fp 32 y ∧ BelowEntry sp0 n y
abbrev J (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : StackEffect.Ef → Prop :=
  SIR sp0 fp fun y => R0 U P y ∨ Has [⟨P 0, 256⟩] y ∧ BelowEntry sp0 n y

theorem GH.r4 (G : GH sp0 n U P) : (sp0 - fp).toNat + 4 ≤ n := by
  have := G.room; have := G.n32; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega
theorem GH.up (G : GH sp0 n U P) {y : Word} (h : AtOrAboveSp sp0 (P 3) y) : AtOrAboveSp sp0 fp y :=
  above_sub h (by have := G.room; have := G.n32; omega)
theorem GH.out (G : GH sp0 n U P) {y : Word} {b : Nat} (hb : b < 256) (h : Region (P 0 + BitVec.ofNat 32 b) 1 y)
    (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.up (G.F y ⟨_, .head _, Rgn.of_region (reg_in h (by omega) (by decide))⟩ he)

/-- A frame segment reading `w` bytes from `fp`, writing within the slots. -/
theorem GH.seg (G : GH sp0 n U P) {s : Seg} {pc : Word} {R : Word → Prop} (w : Nat) (hs : s.As = [.reg0 13])
    (hb : blkChk s.rg s.wg (s.rg ++ s.wg) s.g = true) (hr : winsChk s.As [(0, w)] s.rg = true)
    (hw : winsChk s.As [(0, 32)] s.wg = true) (hR : ∀ y, Region fp w y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 fp R) (Tr.is (blockTrE s.g pc s.As [fp]))
      (SIR sp0 fp fun y => R y ∨ InRD (addrE pc s.As [fp]) s.wg y ∧ BelowEntry sp0 n y) :=
  sir_pass hb (pass_of (vs := [fp]) (by rw [hs]; rfl) hr hw (by pass_tac []; exact hR)
    (by pass_tac []; exact fun y h _ => reg_sub_above h (by omega) (by have := G.room; have := G.n32; omega)))

theorem GH.segK (G : GH sp0 n U P) {s : Seg} {pc : Word} {R : Word → Prop} (w : Nat) (hs : s.As = [.reg0 13])
    (hb : blkChk s.rg s.wg (s.rg ++ s.wg) s.g = true) (hr : winsChk s.As [(0, w)] s.rg = true)
    (hw : winsChk s.As [(0, 32)] s.wg = true) (hR : ∀ y, Region fp w y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 fp R) (Tr.is (blockTrE s.g pc s.As [fp])) (SIR sp0 fp R) :=
  GP.post (G.seg w hs hb hr hw hR) fun _ h => h.mono fun _ h => .inl h

theorem wr_of {s : Seg} {pc y : Word} (c w : Nat) (hs : s.As = [.reg0 13]) (hm : (spA c, w) ∈ s.wg)
    (h : Region (fp + BitVec.ofNat 32 c) w y)
    (ha : StackEffect.atomOf [.reg0 13] (spA c) = some (0, BitVec.ofNat 32 c) := by decide) :
    InRD (addrE pc s.As [fp]) s.wg y :=
  inRD_of (vs := [fp]) (by rw [hs]; rfl) hm (by rw [hs]; exact ha) rfl h

theorem sb_scl {b : Nat} (hb : b < 256) {pc y : Word}
    (h : StackEffect.InR (Ed25519Leaf.blkSt [0, 1] pc (pubOf [P 1, BitVec.ofNat 32 b, fp])) Ed25519Sbit.rd y) :
    Has [⟨P 1, 32⟩] y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  simp only [Ed25519Sbit.rd, List.mem_singleton] at hr; subst hr
  refine ⟨_, .head _, Rgn.of_region ?_⟩
  have : o = 0 := by simp at ho; omega
  subst this
  show Region (P 1) 32 (P 1 + (BitVec.ofNat 32 b >>> 3) + BitVec.ofNat 32 0)
  rw [shr3 (by omega)]; simp only [Region, BitVec.add_zero]; bv_omega

theorem GH.sbF (G : GH sp0 n U P) {b : Nat} (hb : b < 256) {pc y : Word}
    (h : StackEffect.InR (Ed25519Leaf.blkSt [0, 1] pc (pubOf [P 1, BitVec.ofNat 32 b, fp])) Ed25519Sbit.rd y)
    (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.up (G.F y (let ⟨r, hr, h⟩ := sb_scl hb h; ⟨r, .tail _ hr, h⟩) he)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (Tb : Word → (Nat → Word) → List Event) (base : Word)

/-- **The odd window's GP**: `NOW`, `WORD`, `J` join the written slots; each pass keeps them. -/
theorem GH.odd (G : GH sp0 n U P) (hbE : ∀ b q, sbitE b q (Tb b q)) {b : Nat} (hb : b < 256) {Ψo : TrP}
    (ho : GP sp0 n (SIR sp0 fp (Rm sp0 n U P)) Ψo (J sp0 n U P)) :
    GP sp0 n (SIR sp0 fp (Rm sp0 n U P)) (oddTr Tb base P b Ψo) (J sp0 n U P) := by
  have hw : ∀ y, Region fp 32 y → BelowEntry sp0 n y → Rw sp0 n U P y := fun y h hb => .inr ⟨h, hb⟩
  refine GP.cat (GP.post (G.seg 20 rfl (by decide) (by decide) (by decide) fun y h hb => .inr ⟨.inl h, hb⟩)
    fun _ h => h.mono fun y (h : Rw sp0 n U P y) => h.elim .inl fun ⟨h, hb⟩ => (reg_split (x := 20) (w := 12) h).elim
      (fun h => .inl (.inr ⟨.inl h, hb⟩)) fun h => .inr ⟨wr_of 20 12 rfl (by decide) h, hb⟩) ?_
  refine GP.wloop (K := fun _ => SIR sp0 fp (Rw sp0 n U P)) (go := fun j => decide (j < nw P b)) (fun j => nw P b - j)
    (fun j h => by simp at h; omega) (fun j Ψ h => ?_) _ 0 (by omega)
  refine GP.cat (G.segK 32 rfl (by decide) (by decide) (by decide) hw) (cjif_gp rfl rfl _ (fun hT => ?_) fun _ => ?_)
  · have hj : j < nw P b := by simpa using hT
    exact site_gp (G.segK 32 rfl (by decide) (by decide) (by decide) hw) rfl rfl rfl
      (show EffT 4 _ _ _ _ _ from hbE base (pubOf [P 1, BitVec.ofNat 32 (b + j), fp])) G.r4 G.n32
      (fun y h he => G.sbF (by simp only [nw] at hj; omega) h he) (fun y h he => .inl (.inl (.inl (G.R y (sb_scl (by simp only [nw] at hj; omega) h) he))))
      (GP.pre (fun _ h => h.mono fun _ h => .inl h) (GP.cat (G.segK 32 rfl (by decide) (by decide) (by decide) hw) (jmp_gp (h hT))))
  · refine GP.cat (sir_pass (by decide) (pass_of (vs := [fp, P 0 + BitVec.ofNat 32 b]) (Wr := [(0, 28)]) (Ww := [(0, 32), (1, 1)])
      rfl (by decide) (by decide) (by pass_tac []; exact fun y h he => hw y (by simp only [Region] at h ⊢; omega) he)
      (by pass_tac []; exact ⟨fun y h _ => reg_sub_above h (by omega) (by have := G.room; have := G.n32; omega),
        fun y h he => G.out hb h he⟩))) (jmp_gp (GP.pre (fun _ h => h.mono fun _ h => .inl (.inl h)) ho))

/-- **The main loop's GP**: each pass keeps the slots `OUT`–`CARRY` and the digits. -/
theorem GH.loop (G : GH sp0 n U P) (k : Nat) (hbE : ∀ b q, sbitE b q (Tb b q)) :
    GP sp0 n (SIR sp0 fp (Rm sp0 n U P)) (wTr (outTr Tb base P k) (step (wv P) k) 257 init) (J sp0 n U P) := by
  have hm : ∀ y, Region fp 20 y → BelowEntry sp0 n y → Rm sp0 n U P y := fun y h he => .inr ⟨.inl h, he⟩
  refine GP.wloop (K := fun _ => SIR sp0 fp (Rm sp0 n U P)) (go := fun s => decide (s.bit < 256)) (fun s => 256 - s.bit)
    (fun s h => by have := step_bit (k := k) (wv1 P) (s := s); simp at h; omega) (fun s Ψ h => ?_) _ _ (by simp [init])
  refine GP.cat (G.segK 20 rfl (by decide) (by decide) (by decide) hm) (cjif_gp rfl rfl _ (fun hT => ?_)
    fun _ => GP.nil fun _ h => h.mono fun y (h : R0 U P y ∨ _) => h.elim .inl fun ⟨h, he⟩ => .inr ⟨.inr h, he⟩)
  have hb : s.bit < 256 := by simpa using hT
  refine site_gp (G.segK 20 rfl (by decide) (by decide) (by decide) hm) rfl rfl rfl
    (show EffT 4 _ _ _ _ _ from hbE base (pubOf [P 1, BitVec.ofNat 32 s.bit, fp])) G.r4 G.n32 (fun y h he => G.sbF hb h he)
    (fun y h he => .inl (.inl (G.R y (sb_scl hb h) he))) (GP.pre (fun _ h => h.mono fun _ h => .inl h) ?_)
  have hO := G.odd Tb base hbE hb (h hT)
  exact GP.cat (G.segK 20 rfl (by decide) (by decide) (by decide) hm) (cjif_gp rfl rfl _
    (fun _ => GP.cat (G.segK 20 rfl (by decide) (by decide) (by decide) hm) (jmp_gp (h hT)))
    fun _ => GP.cat (G.segK 20 rfl (by decide) (by decide) (by decide) hm)
      (cjif_gp rfl rfl _ (fun _ => GP.cat (G.segK 20 rfl (by decide) (by decide) (by decide) hm) hO) fun _ => hO))

theorem reg_of_has {a y : Word} {w : Nat} (h : Has [⟨a, w⟩] y) (hw : w < 2 ^ 32) : Region a w y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := h
  simp only [List.mem_singleton] at hr; subst hr; simp only [Region] at ho ⊢; bv_omega

/-- **The body's GP**: from the entry's `R0`, the digits and all slots are written before they are read. -/
theorem GH.wn (G : GH sp0 n U P) (k : Nat) (Tz : Word → (Nat → Word) → List Event)
    (hzE : ∀ b q, wloopE false false b q (Tz b q)) (hbE : ∀ b q, sbitE b q (Tb b q)) :
    GP sp0 n (SIR sp0 fp (R0 U P)) (wnTr Tb Tz base P k) (J sp0 n U P) := by
  have z0 : ∀ y, Region fp 0 y → BelowEntry sp0 n y → False := fun y h _ => by simp [Region] at h
  refine site_gp (GP.post (G.seg (s := { s0 with rg := [] }) 0 rfl (by decide) (by decide) (by decide) fun y h he => (z0 y h he).elim)
      fun _ h => h.mono fun y (h : R0 U P y ∨ Region fp 12 y ∧ BelowEntry sp0 n y) => h.elim .inl fun ⟨h, he⟩ =>
        .inr ⟨wr_of 0 12 rfl (by decide) (by simpa using h), he⟩) rfl rfl rfl
    (show EffT 4 _ _ _ _ _ from hzE base (pubOf [P 0, BitVec.ofNat 32 64, BitVec.ofNat 32 64, fp])) G.r4 G.n32
    (fun y h he => G.up (G.F y ⟨_, .head _, Rgn.of_region (by simpa [pubOf] using h)⟩ he)) (fun y h => by simp at h)
    (GP.cat (GP.post (G.seg 0 rfl (by decide) (by decide) (by decide) fun y h he => (z0 y h he).elim) fun _ h => h.mono ?_)
      (G.loop Tb base k hbE))
  intro y (h : Rm sp0 n U P y)
  rcases h with h | ⟨h | h, he⟩
  · exact .inl (.inl (.inl h))
  · exact (reg_split (x := 12) (w := 8) h).elim (fun h => .inl (.inl (.inr ⟨h, he⟩))) fun h => .inr ⟨wr_of 12 8 rfl (by decide) h, he⟩
  · exact .inl (.inr ⟨by simpa [pubOf] using reg_of_has h (by decide), he⟩)
end

end

/-! ## The routine's TE -/

/-- The public values: `OUT`, `SCL`, `W`, `sp`, and the scalar `k` read at `SCL`. -/
def wnPub (_ : Word) (s : State) : (Nat → Word) × Nat :=
  (pubOf [s.regs 0, s.regs 1, s.regs 2, s.regs 13], decodeInt (bytesAt s.mem (s.regs 1) 32))
/-- **The effect of `m0c_sc_wnaf`**: it reads the scalar and writes the digits, in 40 bytes of stack. -/
def wnE (_ : Word) (p : (Nat → Word) × Nat) : TrP :=
  EffT D (Has [⟨p.1 0, 256⟩, ⟨p.1 1, 32⟩]) (Has [⟨p.1 1, 32⟩]) (Has [⟨p.1 0, 256⟩]) (p.1 3)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

noncomputable def wn_te (ok : Ok B BS) (hb : sbitR.TE (leafPub [0, 1]) sbitE)
    (hz : zeroR.TE (wordPub 1) (wloopE false false)) : wnR.TE wnPub wnE := by
  have hP : oP = 156 := rfl
  have hN : oN = 160 := rfl
  have hsz := ok.sz
  refine frame_te (f := wnR) (pub := wnPub) (mask := 0) (k := 8) (epi := O + oP) (spP := fun p => p.1 3)
    (Ψ := fun b p => wnTr hb.T hz.T b p.1 p.2) (Wd := fun _ p => Has [⟨p.1 0, 256⟩]) (by decide) ok.en ok.po ok.cd
    (by simp only [wnR]; refine ⟨hsz.2, ?_, ?_, ?_, by decide, by decide⟩ <;> omega) (fun _ _ => rfl)
    (fun base s e F t tpc t13 tr hm hc => ?_)
    (fun _ _ => by repeat (first | (apply wTr_uniq; intro _ _ _) | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_cond | assumption))
    (fun _ _ => by repeat (first | (apply wTr_ex; intro _ _ _) | exact Tr.ex_is _ | apply Tr.ex_cat | apply Tr.ex_cond | assumption))
    (fun _ _ y ⟨r, hr, h⟩ => ⟨r, by simp only [List.mem_singleton] at hr; simp [hr], h⟩)
    (fun b p sp0 n U hroom hn hF hR => by
      rw [show 4 * nSaved 0 + 4 * 8 = FR by decide, show 4 * nSaved 0 = 4 by decide]
      exact GH.wn hb.T b ⟨hroom, hn, hF, hR⟩ p.2 hz.T hz.eff hb.eff)
  generalize hP' : (wnPub base s).1 = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 2 = P 2 ∧ s.regs 13 = P 3 := by subst hP'; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨q0, q1, q2, q13⟩ := q
  have hpre := e.pre
  simp only [wnR, q0, q1, q2] at hpre
  have L : Lay P := by
    have hsW := e.sepWr; have hsR := e.sepRd; have hroom := e.room; have hsp4 := e.sp4
    simp only [wnR, Routine.win, q0, q1, q13] at hsW hsR hroom hsp4
    fp_simp at hsW hsR
    exact ⟨⟨hroom, hsp4⟩, ⟨by omega, by omega⟩, by omega, by omega, hpre.2.2.2.2⟩
  wn_lay L
  have hW : lowWin wnR 0 s :: wnR.wr s = Wc P := by subst hP'; rfl
  rw [hW, q13] at F
  rw [hW, show wnR.RdP base s = Has (Rc P base) by subst hP'; rfl, show wnR.SpP s = InStackWindow (P 3) D by rw [← q13]; rfl]
  have t13' : t.regs 13 = fp := by rw [t13, q13]; rfl
  have hk : decodeInt (bytesAt t.mem (P 1) 32) = decodeInt (bytesAt s.mem (s.regs 1) 32) := by
    rw [hm.bytes (by simp only [saved, show 4 * nSaved 0 = 4 from rfl, q13]; wn_fp), q1]
  have H : Hy base P t.mem (decodeInt (bytesAt s.mem (s.regs 1) 32)) hb.T :=
    ⟨F, ok, L, hc, ⟨hpre.2.1, hpre.2.2.1⟩, hk, e.pre.1, hb.spec⟩
  refine ReachFT.mono (wn_run H hpre.2.2.2.1 hz.spec ((tr 0 (by decide) (by decide)).trans q0)
    ((tr 1 (by decide) (by decide)).trans q1) ((tr 2 (by decide) (by decide)).trans q2) t13' (by rw [tpc]; rfl))
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun u hq => ?_) (by subst hP'; exact fun _ h => h)
  refine ⟨hq.1, by rw [hq.2.1, t13'], fun r h4 h11 _ hr => absurd (Ed25519Routines.mem_hiRegs h4 h11) hr, fun i hi => ?_⟩
  rw [q0, q2, ← wv_eq H]; exact hq.2.2 i hi
end

open M0Crypto.Release.Ed25519 (Build) in
theorem ok_b : ∀ b : Build, @Ok _ _ b.codeBytes
  | .compact => ok_c
  | .fast => ok_f

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_sc_wnaf` in each build**, with its effect. -/
noncomputable def sc_wnaf_te (b : Build) : letI := b.codeBytes; wnR.TE wnPub wnE :=
  letI := b.codeBytes
  wn_te (ok_b b) (Ed25519Sbit.sbit_te b) (Ed25519WordLoop.zero_te b)

end M0Crypto.Release.Ed25519ScWnaf
