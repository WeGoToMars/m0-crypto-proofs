import M0Crypto.Release.RoutineFlow
import M0Crypto.Release.Ed25519Sha512Block
import M0Crypto.Release.Ed25519ShaInit
import M0Crypto.Release.BlockEffect

set_option linter.unusedSimpArgs false

/-!
# `m0c_sha512_update`

The context at `r0` is the stream length (one word), the chaining value `H` (eight pairs) and the
block buffer (128 bytes); `ShaCtx` relates it to the stream `S`: the length, `H` over the whole
blocks of `S`, and its remaining bytes in the buffer. The routine appends the `r2` bytes at `r1`:
the outer loop copies bytes into the buffer up to its end or the input's (the inner loop), stores
the length, and compresses a full buffer (`m0c_sha512_block`). The branches are `b<c> tgt` after a
segment (`ReachFT.br`); the loops run as `ReachT.wloop`, the trace a function of `r0`–`r2`, `sp`
and the length word.

`Ok` holds in both builds (`ok_b`). `fl_run`, `pass_in`, `pass_out` and `up_run` run the body to
`Qu`, and `post_of` turns `Qu` into `ShaCtx` of the stream with the input appended. `GH.upd` is the
body's stack GP; `sha512_update_te` is the TE in each build with effect `updE`. `updAd` is the
`.update n ℓ` field of `Callees` at relations whose context relation is `ShaCtx` (`shaRels`).
-/

namespace M0Crypto.Release.Ed25519ShaUpdate

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SBool SMem)
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Artifacts
open M0Crypto.Release.Ed25519Sha512Block (blockR blockPub blockE hOf blkOf)
open M0Crypto.Release.RoutineBranch (cmpImm_flags cmpReg_flags cond_eq cond_ne)

/-! ## Code -/

abbrev O : Nat := Ed25519Compact.sha512_update
def cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)
def spA (n : Nat) : SExpr := .add (.reg0 13) (cw n)

/-- A block on the frame: its accesses at `sp`, reading `rg`, writing `wg`. -/
def sg (g : List Instr) (rg wg : List (SExpr × Nat)) : Seg := { g, al := [(.reg0 13, 4)], wg, rg, As := [.reg0 13] }
/-- A block without accesses. -/
def sq (g : List Instr) : Seg := { g, al := [], wg := [], rg := [], As := [] }

/-- The buffer byte `r0 + r4`. -/
def bA : SExpr := .add (.reg0 0) (.reg0 4)
def sZ := sq [.cmpImm 2 0]
def sH : Seg :=
  { g := [.memImm .ldr 3 0 0, .movImm 4 127, .dp .ands 4 3, .addImm8 4 68, .movImm 6 196],
    al := [(.reg0 0, 4)], wg := [], rg := [(.reg0 0, 4)], As := [.reg0 0] }
def sB : Seg :=
  { g := [.memImm .ldrb 5 1 0, .memReg .strb 5 0 4, .addImm8 1 1, .addImm8 4 1, .addImm8 3 1, .subImm8 2 1],
    al := [(.reg0 1, 1), (bA, 1)], wg := [(bA, 1)], rg := [(.reg0 1, 1)], As := [.reg0 1, bA] }
def sC := sq [.dp .cmp 4 6]
def sF : Seg :=
  { g := [.memImm .str 3 0 0, .dp .cmp 4 6], al := [(.reg0 0, 4)], wg := [(.reg0 0, 4)], rg := [], As := [.reg0 0] }
def sS := sg [.strSp 0 0, .strSp 1 1, .strSp 2 2, .movImm 1 68, .addReg 1 1 0, .addImm8 0 4] [] [(spA 0, 12)]
def sR := sg [.ldrSp 0 0, .ldrSp 1 1, .ldrSp 2 2] [(spA 0, 12)] []

/-! ## Layout

Each position is the one before plus the size of what lies between: a segment, a `b<c>` or `b`
(`brSize`), a `bl` (`blSize`). The frame is `lr` and three slots, `FR` bytes below the entry SP,
and `m0c_sha512_block`'s stack below it: `D` in all. -/

local notation "FR" => 16
def D : Nat := FR + Ed25519Sha512Pass.D

def oZ : Nat := seqSize [.push 0 true, .subSp 3]
def oL : Nat := oZ + seqSize sZ.g + brSize
def oB : Nat := oL + seqSize sH.g
def oC : Nat := oB + seqSize sB.g + brSize
def oF : Nat := oC + seqSize sC.g + brSize
def oS : Nat := oF + seqSize sF.g + brSize
def oR : Nat := oS + seqSize sS.g + blSize
def oJ : Nat := oR + seqSize sR.g
def oP : Nat := oJ + brSize
def oN : Nat := oP + seqSize [.addSp 3, .pop 0 true]

def cs : List (Nat × Nat) := (O, O + oN) :: blockR.code

section ok
variable (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS]

def segAt (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && (sglueOk cs s.g (O + o) FR D s.al s.wg s.rg && traceOkE s.g s.As)
def brAt (o : Nat) (c : BitVec 4) (tgt : Nat) : Bool :=
  seqAt B (O + o) [.bcond c (brImm8 (O + o) (O + tgt))] && brOk (B := B) cs (O + o) (O + tgt) FR D (brImm8 (O + o) (O + tgt))
def siteAt (f : Routine) (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && seqAt B (O + o + seqSize s.g) [.bl (blImm (O + o + seqSize s.g) f.entry)] &&
  siteOkE (BS := BS) cs f s (O + o) FR D (blImm (O + o + seqSize s.g) f.entry)
def jmpAt (o tgt : Nat) : Bool :=
  seqAt B (O + o) [.b (brImm11 (O + o) (O + tgt))] && jmpOk (B := B) cs (O + o) (O + tgt) FR D (brImm11 (O + o) (O + tgt))

def segL : List (Nat × Seg) := [(oZ, sZ), (oL, sH), (oB, sB), (oC, sC), (oF, sF), (oR, sR)]

/-- The decided checks of a build. -/
structure Ok : Prop where
  segs : segL.all (fun p => segAt B p.1 p.2) = true
  b0 : brAt B BS (oZ + seqSize sZ.g) 0 oP = true
  b1 : brAt B BS (oB + seqSize sB.g) 0 oF = true
  b2 : brAt B BS (oC + seqSize sC.g) 1 oB = true
  b3 : brAt B BS (oF + seqSize sF.g) 1 oP = true
  st : siteAt B BS blockR oS sS = true
  j : jmpAt B BS oJ oZ = true
  en : seqAt B O [.push 0 true, .subSp (BitVec.ofNat 7 3)] = true
  po : seqAt B (O + oP) [.addSp (BitVec.ofNat 7 3), .pop 0 true] = true
  cd : rangesSub [(O, O + 4), (O + oP, O + oP + 4)] cs = true
  sz : O + oN ≤ BS ∧ O % 2 = 0
end ok

set_option maxHeartbeats 1200000 in
open M0Crypto.Release.Ed25519 (Build) in
theorem ok_b : ∀ b : Build, @Ok _ _ b.codeBytes := by
  intro b; cases b <;>
  refine @Ok.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, segL, List.all_cons, List.all_nil, segAt, siteAt, brAt, jmpAt, seqAt_eq_scan]) <;>
    decide +kernel

/-! ## Block effects -/

def ld0 : SExpr := .ld32 .mem0 (.reg0 0)
def ldS (n : Nat) : SExpr := .ld32 .mem0 (spA n)
def EZ : Eff := { z := some (.isZero (.reg0 2)) }
def EH : Eff := { regs := [(3, ld0), (4, .add (.and (cw 127) ld0) (cw 68)), (6, cw 196)] }
def EB : Eff :=
  { regs := [(1, .add (.reg0 1) (cw 1)), (2, .add (.reg0 2) (.const (-1#32))), (3, .add (.reg0 3) (cw 1)),
      (4, .add (.reg0 4) (cw 1))], clob := [5], z := some (.isZero (.add (.reg0 2) (.const (-1#32)))),
    mem := some (.w8 .mem0 bA (.ld8 .mem0 (.reg0 1))) }
def EC : Eff := { z := some (.isZero (.sub (.reg0 4) (.reg0 6))) }
def EF : Eff := { z := some (.isZero (.sub (.reg0 4) (.reg0 6))), mem := some (.w32 .mem0 (.reg0 0) (.reg0 3)) }
def ES : Eff :=
  { regs := [(0, .add (.reg0 0) (cw 4)), (1, .add (cw 68) (.reg0 0))],
    mem := some (.w32 (.w32 (.w32 .mem0 (spA 0) (.reg0 0)) (spA 4) (.reg0 1)) (spA 8) (.reg0 2)) }
def ER : Eff := { regs := [(0, ldS 0), (1, ldS 4), (2, ldS 8)] }

def effL : List (List Instr × Eff) := [(sZ.g, EZ), (sH.g, EH), (sB.g, EB), (sC.g, EC), (sF.g, EF), (sS.g, ES), (sR.g, ER)]

theorem effs : effL.all (fun p => effOk p.1 p.2) = true := by decide +kernel

theorem eff (i : Nat) {g : List Instr} {E : Eff} (hm : effL[i]? = some (g, E) := by rfl) : effOk g E = true :=
  by have := List.all_eq_true.mp effs _ (List.mem_of_getElem? hm); exact this

/-! ## The context relation -/

open M0Crypto.Spec.Sha512 (compress H0)
open M0Crypto.Release.Ed25519CallProg (ctxSize CtxInit ivWord)

/-- `S`'s whole blocks. -/
abbrev full (n : Nat) : Nat := n / 128 * 128

/-- **The stream `S` in the context at `a`**: its length, `H` over its whole blocks, its other
bytes in the buffer. -/
def ShaCtx (m : Mem) (a : Word) (S : List (BitVec 8)) : Prop :=
  read32 m a = BitVec.ofNat 32 S.length ∧ hOf m (a + 4#32) = Spec.Sha512.hash H0 (S.take (full S.length)) ∧
  ∀ j < S.length % 128, m (a + BitVec.ofNat 32 (68 + j)) = S.getD (full S.length + j) 0

theorem hash_append : ∀ (H : Array (BitVec 64)) (A C : List (BitVec 8)), A.length % 128 = 0 →
    Spec.Sha512.hash H (A ++ C) = Spec.Sha512.hash (Spec.Sha512.hash H A) C
  | H, [], C, _ => by rw [Spec.Sha512.hash, List.nil_append]
  | H, b :: A, C, h => by
    have hl : 128 ≤ (b :: A).length := by have := List.length_cons (a := b) (as := A); omega
    rw [List.cons_append, Spec.Sha512.hash, Spec.Sha512.hash, ← List.cons_append, List.take_append_of_le_length hl,
      List.drop_append_of_le_length hl]
    exact hash_append _ _ _ (by simp only [List.length_drop]; omega)
termination_by _ A => A.length
decreasing_by simp; omega

/-- One more whole block of `X`. -/
theorem hash_block {H : Array (BitVec 64)} {X : List (BitVec 8)} {f : Nat} (hf : f % 128 = 0) (hx : f + 128 ≤ X.length) :
    Spec.Sha512.hash H (X.take (f + 128)) = compress (Spec.Sha512.hash H (X.take f)) ((X.drop f).take 128) := by
  rw [List.take_add, hash_append _ _ _ (by simp; omega)]
  generalize hB : (X.drop f).take 128 = Bk
  have hb : Bk.length = 128 := by subst hB; simp; omega
  match Bk, hb with
  | b :: B', hb => rw [Spec.Sha512.hash, ← hb, List.take_length, List.drop_length, Spec.Sha512.hash]

/-- The bytes of the context agree in `m` and `m'`. -/
def Same196 (m m' : Mem) (a : Word) : Prop := ∀ j < ctxSize, m' (a + BitVec.ofNat 32 j) = m (a + BitVec.ofNat 32 j)

theorem Same196.rd {m m' : Mem} {a : Word} (h : Same196 m m' a) {o : Nat} (ho : o + 4 ≤ ctxSize) :
    read32 m' (a + BitVec.ofNat 32 o) = read32 m (a + BitVec.ofNat 32 o) :=
  Frame.read32_congr fun k hk => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

theorem adr (a : Word) (x y : Nat) : a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rd4 {m m' : Mem} {a : Word} {o n x : Nat}
    (h : ∀ j < n, m' (a + BitVec.ofNat 32 (o + j)) = m (a + BitVec.ofNat 32 (o + j))) (hx : x + 4 ≤ n) :
    read32 m' (a + BitVec.ofNat 32 (o + x)) = read32 m (a + BitVec.ofNat 32 (o + x)) :=
  Frame.read32_congr fun k hk => by rw [adr, Nat.add_assoc]; exact h _ (by omega)

/-- `H` depends on the context's bytes 4 to 67 only. -/
theorem hOf_congr {m m' : Mem} {a : Word} (h : ∀ j < 64, m' (a + BitVec.ofNat 32 (4 + j)) = m (a + BitVec.ofNat 32 (4 + j))) :
    hOf m' (a + 4#32) = hOf m (a + 4#32) := by
  refine congrArg List.toArray (List.map_congr_left fun i hi => ?_)
  have hi : i < 8 := List.mem_range.mp hi
  simp only [Ed25519Sha512Exec.pairAt, adr]
  rw [Nat.add_assoc 4 (8 * i) 4, rd4 h (by omega), rd4 (x := 8 * i) h (by omega)]

theorem ShaCtx.congr {m m' : Mem} {a : Word} {S : List (BitVec 8)} (h : Same196 m m' a) (hc : ShaCtx m a S) :
    ShaCtx m' a S := by
  obtain ⟨h0, h1, h2⟩ := hc
  refine ⟨?_, by rw [hOf_congr fun j hj => h _ (by simp only [ctxSize]; omega)]; exact h1, fun j hj => by rw [h _ (by simp only [ctxSize]; omega)]; exact h2 j hj⟩
  have := h.rd (o := 0) (by decide); simp only [BitVec.add_zero] at this; rw [this]; exact h0

theorem ShaCtx.memEq {W : List Rgn} {m m' : Mem} {a : Word} {S : List (BitVec 8)} (h : MemEq W m m')
    (hs : Sep [⟨a, ctxSize⟩] W) (hc : ShaCtx m a S) : ShaCtx m' a S :=
  hc.congr fun j hj => h _ (Sep.not_has hs ⟨_, List.mem_singleton.mpr rfl, j, hj, rfl⟩)

theorem iv_pairs : ∀ i < 8, ivWord (2 * i + 1) ++ ivWord (2 * i) = H0[i]! := by decide

/-- **A context just after `init` holds the empty stream.** -/
theorem ShaCtx.init {m : Mem} {a : Word} (h : CtxInit m a) : ShaCtx m a [] := by
  refine ⟨h.1, ?_, fun j hj => absurd hj (by simp)⟩
  rw [List.take_nil, Spec.Sha512.hash]
  have hp : ∀ i < 8, Ed25519Sha512Exec.pairAt m (a + 4#32 + BitVec.ofNat 32 (8 * i)) = H0[i]! := fun i hi => by
    simp only [Ed25519Sha512Exec.pairAt, adr]
    rw [show 4 + 8 * i + 4 = 4 + 4 * (2 * i + 1) by omega, show 4 + 8 * i = 4 + 4 * (2 * i) by omega,
      h.2 _ (by omega), h.2 _ (by omega)]
    exact iv_pairs i hi
  have : H0 = ((List.range 8).map fun i => H0[i]!).toArray := by decide
  rw [this]; exact congrArg List.toArray (List.map_congr_left fun i hi => hp i (List.mem_range.mp hi))

/-! ## The routine -/

/-- The input's region; none when it is empty. -/
def inR (s : State) : List Rgn := if (s.regs 2).toNat = 0 then [] else [⟨s.regs 1, (s.regs 2).toNat⟩]

/-- **`m0c_sha512_update`**: a context holding `M` comes to hold `M` and the `r2` bytes at `r1`. -/
def updR : Routine where
  entry := O
  code := cs
  stack := D
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ Sep [⟨s.regs 0, ctxSize⟩] (inR s)
  wr := fun s => [⟨s.regs 0, ctxSize⟩]
  rd := fun s => inR s ++ [⟨s.regs 0, ctxSize⟩]
  Post := fun s m _ => ∀ M, ShaCtx s.mem (s.regs 0) M → ShaCtx m (s.regs 0) (M ++ bytesAt s.mem (s.regs 1) (s.regs 2).toNat)
  clob := Ed25519Routines.hiRegs

/-! ## The loop state -/

section
variable (P : Nat → Word)
/-- The input's length, the stream length at the entry, the bytes in the buffer after `k` more. -/
def len : Nat := (P 2).toNat
def c0 : Nat := (P 4).toNat
def pos (k : Nat) : Nat := (c0 P + k) % 128
/-- The bytes outer pass `k` copies: up to the input's end or the buffer's. -/
def jn (k : Nat) : Nat := min (len P - k) (128 - pos P k)

def Wc : List Rgn := [⟨P 3 - BitVec.ofNat 32 D, D - 4⟩, ⟨P 0, ctxSize⟩]
def Rc {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) : List Rgn :=
  codeR base :: ⟨P 3 - BitVec.ofNat 32 D, D⟩ :: [⟨P 1, len P⟩, ⟨P 0, ctxSize⟩]

/-- The layout: the frame below `sp`; the context and the input apart from it and each other. -/
structure Lay : Prop where
  sp : D ≤ (P 3).toNat ∧ (P 3).toNat % 4 = 0
  a4 : (P 0).toNat % 4 = 0
  ab : (P 0).toNat + ctxSize ≤ 2 ^ 32 ∧ (P 1).toNat + len P ≤ 2 ^ 32
  w0 : (P 0).toNat + ctxSize ≤ (P 3).toNat - D ∨ (P 3).toNat ≤ (P 0).toNat
  w1 : len P = 0 ∨ (P 1).toNat + len P ≤ (P 3).toNat - D ∨ (P 3).toNat ≤ (P 1).toNat
  d : len P = 0 ∨ (P 0).toNat + ctxSize ≤ (P 1).toNat ∨ (P 1).toNat + len P ≤ (P 0).toNat

variable (m1 : Mem)
/-- The stream from the entry's whole blocks: the buffered bytes, then the input. -/
def Yof : List (BitVec 8) :=
  (List.range (c0 P % 128)).map (fun j => m1 (P 0 + BitVec.ofNat 32 (68 + j))) ++ bytesAt m1 (P 1) (len P)
def H₀ : Array (BitVec 64) := hOf m1 (P 0 + 4#32)
end

/-- `H` at `a` is `H` over `Y.take f`; the buffer holds `b` bytes of `Y` from `f`. -/
structure Ct (m : Mem) (a : Word) (H : Array (BitVec 64)) (Y : List (BitVec 8)) (f b : Nat) : Prop where
  h : hOf m (a + 4#32) = Spec.Sha512.hash H (Y.take f)
  bf : ∀ j < b, m (a + BitVec.ofNat 32 (68 + j)) = Y.getD (f + j) 0

set_option hygiene false in
local notation "fp" => (P 3 - BitVec.ofNat 32 FR)

section
variable (P : Nat → Word) (m1 : Mem)

/-- Before outer pass `k`. -/
structure IO (k : Nat) (u : State) : Prop where
  r0 : u.regs 0 = P 0
  r1 : u.regs 1 = P 1 + BitVec.ofNat 32 k
  r2 : u.regs 2 = BitVec.ofNat 32 (len P - k)
  r13 : u.regs 13 = fp
  fr : MemEq (Wc P) m1 u.mem
  n : read32 u.mem (P 0) = BitVec.ofNat 32 (c0 P + k)
  ct : Ct u.mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + k)) ((c0 P % 128 + k) % 128)
  k : k ≤ len P

/-- Before byte `i` of outer pass `k`. -/
structure II (k i : Nat) (u : State) : Prop where
  r0 : u.regs 0 = P 0
  r1 : u.regs 1 = P 1 + BitVec.ofNat 32 (k + i)
  r2 : u.regs 2 = BitVec.ofNat 32 (len P - k - i)
  r3 : u.regs 3 = BitVec.ofNat 32 (c0 P + k + i)
  r4 : u.regs 4 = BitVec.ofNat 32 (68 + pos P k + i)
  r6 : u.regs 6 = BitVec.ofNat 32 196
  r13 : u.regs 13 = fp
  fr : MemEq (Wc P) m1 u.mem
  n : read32 u.mem (P 0) = BitVec.ofNat 32 (c0 P + k)
  ct : Ct u.mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + k)) (pos P k + i)
  k : k < len P

variable (base : Word)
/-- The end of the body: the stream after the input. -/
def Qu (u : State) : Prop := u.pc = base + BitVec.ofNat 32 (O + oP) ∧ u.regs 13 = fp ∧
  read32 u.mem (P 0) = BitVec.ofNat 32 (c0 P + len P) ∧
  Ct u.mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + len P)) ((c0 P % 128 + len P) % 128)
end

/-! ## The trace -/

section
variable (Tb : Word → (Nat → Word) → List Event) (base : Word) (P : Nat → Word)

def bT (o : Nat) (s : Seg) (vs : List Word) : TrP := Tr.is (blockTrE s.g (base + BitVec.ofNat 32 (O + o)) s.As vs)
def rT (o : Nat) (c : BitVec 4) (tgt : Nat) (p : Bool) (ΨT ΨF : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), .bcond c (brImm8 (O + o) (O + tgt)), []⟩]) (Tr.cond p ΨT ΨF)
def jT (o tgt : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), .b (brImm11 (O + o) (O + tgt)), []⟩]) Ψ

/-- The length store after outer pass `k`; at the buffer's end, its compression and `Ψ`. -/
def flTr (k : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oF sF [P 0]) (rT base (oF + seqSize sF.g) 1 oP (decide (pos P k + jn P k ≠ 128)) (Tr.is [])
    (Tr.cat (bT base oS sS [fp]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + oS + seqSize sS.g),
      .bl (blImm (O + oS + seqSize sS.g) blockR.entry), []⟩])
      (Tr.cat (Tr.is (Tb base (pubOf [P 0 + 4#32, BitVec.ofNat 32 68 + P 0, fp])))
        (Tr.cat (bT base oR sR [fp]) (jT base oJ oZ Ψ))))))

/-- Byte `i` of outer pass `k`, the flush and `Ψo` after the last. -/
def inTr (k : Nat) (Ψo : TrP) (i : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oB sB [P 1 + BitVec.ofNat 32 (k + i), P 0 + BitVec.ofNat 32 (68 + pos P k + i)])
    (rT base (oB + seqSize sB.g) 0 oF (decide (len P - k = i + 1)) (flTr Tb base P k Ψo)
      (Tr.cat (bT base oC sC []) (rT base (oC + seqSize sC.g) 1 oB (decide (pos P k + i + 1 ≠ 128)) Ψ
        (flTr Tb base P k Ψo))))

/-- Outer pass `k`. -/
def outTr (k : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oZ sZ []) (rT base (oZ + seqSize sZ.g) 0 oP (decide (len P = k)) (Tr.is [])
    (Tr.cat (bT base oL sH [P 0]) (wTr (inTr Tb base P k Ψ) Nat.succ 128 0)))

/-- **The body's trace**: a function of `base`, `r0`–`r2`, `sp` and the stream length. -/
def upTr : TrP := wTr (outTr Tb base P) (fun k => k + jn P k) (len P + 1) 0
end

/-! ## Values -/

theorem and127 (x : Nat) : (BitVec.ofNat 32 127 &&& BitVec.ofNat 32 x) + BitVec.ofNat 32 68 = BitVec.ofNat 32 (68 + x % 128) := by
  apply BitVec.eq_of_toNat_eq
  have : 127 &&& x % 2 ^ 32 = x % 128 := by
    rw [Nat.and_comm, show 127 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reduceMod, this]; omega
theorem dec1 {x : Nat} (h : 1 ≤ x) : BitVec.ofNat 32 x + -1#32 = BitVec.ofNat 32 (x - 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel, BitVec.ofNat_add, BitVec.add_assoc]; simp
theorem inc (x : Nat) : BitVec.ofNat 32 x + BitVec.ofNat 32 1 = BitVec.ofNat 32 (x + 1) := (BitVec.ofNat_add x 1).symm
theorem beq0 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  by_cases e : x = 0
  · subst e; rfl
  · have : BitVec.ofNat 32 x ≠ 0#32 := fun h' => e (by have := congrArg BitVec.toNat h'; simp at this; omega)
    simp [this, e]
theorem sub196 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x - BitVec.ofNat 32 196 == 0) = decide (x = 196) := by
  by_cases e : x = 196
  · subst e; rfl
  · have : BitVec.ofNat 32 x - BitVec.ofNat 32 196 ≠ 0#32 := fun h' => e (by
      have := congrArg BitVec.toNat h'; simp [BitVec.toNat_sub] at this; omega)
    simp [this, e]
theorem ext8 (b : BitVec 8) : (b.setWidth 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]; omega
theorem ofs_ne (a : Word) {x y : Nat} (h : x ≠ y) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    a + BitVec.ofNat 32 x ≠ a + BitVec.ofNat 32 y := by bv_omega
theorem w32_ne (m : Mem) (a v : Word) {x : Nat} (h4 : 4 ≤ x) (hx : x < 2 ^ 32) :
    write32 m a v (a + BitVec.ofNat 32 x) = m (a + BitVec.ofNat 32 x) := by
  have h0 : a + BitVec.ofNat 32 x ≠ a := by bv_omega
  have h1 : a + BitVec.ofNat 32 x ≠ a + 1#32 := ofs_ne a (y := 1) (by omega) hx (by omega)
  have h2 : a + BitVec.ofNat 32 x ≠ a + 2#32 := ofs_ne a (y := 2) (by omega) hx (by omega)
  have h3 : a + BitVec.ofNat 32 x ≠ a + 3#32 := ofs_ne a (y := 3) (by omega) hx (by omega)
  simp only [write32, h0, h1, h2, h3, ↓reduceIte]

theorem w8_ne (m : Mem) (a v : Word) {x y : Nat} (h : x ≠ y) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    write8 m (a + BitVec.ofNat 32 y) v (a + BitVec.ofNat 32 x) = m (a + BitVec.ofNat 32 x) := by
  simp only [write8, ofs_ne a h hx hy, ↓reduceIte]

section
variable {m : Mem} {a : Word} {H : Array (BitVec 64)} {Y : List (BitVec 8)} {f b : Nat}

/-- A byte stored at buffer position `b`. -/
theorem Ct.w8 (c : Ct m a H Y f b) (hb : b < 128) {v : Word} (hv : v.extractLsb' 0 8 = Y.getD (f + b) 0) :
    Ct (write8 m (a + BitVec.ofNat 32 (68 + b)) v) a H Y f (b + 1) := by
  refine ⟨by rw [hOf_congr fun j hj => w8_ne m a v (by omega) (by omega) (by omega)]; exact c.h, fun j hj => ?_⟩
  by_cases e : j = b
  · subst e; simp only [write8, ite_true]; exact hv
  · rw [w8_ne m a v (by omega) (by omega) (by omega)]; exact c.bf j (by omega)
/-- The length word stored. -/
theorem Ct.w32 (c : Ct m a H Y f b) (hb : b ≤ 128) (v : Word) : Ct (write32 m a v) a H Y f b :=
  ⟨by rw [hOf_congr fun j hj => w32_ne m a v (by omega) (by omega)]; exact c.h,
    fun j hj => by rw [w32_ne m a v (by omega) (by omega)]; exact c.bf j hj⟩
theorem rd_w8 {x : Nat} (hx : 4 ≤ x) (hx' : x < 2 ^ 32) (v : Word) :
    read32 (write8 m (a + BitVec.ofNat 32 x) v) a = read32 m a := by
  have := rd4 (m := m) (m' := write8 m (a + BitVec.ofNat 32 x) v) (a := a) (o := 0) (n := 4) (x := 0)
    (fun j hj => w8_ne m a v (by omega) (by omega) hx') (by omega)
  simpa using this
end

section
variable {P : Nat → Word} {m1 : Mem}

theorem len_lt (P : Nat → Word) : len P < 2 ^ 32 := (P 2).isLt
theorem c0_lt (P : Nat → Word) : c0 P < 2 ^ 32 := (P 4).isLt

theorem Y_len : (Yof P m1).length = c0 P % 128 + len P := by simp [Yof, bytesAt_length]
theorem Y_get {x : Nat} (hx : x < len P) : (Yof P m1).getD (c0 P % 128 + x) 0 = m1 (P 1 + BitVec.ofNat 32 x) := by
  simp only [Yof, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]; simp [bytesAt, hx]

/-- The buffer's 128 bytes are the block of `Y` from `f`. -/
theorem blk_of {m : Mem} {a : Word} {H : Array (BitVec 64)} {Y : List (BitVec 8)} {f : Nat} (hc : Ct m a H Y f 128)
    (hf : f + 128 ≤ Y.length) : blkOf m (BitVec.ofNat 32 68 + a) = (Y.drop f).take 128 := by
  apply List.ext_getElem (by simp [blkOf]; omega)
  intro j h1 h2
  simp only [blkOf, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [show BitVec.ofNat 32 68 + a + BitVec.ofNat 32 j = a + BitVec.ofNat 32 (68 + j) by
    rw [BitVec.ofNat_add 68 j]; ac_rfl, hc.bf j (by simpa [blkOf] using h1)]
  simp [List.getD_eq_getElem?_getD, show f + j < Y.length by simp [blkOf] at h1; omega]

theorem hOf_of {m : Mem} {b : Word} {A : Array (BitVec 64)} (hs : A.size = 8)
    (h : ∀ i < 8, Ed25519Sha512Exec.pairAt m (b + BitVec.ofNat 32 (8 * i)) = A[i]!) : hOf m b = A := by
  apply Array.ext (by simp [hOf, hs])
  intro i h1 h2
  have hi : i < 8 := by simpa [hOf] using h1
  have := h i hi
  simp only [getElem!_pos A i (by omega)] at this
  simp [hOf, this]
end

theorem Ct.memEq {m m' : Mem} {a : Word} {H : Array (BitVec 64)} {Y : List (BitVec 8)} {f b : Nat} {W : List Rgn}
    (h : MemEq W m m') (hs : Sep [⟨a, ctxSize⟩] W) (c : Ct m a H Y f b) (hb : b ≤ 128) : Ct m' a H Y f b :=
  have e : ∀ x < ctxSize, m' (a + BitVec.ofNat 32 x) = m (a + BitVec.ofNat 32 x) := fun x hx =>
    h _ (Sep.not_has hs ⟨_, List.mem_singleton.mpr rfl, x, hx, rfl⟩)
  ⟨by rw [hOf_congr fun j hj => e _ (by simp only [ctxSize]; omega)]; exact c.h,
    fun j hj => by rw [e _ (by simp only [ctxSize]; omega)]; exact c.bf j hj⟩

theorem memEq_w32 (m : Mem) (a v : Word) : MemEq [⟨a, 4⟩] m (write32 m a v) := fun y hy => by
  have h : ∀ i < 4, y ≠ a + BitVec.ofNat 32 i := fun i hi e => hy ⟨_, List.mem_singleton.mpr rfl, i, hi, e⟩
  have := h 0 (by omega); have := h 1 (by omega); have := h 2 (by omega); have := h 3 (by omega)
  simp_all [write32]

/-- The three slot stores of the call site. -/
theorem slots3 (m : Mem) (p x y z : Word) :
    let m' := write32 (write32 (write32 m (p + BitVec.ofNat 32 0) x) (p + BitVec.ofNat 32 4) y) (p + BitVec.ofNat 32 8) z
    read32 m' (p + BitVec.ofNat 32 0) = x ∧ read32 m' (p + BitVec.ofNat 32 4) = y ∧ read32 m' (p + BitVec.ofNat 32 8) = z := by
  refine ⟨?_, ?_, M0Crypto.Armv6M.read32_write32_same _ _ _⟩
  · rw [read32_write32_add _ _ _ 8 0 (by omega) (by omega) (by omega), read32_write32_add _ _ _ 4 0 (by omega) (by omega) (by omega),
      M0Crypto.Armv6M.read32_write32_same]
  · rw [read32_write32_add _ _ _ 8 4 (by omega) (by omega) (by omega), M0Crypto.Armv6M.read32_write32_same]

theorem at_regs {base : Word} {f : Routine} {g : List Instr} {o : Nat} {u : State} (r : Reg)
    (h : r.val ≠ 14 ∧ r.val ≠ 15 := by decide) : (atCall base f g o u).regs r = (execAll g u).regs r :=
  blState_regs _ _ _ r h.1 h.2

theorem compress_size (H : Array (BitVec 64)) (b : List (BitVec 8)) : (compress H b).size = 8 := by
  simp [compress]

/-! ## The run -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem Ok.seg (h : Ok B BS) {o : Nat} {s : Seg} (hm : (o, s) ∈ segL) :
    seqAt B (O + o) s.g = true ∧ (sglueOk cs s.g (O + o) FR D s.al s.wg s.rg && traceOkE s.g s.As) = true := by
  have := List.all_eq_true.mp h.segs _ hm; simpa [segAt] using this

/-- The hypotheses of the run: the caller frame, the decided checks, the layout, the code at `m1`,
the call lemma of `m0c_sha512_block` with trace `Tb`. -/
structure Hy (base : Word) (P : Nat → Word) (m1 : Mem) (Tb : Word → (Nat → Word) → List Event) : Prop where
  F : Caller base (P 3) D (Wc P)
  ok : Ok B BS
  L : Lay P
  cd : CodeAt m1 base B
  bl : blockR.SpecT fun b s => Tr.is (Tb b (blockPub b s))

abbrev RF (base : Word) (P : Nat → Word) (u : State) (Q : State → Prop) (Ψ : TrP) : Prop :=
  ReachFT base (PcIn base cs) (Has (Rc P base)) (Has (Wc P)) (InStackWindow (P 3) D) u Q Ψ

variable {base : Word} {P : Nat → Word} {m1 : Mem} {Tb : Word → (Nat → Word) → List Event} {t : State}
  {Q : State → Prop}

theorem Hy.code (H : Hy base P m1 Tb) {u : State} (h : MemEq (Wc P) m1 u.mem) : CodeAt u.mem base B :=
  CodeAt.of_memEq H.cd h H.F.codeW

theorem Hy.cb (H : Hy base P m1 Tb) : base.toNat + BS ≤ 2 ^ 32 := by
  have h := H.F.codeW; simp only [codeR, Wc] at h; fp_simp at h; omega

theorem Hy.seg (H : Hy base P m1 Tb) (i : Nat) {o : Nat} {s : Seg} {Ψ : TrP} {vs : List Word}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp) (hfr : MemEq (Wc P) m1 t.mem)
    (hs : SGlueSides t (Rc P base) (Wc P) s.al s.wg s.rg) (hv : s.As.map (·.denote t) = vs)
    (kk : (execAll s.g t).pc = base + BitVec.ofNat 32 (O + o + seqSize s.g) → (execAll s.g t).regs 13 = fp →
      MemEq (sregions t s.wg) t.mem (execAll s.g t).mem → RF base P (execAll s.g t) Q Ψ)
    (hm : segL[i]? = some (o, s) := by rfl) : RF base P t Q (Tr.cat (bT base o s vs) Ψ) :=
  have h := H.ok.seg (List.mem_of_getElem? hm)
  ReachFT.seg1 H.F s h.1 h.2 hpc h13 (H.code hfr) hs hv fun hp h13 _ hm => kk hp h13 hm

theorem Hy.br (H : Hy base P m1 Tb) {o tgt : Nat} {c : BitVec 4} (hb : brAt B BS o c tgt = true) {ΨT ΨF : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp) (p : Bool) (hc : condPassed c t = p)
    (kT : p = true → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + tgt) → RF base P u Q ΨT)
    (kF : p = false → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + o + 2) → RF base P u Q ΨF) :
    RF base P t Q (rT base o c tgt p ΨT ΨF) := by
  simp only [brAt, Bool.and_eq_true] at hb
  exact ReachFT.br H.F (instrAt_of_seqAt hb.1) hb.2 hpc h13 p hc kT kF

theorem Hy.jmp (H : Hy base P m1 Tb) {Ψ : TrP} (hpc : t.pc = base + BitVec.ofNat 32 (O + oJ)) (h13 : t.regs 13 = fp)
    (kk : ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + oZ) → RF base P u Q Ψ) : RF base P t Q (jT base oJ oZ Ψ) := by
  have hj := H.ok.j
  simp only [jmpAt, Bool.and_eq_true] at hj
  exact ReachFT.jmp H.F (instrAt_of_seqAt hj.1) hj.2 hpc h13 kk

/-- A block that keeps the registers and the memory. -/
theorem same_of {g : List Instr} {E : Eff} (h : effOk g E = true) (hr : E.regs = []) (hc : E.clob = [])
    (hm : E.mem = some .mem0) (u : State) : Same u (execAll g u) :=
  ⟨(eff_run h u).mem _ hm, fun r hr' => by rw [(eff_run h u).reg r hr' (by simp [hc])]; simp [Eff.reg, hr, SExpr.denote]⟩
end

section
variable {P : Nat → Word} {m1 : Mem} {k i : Nat} {t u : State}

theorem II.same (h : II P m1 k i t) (hs : Same t u) : II P m1 k i u :=
  have e := fun (r : Reg) (hr : r.val ≠ 15) => hs.2 r hr
  ⟨(e 0 (by decide)).trans h.r0, (e 1 (by decide)).trans h.r1, (e 2 (by decide)).trans h.r2, (e 3 (by decide)).trans h.r3,
    (e 4 (by decide)).trans h.r4, (e 6 (by decide)).trans h.r6, (e 13 (by decide)).trans h.r13, hs.1 ▸ h.fr, hs.1 ▸ h.n,
    hs.1 ▸ h.ct, h.k⟩
theorem IO.same (h : IO P m1 k t) (hs : Same t u) : IO P m1 k u :=
  have e := fun (r : Reg) (hr : r.val ≠ 15) => hs.2 r hr
  ⟨(e 0 (by decide)).trans h.r0, (e 1 (by decide)).trans h.r1, (e 2 (by decide)).trans h.r2,
    (e 13 (by decide)).trans h.r13, hs.1 ▸ h.fr, hs.1 ▸ h.n, hs.1 ▸ h.ct, h.k⟩
end

macro "up_lay" L:ident : tactic =>
  `(tactic| (have := ($L).sp; have := ($L).a4; have := ($L).ab; have := ($L).w0; have := ($L).w1; have := ($L).d; have : D = 224 := rfl; have : ctxSize = 196 := rfl))
macro "at_pc" h:term : tactic => `(tactic| (rw [$h:term]; try rfl))
macro "up_fp" : tactic => `(tactic| ((try simp only [Wc, Rc]); fp_tac))

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {P : Nat → Word} {m1 : Mem}
  {Tb : Word → (Nat → Word) → List Event} {t : State}

/-- **Byte `i` of outer pass `k`**: copy it into the buffer, then the flush after the last. -/
theorem pass_in (H : Hy base P m1 Tb) {k i : Nat} {Ψo Ψ : TrP} (hI : II P m1 k i t) (hi : i < jn P k)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oB))
    (hx : ∀ u, II P m1 k (jn P k) u → u.pc = base + BitVec.ofNat 32 (O + oF) →
      RF base P u (Qu P m1 base) (flTr Tb base P k Ψo))
    (hg : i + 1 < jn P k → ∀ u, II P m1 k (i + 1) u → u.pc = base + BitVec.ofNat 32 (O + oB) →
      RF base P u (Qu P m1 base) Ψ) :
    RF base P t (Qu P m1 base) (inTr Tb base P k Ψo i Ψ) := by
  have L := H.L; up_lay L; have := len_lt P
  have hj : pos P k + i < 128 ∧ k + i < len P := by simp only [jn] at hi; have := hI.k; omega
  have hp : pos P k = (c0 P + k) % 128 := rfl
  have := c0_lt P
  refine H.seg 2 hpc hI.r13 hI.fr (by glue_tac [sB, bA, hI.r0, hI.r1, hI.r4, Wc, Rc])
    (by simp [sB, bA, SExpr.denote, hI.r0, hI.r1, hI.r4, Nat.add_assoc]) fun hp' h13 hm => ?_
  have E := eff_run (eff 2) t
  have J : II P m1 k (i + 1) (execAll sB.g t) := by
    have r := fun (r : Reg) (h1 : r.val ≠ 15) (h2 : r ∉ EB.clob) => E.reg r h1 h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h13, hI.fr.grow hm (by simp [sregions, sB, bA, SExpr.denote, hI.r0, hI.r4]; up_fp), ?_, ?_, hI.k⟩
    · rw [r 0 (by decide) (by decide)]; exact hI.r0
    · rw [r 1 (by decide) (by decide)]; show t.regs 1 + BitVec.ofNat 32 1 = _; rw [hI.r1, adr]; rfl
    · rw [r 2 (by decide) (by decide)]; show t.regs 2 + -1#32 = _; rw [hI.r2, dec1 (by omega)]; rfl
    · rw [r 3 (by decide) (by decide)]; show t.regs 3 + BitVec.ofNat 32 1 = _; rw [hI.r3, inc]; rfl
    · rw [r 4 (by decide) (by decide)]; show t.regs 4 + BitVec.ofNat 32 1 = _; rw [hI.r4, inc]; rfl
    · rw [r 6 (by decide) (by decide)]; exact hI.r6
    · rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, bA, hI.r0, hI.r4]
      rw [rd_w8 (by omega) (by omega)]; exact hI.n
    · rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, bA, hI.r0, hI.r4, hI.r1, Nat.add_assoc]
      refine hI.ct.w8 hj.1 ?_
      rw [read8, ext8, hI.fr.byte (by up_fp), show full (c0 P % 128 + k) + (pos P k + i) = c0 P % 128 + (k + i) by
        simp only [full, hp]; omega, Y_get hj.2]
  have hz : condPassed 0 (execAll sB.g t) = decide (len P - k = i + 1) := by
    rw [cond_eq, E.z _ rfl]; simp only [SBool.denote, SExpr.denote, hI.r2]
    rw [dec1 (by omega), beq0 (by omega)]; simp only [decide_eq_decide]; omega
  refine H.br H.ok.b1 (by at_pc hp') h13 _ hz (fun hT u hs hpu => ?_) (fun hF u hs hpu => ?_)
  · have e : jn P k = i + 1 := by simp only [jn, decide_eq_true_eq] at hi hT ⊢; omega
    exact hx u (e ▸ J.same hs) hpu
  have hF' : len P - k ≠ i + 1 := by simpa using hF
  have J' := J.same hs
  refine H.seg 3 (by at_pc hpu) J'.r13 J'.fr (by glue_tac [sC, sq]) (by simp [sC, sq]) fun hp2 h132 _ => ?_
  have E3 := eff_run (eff 3) u
  have J2 := J'.same (same_of (eff 3) rfl rfl rfl u)
  have hz : condPassed 1 (execAll sC.g u) = decide (pos P k + i + 1 ≠ 128) := by
    rw [cond_ne, E3.z _ rfl]; simp only [SBool.denote, SExpr.denote, J'.r4, J'.r6]
    have e : (68 + pos P k + (i + 1) = 196) ↔ (pos P k + i + 1 = 128) := by omega
    rw [sub196 (by omega)]; simp [e]
  refine H.br H.ok.b2 (by at_pc hp2) h132 _ hz (fun hT u2 hs2 hpu2 => ?_) (fun hF2 u2 hs2 hpu2 => ?_)
  · exact hg (by simp only [jn, decide_eq_true_eq] at hi hT ⊢; omega) u2 (J2.same hs2) hpu2
  · have e : jn P k = i + 1 := by simp only [jn, decide_eq_false_iff_not, ne_eq, Decidable.not_not] at hi hF2 ⊢; omega
    exact hx u2 (e ▸ J2.same hs2) (by at_pc hpu2)
end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {P : Nat → Word} {m1 : Mem}
  {Tb : Word → (Nat → Word) → List Event} {t : State} {Q : State → Prop}

theorem Hy.site (H : Hy base P m1 Tb) {Ψ : TrP} (hpc : t.pc = base + BitVec.ofNat 32 (O + oS)) (h13 : t.regs 13 = fp)
    (hfr : MemEq (Wc P) m1 t.mem) (hsd : SiteSidesE blockR base sS (O + oS) t (Rc P base) (Wc P))
    (hpre : blockR.Pre base (atCall base blockR sS.g (O + oS) t)) {pb : Nat → Word}
    (hb : blockPub base (atCall base blockR sS.g (O + oS) t) = pb)
    (kk : ∀ u, u.pc = base + BitVec.ofNat 32 (O + oR) → u.regs 13 = fp →
      MemEq (sregions t sS.wg ++ blockR.win (atCall base blockR sS.g (O + oS) t) ::
        blockR.wr (atCall base blockR sS.g (O + oS) t)) t.mem u.mem →
      MemEq (blockR.win (atCall base blockR sS.g (O + oS) t) :: blockR.wr (atCall base blockR sS.g (O + oS) t))
        (execAll sS.g t).mem u.mem →
      blockR.Post (atCall base blockR sS.g (O + oS) t) u.mem (u.regs 0) → RF base P u Q Ψ) :
    RF base P t Q (Tr.cat (bT base oS sS [fp]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + oS + seqSize sS.g),
      .bl (blImm (O + oS + seqSize sS.g) blockR.entry), []⟩])
      (Tr.cat (Tr.is (Tb base pb)) Ψ))) := by
  have h := H.ok.st
  simp only [siteAt, Bool.and_eq_true] at h
  exact ReachFT.siteE H.bl H.F sS h.1.1 (instrAt_of_seqAt h.1.2) h.2 hpc (Hi.self t) h13 (H.code hfr) hsd
    (by simp [sS, sg, SExpr.denote, h13]) hpre (by rw [hb]) fun u hu _ h13 _ hm hm' hp => kk u hu h13 hm hm' hp

/-- **The flush** after outer pass `k`: the length; at the buffer's end, its compression. -/
theorem fl_run (H : Hy base P m1 Tb) {k : Nat} {Ψ : TrP} (hI : II P m1 k (jn P k) t)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oF))
    (hn : ∀ u, IO P m1 (k + jn P k) u → u.pc = base + BitVec.ofNat 32 (O + oZ) → RF base P u (Qu P m1 base) Ψ) :
    RF base P t (Qu P m1 base) (flTr Tb base P k Ψ) := by
  have L := H.L; up_lay L; have := len_lt P; have := c0_lt P; have : Ed25519Sha512Pass.D = 208 := rfl; have := H.cb
  have hp : pos P k = (c0 P + k) % 128 := rfl
  have hj : pos P k + jn P k ≤ 128 ∧ k + jn P k ≤ len P := by simp only [jn]; have := hI.k; omega
  refine H.seg 4 hpc hI.r13 hI.fr (by glue_tac [sF, hI.r0, Wc, Rc]) (by simp [sF, SExpr.denote, hI.r0]) fun hp1 h13 hm => ?_
  have E := eff_run (eff 4) t
  have hmem : (execAll sF.g t).mem = write32 t.mem (P 0) (BitVec.ofNat 32 (c0 P + k + jn P k)) := by
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, hI.r0, hI.r3]
  have hn1 : read32 (execAll sF.g t).mem (P 0) = BitVec.ofNat 32 (c0 P + k + jn P k) := by
    rw [hmem]; exact M0Crypto.Armv6M.read32_write32_same _ _ _
  have hc1 : Ct (execAll sF.g t).mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + k)) (pos P k + jn P k) := by
    rw [hmem]; exact hI.ct.w32 hj.1 _
  have hf1 : MemEq (Wc P) m1 (execAll sF.g t).mem := hI.fr.grow hm (by simp [sregions, sF, SExpr.denote, hI.r0]; up_fp)
  have E1 : ∀ r : Reg, r.val ≠ 15 → (execAll sF.g t).regs r = t.regs r := fun r h => by
    rw [E.reg r h (by simp [EF])]; simp [Eff.reg, EF, SExpr.denote]
  have hz : condPassed 1 (execAll sF.g t) = decide (pos P k + jn P k ≠ 128) := by
    rw [cond_ne, E.z _ rfl]; simp only [SBool.denote, SExpr.denote, hI.r4, hI.r6]
    have e : (68 + pos P k + jn P k = 196) ↔ (pos P k + jn P k = 128) := by omega
    rw [sub196 (by omega)]; simp [e]
  refine H.br H.ok.b3 (by at_pc hp1) h13 _ hz (fun hT u hs hpu => ?_) (fun hF u hs hpu => ?_)
  · -- the input ends inside the buffer
    have hT' : pos P k + jn P k ≠ 128 := by simpa using hT
    have e : k + jn P k = len P := by simp only [jn] at hT' ⊢; omega
    have e1 : full (c0 P % 128 + k) = full (c0 P % 128 + len P) := by simp only [full, jn] at hT' ⊢; omega
    have e2 : pos P k + jn P k = (c0 P % 128 + len P) % 128 := by simp only [jn] at hT' ⊢; omega
    refine ReachT.done ⟨hpu, (hs.2 13 (by decide)).trans h13, ?_, ?_⟩
    · rw [hs.1, hn1, Nat.add_assoc, e]
    · rw [hs.1, ← e1, ← e2]; exact hc1
  -- the buffer is full: compress it
  have e : pos P k + jn P k = 128 := by simpa using hF
  have ur : ∀ r : Reg, r.val ≠ 15 → u.regs r = t.regs r := fun r h => (hs.2 r h).trans (E1 r h)
  have u0 := (ur 0 (by decide)).trans hI.r0; have u1 := (ur 1 (by decide)).trans hI.r1
  have u2 := (ur 2 (by decide)).trans hI.r2; have u13 := (ur 13 (by decide)).trans hI.r13
  have E5 := eff_run (eff 5) u
  have a0 : (atCall base blockR sS.g (O + oS) u).regs 0 = P 0 + 4#32 := by
    rw [at_regs 0, E5.reg 0 (by decide) (by decide)]; show u.regs 0 + BitVec.ofNat 32 4 = _; rw [u0]
  have a1 : (atCall base blockR sS.g (O + oS) u).regs 1 = BitVec.ofNat 32 68 + P 0 := by
    rw [at_regs 1, E5.reg 1 (by decide) (by decide)]; show BitVec.ofNat 32 68 + u.regs 0 = _; rw [u0]
  have a13 : (atCall base blockR sS.g (O + oS) u).regs 13 = fp := by
    rw [at_regs 13, E5.reg 13 (by decide) (by decide)]; exact u13
  have m5 : (execAll sS.g u).mem = write32 (write32 (write32 u.mem (fp + BitVec.ofNat 32 0) (P 0))
      (fp + BitVec.ofNat 32 4) (P 1 + BitVec.ofNat 32 (k + jn P k))) (fp + BitVec.ofNat 32 8)
      (BitVec.ofNat 32 (len P - k - jn P k)) := by
    rw [E5.mem _ rfl]; simp only [SMem.denote, SExpr.denote, spA, cw, u13, u0, u1, u2]
  have hm5 : MemEq [⟨fp + BitVec.ofNat 32 0, 4⟩, ⟨fp + BitVec.ofNat 32 4, 4⟩, ⟨fp + BitVec.ofNat 32 8, 4⟩] u.mem
      (execAll sS.g u).mem := by rw [m5]; exact ((memEq_w32 _ _ _).trans (memEq_w32 _ _ _)).trans (memEq_w32 _ _ _)
  have hc5 := Ct.memEq hm5 (by up_fp) (hs.1 ▸ hc1) (by omega)
  have sl := slots3 u.mem fp (P 0) (P 1 + BitVec.ofNat 32 (k + jn P k)) (BitVec.ofNat 32 (len P - k - jn P k))
  rw [← m5] at sl
  refine H.site (by at_pc hpu) u13 (hs.1 ▸ hf1) ?_ ?_ (by simp only [blockPub, a0, a1, a13]) fun u3 hp3 h133 hm3 hm3' hpost => ?_
  · unfold SiteSidesE; generalize atCall base blockR sS.g (O + oS) u = a at a0 a1 a13 ⊢
    glue_tac [sg, sS, Wc, Rc, spA, cw, blockR, a0, a1, a13, u13]
  · show (_ : Word).toNat % 4 = 0 ∧ (_ : Word).toNat % 4 = 0; rw [a0, a1]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize ha : atCall base blockR sS.g (O + oS) u = a at a0 a1 a13 hm3 hm3' hpost
  have am : a.mem = (execAll sS.g u).mem := by rw [← ha]; rfl
  simp only [blockR, Routine.win, a0, a1, a13, Ed25519Sha512Pass.D, Ed25519Sha512Code.BFRAME] at hm3 hm3' hpost
  rw [am] at hpost
  have hY := Y_len (P := P) (m1 := m1)
  have hf : full (c0 P % 128 + (k + jn P k)) = full (c0 P % 128 + k) + 128 := by simp only [full]; omega
  have hW3 : Sub (sregions u sS.wg ++ [⟨fp - BitVec.ofNat 32 (4 + 204), 4 + 204⟩, ⟨P 0 + 4#32, 8 * 8⟩]) (Wc P) := by
    simp only [sregions, sS, sg, List.map, SExpr.denote, spA, cw, u13, List.cons_append, List.nil_append]; up_fp
  have fr3 : MemEq (Wc P) m1 u3.mem := (hs.1 ▸ hf1).grow hm3 hW3
  have n3 : read32 u3.mem (P 0) = BitVec.ofNat 32 (c0 P + (k + jn P k)) := by
    rw [hm3.read32 (by simp only [sregions, sS, sg, List.map, SExpr.denote, spA, cw, u13, List.cons_append, List.nil_append]; up_fp),
      hs.1, hn1, Nat.add_assoc]
  have ct3 : Ct u3.mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + (k + jn P k))) ((c0 P % 128 + (k + jn P k)) % 128) := by
    refine ⟨?_, fun j hj => absurd hj (by omega)⟩
    have hc5' : Ct (execAll sS.g u).mem (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + k)) 128 := e ▸ hc5
    have hb1 := hash_block (H := H₀ P m1) (X := Yof P m1) (f := full (c0 P % 128 + k)) (by simp only [full]; omega)
      (by rw [hY]; simp only [full]; omega)
    rw [hf, hb1, hOf_of (compress_size _ _) hpost, hc5'.h, blk_of hc5' (by rw [hY]; simp only [full]; omega)]
  have rd3 : ∀ o, o ≤ 8 → read32 u3.mem (fp + BitVec.ofNat 32 o) = read32 (execAll sS.g u).mem (fp + BitVec.ofNat 32 o) :=
    fun o ho => hm3'.read32 (by up_fp)
  refine H.seg 5 (by at_pc hp3) h133 fr3 (by glue_tac [sR, sg, spA, cw, Wc, Rc, h133])
    (by simp [sR, sg, SExpr.denote, h133]) fun hp4 h134 _ => ?_
  have E6 := eff_run (eff 6) u3
  have v0 : (execAll sR.g u3).regs 0 = P 0 := by
    rw [E6.reg 0 (by decide) (by decide)]; show read32 u3.mem (u3.regs 13 + BitVec.ofNat 32 0) = _; rw [h133, rd3 0 (by omega)]; exact sl.1
  have v1 : (execAll sR.g u3).regs 1 = P 1 + BitVec.ofNat 32 (k + jn P k) := by
    rw [E6.reg 1 (by decide) (by decide)]; show read32 u3.mem (u3.regs 13 + BitVec.ofNat 32 4) = _; rw [h133, rd3 4 (by omega)]; exact sl.2.1
  have v2 : (execAll sR.g u3).regs 2 = BitVec.ofNat 32 (len P - (k + jn P k)) := by
    rw [E6.reg 2 (by decide) (by decide), ← Nat.sub_sub]; show read32 u3.mem (u3.regs 13 + BitVec.ofNat 32 8) = _
    rw [h133, rd3 8 (by omega)]; exact sl.2.2
  have vm : (execAll sR.g u3).mem = u3.mem := E6.mem _ rfl
  have J : IO P m1 (k + jn P k) (execAll sR.g u3) := ⟨v0, v1, v2, h134, vm ▸ fr3, vm ▸ n3, vm ▸ ct3, by omega⟩
  exact H.jmp (by at_pc hp4) h134 fun w hw hpw => hn w (J.same hw) hpw

/-- **Outer pass `k`**: at the input's end, `Qu`; else the inner loop over `jn P k` bytes. -/
theorem pass_out (H : Hy base P m1 Tb) {k : Nat} {Ψ : TrP} (hI : IO P m1 k t) (hpc : t.pc = base + BitVec.ofNat 32 (O + oZ))
    (hn : k < len P → ∀ u, IO P m1 (k + jn P k) u → u.pc = base + BitVec.ofNat 32 (O + oZ) → RF base P u (Qu P m1 base) Ψ) :
    RF base P t (Qu P m1 base) (outTr Tb base P k Ψ) := by
  have L := H.L; up_lay L; have := len_lt P; have := c0_lt P; have := H.cb; have := hI.k
  refine H.seg 0 hpc hI.r13 hI.fr (by glue_tac [sZ, sq]) (by simp [sZ, sq]) fun hp1 h13 _ => ?_
  have E := eff_run (eff 0) t
  have I1 := hI.same (same_of (eff 0) rfl rfl rfl t)
  have hz : condPassed 0 (execAll sZ.g t) = decide (len P = k) := by
    rw [cond_eq, E.z _ rfl]; simp only [SBool.denote, SExpr.denote, hI.r2]
    rw [beq0 (by omega)]; simp only [decide_eq_decide]; omega
  refine H.br H.ok.b0 (by at_pc hp1) h13 _ hz (fun hT u hs hpu => ?_) (fun hF u hs hpu => ?_)
  · have e : k = len P := by simpa [eq_comm] using hT
    have I2 := I1.same hs
    exact ReachT.done ⟨hpu, I2.r13, e ▸ I2.n, e ▸ I2.ct⟩
  have hk : k < len P := by have : len P ≠ k := by simpa using hF
                            omega
  have I2 := I1.same hs
  refine H.seg 1 (by at_pc hpu) I2.r13 I2.fr (by glue_tac [sH, I2.r0, Wc, Rc]) (by simp [sH, SExpr.denote, I2.r0])
    fun hp2 h132 _ => ?_
  have E1 := eff_run (eff 1) u
  have hl : read32 u.mem (u.regs 0) = BitVec.ofNat 32 (c0 P + k) := by rw [I2.r0]; exact I2.n
  have hp : pos P k = (c0 P + k) % 128 := rfl
  have J : II P m1 k 0 (execAll sH.g u) := by
    have r := fun (r : Reg) (h1 : r.val ≠ 15) (h2 : r ∉ EH.clob) => E1.reg r h1 h2
    have vm : (execAll sH.g u).mem = u.mem := E1.mem _ rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h132, vm ▸ I2.fr, vm ▸ I2.n, ?_, hk⟩
    · rw [r 0 (by decide) (by decide)]; exact I2.r0
    · rw [r 1 (by decide) (by decide)]; exact I2.r1
    · rw [r 2 (by decide) (by decide)]; exact I2.r2
    · rw [r 3 (by decide) (by decide)]; show read32 u.mem (u.regs 0) = _; rw [hl, Nat.add_zero]
    · rw [r 4 (by decide) (by decide)]; show (BitVec.ofNat 32 127 &&& read32 u.mem (u.regs 0)) + BitVec.ofNat 32 68 = _
      rw [hl, and127, hp, Nat.add_zero]
    · rw [r 6 (by decide) (by decide)]; rfl
    · have e : (c0 P % 128 + k) % 128 = pos P k + 0 := by rw [hp]; omega
      exact vm ▸ e ▸ I2.ct
  have hj0 : 0 < jn P k := by simp only [jn]; have : pos P k < 128 := Nat.mod_lt _ (by decide); omega
  have hj1 : jn P k ≤ 128 := by simp only [jn]; omega
  refine ReachT.wloop (I := fun i u => II P m1 k i u ∧ i < jn P k ∧ u.pc = base + BitVec.ofNat 32 (O + oB))
    (go := fun i => decide (i + 1 < jn P k)) (fun i => jn P k - 1 - i) (fun i hi => by simp at hi; omega)
    (fun i u Ψ' hI' hc => pass_in H hI'.1 hI'.2.1 hI'.2.2 (fun u hu hpu => fl_run H hu hpu (hn hk))
      fun hj u' hu hp' => hc (by simpa using hj) u' ⟨hu, hj, hp'⟩)
    _ 0 _ (by omega) ⟨J, hj0, by at_pc hp2⟩

/-- **The body's loop** from `IO 0` reaches `Qu`. -/
theorem up_run (H : Hy base P m1 Tb) (hI : IO P m1 0 t) (hpc : t.pc = base + BitVec.ofNat 32 (O + oZ)) :
    RF base P t (Qu P m1 base) (upTr Tb base P) :=
  ReachT.wloop (I := fun k u => IO P m1 k u ∧ u.pc = base + BitVec.ofNat 32 (O + oZ))
    (go := fun k => decide (k < len P)) (fun k => len P - k)
    (fun k hk => by have : pos P k < 128 := Nat.mod_lt _ (by decide)
                    simp only [jn, decide_eq_true_eq] at hk ⊢; omega)
    (fun k u Ψ hI' hc => pass_out H hI'.1 hI'.2 fun hk u' hu hp => hc (by simpa using hk) u' ⟨hu, hp⟩)
    _ 0 t (by omega) ⟨hI, hpc⟩

/-! ## The result -/

theorem take_full {M : List (BitVec 8)} : (M.take (full M.length)).length = full M.length := by
  simp only [List.length_take, full]; omega

/-- **The result**: from `ShaCtx` of `M` at the entry, the context holds `M` and the input. -/
theorem post_of {m0 m1 u : Mem} {P : Nat → Word} {M : List (BitVec 8)} (hM : ShaCtx m0 (P 0) M)
    (h4 : read32 m0 (P 0) = P 4) (hc : Same196 m0 m1 (P 0)) (hi : bytesAt m1 (P 1) (len P) = bytesAt m0 (P 1) (len P))
    (hn : read32 u (P 0) = BitVec.ofNat 32 (c0 P + len P))
    (hct : Ct u (P 0) (H₀ P m1) (Yof P m1) (full (c0 P % 128 + len P)) ((c0 P % 128 + len P) % 128)) :
    ShaCtx u (P 0) (M ++ bytesAt m0 (P 1) (len P)) := by
  obtain ⟨h0, hh, hb⟩ := hM
  have hc0 : c0 P = M.length % 2 ^ 32 := by simp only [c0, ← h4, h0, BitVec.toNat_ofNat]
  have hcl : c0 P % 128 = M.length % 128 := by rw [hc0]; omega
  have hY : Yof P m1 = M.drop (full M.length) ++ bytesAt m0 (P 1) (len P) := by
    rw [Yof, hi]; congr 1
    refine List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_drop, full]; omega) fun j h1 _ => ?_
    have hj : j < M.length % 128 := by simp only [List.length_map, List.length_range] at h1; omega
    rw [List.getElem_map, List.getElem_range, List.getElem_drop, hc _ (by simp only [ctxSize]; omega), hb j hj,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [full]; omega), Option.getD_some]
  have hsplit : M ++ bytesAt m0 (P 1) (len P) = M.take (full M.length) ++ Yof P m1 := by
    rw [hY, ← List.append_assoc, List.take_append_drop]
  have hlen : (M ++ bytesAt m0 (P 1) (len P)).length = M.length + len P := by simp [bytesAt_length]
  have hf : full M.length + full (c0 P % 128 + len P) = full (M.length + len P) := by simp only [full]; omega
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [hn, hlen]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, hc0]; omega
  · have e := List.take_length_add_append (l₁ := M.take (full M.length)) (l₂ := Yof P m1) (full (c0 P % 128 + len P))
    rw [take_full] at e
    rw [hct.h, H₀, hOf_congr (fun j hj => hc _ (by simp only [ctxSize]; omega)), hh,
      ← hash_append _ _ _ (by rw [take_full]; simp only [full]; omega), hlen, ← hf, hsplit, e]
  · rw [hlen] at hj
    rw [hct.bf j (by omega), hlen, ← hf, hsplit, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [take_full]; omega), take_full]
    congr 2; omega

/-- **The state at the body's start**: outer pass 0. -/
theorem io0 {P : Nat → Word} {t : State} (q0 : t.regs 0 = P 0) (q1 : t.regs 1 = P 1) (q2 : t.regs 2 = P 2)
    (q13 : t.regs 13 = fp) (qn : read32 t.mem (P 0) = P 4) : IO P t.mem 0 t := by
  refine ⟨q0, by rw [q1]; exact (BitVec.add_zero _).symm, by rw [q2, Nat.sub_zero, len, BitVec.ofNat_toNat, BitVec.setWidth_eq], q13,
    fun _ _ => rfl, by rw [qn, Nat.add_zero, c0, BitVec.ofNat_toNat, BitVec.setWidth_eq], ⟨?_, fun j hj => ?_⟩, Nat.zero_le _⟩
  · rw [Nat.add_zero, show full (c0 P % 128) = 0 by simp only [full]; omega, List.take_zero, Spec.Sha512.hash]; rfl
  · rw [Nat.add_zero, Nat.mod_mod] at hj
    rw [show full (c0 P % 128 + 0) = 0 by simp only [full]; omega, Nat.zero_add, Yof,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj), List.getElem?_eq_getElem (by simpa using hj),
      Option.getD_some, List.getElem_map, List.getElem_range]
end

/-! ## The stack effect -/

open M0Crypto.Release.StackEffect (Ef EffT frame_te GP SIR pass_of sir_pass above_sub reg_in reg_sub_above inRD_of
  site_gp jmp_gp br_gp InRD reg_split winsChk blkChk)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The public values: `r0`–`r2`, `sp` and the stream length at `r0`. -/
def updPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 1, s.regs 2, s.regs 13, read32 s.mem (s.regs 0)]
def updFp (base : Word) (P : Nat → Word) : Word → Prop := Has [codeR base, ⟨P 1, len P⟩, ⟨P 0, ctxSize⟩]
def updRq (base : Word) (P : Nat → Word) (y : Word) : Prop :=
  Has [codeR base] y ∨ Region (P 0) (68 + c0 P % 128) y ∨ Region (P 1) (len P) y
def updWd (P : Nat → Word) : Word → Prop := Region (P 0) (68 + (c0 P + len P) % 128)
/-- **The effect of `m0c_sha512_update`**: it reads the context's bytes before the buffer, its pending
bytes and the input, and writes the context's bytes before the buffer and its new pending bytes. -/
def updE (base : Word) (P : Nat → Word) : TrP := EffT D (updFp base P) (updRq base P) (updWd P) (P 3)

/-- The GP's hypotheses at public values `P` (as `frame_te`'s). -/
structure GH (base sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Prop where
  room : (sp0 - P 3).toNat + D ≤ n
  n32 : n < 2 ^ 32
  F : ∀ y, updFp base P y → BelowEntry sp0 n y → AtOrAboveSp sp0 (P 3) y
  R : ∀ y, updRq base P y → BelowEntry sp0 n y → U y
end

section
variable {sp0 : Word} {n : Nat} {U : Word → Prop} {P : Nat → Word}

/-- At the entry; with the buffer's first `w` bytes. -/
def R0 (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop := U y ∨ Region (P 3 - BitVec.ofNat 32 4) 4 y
def Rk (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (w : Nat) (y : Word) : Prop :=
  R0 U P y ∨ Region (P 0) (68 + w) y ∧ BelowEntry sp0 n y
/-- The buffer bytes known written before byte `i` of outer pass `k`: after the first, all. -/
def wk (P : Nat → Word) (k i : Nat) : Nat := if k = 0 then c0 P % 128 + i else 128
abbrev Jf (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Ef → Prop :=
  SIR sp0 fp fun y => R0 U P y ∨ updWd P y ∧ BelowEntry sp0 n y
abbrev KO (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (k : Nat) : Ef → Prop :=
  fun q => k ≤ len P ∧ SIR sp0 fp (Rk sp0 n U P (wk P k 0)) q
abbrev KI (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (k i : Nat) : Ef → Prop :=
  fun q => i < jn P k ∧ SIR sp0 fp (Rk sp0 n U P (wk P k i)) q

theorem gp_fact {p : Prop} {I J : Ef → Prop} {Φ : TrP} (h : p → GP sp0 n I Φ J) : GP sp0 n (fun q => p ∧ I q) Φ J :=
  fun q hq => h hq.1 q hq.2

theorem reg_le {a y : Word} {x N : Nat} (h : Region a x y) (hx : x ≤ N) : Region a N y := by
  simp only [Region] at h ⊢; omega

theorem wk_le (P : Nat → Word) (k : Nat) : wk P k 0 ≤ 128 := by
  have := Nat.mod_lt (c0 P) (by decide : 128 > 0); unfold wk; split <;> omega

/-- A segment without accesses keeps `SIR`. -/
theorem q_gp {sp : Word} {R : Word → Prop} {s : Seg} {pc : Word} (hb : blkChk s.rg s.wg (s.rg ++ s.wg) s.g = true)
    (hl : s.As = []) (hr : winsChk s.As [] s.rg = true) (hw : winsChk s.As [] s.wg = true) :
    GP sp0 n (SIR sp0 sp R) (Tr.is (blockTrE s.g pc s.As [])) (SIR sp0 sp R) :=
  GP.post (sir_pass hb (pass_of (vs := []) (Wr := []) (Ww := []) (by rw [hl]; rfl) hr hw (by simp) (by simp)))
    fun _ h => h.mono fun _ h => .inl h

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

theorem GH.r16 (G : GH base sp0 n U P) : (sp0 - fp).toNat + Ed25519Sha512Pass.D ≤ n := by
  have := G.room; have := G.n32; have : Ed25519Sha512Pass.D = 208 := rfl; simp only [D] at *
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega
theorem GH.up (G : GH base sp0 n U P) {y : Word} (h : AtOrAboveSp sp0 (P 3) y) : AtOrAboveSp sp0 fp y :=
  above_sub h (by have := G.room; have := G.n32; simp only [D] at *; omega)
theorem GH.ctx (G : GH base sp0 n U P) {y : Word} {w : Nat} (h : Region (P 0) w y) (hw : w ≤ ctxSize)
    (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.up (G.F y ⟨_, .tail _ (.tail _ (.head _)), Rgn.of_region (reg_le h hw)⟩ he)
theorem GH.ctxo (G : GH base sp0 n U P) {y : Word} {x w : Nat} (h : Region (P 0 + BitVec.ofNat 32 x) w y)
    (hw : x + w ≤ ctxSize) (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.ctx (reg_in h hw (by decide)) (Nat.le_refl _) he
theorem GH.buf (G : GH base sp0 n U P) {y : Word} {x : Nat} (h : Region (P 0) x y) (hx : x ≤ 68 + c0 P % 128)
    (he : BelowEntry sp0 n y) : U y := G.R y (.inr (.inl (reg_le h hx))) he
theorem GH.inp (G : GH base sp0 n U P) {y : Word} {x w : Nat} (h : Region (P 1 + BitVec.ofNat 32 x) w y)
    (hx : x + w ≤ len P) (he : BelowEntry sp0 n y) : U y := G.R y (.inr (.inr (reg_in h hx (len_lt P)))) he
theorem GH.code (G : GH base sp0 n U P) {y : Word} (h : Region base BS y) (he : BelowEntry sp0 n y) : U y :=
  G.R y (.inl ⟨_, .head _, Rgn.of_region h⟩) he

variable {Tb : Word → (Nat → Word) → List Event}

/-- **The flush's GP**: the length, and at the buffer's end the block on the full buffer. -/
theorem GH.fl (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) {k : Nat} (hk : k ≤ len P) {Ψ : TrP}
    (hn : GP sp0 n (KO sp0 n U P (k + jn P k)) Ψ (Jf sp0 n U P)) :
    GP sp0 n (SIR sp0 fp (Rk sp0 n U P (wk P k (jn P k)))) (flTr Tb base P k Ψ) (Jf sp0 n U P) := by
  have hj : pos P k + jn P k ≤ 128 ∧ k + jn P k ≤ len P := by simp only [jn, pos]; omega
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0]) (Wr := []) (Ww := [(0, 4)]) rfl (by decide) (by decide)
    (by simp) (by pass_tac []; exact fun y h he => G.ctx h (by decide) he))) fun _ h => h.mono fun _ h => .inl h)
    (br_gp _ (fun hT => GP.nil fun q h => h.mono fun y hy => ?_) fun hF => ?_)
  · have hT' : pos P k + jn P k ≠ 128 := by simpa using hT
    rcases hy with hy | ⟨h, he⟩
    · exact .inl hy
    · refine .inr ⟨reg_le h ?_, he⟩
      unfold wk; split
      · subst k; simp only [jn, pos] at hT' ⊢; omega
      · omega
  have e : pos P k + jn P k = 128 := by simpa using hF
  have w128 : wk P k (jn P k) = 128 := by
    unfold wk; split
    · subst k; simp only [pos] at e; omega
    · rfl
  refine site_gp (sir_pass (by decide) (pass_of (vs := [fp]) (Wr := []) (Ww := [(0, 12)]) rfl (by decide) (by decide) (by simp)
      (by pass_tac []; exact fun y h _ => reg_sub_above h (by omega) (by have := G.room; have := G.n32; simp only [D] at *; omega))))
    rfl rfl rfl (show EffT _ _ _ _ fp _ from hbE base (pubOf [P 0 + 4#32, BitVec.ofNat 32 68 + P 0, fp])) G.r16 G.n32
    (fun y h _ => h.elim) (fun y h he => ?_) ?_
  · rcases h with h | h | h
    · exact .inl (.inl (.inl (G.R y (.inr (.inl (reg_in (c := 4) (w := 64) h (by omega) (by omega)))) he)))
    · change Region (BitVec.ofNat 32 68 + P 0) 128 y at h
      rw [BitVec.add_comm] at h
      exact .inl (.inr ⟨by rw [w128]; exact reg_in h (by decide) (by decide), he⟩)
    · exact .inl (.inl (.inl (G.code h he)))
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [fp]) (Wr := [(0, 12)]) (Ww := []) rfl (by decide) (by decide)
    (by pass_tac []; exact fun y h he => .inl (.inr ⟨inRD_of (vs := [fp]) rfl (List.mem_singleton_self _)
      (by decide : StackEffect.atomOf [.reg0 13] (spA 0) = some (0, BitVec.ofNat 32 0)) rfl (by simpa using h), he⟩)) (by simp)))
    fun q h => h.mono (R' := Rk sp0 n U P (wk P (k + jn P k) 0)) fun y hy => ?_) (jmp_gp (GP.pre (fun q h => ⟨hj.2, h⟩) hn))
  rcases hy with hy | ⟨h, he⟩
  · exact .inl (.inl (.inl (.inl hy)))
  · exact .inl (.inl (.inl (.inr ⟨by rw [w128]; exact reg_le h (by have := wk_le P (k + jn P k); omega), he⟩)))

/-- **The inner loop's GP**: each byte joins the buffer's written prefix. -/
theorem GH.inner (G : GH base sp0 n U P) {k : Nat} {Ψo : TrP}
    (hx : GP sp0 n (SIR sp0 fp (Rk sp0 n U P (wk P k (jn P k)))) (flTr Tb base P k Ψo) (Jf sp0 n U P)) :
    ∀ f i, jn P k - 1 - i < f → GP sp0 n (KI sp0 n U P k i) (wTr (inTr Tb base P k Ψo) Nat.succ f i) (Jf sp0 n U P) := by
  refine GP.wloop (K := KI sp0 n U P k) (go := fun i => decide (i + 1 < jn P k)) (fun i => jn P k - 1 - i)
    (fun i h => by simp at h; omega) fun i Ψ h => gp_fact fun hi => ?_
  have hj : pos P k + i < 128 ∧ k + i < len P := by simp only [jn, pos] at hi ⊢; omega
  have hx' : ∀ {i'}, jn P k = i' → GP sp0 n (SIR sp0 fp (Rk sp0 n U P (wk P k i'))) (flTr Tb base P k Ψo) (Jf sp0 n U P) :=
    fun e => e ▸ hx
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 1 + BitVec.ofNat 32 (k + i),
      P 0 + BitVec.ofNat 32 (68 + pos P k + i)]) (Wr := [(0, 1)]) (Ww := [(1, 1)]) rfl (by decide) (by decide)
    (by pass_tac []; exact fun y h he => .inl (.inl (G.inp h (by omega) he)))
    (by pass_tac []; exact fun y h he => G.ctxo h (by simp only [ctxSize]; omega) he)))
    fun q h => h.mono (R' := Rk sp0 n U P (wk P k (i + 1))) fun y hy => ?_) ?_
  · rcases hy with hy | ⟨h, he⟩
    · exact .inl (.inl hy)
    · unfold wk at h ⊢; split
      · rename_i h0; subst h0
        simp only [↓reduceIte] at h
        rw [show 68 + (c0 P % 128 + (i + 1)) = 68 + c0 P % 128 + i + 1 by omega] at h
        rcases reg_split h with h | h
        · exact .inl (.inr ⟨by rw [show 68 + (c0 P % 128 + i) = 68 + c0 P % 128 + i by omega]; exact h, he⟩)
        · refine .inr ⟨inRD_of (vs := [P 1 + BitVec.ofNat 32 (0 + i), P 0 + BitVec.ofNat 32 (68 + pos P 0 + i)]) rfl
            (List.mem_singleton_self _) (by decide : StackEffect.atomOf [.reg0 1, bA] bA = some (1, 0#32)) rfl ?_, he⟩
          rw [BitVec.add_zero, show pos P 0 = c0 P % 128 by simp only [pos, Nat.add_zero]]; exact h
      · rename_i h0; simp only [h0, ↓reduceIte] at h; exact .inl (.inr ⟨h, he⟩)
  refine br_gp _ (fun hT => hx' (by simp only [jn, pos, decide_eq_true_eq] at hi hT ⊢; omega)) fun hF => ?_
  refine GP.cat (q_gp (by decide) rfl (by decide) (by decide)) (br_gp _ (fun hT => ?_) fun hF2 => ?_)
  · have t1 : pos P k + i + 1 ≠ 128 := by simpa using hT
    have t2 : len P - k ≠ i + 1 := by simpa using hF
    have hg : i + 1 < jn P k := by simp only [jn, pos] at hi t1 t2 ⊢; omega
    exact GP.pre (fun q h => ⟨hg, h⟩) (h (by simpa using hg))
  · have t1 : pos P k + i + 1 = 128 := by simpa using hF2
    exact hx' (by simp only [jn, pos] at hi t1 ⊢; omega)

/-- **Outer pass `k`'s GP**. -/
theorem GH.out (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) {k : Nat} {Ψ : TrP}
    (hn : k < len P → GP sp0 n (KO sp0 n U P (k + jn P k)) Ψ (Jf sp0 n U P)) :
    GP sp0 n (KO sp0 n U P k) (outTr Tb base P k Ψ) (Jf sp0 n U P) := by
  refine gp_fact fun hk => ?_
  refine GP.cat (q_gp (by decide) rfl (by decide) (by decide))
    (br_gp _ (fun hT => GP.nil fun q h => h.mono fun y hy => ?_) fun hF => ?_)
  · have e : len P = k := by simpa using hT
    rcases hy with hy | ⟨h, he⟩
    · exact .inl hy
    · refine .inr ⟨reg_le h ?_, he⟩
      unfold wk; split
      · subst k; omega
      · omega
  have hk' : k < len P := by have : len P ≠ k := by simpa using hF
                             omega
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0]) (Wr := [(0, 4)]) (Ww := []) rfl (by decide) (by decide)
    (by pass_tac []; exact fun y h he => .inl (.inl (G.buf h (by omega) he))) (by simp))) fun _ h => h.mono fun _ h => .inl h) ?_
  have hj0 : 0 < jn P k := by simp only [jn, pos]; omega
  exact GP.pre (fun q h => ⟨hj0, h⟩) (G.inner (G.fl hbE (Nat.le_of_lt hk') (hn hk')) 128 0 (by simp only [jn, pos]; omega))

/-- **The body's GP**: from the entry's `R0`, the context's bytes before the buffer and its pending bytes. -/
theorem GH.upd (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) :
    GP sp0 n (SIR sp0 fp (R0 U P)) (upTr Tb base P) (Jf sp0 n U P) :=
  GP.pre (fun q h => ⟨Nat.zero_le _, h.mono fun y hy => hy.elim id fun ⟨h, he⟩ =>
      .inl (G.buf h (by simp only [wk, ↓reduceIte]; omega) he)⟩)
    (GP.wloop (K := KO sp0 n U P) (go := fun k => decide (k < len P)) (fun k => len P - k)
      (fun k hk => by simp only [jn, pos, decide_eq_true_eq] at hk ⊢; omega)
      (fun k Ψ h => G.out hbE fun hk => h (by simpa using hk)) _ 0 (by omega))
end
end

/-! ## The routine's TE -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The body's reads lie in the routine's: the input's region is empty when its length is 0. -/
theorem rc_rd {base : Word} {s : State} {P : Nat → Word} (q0 : s.regs 0 = P 0) (q1 : s.regs 1 = P 1)
    (q2 : s.regs 2 = P 2) (q13 : s.regs 13 = P 3) {y : Word} (h : Has (Rc P base) y) : updR.RdP base s y := by
  obtain ⟨r, hr, hy⟩ := h
  simp only [Rc, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, .head _, hy⟩
  · exact ⟨_, .tail _ (.head _), by simpa [Routine.win, updR, q13] using hy⟩
  · obtain ⟨o, ho, rfl⟩ := hy
    have h0 : (s.regs 2).toNat ≠ 0 := by rw [q2]; exact fun h => by simp only [len, h] at ho; omega
    exact ⟨⟨s.regs 1, (s.regs 2).toNat⟩, .tail _ (.tail _ (List.mem_append_left _ (by simp [inR, h0]))), o,
      by rw [q2]; exact ho, by rw [q1]⟩
  · exact ⟨_, .tail _ (.tail _ (List.mem_append_right _ (by rw [q0]; exact List.mem_singleton_self _))), hy⟩

noncomputable def upd_te (ok : Ok B BS) (hb : blockR.TE blockPub (blockE (BS := BS))) : updR.TE updPub updE := by
  have hP : oP = 66 := rfl
  have hN : oN = 70 := rfl
  have hsz := ok.sz
  refine frame_te (f := updR) (pub := updPub) (mask := 0) (k := 3) (epi := O + oP) (spP := fun p => p 3)
    (Ψ := fun b p => upTr hb.T b p) (Fp := updFp) (Rq := updRq) (Wd := fun _ p => updWd p) (by decide) ok.en ok.po ok.cd
    (by simp only [updR]; refine ⟨hsz.2, ?_, ?_, ?_, by decide, by decide⟩ <;> omega) (fun _ _ => rfl)
    (fun base s e F t tpc t13 tr hm hc => ?_)
    (fun _ _ => by repeat (first | (apply wTr_uniq; intro _ _ _) | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_cond | assumption))
    (fun _ _ => by repeat (first | (apply wTr_ex; intro _ _ _) | exact Tr.ex_is _ | apply Tr.ex_cat | apply Tr.ex_cond | assumption))
    (fun _ p y h => ⟨_, .tail _ (.tail _ (.head _)), Rgn.of_region (reg_le h (by
      have := Nat.mod_lt (c0 p + len p) (by decide : 128 > 0); simp only [ctxSize]; omega))⟩)
    (fun b p sp0 n U hroom hn hF hR => by
      rw [show 4 * nSaved 0 + 4 * 3 = FR by decide, show 4 * nSaved 0 = 4 by decide]
      exact GH.upd ⟨hroom, hn, hF, hR⟩ hb.eff)
  generalize hP' : updPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 2 = P 2 ∧ s.regs 13 = P 3 ∧ read32 s.mem (P 0) = P 4 := by
    subst hP'; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨q0, q1, q2, q13, q4⟩ := q
  have hpre := e.pre
  have hsW := e.sepWr; have hsR := e.sepRd; have hroom := e.room; have hsp4 := e.sp4
  simp only [updR, Routine.win, inR, q0, q1, q2, q13] at hpre hsW hsR hroom hsp4
  fp_simp at hsW
  have : D = 224 := rfl
  have L : Lay P := by
    by_cases h0 : (P 2).toNat = 0
    · exact ⟨⟨hroom, hsp4⟩, hpre.1, ⟨by omega, by have := (P 1).isLt; simp only [len, h0]; omega⟩, by omega, .inl h0, .inl h0⟩
    · simp only [h0, ↓reduceIte] at hpre hsR
      have hd := hpre.2
      simp only [List.cons_append, List.nil_append] at hsR
      fp_simp at hsR hd
      exact ⟨⟨hroom, hsp4⟩, hpre.1, ⟨by omega, by simp only [len]; omega⟩, by omega, .inr (by simp only [len]; omega),
        .inr (by simp only [len]; omega)⟩
  up_lay L
  have hW : lowWin updR 0 s :: updR.wr s = Wc P := by subst hP'; rfl
  rw [hW, q13] at F
  have t13' : t.regs 13 = fp := by rw [t13, q13]; rfl
  have H : Hy base P t.mem hb.T := ⟨F, ok, L, hc, hb.spec⟩
  have hsep : Sep [⟨P 0, ctxSize⟩] [saved 0 s] := by simp only [saved, q13, show 4 * nSaved 0 = 4 from rfl]; fp_tac
  have hs0 : Same196 s.mem t.mem (P 0) := fun j hj => hm _ (Sep.not_has hsep ⟨_, List.mem_singleton.mpr rfl, j, hj, rfl⟩)
  have hin : bytesAt t.mem (P 1) (len P) = bytesAt s.mem (P 1) (len P) := by
    by_cases h0 : len P = 0
    · rw [h0]; rfl
    · exact hm.bytes (by simp only [saved, q13, show 4 * nSaved 0 = 4 from rfl]; fp_tac)
  have qn : read32 t.mem (P 0) = P 4 := by
    have := hs0.rd (o := 0) (by decide); simp only [BitVec.add_zero] at this; rw [this, q4]
  refine ReachFT.mono (up_run H (io0 ((tr 0 (by decide) (by decide)).trans q0) ((tr 1 (by decide) (by decide)).trans q1)
    ((tr 2 (by decide) (by decide)).trans q2) t13' qn) (by rw [tpc]; rfl))
    (fun _ h => h) (fun _ h => rc_rd q0 q1 q2 q13 h) (fun _ h => by rw [hW]; exact h)
    (fun _ h => by show InStackWindow (s.regs 13) _ _; rw [q13]; exact h) (fun u hq => ?_)
    (by subst hP'; exact fun _ h => h)
  refine ⟨hq.1, by rw [hq.2.1, t13'], fun r h4 h11 _ hr => absurd (Ed25519Routines.mem_hiRegs h4 h11) hr, fun M hM => ?_⟩
  rw [q0] at hM; rw [q0, q1, q2]
  exact post_of hM q4 hs0 hin hq.2.2.1 hq.2.2.2
end

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_sha512_update` in each build**, with its effect. -/
noncomputable def sha512_update_te (b : Build) : letI := b.codeBytes; updR.TE updPub (@updE _ b.size b.codeBytes) :=
  letI := b.codeBytes
  upd_te (ok_b b) (Ed25519Sha512Block.sha512_block_te b)

/-! ## The `Callees` adapter -/

section
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (sha512_update)

/-- **The relation pair with `ShaCtx`** as the context relation, for a point relation `pt`. -/
def shaRels (pt : Mem → Word → Spec.Ed25519.Point → Prop)
    (hpt : ∀ {W m m' a P}, MemEq W m m' → Sep [⟨a, 128⟩] W → pt m a P → pt m' a P) : Rels where
  ctx := ShaCtx
  pt := pt
  ctx_len := fun h => h.1
  ctx_memEq := fun h hs hc => hc.memEq h hs
  pt_memEq := hpt

/-- **The `.update n ℓ` field of `Callees`** for build `b`: `m0c_sha512_update`'s adapter and effect, at
relations whose context relation is `ShaCtx`. -/
noncomputable def updAd (b : Build) (Rs : Rels) (hR : Rs.ctx = ShaCtx) (n : List SV) (ℓ : SV) :
    @AdE Rs b.bytes b.size b.codeBytes (eaS (.update n ℓ)) := by
  letI := b.codeBytes
  refine Ad.ofTSpec { updR with code := footprint sha512_update } rfl rfl (show D = stackOf sha512_update by decide)
    ((sha512_update_te b).code (footprint sha512_update) (by decide))
    (fun base p tr h => EffT.mono h (show D ≤ stackOf sha512_update by decide) (fun y hy => ?_) (fun y hy => ?_) fun y hy => ?_)
    (semE (.update n ℓ))
    (fun c sp base st vs hg hv _ => ⟨hg.1 0 (List.mem_singleton_self _), by
      have := hv.2.2 _ (List.mem_singleton_self _)
      by_cases h0 : (st.regs 2).toNat = 0 <;>
        simpa [rgnsC, SRgn.rgnC, ALen.val, inR, ctxSize, h0] using this⟩)
    (fun st => by simp [updR, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioUpdate, ctxSize])
    (fun st => by by_cases h0 : (st.regs 2).toNat = 0 <;> simp [updR, inR, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioUpdate, ctxSize, h0])
    fun c sp st m _ vs hv hi hp => ?_
  all_goals have iR : (eaS (.update n ℓ)).io.rd = [⟨1, 0, .r 2⟩, ⟨0, 0, .k ctxSize⟩] := rfl
  all_goals have iW : (eaS (.update n ℓ)).io.wr = [⟨0, 0, .k ctxSize⟩] := rfl
  all_goals have iI : (eaS (.update n ℓ)).io.ins = [(0, 0, .view (.ctx n)), (1, 0, .raw (.r 2))] := rfl
  all_goals have iO : (eaS (.update n ℓ)).io.outs = [(0, 0, .ctx (n ++ [ℓ]))] := rfl
  all_goals have hc : ctxSize ≠ 0 := by decide
  · have r0 : (eaS (.update n ℓ)).reg p 0 = p 0 := rfl
    have r1 : (eaS (.update n ℓ)).reg p 1 = p 1 := rfl
    have r2 : (eaS (.update n ℓ)).reg p 2 = p 2 := rfl
    simp only [CalleeS.Fp, rgnsC, iR, iW, List.flatMap_cons, List.flatMap_nil, SRgn.rgnC, ALen.val, r0, r1, r2,
      BitVec.add_zero, List.append_nil, hc, ↓reduceIte] 
    obtain ⟨r, hr, hy⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, hy⟩
    · obtain ⟨o, ho, rfl⟩ := hy
      have h0 : (p 2).toNat ≠ 0 := fun h => by simp only [len, h] at ho; omega
      exact ⟨⟨p 1, (p 2).toNat⟩, by simp [h0], o, ho, rfl⟩
    · exact ⟨_, by simp, hy⟩
  · have r0 : (eaS (.update n ℓ)).reg p 0 = p 0 := rfl
    have r1 : (eaS (.update n ℓ)).reg p 1 = p 1 := rfl
    have rc : (eaS (.update n ℓ)).cnt p = (p 4).toNat := rfl
    simp only [CalleeS.Rq, CalleeS.iniIn, iI, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      ALen.val, r0, r1, rc, BitVec.add_zero] 
    exact hy
  · have r0 : (eaS (.update n ℓ)).reg p 0 = p 0 := rfl
    have rc : (eaS (.update n ℓ)).cnt p = (p 4).toNat := rfl
    have rl : (eaS (.update n ℓ)).rawLen p = (p 2).toNat := rfl
    simp only [CalleeS.Wd, CalleeS.iniOut, iO, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, r0, rc, rl,
      BitVec.add_zero] at hy
    exact hy
  · change ∀ M, ShaCtx st.mem (st.regs 0) M → ShaCtx m (st.regs 0) (M ++ bytesAt st.mem (st.regs 1) (st.regs 2).toNat) at hp
    have h2 : st.regs 2 = ℓ.val c sp := hv.1 (2, ℓ) (List.mem_singleton_self _)
    simp only [InsRel, iI] at hi
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, vs⟩⟩⟩ <;> simp only [All2, and_false] at hi
    cases v1 <;> cases v2 <;> simp [Rel, In.kd, ALen.val] at hi
    obtain ⟨⟨hM, hl⟩, hd⟩ := hi
    simp only [OutsRel, iO, All2, semE, Rel, BitVec.add_zero, and_true]
    rw [hR] at hM ⊢
    refine ⟨by rw [← hd]; exact hp _ hM, ?_⟩
    rw [List.length_append, ← hd, bytesAt_length, hl, slen, slen, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, h2]
end

end M0Crypto.Release.Ed25519ShaUpdate
