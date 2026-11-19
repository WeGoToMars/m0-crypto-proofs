import M0Crypto.Release.Ed25519RecodeCode
import M0Crypto.Release.Ed25519FieldRoutines
import M0Crypto.Release.Ed25519CombDigits
import M0Crypto.Release.Ed25519Bytes
import M0Crypto.Release.BlockEffect
import M0Crypto.Release.SegEffect
import M0Crypto.Release.Ed25519Sbit
import M0Crypto.Release.Ed25519Leaf
import M0Crypto.Release.Ed25519WordLoop
import M0Crypto.Release.Ed25519SignProg

set_option linter.unusedSimpArgs false

/-!
# `m0c_sc_recode_comb`

Each block's effect is a decided `Eff`: the frame store (`preE`), a pass of the first loop
(`l1E`, the byte `U_i = (e_i >> 1) | (e_{i+1} << 7)`, `u_byte`), its last byte (`midE`), and the
second loop's body split at its four teeth (`hdE`, `toothE`, `tlE`). `body_val`: a pass `q < 64`
of the second loop stores `combDigit (combTeeth n U q) + 8` for the 32 bytes `U` at `sp`
(`teeth_or`, `sign_byte`, each tooth by `bit_word` and `decodeInt_bit`) at `E + q`, stores `q + 1`
in the frame, and sets `Z` exactly after the last pass. `ub_dec`: those bytes `U` decode to
`recode_u e` for `e < 2^255`.

`recode_te`: in each build, from `e < 2^255` at `r1`, the routine writes at `r0` the 64 bytes
`digitAt n e q + 8`, with the byte effect `rcE`: 44 stack bytes, footprint `e` and the
digits, `e` required written, the digits written. The body is the top segments then 64 passes closed by
`beq +0; b back` (`ReachFT.segs`, `ReachFT.segLoopFar`), framed by `frame_te`; its `GP` is
`segsTr_gp` per pass (`body_gp`). `rc_eff`: `rcE` is the effect of the callee `rcS`.
-/
namespace M0Crypto.Release.Ed25519Recode

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Ed25519RecodeCode
open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SBool SMem)

def cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)

/-! ## Block effects -/

def preE : Eff := { regs := [(3, .reg0 13), (2, cw 31)], mem := some (.w32 .mem0 (spA 32) (.reg0 0)) }
/-- `U_i = (e_i >> 1) | (e_{i+1} << 7)`. -/
def uE : SExpr := .or (.lsr (.ld8 .mem0 (.reg0 1)) 1) (.lsl (.ld8 .mem0 (.add (.reg0 1) (cw 1))) 7)
def l1E : Eff :=
  { regs := [(4, uE), (1, .add (.reg0 1) (cw 1)), (3, .add (.reg0 3) (cw 1)), (2, .add (.reg0 2) (.const (-1#32)))],
    clob := [5], z := some (.isZero (.add (.reg0 2) (.const (-1#32)))), mem := some (.w8 .mem0 (.reg0 3) uE) }
def u31 : SExpr := .or (.lsr (.ld8 .mem0 (.reg0 1)) 1) (cw 128)
def midE : Eff :=
  { regs := [(2, cw 0)], clob := [4, 5], mem := some (.w32 (.w8 .mem0 (.reg0 3) u31) (spA 36) (cw 0)) }
def hdE (n : Nat) : Eff :=
  { regs := [(2, ldS 36), (3, rowE n), (7, .reg0 13), (6, cw 0)], clob := [4, 5] }
/-- Tooth `k` at bit `p = r3 + k (64 / n)`: bit `p & 7` of byte `(p >> 3) & 31` at `r7`. -/
def pT (n k : Nat) : SExpr := if k = 0 then .reg0 3 else .add (.reg0 3) (cw (k * (64 / n)))
def pC (n k : Nat) : SExpr :=
  if k = 0 then .awc (.reg0 3) (cw 0) (.const false)
  else .awc (.awc (.reg0 3) (cw 0) (.const false)) (cw (k * (64 / n))) (.const false)
def bitT (n k : Nat) : SExpr :=
  .and (.lsrR (.ld8 .mem0 (.add (.reg0 7) (.and (.lsr (pT n k) 3) (cw 31)))) (.and (pT n k) (cw 7))
    (.lsrC (pC n k) 3)) (cw 1)
def toothE (n k : Nat) : Eff :=
  { regs := [(6, .or (.reg0 6) (if k = 0 then bitT n k else .lsl (bitT n k) k))], clob := [0, 4, 5] }
/-- The sign step of `sign_byte` on `x`. -/
def signE (x : SExpr) : SExpr :=
  let m := SExpr.add (.lsr x 3) (.const (-1#32))
  .add (.sub (.xor (.add (.and (.xor x m) (cw 7)) (cw 1)) m) m) (cw 8)
def q1 : SExpr := .add (.and (.reg0 2) (cw 63)) (cw 1)
def tlE : Eff :=
  { regs := [(2, q1)], clob := [0, 1, 4, 6], z := some (.isZero (.add (.and (.reg0 2) (cw 63)) (.const (-63#32)))),
    mem := some (.w32 (.w8 .mem0 (.add (ldS 32) (.and (.reg0 2) (cw 63))) (signE (.reg0 6))) (spA 36) q1) }

theorem pre_ok : effOk pre preE = true := by decide +kernel
theorem l1_ok : effOk l1 l1E = true := by decide +kernel
theorem mid_ok : effOk mid midE = true := by decide +kernel
theorem hd_ok : ∀ n ∈ [2, 16], effOk (hd n) (hdE n) = true := by decide +kernel
theorem tooth_ok : ∀ n ∈ [2, 16], ∀ k ∈ [0, 1, 2, 3], effOk (tooth n k) (toothE n k) = true := by decide +kernel
theorem tl_ok : effOk tl tlE = true := by decide +kernel

/-! ## The arithmetic -/

open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.Ed25519CombDigits
open M0Crypto.Release.Ed25519Bytes (decodeInt_bit)
open M0Crypto.Release.Ed25519Sbit (bit_val bytesAt_getD)

/-- A stored `U` byte: the low byte of `(x >> 1) | (y << 7)` is `x / 2` and the low bit of `y`. -/
theorem u_byte (x y : Word) (hx : x.toNat < 256) (hy : y.toNat < 256) :
    ((x >>> 1 ||| y <<< 7).extractLsb' 0 8).toNat = x.toNat / 2 + 128 * (y.toNat % 2) := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    Nat.shiftRight_zero, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : y.toNat * 2 ^ 7 < 2 ^ 32), Nat.or_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftRight_eq_div_pow]; omega),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem byte_lt (b : BitVec 8) : (b.setWidth 32).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega

/-- The bit position `r3 + k (64 / n)` of tooth `k` of digit `q` is `combPos n q k`. -/
def posW (n q k : Nat) : Word :=
  let r := (BitVec.ofNat 32 q >>> lg n) +
    ((BitVec.ofNat 32 (n - 1) - (BitVec.ofNat 32 (n - 1) &&& BitVec.ofNat 32 q)) <<< sh n)
  if k = 0 then r else r + BitVec.ofNat 32 (k * (64 / n))

theorem posW_eq : ∀ n ∈ [2, 16], ∀ q : Fin 64, ∀ k : Fin 4,
    posW n q k = BitVec.ofNat 32 (combPos n q k) ∧ combPos n q k < 256 := by decide +kernel

theorem pos_bits : ∀ c : Fin 256, BitVec.ofNat 32 c >>> 3 &&& 31#32 = BitVec.ofNat 32 (c / 8) := by decide +kernel

theorem q_bits : ∀ q : Fin 64, BitVec.ofNat 32 q &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 q ∧
    ((BitVec.ofNat 32 q + -63#32 == 0#32) = decide (64 ≤ q.val + 1)) := by decide +kernel

/-- Tooth `k` of digit `q < 64` with `r3` at its row: bit `combPos n q k` of the 32 bytes at `r7`. -/
theorem bit_word {n k q : Nat} (hn : n ∈ [2, 16]) (hk : k < 4) (hq : q < 64) (u : State) (h3 : u.regs 3 = posW n q 0) :
    (bitT n k).denote u = BitVec.ofNat 32 (ubit (decodeInt (bytesAt u.mem (u.regs 7) 32)) (combPos n q k)) := by
  obtain ⟨hp, hlt⟩ := posW_eq n hn ⟨q, hq⟩ ⟨k, hk⟩
  dsimp only at hp hlt
  have hpk : (pT n k).denote u = BitVec.ofNat 32 (combPos n q k) := by
    rw [← hp]; unfold pT posW; split <;> simp_all [SExpr.denote, cw, posW]
  have pb := pos_bits ⟨_, hlt⟩
  dsimp only at pb
  apply BitVec.eq_of_toNat_eq
  simp only [bitT, SExpr.denote, SMem.denote, hpk, pb, Thumb.read8, cw, BitVec.and_comm _ (BitVec.ofNat 32 1)]
  rw [show BitVec.ofNat 32 1 = 1#32 from rfl, bit_val, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := combPos n q k) (b := 2 ^ 32) (by omega), ubit, decodeInt_bit,
    bytesAt_getD _ _ (n := 32) (by omega), Nat.mod_eq_of_lt (b := 2 ^ 32) (by omega)]

/-- **The second loop's body**: with `q < 64` in the frame's `Q` word, it stores the digit of the
packed teeth of the bytes at `sp` at `E + q` and `q + 1` in `Q`, and sets `Z` exactly at `q = 63`. -/
theorem body_val {n q : Nat} (hn : n ∈ [2, 16]) (hq : q < 64) (u : State)
    (hQ : read32 u.mem (u.regs 13 + BitVec.ofNat 32 36) = BitVec.ofNat 32 q) :
    ∃ w : Word, (execAll (body n) u).mem = write32 (write8 u.mem (read32 u.mem (u.regs 13 + BitVec.ofNat 32 32) +
        BitVec.ofNat 32 q) w) (u.regs 13 + BitVec.ofNat 32 36) (BitVec.ofNat 32 (q + 1)) ∧
      (w.extractLsb' 0 8).toNat = (combDigit (combTeeth n (decodeInt (bytesAt u.mem (u.regs 13) 32)) q) + 8).toNat ∧
      (execAll (body n) u).regs 13 = u.regs 13 ∧ condPassed 0 (execAll (body n) u) = decide (64 ≤ q + 1) := by
  have H := eff_run (hd_ok n hn) u
  have h2 : (execAll (hd n) u).regs 2 = BitVec.ofNat 32 q := by
    rw [H.reg 2 (by decide) (by simp [hdE])]; simpa [Eff.reg, hdE, SExpr.denote, SMem.denote, ldS, spA, cw] using hQ
  have h3 : (execAll (hd n) u).regs 3 = posW n q 0 := by
    rw [H.reg 3 (by decide) (by simp [hdE])]; simp [Eff.reg, hdE, rowE, posW, SExpr.denote, SMem.denote, ldS, spA, cw, hQ]
  have h6 : (execAll (hd n) u).regs 6 = 0#32 := by rw [H.reg 6 (by decide) (by simp [hdE])]; rfl
  have h7 : (execAll (hd n) u).regs 7 = u.regs 13 := by rw [H.reg 7 (by decide) (by simp [hdE])]; rfl
  have h13 : (execAll (hd n) u).regs 13 = u.regs 13 := by rw [H.reg 13 (by decide) (by simp [hdE])]; rfl
  have hm := H.mem _ rfl
  simp only [SMem.denote] at hm
  rw [body, execAll_append, execAll_append, execAll_append, execAll_append, execAll_append]
  generalize execAll (hd n) u = u0 at h2 h3 h6 h7 h13 hm
  /- each tooth sets `r6` and keeps `r2`, `r3`, `r7`, `sp` and the memory -/
  have T : ∀ k ∈ [0, 1, 2, 3], ∀ v : State,
      (execAll (tooth n k) v).regs 6 = v.regs 6 ||| (if k = 0 then (bitT n k).denote v else (bitT n k).denote v <<< k) ∧
      (execAll (tooth n k) v).regs 2 = v.regs 2 ∧ (execAll (tooth n k) v).regs 3 = v.regs 3 ∧
      (execAll (tooth n k) v).regs 7 = v.regs 7 ∧ (execAll (tooth n k) v).regs 13 = v.regs 13 ∧
      (execAll (tooth n k) v).mem = v.mem := by
    intro k hk v
    have E := eff_run (tooth_ok n hn k hk) v
    refine ⟨?_, ?_, ?_, ?_, ?_, E.mem _ rfl⟩
    · rw [E.reg 6 (by decide) (by simp [toothE])]; split <;> simp_all [Eff.reg, toothE, SExpr.denote]
    all_goals first
      | (rw [E.reg 2 (by decide) (by simp [toothE])]; rfl) | (rw [E.reg 3 (by decide) (by simp [toothE])]; rfl)
      | (rw [E.reg 7 (by decide) (by simp [toothE])]; rfl) | (rw [E.reg 13 (by decide) (by simp [toothE])]; rfl)
  obtain ⟨a6, a2, a3, a7, a13, am⟩ := T 0 (by simp) u0
  have b0 := bit_word hn (k := 0) (by decide) hq u0 h3
  generalize execAll (tooth n 0) u0 = u1 at a6 a2 a3 a7 a13 am
  obtain ⟨c6, c2, c3, c7, c13, cm⟩ := T 1 (by simp) u1
  have b1 := bit_word hn (k := 1) (by decide) hq u1 (a3.trans h3)
  generalize execAll (tooth n 1) u1 = u2 at c6 c2 c3 c7 c13 cm
  obtain ⟨d6, d2, d3, d7, d13, dm⟩ := T 2 (by simp) u2
  have b2 := bit_word hn (k := 2) (by decide) hq u2 (c3.trans (a3.trans h3))
  generalize execAll (tooth n 2) u2 = u3 at d6 d2 d3 d7 d13 dm
  obtain ⟨e6, e2, e3, e7, e13, em⟩ := T 3 (by simp) u3
  have b3 := bit_word hn (k := 3) (by decide) hq u3 (d3.trans (c3.trans (a3.trans h3)))
  generalize execAll (tooth n 3) u3 = u4 at e6 e2 e3 e7 e13 em
  have E := eff_run tl_ok u4
  obtain ⟨hb, hz⟩ := q_bits ⟨q, hq⟩
  dsimp only at hb hz
  have r2 : u4.regs 2 = BitVec.ofNat 32 q := by rw [e2, d2, c2, a2, h2]
  have r13 : u4.regs 13 = u.regs 13 := by rw [e13, d13, c13, a13, h13]
  have rm : u4.mem = u.mem := by rw [em, dm, cm, am, hm]
  have r7 : ∀ v : State, v.mem = u.mem → v.regs 7 = u.regs 13 →
      decodeInt (bytesAt v.mem (v.regs 7) 32) = decodeInt (bytesAt u.mem (u.regs 13) 32) := fun v h1 h2 => by rw [h1, h2]
  rw [r7 u0 hm h7] at b0
  rw [r7 u1 (am.trans hm) (a7.trans h7)] at b1
  rw [r7 u2 (cm.trans (am.trans hm)) (c7.trans (a7.trans h7))] at b2
  rw [r7 u3 (dm.trans (cm.trans (am.trans hm))) (d7.trans (c7.trans (a7.trans h7)))] at b3
  generalize decodeInt (bytesAt u.mem (u.regs 13) 32) = U at b0 b1 b2 b3
  have hv : u4.regs 6 = BitVec.ofNat 32 (combTeeth n U q) := by
    rw [e6, d6, c6, a6, h6, b0, b1, b2, b3]
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [teeth_or (ubit U (combPos n q 0)) (ubit U (combPos n q 1)) (ubit U (combPos n q 2)) (ubit U (combPos n q 3))
      (by unfold ubit; omega) (by unfold ubit; omega) (by unfold ubit; omega)
      (by unfold ubit; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := combTeeth_lt n U q; omega)]
    rfl
  refine ⟨(signE (.reg0 6)).denote u4, ?_, ?_, ?_, ?_⟩
  · rw [E.mem _ rfl]
    simp only [q1, cw, SMem.denote, SExpr.denote, ldS, spA, r2, r13, rm, hb, BitVec.ofNat_add]
  · have hs := sign_byte _ (combTeeth_lt n U q)
    have hd := combDigit_bound (combTeeth n U q)
    simp only [signE, cw, SExpr.denote, hv, BitVec.sub_eq_add_neg] at hs ⊢
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hs, Nat.mod_eq_of_lt (by omega)]
  · rw [E.reg 13 (by decide) (by decide)]; exact r13
  · rw [RoutineBranch.cond_eq, E.z _ rfl]
    simpa [tlE, cw, SBool.denote, SExpr.denote, r2, hb] using hz


/-- `U = (e >> 1) | 2^255` from its bytes: the byte stored at `fP + j` by the first loop. -/
def ubv (m : Mem) (a : Word) (j : Nat) : Nat :=
  (m (a + BitVec.ofNat 32 j)).toNat / 2 + 128 * (if j < 31 then (m (a + BitVec.ofNat 32 (j + 1))).toNat % 2 else 1)

theorem ub_dec {m1 m : Mem} {a f : Word} (h : ∀ j < 32, (m (f + BitVec.ofNat 32 j)).toNat = ubv m1 a j)
    (he : decodeInt (bytesAt m1 a 32) < 2 ^ 255) :
    decodeInt (bytesAt m f 32) = recode_u (decodeInt (bytesAt m1 a 32)) := by
  refine recode_u_bytes (Footprint.bytesAt_length _ _ _) he (fun i hi => ?_) ?_
  · rw [bytesAt_getD _ _ (by omega : i < 32), bytesAt_getD _ _ (by omega : i < 32),
      bytesAt_getD _ _ (by omega : i + 1 < 32), h i (by omega)]
    simp [ubv, hi]
  · rw [bytesAt_getD _ _ (by omega : 31 < 32), bytesAt_getD _ _ (by omega : 31 < 32), h 31 (by omega)]; simp [ubv]

/-! ## The routine -/

open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.Ed25519WordLoop (add_ofNat_add memEq_write32)
open M0Crypto.Release.StackEffect (segsEffOk winsChk EffT GP SIR WS segN segsTr_gp pass_of frame_te farPass_gp above_sub reg_split
  reg_in reg_sub_above inRD_of ex_cat ex_rep ex_segsTr)

def D : Nat := 44
def cs (n : Nat) : List (Nat × Nat) := [(O, oE n O + seqSize post)]

/-- **`m0c_sc_recode_comb`** for `n` combs: the 64 bytes at `r0` become the digits plus 8 of the
scalar `e < 2^255` at `r1`. -/
def rcR (n : Nat) : Routine where
  entry := O
  code := cs n
  stack := D
  Pre := fun _ s => decodeInt (bytesAt s.mem (s.regs 1) 32) < 2 ^ 255
  wr := fun s => [⟨s.regs 0, 64⟩]
  rd := fun s => [⟨s.regs 1, 32⟩]
  Post := fun s m _ => ∀ q < 64, (m (s.regs 0 + BitVec.ofNat 32 q)).toNat =
    (digitAt n (decodeInt (bytesAt s.mem (s.regs 1) 32)) q + 8).toNat
  clob := Ed25519Routines.hiRegs

/-- The public values: `E`, `e` and `sp`. -/
def rcPub : Word → State → Nat → Word := Ed25519Leaf.leafPub [0, 1]

set_option hygiene false in
local notation "fP" => (P 2 - BitVec.ofNat 32 D)

section
variable (n : Nat) (P : Nat → Word) (m1 : Mem)

structure Lay : Prop where
  sp : D ≤ (P 2).toNat ∧ (P 2).toNat % 4 = 0
  ab : (P 0).toNat + 64 ≤ 2 ^ 32 ∧ (P 1).toNat + 32 ≤ 2 ^ 32
  w0 : (P 0).toNat + 64 ≤ (P 2).toNat - D ∨ (P 2).toNat ≤ (P 0).toNat
  w1 : (P 1).toNat + 32 ≤ (P 2).toNat - D ∨ (P 2).toNat ≤ (P 1).toNat

def WcP : List Rgn := [⟨fP, 40⟩, ⟨P 0, 64⟩]
def RcP {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) : List Rgn := codeR base :: ⟨fP, D⟩ :: [⟨P 1, 32⟩]

/-- Memory as `m1` outside `W`, `sp` at the frame, `E` in its word. -/
def Fr (W : List Rgn) (u : State) : Prop :=
  MemEq W m1 u.mem ∧ u.regs 13 = fP ∧ read32 u.mem (fP + BitVec.ofNat 32 32) = P 0
/-- The first `i` bytes of `U`. -/
def Ub (i : Nat) (u : State) : Prop := ∀ j < i, (u.mem (fP + BitVec.ofNat 32 j)).toNat = ubv m1 (P 1) j
/-- The first loop before pass `i`. -/
def L1 (i : Nat) (u : State) : Prop := Fr P m1 [⟨fP, 40⟩] u ∧ u.regs 1 = P 1 + BitVec.ofNat 32 i ∧
  u.regs 3 = fP + BitVec.ofNat 32 i ∧ u.regs 2 = BitVec.ofNat 32 (31 - i) ∧ Ub P m1 i u
/-- The second loop before pass `q`: the digits below `q` stored. -/
def L2 (q : Nat) (u : State) : Prop := Fr P m1 (WcP P) u ∧ Ub P m1 32 u ∧
  read32 u.mem (fP + BitVec.ofNat 32 36) = BitVec.ofNat 32 q ∧
  ∀ j < q, (u.mem (P 0 + BitVec.ofNat 32 j)).toNat = (digitAt n (decodeInt (bytesAt m1 (P 1) 32)) j + 8).toNat

def JT : Nat → Nat → State → Prop
  | 0, 0, u => u.regs 13 = fP ∧ u.mem = m1 ∧ u.regs 0 = P 0 ∧ u.regs 1 = P 1
  | 0, _, u => L1 P m1 0 u
  | 1, i, u => L1 P m1 i u
  | 2, 0, u => L1 P m1 31 u
  | _, _, u => L2 n P m1 0 u

def JL (j : Nat) : Nat → Nat → State → Prop
  | 0, 0, u => L2 n P m1 j u
  | _, _, u => L2 n P m1 (j + 1) u ∧ condPassed 0 u = decide (64 ≤ j + 1)

def nT (k : Nat) : Nat := if k = 1 then 31 else 1
def vsT (k i : Nat) : List Word := match k with
  | 0 => [fP]
  | 1 => [P 1 + BitVec.ofNat 32 i, fP + BitVec.ofNat 32 i]
  | _ => [P 1 + BitVec.ofNat 32 31, fP + BitVec.ofNat 32 31, fP]
def vsL (j _ _ : Nat) : List Word :=
  [fP, P 0 + BitVec.ofNat 32 j, fP + BitVec.ofNat 32 (combPos n j 0 / 8), fP + BitVec.ofNat 32 (combPos n j 1 / 8),
   fP + BitVec.ofNat 32 (combPos n j 2 / 8), fP + BitVec.ofNat 32 (combPos n j 3 / 8)]
end

macro "rc_fp" : tactic => `(tactic| (simp only [D, WcP, RcP] at *; fp_tac))
macro "rc_lay" L:ident : tactic =>
  `(tactic| (have := ($L).sp; have := ($L).ab; have := ($L).w0; have := ($L).w1; try simp only [D] at *))

section
variable {n : Nat} {P : Nat → Word} {m1 : Mem}

/-- The digit's byte and the teeth's bytes at a pass `q` of the second loop. -/
theorem atoms_at (hn : n ∈ [2, 16]) {q : Nat} (hq : q < 64) (u : State)
    (hQ : read32 u.mem (u.regs 13 + BitVec.ofNat 32 36) = BitVec.ofNat 32 q) :
    digA.denote u = read32 u.mem (u.regs 13 + BitVec.ofNat 32 32) + BitVec.ofNat 32 q ∧
    ∀ k < 4, (toothA n k).denote u = u.regs 13 + BitVec.ofNat 32 (combPos n q k / 8) ∧ combPos n q k < 256 := by
  refine ⟨by simp [digA, ldS, spA, SExpr.denote, SMem.denote, hQ, (q_bits ⟨q, hq⟩).1], fun k hk => ?_⟩
  obtain ⟨hp, hlt⟩ := posW_eq n hn ⟨q, hq⟩ ⟨k, hk⟩
  dsimp only at hp hlt
  have e : (posE n k).denote u = posW n q k := by
    unfold posE posW; split <;> simp [rowE, SExpr.denote, SMem.denote, ldS, spA, hQ]
  have pb := pos_bits ⟨_, hlt⟩
  dsimp only at pb
  exact ⟨by simp only [toothA, SExpr.denote, e, hp, pb], hlt⟩

theorem top_side {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} (L : Lay P) :
    ∀ k sg i u, top[k]? = some sg → i < nT k → JT n P m1 k i u →
      SGlueSides u (RcP P base) (WcP P) sg.al sg.wg sg.rg ∧ sg.As.map (·.denote u) = vsT P k i := by
  intro k sg i u hk hi h; rc_lay L
  seg_cases top k hk
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    exact ⟨by glue_tac [WcP, RcP, D, h.1, spA], by simp [vsT, SExpr.denote, h.1]⟩
  · simp only [nT, ↓reduceIte] at hi
    obtain ⟨-, h1, h3, -⟩ := h
    exact ⟨by glue_tac [WcP, RcP, D, h1, h3], by simp [vsT, SExpr.denote, h1, h3]⟩
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    obtain ⟨⟨-, h13, -⟩, h1, h3, -⟩ := h
    exact ⟨by glue_tac [WcP, RcP, D, h1, h3, h13, spA], by simp [vsT, SExpr.denote, h1, h3, h13]⟩

theorem top_step (L : Lay P) : ∀ k sg i u, top[k]? = some sg → i < nT k → JT n P m1 k i u →
    MemEq (sregions u sg.wg) u.mem (execAll sg.g u).mem → JT n P m1 k (i + 1) (execAll sg.g u) ∧
      ∀ c, sg.br = some c → condPassed c (execAll sg.g u) = decide (i + 1 < nT k) := by
  intro k sg i u hk hi h hm; rc_lay L
  seg_cases top k hk <;> dsimp only at hm ⊢
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    obtain ⟨h13, rfl, h0, h1⟩ := h
    have E := eff_run pre_ok u
    simp only [sregions, List.map, SExpr.denote, spA, h13] at hm
    refine ⟨⟨⟨hm.mono (by rc_fp), by rw [E.reg 13 (by decide) (by decide)]; exact h13, ?_⟩, ?_, ?_, ?_,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun c hc => nomatch hc⟩
    · rw [E.mem _ rfl]; simp [preE, SMem.denote, SExpr.denote, spA, h13, h0, M0Crypto.Armv6M.read32_write32_same]
    · rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, preE, SExpr.denote, h1]
    · rw [E.reg 3 (by decide) (by decide)]; simp [Eff.reg, preE, SExpr.denote, h13]
    · rw [E.reg 2 (by decide) (by decide)]; rfl
  · simp only [nT, ↓reduceIte] at hi
    obtain ⟨⟨hf, h13, he⟩, h1, h3, h2, hu⟩ := h
    have E := eff_run l1_ok u
    simp only [sregions, List.map, SExpr.denote, h3] at hm
    have c := cnt hi (by omega)
    have c1 : BitVec.ofNat 32 (31 - i) + -1#32 = BitVec.ofNat 32 (31 - (i + 1)) := by
      rw [← BitVec.sub_eq_add_neg]; exact c.1
    have hv : (execAll l1 u).mem = write8 u.mem (fP + BitVec.ofNat 32 i) (uE.denote u) := by rw [E.mem _ rfl, ← h3]; rfl
    have rb : ∀ j ≤ 31, u.mem (P 1 + BitVec.ofNat 32 j) = m1 (P 1 + BitVec.ofNat 32 j) := fun j hj =>
      hf.byte (by rc_fp)
    refine ⟨⟨⟨hf.grow hm (by rc_fp), by rw [E.reg 13 (by decide) (by decide)]; exact h13,
      (hm.read32 (by rc_fp)).trans he⟩, ?_, ?_, ?_, fun j hj => ?_⟩, ?_⟩
    · rw [E.reg 1 (by decide) (by decide)]; simp [Eff.reg, l1E, SExpr.denote, cw, h1, add_ofNat_add]
    · rw [E.reg 3 (by decide) (by decide)]; simp [Eff.reg, l1E, SExpr.denote, cw, h3, add_ofNat_add]
    · rw [E.reg 2 (by decide) (by decide)]; simpa [Eff.reg, l1E, SExpr.denote, h2] using c1
    · by_cases e : j = i
      · subst e
        rw [hv]; simp only [write8, ↓reduceIte, uE, SExpr.denote, SMem.denote, cw, h1, Thumb.read8]
        rw [u_byte _ _ (byte_lt _) (byte_lt _), BitVec.toNat_setWidth, BitVec.toNat_setWidth, add_ofNat_add,
          rb j (by omega), rb (j + 1) (by omega)]
        have := (m1 (P 1 + BitVec.ofNat 32 j)).isLt; have := (m1 (P 1 + BitVec.ofNat 32 (j + 1))).isLt
        simp [ubv, hi]; omega
      · rw [hm.byte (by rc_fp)]; exact hu j (by omega)
    · rintro _ ⟨⟩
      rw [RoutineBranch.cond_ne, E.z _ rfl]
      simp only [l1E, SBool.denote, SExpr.denote, h2, c1, nT, ↓reduceIte]; exact c.2
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    obtain ⟨⟨hf, h13, he⟩, h1, h3, -, hu⟩ := h
    have E := eff_run mid_ok u
    simp only [sregions, List.map, SExpr.denote, spA, h3, h13] at hm
    have hv : (execAll mid u).mem = write32 (write8 u.mem (fP + BitVec.ofNat 32 31) (u31.denote u))
        (fP + BitVec.ofNat 32 36) 0 := by rw [E.mem _ rfl, ← h3, ← h13]; rfl
    refine ⟨⟨⟨(hf.grow hm (by rc_fp)).mono (by rc_fp), by rw [E.reg 13 (by decide) (by decide)]; exact h13,
      (hm.read32 (by rc_fp)).trans he⟩, fun j hj => ?_, by rw [hv, M0Crypto.Armv6M.read32_write32_same]; rfl,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun c hc => nomatch hc⟩
    by_cases e : j = 31
    · subst e
      rw [hv, (memEq_write32 _ _ _).byte (by rc_fp)]
      simp only [write8, ↓reduceIte, u31, SExpr.denote, SMem.denote, cw, h1, Thumb.read8]
      rw [show (BitVec.ofNat 32 128 : Word) = 1#32 <<< 7 by decide, u_byte _ _ (byte_lt _) (by decide),
        BitVec.toNat_setWidth, hf.byte (by rc_fp)]
      have := (m1 (P 1 + BitVec.ofNat 32 31)).isLt
      simp [ubv]; omega
    · rw [hm.byte (by rc_fp)]; exact hu j (by omega)

theorem loop_side {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} (L : Lay P) (hn : n ∈ [2, 16])
    {j : Nat} (hj : j < 64) : ∀ k sg i u, (loop n)[k]? = some sg → i < 1 → JL n P m1 j k i u →
      SGlueSides u (RcP P base) (WcP P) sg.al sg.wg sg.rg ∧ sg.As.map (·.denote u) = vsL n P j k i := by
  intro k sg i u hk hi h; rc_lay L
  seg_cases loop k hk
  obtain rfl : i = 0 := by omega
  obtain ⟨⟨-, h13, he⟩, -, hQ, -⟩ := h
  rw [← h13] at hQ
  obtain ⟨dv, tv⟩ := atoms_at hn hj u hQ
  rw [h13, he] at dv
  obtain ⟨t0, l0⟩ := tv 0 (by decide); obtain ⟨t1, l1⟩ := tv 1 (by decide)
  obtain ⟨t2, l2⟩ := tv 2 (by decide); obtain ⟨t3, l3⟩ := tv 3 (by decide)
  rw [h13] at t0 t1 t2 t3
  refine ⟨?_, by simp [vsL, SExpr.denote, h13, dv, t0, t1, t2, t3]⟩
  simp only [SGlueSides, sregions, List.map_cons, List.map_nil, dv, t0, t1, t2, t3]
  glue_tac [WcP, RcP, D, h13, spA]


theorem loop_step (L : Lay P) (hn : n ∈ [2, 16]) (he : decodeInt (bytesAt m1 (P 1) 32) < 2 ^ 255) {j : Nat}
    (hj : j < 64) : ∀ k sg i u, (loop n)[k]? = some sg → i < 1 → JL n P m1 j k i u →
      MemEq (sregions u sg.wg) u.mem (execAll sg.g u).mem → JL n P m1 j k (i + 1) (execAll sg.g u) ∧
        ∀ c, sg.br = some c → condPassed c (execAll sg.g u) = decide (i + 1 < 1) := by
  intro k sg i u hk hi h hm; rc_lay L
  seg_cases loop k hk
  obtain rfl : i = 0 := by omega
  obtain ⟨⟨hf, h13, hE⟩, hu, hQ, hd⟩ := h
  rw [← h13] at hQ
  obtain ⟨w, hw, hv, s13, hc⟩ := body_val hn hj u hQ
  have dv := (atoms_at hn hj u hQ).1
  rw [h13, hE] at dv hw; rw [h13] at hv
  dsimp only at hm ⊢
  simp only [sregions, List.map, dv, spA, SExpr.denote, h13] at hm
  refine ⟨⟨(?_ : L2 n P m1 (j + 1) _), hc⟩, fun c hc => nomatch hc⟩
  have g1 : MemEq (WcP P) m1 (execAll (body n) u).mem := hf.grow hm (by clear hw hv he hd hu hc s13 dv hQ hE; rc_fp)
  have g2 := hm.read32 (a := P 2 - BitVec.ofNat 32 D + 32#32) (by clear hw hv he hd hu hc s13 dv hQ hE; rc_fp)
  refine ⟨?_, fun j' hj' => ?_, ?_, fun j' hj' => ?_⟩
  · refine ⟨g1, ?_, ?_⟩
    · rw [s13, h13]
    · rw [g2, hE]
  · rw [hm.byte (by clear hw hv he hd hu hc; rc_fp)]; exact hu j' hj'
  · rw [hw]; exact M0Crypto.Armv6M.read32_write32_same _ _ _
  · by_cases e : j' = j
    · subst e
      rw [ub_dec hu he] at hv
      rw [hw, (memEq_write32 _ _ _).byte (by clear hw hv he hd hu hc; rc_fp)]
      simpa [write8, digitAt] using hv
    · rw [hm.byte (by clear hw hv he hd hu hc; rc_fp)]; exact hd j' (by omega)

end

/-! ## The byte effect -/

/-- **The effect of `m0c_sc_recode_comb`**: it reads `e` and writes the digits, in `D` bytes of stack. -/
def rcE (_ : Word) (P : Nat → Word) : TrP :=
  EffT D (Has [⟨P 0, 64⟩, ⟨P 1, 32⟩]) (Has [⟨P 1, 32⟩]) (Has [⟨P 0, 64⟩]) (P 2)

/-- The body's trace: the top segments, then the 64 digits closed by `beq +0; b back`. -/
def rcTr (n : Nat) (base : Word) (P : Nat → Word) : TrP :=
  segsTr base (oP O) top (vsT P) nT (Tr.rep (farPass base (oL O + segsSize (loop n)) 0
    (brImm8 (oL O + segsSize (loop n)) (oL O + segsSize (loop n) + 4)) (brImm11 (oL O + segsSize (loop n) + 2) (oL O))
    (fun j => segsTr base (oL O) (loop n) (vsL n P j) (fun _ => 1) (Tr.is [])) 64) 0 64 (Tr.is []))

theorem loop_ok : ∀ n ∈ [2, 16], segsEffOk (loop n) = true ∧ ∀ s ∈ loop n,
    winsChk s.As [(0, 40), (2, 1), (3, 1), (4, 1), (5, 1)] s.rg = true ∧ winsChk s.As [(1, 1), (0, 40)] s.wg = true := by
  decide +kernel

section
variable {n : Nat} {P : Nat → Word}

/-- The bytes the top segments write: the frame. -/
abbrev WT (P : Nat → Word) (base : Word) : Word → Prop := WS base (oP O) top (vsT P) nT 3

theorem frame_wt {base y : Word} (h : Region fP 40 y) : WT P base y := by
  obtain ⟨o, ho, rfl⟩ := Region.exists h
  by_cases h1 : o < 31
  · exact ⟨1, by decide, _, o, rfl, by simpa [segN, top, nT] using h1, inRD_of (d := 0) rfl (.head _) rfl rfl
      (by simp [Region])⟩
  by_cases h2 : o = 31
  · subst h2; exact ⟨2, by decide, _, 0, rfl, by simp [segN, top], inRD_of (d := 0) rfl (.head _) rfl rfl
      (by simp [Region])⟩
  by_cases h3 : o < 36
  · exact ⟨0, by decide, _, 0, rfl, by simp [segN, top], inRD_of (d := BitVec.ofNat 32 32) rfl (.head _) rfl rfl
      (by simp only [Region]; bv_omega)⟩
  · exact ⟨2, by decide, _, 0, rfl, by simp [segN, top], inRD_of (d := BitVec.ofNat 32 36) rfl (.tail _ (.head _)) rfl
      rfl (by simp only [Region]; bv_omega)⟩

theorem dig_cov {y : Word} (h : Has [⟨P 0, 64⟩] y) : ∃ q < 64, Region (P 0 + BitVec.ofNat 32 q) 1 y := by
  obtain ⟨_, hr, o, ho, rfl⟩ := h
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨o, ho, by simp [Region]⟩

/-- The readable bytes before digit `j`: `U`, the frame and the digits stored. -/
def IR (base sp0 : Word) (N : Nat) (U : Word → Prop) (j : Nat) (y : Word) : Prop :=
  (U y ∨ WT P base y ∧ BelowEntry sp0 N y) ∨ (∃ q < j, Region (P 0 + BitVec.ofNat 32 q) 1 y) ∧ BelowEntry sp0 N y

/-- Pass `j` of the digit loop. -/
theorem pass_gp (hn : n ∈ [2, 16]) (base : Word) {sp0 : Word} {N : Nat} {U : Word → Prop}
    (hroom : (sp0 - P 2).toNat + D ≤ N) (hN : N < 2 ^ 32)
    (hF : ∀ y, Has [⟨P 0, 64⟩, ⟨P 1, 32⟩] y → BelowEntry sp0 N y → AtOrAboveSp sp0 (P 2) y) {j : Nat} (hj : j < 64) :
    GP sp0 N (SIR sp0 fP (IR (P := P) base sp0 N U j)) (segsTr base (oL O) (loop n) (vsL n P j) (fun _ => 1) (Tr.is []))
      (SIR sp0 fP (IR (P := P) base sp0 N U (j + 1))) := by
  have cb : ∀ k < 4, combPos n j k < 256 := fun k hk => (posW_eq n hn ⟨j, hj⟩ ⟨k, hk⟩).2
  have fa : ∀ y, Region fP 40 y → AtOrAboveSp sp0 fP y := fun y h => reg_sub_above h (by decide) (by omega)
  obtain ⟨hl0, hl1⟩ := loop_ok n hn
  obtain ⟨w1, w2⟩ := hl1 _ (List.mem_singleton_self _)
  have tr : ∀ y k, k < 4 → Region (fP + BitVec.ofNat 32 (combPos n j k / 8)) 1 y → BelowEntry sp0 N y →
      IR (P := P) base sp0 N U j y := fun y k hk h hb =>
    .inl (.inr ⟨frame_wt (reg_in h (by have := cb k hk; omega) (by decide)), hb⟩)
  refine segsTr_gp base _ (loop n) _ _ _ hl0 (fun k s i hk hi => ?_) (GP.nil fun _ hq => hq.mono fun y h => ?_)
  · seg_cases loop k hk
    exact pass_of rfl w1 w2
      (by pass_tac [vsL]; exact ⟨fun y h hb => .inl (.inl (.inr ⟨frame_wt h, hb⟩)),
        fun y h hb => .inl (tr y 0 (by decide) h hb), fun y h hb => .inl (tr y 1 (by decide) h hb),
        fun y h hb => .inl (tr y 2 (by decide) h hb), fun y h hb => .inl (tr y 3 (by decide) h hb)⟩)
      (by pass_tac [vsL]; exact ⟨fun y h hb => above_sub (hF y ⟨_, .head _, Rgn.of_region (reg_in h
        (by omega : j + 1 ≤ 64) (by decide))⟩ hb) (by omega), fun y h _ => fa y h⟩)
  · rcases h with h | ⟨⟨q, hq, h⟩, hb⟩
    · exact .inl (.inl h)
    · by_cases e : q = j
      · subst e
        exact .inr ⟨⟨0, by simp [loop], _, 0, rfl, by simp [segN, loop], inRD_of (d := 0) rfl (.head _) rfl rfl
          (by simpa using h)⟩, hb⟩
      · exact .inl (.inr ⟨⟨q, by omega, h⟩, hb⟩)

/-- **The body** at the frame's SP: from `e`, it writes the digits. -/
theorem body_gp (hn : n ∈ [2, 16]) (base : Word) {sp0 : Word} {N : Nat} {U : Word → Prop}
    (hroom : (sp0 - P 2).toNat + D ≤ N) (hN : N < 2 ^ 32)
    (hF : ∀ y, Has [⟨P 0, 64⟩, ⟨P 1, 32⟩] y → BelowEntry sp0 N y → AtOrAboveSp sp0 (P 2) y)
    (hR : ∀ y, Has [⟨P 1, 32⟩] y → BelowEntry sp0 N y → U y) :
    GP sp0 N (SIR sp0 fP U) (rcTr n base P) (SIR sp0 fP fun y => U y ∨ Has [⟨P 0, 64⟩] y ∧ BelowEntry sp0 N y) := by
  have fa : ∀ y, Region fP 40 y → AtOrAboveSp sp0 fP y := fun y h => reg_sub_above h (by decide) (by omega)
  have ra : ∀ y c w, Region (fP + BitVec.ofNat 32 c) w y → c + w ≤ 40 → AtOrAboveSp sp0 fP y :=
    fun y c w h hc => fa y (reg_in h hc (by decide))
  have eR : ∀ y c w, Region (P 1 + BitVec.ofNat 32 c) w y → c + w ≤ 32 → BelowEntry sp0 N y → U y :=
    fun y c w h hc hb => hR y ⟨_, .head _, Rgn.of_region (reg_in h hc (by decide))⟩ hb
  refine segsTr_gp base _ top _ _ U (by decide +kernel) (fun k s i hk hi => ?_)
    (GP.pre (fun _ hq => hq.mono fun y h => h.elim id fun ⟨⟨_, hk, _⟩, _⟩ => absurd hk (Nat.not_lt_zero _))
      (GP.repI (I := fun j => SIR sp0 fP (IR (P := P) base sp0 N U j)) 64 0
        (fun j _ hj => farPass_gp (pass_gp hn base hroom hN hF hj))
        (GP.nil fun _ hq => hq.mono fun y h => h.imp (.inl ·) fun ⟨h, hb⟩ => ⟨dig_cov h, hb⟩)))
  seg_cases top k hk <;> simp [segN, nT] at hi
  · exact pass_of (Wr := []) (Ww := [(0, 40)]) rfl rfl rfl (by pass_tac []) (by pass_tac [vsT]; exact fun y h _ => fa y h)
  · exact pass_of (Wr := [(0, 2)]) (Ww := [(1, 1)]) rfl rfl rfl
      (by pass_tac [vsT]; exact fun y h hb => .inl (eR y i 2 h (by omega) hb))
      (by pass_tac [vsT]; exact fun y h _ => ra y i 1 h (by omega))
  · exact pass_of (Wr := [(0, 1)]) (Ww := [(1, 1), (2, 40)]) rfl rfl rfl
      (by pass_tac [vsT]; exact fun y h hb => .inl (eR y 31 1 h (by omega) hb))
      (by pass_tac [vsT]; exact ⟨fun y h _ => ra y 31 1 h (by omega), fun y h _ => fa y h⟩)
end

/-! ## The routine's TE -/

/-- The decided layout checks of a build with `n` combs. -/
def rcOk (n : Nat) (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Bool :=
  rcAt n O B && seqAt B (oE n O) post && segsOk (B := B) (cs n) (oP O) D D top &&
  (segsOk (B := B) (cs n) (oL O) D D (loop n) && loopFarOk (B := B) (cs n) (oL O) (oL O + segsSize (loop n)) D D
    (brImm8 (oL O + segsSize (loop n)) (oL O + segsSize (loop n) + 4)) (brImm11 (oL O + segsSize (loop n) + 2) (oL O))) &&
  rangesSub [(O, O + 4), (oE n O, oE n O + 4)] (cs n) && decide (oE n O % 2 = 0 ∧ oE n O + seqSize post ≤ BS)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {n : Nat}

theorem Fr.pc {W : List Rgn} {P : Nat → Word} {m1 : Mem} {u : State} {v : Word} :
    Fr P m1 W { u with regs := fun i => if i = 15 then v else u.regs i } ↔ Fr P m1 W u := by simp [Fr]

noncomputable def rc_te (hn : n ∈ [2, 16]) (hok : rcOk n B BS = true) : (rcR n).TE rcPub rcE := by
  simp only [rcOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hL, hpo⟩, hT⟩, hR⟩, hcode⟩, he2, hbs⟩ := hok
  obtain ⟨hen, hL⟩ := piecesAt_cons hL
  have hbs' : oE n O + 4 ≤ BS := Nat.le_trans (Nat.le_refl _) hbs
  refine frame_te (mask := 0) (k := 10) (epi := oE n O) (spP := fun P => P 2) (Ψ := rcTr n)
    (Wd := fun _ P => Has [⟨P 0, 64⟩]) (by decide) hen hpo hcode
    ⟨by simp only [rcR]; decide, he2, hbs', Nat.le_trans (show O + 4 ≤ oE n O + 4 by
      simp only [oE, oB, oL, oP, show seqSize enter = 4 from rfl]; omega) hbs', by decide, by simp only [rcR]; decide⟩
    (fun _ _ => rfl) (fun base s e F t tpc t13 tr hm hc => ?_)
    (fun _ _ => by repeat (first | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_rep | apply farPass_uniq | apply segsTr_uniq | intro))
    (fun _ _ => by repeat (first | exact ⟨_, rfl⟩ | apply ex_cat | apply ex_segsTr | apply ex_rep | simp only [farPass] | intro))
    (fun _ _ y ⟨r, hr, h⟩ => ⟨r, by simp only [List.mem_singleton] at hr; simp [hr], h⟩)
    (fun b P sp0 N U hroom hN hF hR => by
      rw [show 4 * nSaved 0 + 4 * 10 = D by decide]; exact body_gp hn b hroom hN hF fun y h hb => .inl (hR y h hb))
  generalize hP : rcPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 13 = P 2 := by subst hP; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨q0, q1, q2⟩ := q
  have L : Lay P := by
    have hsW := e.sepWr; have hsR := e.sepRd; have hroom := e.room; have hsp4 := e.sp4
    simp only [rcR, Routine.win, D, q0, q1, q2] at hsW hsR hroom hsp4
    fp_simp at hsW hsR
    exact ⟨⟨hroom, hsp4⟩, ⟨by omega, by omega⟩, by simp only [D]; omega, by simp only [D]; omega⟩
  rc_lay L
  have hW : lowWin (rcR n) 0 s :: (rcR n).wr s = WcP P := by subst hP; rfl
  rw [hW, q2] at F
  rw [hW, show (rcR n).RdP base s = Has (RcP P base) by subst hP; rfl,
    show (rcR n).SpP s = InStackWindow (P 2) D by rw [← q2]; rfl]
  have t13' : t.regs 13 = P 2 - BitVec.ofNat 32 D := by rw [t13, q2]; rfl
  simp only [saved, show nSaved 0 = 1 from rfl, q2] at hm
  have hb1 : bytesAt t.mem (P 1) 32 = bytesAt s.mem (P 1) 32 := hm.bytes (by rc_fp)
  have he : decodeInt (bytesAt t.mem (P 1) 32) < 2 ^ 255 := by rw [hb1, ← q1]; exact e.pre
  trefine ReachFT.segs (d := D) F _ top (oP O) (JT n P t.mem) nT (vsT P) hL hT
    (fun k i u v h => by
      rcases k with _ | _ | _ | k <;> rcases i with _ | i <;> simpa [JT, L1, L2, Ub, Fr.pc, State.setReg] using h)
    (fun k sg hk => by seg_cases top k hk <;> simp [nT])
    (fun k sg i u hk hi h => top_side L k sg i u hk hi h) (top_step L)
    (fun k sg u hk h => by seg_cases top k hk <;> exact h) (fun t' hp hJ h13 hc' hl => ?_) t tpc
    ⟨t13', rfl, (tr 0 (by decide) (by decide)).trans q0, (tr 1 (by decide) (by decide)).trans q1⟩ t13' hc
  trefine ReachFT.segLoopFar (d := D) F [.seq post] (loop n) 0 (oL O) 64 (L2 n P t.mem) (JL n P t.mem)
    (fun _ _ => 1) (vsL n P) hl (by rw [Bool.and_eq_true]; exact hR)
    (fun j u v h => by simpa [L2, Ub, Fr.pc, State.setReg] using h)
    (fun j k i u v h => by
      rcases k with _ | k <;> rcases i with _ | i <;> simpa [JL, L2, Ub, Fr.pc, cond_pc, State.setReg] using h)
    (fun j u _ h => h) (fun j k sg _ hk => by seg_cases loop k hk; simp)
    (fun j k sg i u hj hk hi h => loop_side L hn hj k sg i u hk hi h) (fun j k sg i u hj => loop_step L hn he hj k sg i u)
    (fun j k sg u _ hk h => by seg_cases loop k hk; exact h) (fun j u _ h => h)
    (fun u hp hI h13 _ _ => ReachT.done ⟨hp, by rw [h13, t13'], fun r h4 h11 _ hr =>
      absurd (Ed25519Routines.mem_hiRegs h4 h11) hr, ?_⟩) t' (by decide) hp hJ h13 hc'
  intro q hq
  show (u.mem (s.regs 0 + BitVec.ofNat 32 q)).toNat = (digitAt n (decodeInt (bytesAt s.mem (s.regs 1) 32)) q + 8).toNat
  rw [q0, q1, ← hb1]; exact hI.2.2.2 q hq
end


/-! ## The callee -/

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_sc_recode_comb` in each build**, with its effect. -/
noncomputable def recode_te (b : Build) : letI := b.codeBytes; (rcR b.combs).TE rcPub rcE :=
  letI := b.codeBytes
  rc_te (by cases b <;> decide) (by simp only [rcOk, rc_at, Bool.true_and]; cases b <;> decide +kernel)

open M0Crypto.Release.Ed25519 (Build) in
theorem recode_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => rcR b.combs) rcPub :=
  letI := b.codeBytes; ⟨(recode_te b).T, fun _ => (recode_te b).spec⟩


open M0Crypto.Release.Ed25519CallProg in
def rcS : M0Crypto.Release.Ed25519CallProg.CalleeS := calleeAt O (io1 32 .cl 64 (.bytes 64)) [0, 1]

open M0Crypto.Release.Ed25519CallProg in
theorem rc_pub : rcS.pub = rcPub := rfl

open M0Crypto.Release.Ed25519CallProg in
/-- The effect is the callee's. -/
theorem rc_eff (base : Word) (p : Nat → Word) (tr : List Event) (h : rcE base p tr) : rcS.Eff p base tr := by
  refine EffT.mono h (by decide +kernel) (fun y ⟨r, hr, hy⟩ => ⟨r, ?_, hy⟩)
    (fun y ⟨r, hr, hy⟩ => .inr ⟨_, .head _, ?_⟩) (fun y ⟨x, hx, hy⟩ => ⟨_, .head _, ?_⟩)
  · show r ∈ [codeR base, ⟨p 1 + BitVec.ofNat 32 0, 32⟩, ⟨p 0 + BitVec.ofNat 32 0, 64⟩]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  · simp only [List.mem_singleton] at hr; subst hr
    show Region (p 1 + BitVec.ofNat 32 0) 32 y; rw [BitVec.add_zero]; obtain ⟨_, ho, e⟩ := hy; exact Region.mk ho e
  · simp only [rcS, calleeAt, io1, List.mem_singleton] at hx; subst hx
    have hy : Region (p 0 + BitVec.ofNat 32 0) 64 y := hy
    rw [BitVec.add_zero] at hy; exact Rgn.of_region hy
end M0Crypto.Release.Ed25519Recode
