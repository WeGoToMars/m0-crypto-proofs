import M0Crypto.Release.Ed25519MpMulCode
import M0Crypto.Release.Ed25519ScalarChain
import M0Crypto.Release.BlockEffect
import M0Crypto.Release.SegEffect

set_option linter.unusedSimpArgs false

/-!
# `m0c_mp_mul`

`mp_mul_tspec`: in each build, a call with `n = r3 > 0` words `a` at `r1` and `b` at `r2`, each
apart from the `2 n` words at `r0`, leaves `dst = a · b` (`wsum`). It writes only `dst` and its
`D`-byte stack window (the `FRAME`-byte frame and the saved LR), reads only `dst`, `a`, `b` and
that window (code reads are admitted by the common judgment), and has a trace that is a function
of the pointers, `n` and `sp`.

Each block's effect is one decided `Eff` (`BlockEffect`). The top segments (the frame stores, the
zero loop, the row counter) and each row (start, inner loop, end) are `Routine.ReachFT.segs` and
`ReachFT.segLoop`; the invariants at their boundaries are `JT` and `JR`, and `top_side`/`top_step`,
`row_side`/`row_step` discharge each segment's footprints and effect.

`mp_mul_te` is that call lemma with its byte effect `mpE` (`Routine.TE`, by `StackEffect.frame_te`):
with `D` bytes of stack it reads `a` and `b` and writes `dst`. `body_gp` derives it from each
segment's decided block effect (`StackEffect.segsTr_gp`): the top segments write the frame and
`dst` (`WT`), the rows read those, `a` and `b`, and write `dst` and the row slot.
-/

namespace M0Crypto.Release.Ed25519MpMul

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 addWithCarry slot)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Ed25519MpMulCode
open M0Crypto.Release.Ed25519ScalarChain (wv)

open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SBool SMem)

/-- The word at register `r`, a constant. -/
abbrev ld (r : Reg) : SExpr := .ld32 .mem0 (.reg0 r)
abbrev cw (n : Nat) : SExpr := .const (BitVec.ofNat 32 n)

/-! ## The inner step -/

/-- `a[i] · b[j]` (`r8`, the word at `r10`) from `mul32`, plus `dst[i + j]` (at `r11`), plus `r12`. -/
def mulM : SExpr × SExpr := mulS 0 1 2 3 5 (.reg0 8) (ld 10)
def lo1 : SExpr := .awc mulM.1 (ld 11) (.const false)
def loM : SExpr := .awc lo1 (.reg0 12) (.const false)
def hiM : SExpr := .awc (.awc mulM.2 (cw 0) (.awcC mulM.1 (ld 11) (.const false))) (cw 0)
  (.awcC lo1 (.reg0 12) (.const false))

/-- **The effect of `mac`**: `loM` stored at `r11` and kept in `r0`, `hiM` the new carry `r12`,
`r10` and `r11` up a word, the count `r9` down by one with its zero flag. -/
def macE : Eff where
  regs := [(0, loM), (12, hiM), (10, .add (.reg0 10) (cw 4)), (11, .add (.reg0 11) (cw 4)),
    (9, subS (.reg0 9) 1)]
  clob := [1, 2, 3, 4, 5]
  z := some (.isZero (subS (.reg0 9) 1))
  mem := some (.w32 .mem0 (.reg0 11) loM)

theorem mac_ok : effOk mac macE = true := by decide +kernel

/-- The value of an inner step: `lo + 2^32 hi = a[i] · b[j] + dst[i + j] + carry`. -/
theorem mac_nat (u : State) : (loM.denote u).toNat + 2 ^ 32 * (hiM.denote u).toNat =
    (u.regs 8).toNat * (read32 u.mem (u.regs 10)).toNat + (read32 u.mem (u.regs 11)).toNat +
      (u.regs 12).toNat :=
  acc2_nat (mulS_nat (by constructor <;> decide) _ _ u)
    (Nat.mul_le_mul (Nat.le_sub_one_of_lt (u.regs 8).isLt) (Nat.le_sub_one_of_lt (read32 _ _).isLt))

/-! ## The other blocks -/

/-- The arguments stored in the frame; `r4 = n << 1`, `r5 = 0`. -/
def preE : Eff where
  regs := [(4, .lsl (.reg0 3) 1), (5, cw 0)]
  mem := none
  reads := [(spA SD, .reg0 0), (spA SA, .reg0 1), (spA SB, .reg0 2), (spA SN, .reg0 3)]

/-- `r5` stored at `r0`, which steps; the count `r4` down by one with its zero flag. -/
def zbE : Eff where
  regs := [(0, .add (.reg0 0) (cw 4)), (4, subS (.reg0 4) 1)]
  z := some (.isZero (subS (.reg0 4) 1))
  mem := some (.w32 .mem0 (.reg0 0) (.reg0 5))

def zpE : Eff where
  mem := none
  reads := [(spA ROW, .reg0 4)]

/-- `r8 = a[row]`, `r11 = dst + 4 row`, `r10 = b`, `r9 = n`, `r12 = 0`. -/
def headE : Eff where
  regs := [(8, .ld32 .mem0 aiA), (9, ldS SN), (10, ldS SB), (11, .add (ldS SD) (.lsl (ldS ROW) 2)),
    (12, cw 0)]
  clob := [0, 1, 2, 3, 4, 5]

/-- The row slot after the carry's store, plus one. -/
def rowS : SExpr := .add (.ld32 (.w32 .mem0 (.reg0 11) (.reg0 12)) (spA ROW)) (cw 1)

/-- The carry stored at `r11`, the row slot up by one, compared with `n`. -/
def tailE : Eff where
  clob := [1, 3, 4]
  z := some (.isZero (.awc rowS (.not (.ld32 (.w32 .mem0 (.reg0 11) (.reg0 12)) (spA SN))) (.const true)))
  mem := some (.w32 (.w32 .mem0 (.reg0 11) (.reg0 12)) (spA ROW) rowS)

theorem pre_ok : effOk pre preE = true := by decide +kernel
theorem zb_ok : effOk zbody zbE = true := by decide +kernel
theorem zp_ok : effOk zpost zpE = true := by decide +kernel
theorem head_ok : effOk head headE = true := by decide +kernel
theorem tail_ok : effOk tail tailE = true := by decide +kernel

/-! ## The routine -/

open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.Ed25519Words (wsum upd wsum_congr mp_mul_start mp_mul_inner mp_mul_row)
open M0Crypto.Release.Ed25519ScalarChain (wv_keep wv_write)
open M0Crypto.Release.Ed25519WordLoop (add_ofNat_add memEq_write32)

def cs : List (Nat × Nat) := [(O, oE O + seqSize post)]
def D : Nat := 4 + FRAME

/-- **`m0c_mp_mul`**: the `2 n` words at `r0` become `a · b`, for the `n = r3` words `a` at `r1`
and `b` at `r2`, each apart from the result. -/
def mpR : Routine where
  entry := O
  code := cs
  stack := D
  Pre := fun _ s => 0 < (s.regs 3).toNat ∧ (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧
    (s.regs 2).toNat % 4 = 0 ∧ Disj (s.regs 0) (8 * (s.regs 3).toNat) (s.regs 1) (4 * (s.regs 3).toNat) ∧
    Disj (s.regs 0) (8 * (s.regs 3).toNat) (s.regs 2) (4 * (s.regs 3).toNat)
  wr := fun s => [⟨s.regs 0, 8 * (s.regs 3).toNat⟩]
  rd := fun s => [⟨s.regs 0, 8 * (s.regs 3).toNat⟩, ⟨s.regs 1, 4 * (s.regs 3).toNat⟩,
    ⟨s.regs 2, 4 * (s.regs 3).toNat⟩]
  Post := fun s m _ => wsum (wv m (s.regs 0)) (2 * (s.regs 3).toNat) =
    wsum (wv s.mem (s.regs 1)) (s.regs 3).toNat * wsum (wv s.mem (s.regs 2)) (s.regs 3).toNat
  clob := Ed25519Routines.hiRegs

/-- The public values: the three pointers, `n` and `sp`. -/
def mpPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 1, s.regs 2, s.regs 3, s.regs 13]

set_option hygiene false in
/-- `n`, and the frame's base `sp − D`, of the public values `P`. -/
local notation "nP" => (P 3).toNat
set_option hygiene false in
local notation "fP" => (P 4 - BitVec.ofNat 32 D)

section
variable (P : Nat → Word) (m1 : Mem)

/-- The layout of a call in `toNat` form. -/
structure Lay : Prop where
  n0 : 0 < nP
  sp : D ≤ (P 4).toNat ∧ (P 4).toNat % 4 = 0
  al : (P 0).toNat % 4 = 0 ∧ (P 1).toNat % 4 = 0 ∧ (P 2).toNat % 4 = 0
  ab : (P 0).toNat + 8 * nP ≤ 2 ^ 32 ∧ (P 1).toNat + 4 * nP ≤ 2 ^ 32 ∧ (P 2).toNat + 4 * nP ≤ 2 ^ 32
  da : (P 0).toNat + 8 * nP ≤ (P 1).toNat ∨ (P 1).toNat + 4 * nP ≤ (P 0).toNat
  db : (P 0).toNat + 8 * nP ≤ (P 2).toNat ∨ (P 2).toNat + 4 * nP ≤ (P 0).toNat
  w0 : (P 0).toNat + 8 * nP ≤ (P 4).toNat - D ∨ (P 4).toNat ≤ (P 0).toNat
  w1 : (P 1).toNat + 4 * nP ≤ (P 4).toNat - D ∨ (P 4).toNat ≤ (P 1).toNat
  w2 : (P 2).toNat + 4 * nP ≤ (P 4).toNat - D ∨ (P 4).toNat ≤ (P 2).toNat

/-- The caller footprints: writes to the frame and `dst`, reads also of the saved LR, `a`, `b`. -/
def WcP : List Rgn := [⟨fP, FRAME⟩, ⟨P 0, 8 * nP⟩]
def RcP {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) : List Rgn :=
  codeR base :: ⟨fP, D⟩ :: [⟨P 0, 8 * nP⟩, ⟨P 1, 4 * nP⟩, ⟨P 2, 4 * nP⟩]

/-- Memory as `m1` (after the push) but for the frame and `dst`; the arguments in the frame. -/
structure Fr (u : State) : Prop where
  mem : MemEq [⟨fP, FRAME⟩, ⟨P 0, 8 * nP⟩] m1 u.mem
  sp : u.regs 13 = fP
  sd : read32 u.mem (fP + BitVec.ofNat 32 SD) = P 0
  sa : read32 u.mem (fP + BitVec.ofNat 32 SA) = P 1
  sb : read32 u.mem (fP + BitVec.ofNat 32 SB) = P 2
  sn : read32 u.mem (fP + BitVec.ofNat 32 SN) = P 3

/-- The zero loop before pass `j`. -/
def ZI (j : Nat) (u : State) : Prop := Fr P m1 u ∧ u.regs 0 = P 0 + BitVec.ofNat 32 (4 * j) ∧
  u.regs 4 = BitVec.ofNat 32 (2 * nP - j) ∧ u.regs 5 = 0 ∧ ∀ k < j, wv u.mem (P 0) k = 0

/-- The words of `dst` from `n + i` are zero. -/
def Zs (i : Nat) (u : State) : Prop := ∀ k, nP + i ≤ k → k < 2 * nP → wv u.mem (P 0) k = 0

/-- Before row `i`: `dst = a[0 … i) · b`. -/
def Out (i : Nat) (u : State) : Prop := Fr P m1 u ∧ read32 u.mem (fP + BitVec.ofNat 32 ROW) = BitVec.ofNat 32 i ∧
  wsum (wv u.mem (P 0)) (2 * nP) = wsum (wv m1 (P 1)) i * wsum (wv m1 (P 2)) nP ∧ Zs P i u

/-- Row `i` before inner step `j` (`Ed25519Words.mp_mul_inner`). -/
def II (i j : Nat) (u : State) : Prop := Fr P m1 u ∧
  read32 u.mem (fP + BitVec.ofNat 32 ROW) = BitVec.ofNat 32 i ∧ (u.regs 8).toNat = wv m1 (P 1) i ∧
  u.regs 9 = BitVec.ofNat 32 (nP - j) ∧ u.regs 10 = P 2 + BitVec.ofNat 32 (4 * j) ∧
  u.regs 11 = P 0 + BitVec.ofNat 32 (4 * (i + j)) ∧
  wsum (wv u.mem (P 0)) (2 * nP) + 2 ^ (32 * (i + j)) * (u.regs 12).toNat =
    wsum (wv m1 (P 1)) i * wsum (wv m1 (P 2)) nP + 2 ^ (32 * i) * (wv m1 (P 1) i * wsum (wv m1 (P 2)) j) ∧
  Zs P i u

/-- The boundaries of the top segments. -/
def JT : Nat → Nat → State → Prop
  | 0, 0, u => u.regs 13 = fP ∧ u.mem = m1 ∧ u.regs 0 = P 0 ∧ u.regs 1 = P 1 ∧ u.regs 2 = P 2 ∧ u.regs 3 = P 3
  | 0, _, u => ZI P m1 0 u
  | 1, j, u => ZI P m1 j u
  | 2, 0, u => ZI P m1 (2 * nP) u
  | _, _, u => Out P m1 0 u

/-- The boundaries of row `i`. -/
def JR (i : Nat) : Nat → Nat → State → Prop
  | 0, 0, u => Out P m1 i u
  | 0, _, u => II P m1 i 0 u
  | 1, j, u => II P m1 i j u
  | 2, 0, u => II P m1 i nP u
  | _, _, u => Out P m1 (i + 1) u ∧ condPassed 1 u = decide (i + 1 < nP)

def nT (k : Nat) : Nat := if k = 1 then 2 * nP else 1
def nR (_ k : Nat) : Nat := if k = 1 then nP else 1
def vsT (k j : Nat) : List Word := if k = 1 then [P 0 + BitVec.ofNat 32 (4 * j)] else [fP]
def vsR (i k j : Nat) : List Word := match k with
  | 0 => [fP, P 1 + BitVec.ofNat 32 (4 * i)]
  | 1 => [P 2 + BitVec.ofNat 32 (4 * j), P 0 + BitVec.ofNat 32 (4 * (i + j))]
  | _ => [fP, P 0 + BitVec.ofNat 32 (4 * (i + nP))]
end

/-! ## The byte effect -/

open M0Crypto.Release.StackEffect (EffT GP SIR WS segN segsTr_gp pass_of frame_te above_sub reg_split
  reg_sub_above inRD_of ex_cat ex_rep ex_segsTr)
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)

/-- **The effect of `m0c_mp_mul`**: it reads `a` and `b` and writes `dst`, in a frame of `D` bytes. -/
def mpE (_ : Word) (P : Nat → Word) : TrP :=
  EffT D (Has [⟨P 0, 8 * nP⟩, ⟨P 1, 4 * nP⟩, ⟨P 2, 4 * nP⟩]) (Has [⟨P 1, 4 * nP⟩, ⟨P 2, 4 * nP⟩])
    (Has [⟨P 0, 8 * nP⟩]) (P 4)

/-- The body's trace: the top segments, then the rows closed by `bne`. -/
def mpTr (base : Word) (P : Nat → Word) : TrP :=
  segsTr base (oP O) top (vsT P) (nT P) (Tr.rep (fun j => Tr.cat (segsTr base (oH O) row (vsR P j) (nR P j)
    (Tr.is [])) (Tr.is [⟨base + BitVec.ofNat 32 (oH O + segsSize row), .bcond 1 (brImm8 (oH O + segsSize row) (oH O)),
      []⟩])) 0 nP (Tr.is []))

section
variable {P : Nat → Word} {sp0 : Word} {n : Nat}

theorem rgn_word {a : Word} {m j o : Nat} (h : 4 * j + o < m) :
    Rgn.Has ⟨a, m⟩ (a + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 o) :=
  ⟨4 * j + o, h, add_add_ofNat _ _ _⟩

theorem has_word {a y : Word} {j m : Nat} (h : Region (a + BitVec.ofNat 32 (4 * j)) 4 y) (hj : 4 * j + 4 ≤ m) :
    Rgn.Has ⟨a, m⟩ y := by
  obtain ⟨t, ht, rfl⟩ := Region.exists h; exact rgn_word (by omega)

/-- The bytes the top segments write: the frame and `dst`. -/
abbrev WT (P : Nat → Word) (base : Word) : Word → Prop := WS base (oP O) top (vsT P) (nT P) 3

theorem dst_wt {base y : Word} {j : Nat} (hj : j < 2 * nP) (h : Region (P 0 + BitVec.ofNat 32 (4 * j)) 4 y) :
    WT P base y :=
  ⟨1, by decide, _, j, rfl, by simpa [segN, top, nT] using hj, inRD_of (d := 0) rfl (.head _) rfl rfl (by simpa using h)⟩

theorem frame_wt {base y : Word} (h : Region fP 20 y) : WT P base y := by
  rcases reg_split (x := 16) (w := 4) h with h | h
  · exact ⟨0, by decide, _, 0, rfl, by simp [segN, top], inRD_of (d := 0) rfl (.head _) rfl rfl (by simpa using h)⟩
  · exact ⟨2, by decide, _, 0, rfl, by simp [segN, top], inRD_of (d := BitVec.ofNat 32 16) rfl (.head _) rfl rfl h⟩

theorem dst_cov {base y : Word} (h : Has [⟨P 0, 8 * nP⟩] y) : WT P base y := by
  obtain ⟨_, hr, o, ho, rfl⟩ := h
  simp only [List.mem_singleton] at hr; subst hr
  dsimp only at ho ⊢
  rw [← Nat.div_add_mod o 4, ← add_add_ofNat]
  exact dst_wt (j := o / 4) (by omega) (by simp only [Region]; bv_omega)

/-- **The body** at the frame's SP: from `a` and `b`, it writes `dst`. -/
theorem body_gp (base : Word) {U : Word → Prop} (hroom : (sp0 - P 4).toNat + D ≤ n) (hn : n < 2 ^ 32)
    (hF : ∀ y, Has [⟨P 0, 8 * nP⟩, ⟨P 1, 4 * nP⟩, ⟨P 2, 4 * nP⟩] y → BelowEntry sp0 n y → AtOrAboveSp sp0 (P 4) y)
    (hR : ∀ y, Has [⟨P 1, 4 * nP⟩, ⟨P 2, 4 * nP⟩] y → BelowEntry sp0 n y → U y) :
    GP sp0 n (SIR sp0 fP U) (mpTr base P) (SIR sp0 fP fun y => U y ∨ Has [⟨P 0, 8 * nP⟩] y ∧ BelowEntry sp0 n y) := by
  have fa : ∀ y, Region fP 20 y → AtOrAboveSp sp0 fP y := fun y h => reg_sub_above h (by decide) (by omega)
  have da : ∀ y j, j < 2 * nP → Region (P 0 + BitVec.ofNat 32 (4 * j)) 4 y → BelowEntry sp0 n y →
      AtOrAboveSp sp0 fP y := fun y j hj h hb =>
    above_sub (hF y ⟨_, .head _, has_word h (by omega)⟩ hb) (by omega)
  refine segsTr_gp base _ top _ _ U (by decide +kernel) (fun k s i hk hi => ?_)
    (GP.rep (GP.nil fun _ hq => hq.mono fun y h => h.imp_right fun ⟨h, hb⟩ => ⟨dst_cov h, hb⟩) nP 0
      fun j hj => GP.cat (segsTr_gp base _ row _ _ _ (by decide +kernel) (fun k s i hk hi => ?_)
        (GP.nil fun _ hq => hq.mono fun _ h => .inl h)) (StackEffect.sir_quietC rfl rfl rfl))
  · seg_cases top k hk <;> simp [segN, nT] at hi
    · exact pass_of (Wr := []) (Ww := [(0, 20)]) rfl rfl rfl (by pass_tac []) (by pass_tac [vsT]; exact fun y h _ => fa y h)
    · exact pass_of (Wr := []) (Ww := [(0, 4)]) rfl rfl rfl (by pass_tac []) (by pass_tac [vsT]; exact fun y h => da y i hi h)
    · exact pass_of (Wr := []) (Ww := [(0, 20)]) rfl rfl rfl (by pass_tac []) (by pass_tac [vsT]; exact fun y h _ => fa y h)
  · seg_cases row k hk <;> simp [segN, nR] at hi
    · exact pass_of (Wr := [(0, 20), (1, 4)]) (Ww := []) rfl rfl rfl
        (by pass_tac [vsR]; exact ⟨fun y h hb => .inl (.inr ⟨frame_wt h, hb⟩),
          fun y h hb => .inl (.inl (hR y ⟨_, .head _, has_word h (by omega)⟩ hb))⟩) (by pass_tac [])
    · exact pass_of (Wr := [(0, 4), (1, 4)]) (Ww := [(1, 4)]) rfl rfl rfl
        (by pass_tac [vsR]; exact ⟨fun y h hb => .inl (.inl (hR y ⟨_, .tail _ (.head _), has_word h (by omega)⟩ hb)),
          fun y h hb => .inl (.inr ⟨dst_wt (by omega) h, hb⟩)⟩)
        (by pass_tac [vsR]; exact fun y h => da y _ (by omega) h)
    · exact pass_of (Wr := [(0, 20)]) (Ww := [(1, 4), (0, 20)]) rfl rfl rfl
        (by pass_tac [vsR]; exact fun y h hb => .inl (.inr ⟨frame_wt h, hb⟩))
        (by pass_tac [vsR]; exact ⟨fun y h => da y _ (by omega) h, fun y h _ => fa y h⟩)

end

/-- The layout facts as hypotheses, for `fp_tac` and `omega`. -/
macro "lay_tac" L:ident : tactic => `(tactic| (
  have := ($L).n0; have := ($L).sp; have := ($L).al; have := ($L).ab; have := ($L).da
  have := ($L).db; have := ($L).w0; have := ($L).w1; have := ($L).w2
  simp only [D, FRAME] at *))

/-- `fp_tac` with the frame's offsets. -/
macro "mp_fp" : tactic => `(tactic| (simp only [SD, SA, SB, SN, ROW, D, FRAME] at *; fp_tac))

section
variable {P : Nat → Word} {m1 : Mem}

/-- `Fr` after a block that writes `W`, inside the row slot and `dst`. -/
theorem Fr.step {u v : State} (L : Lay P) (h : Fr P m1 u) {W : List Rgn} (hm : MemEq W u.mem v.mem)
    (hW : Sub W [⟨fP, FRAME⟩, ⟨P 0, 8 * nP⟩]) (hS : Sep W [⟨fP, ROW⟩]) (h13 : v.regs 13 = u.regs 13) :
    Fr P m1 v := by
  lay_tac L
  have hs : ∀ a, a ≤ SN → Sep [⟨fP + BitVec.ofNat 32 a, 4⟩] W := fun a ha =>
    Sub.sep (g := [⟨fP, ROW⟩]) (by mp_fp) hS.symm
  exact ⟨h.mem.grow hm hW, h13.trans h.sp, (hm.read32 (hs _ (by decide))).trans h.sd,
    (hm.read32 (hs _ (by decide))).trans h.sa, (hm.read32 (hs _ (by decide))).trans h.sb,
    (hm.read32 (hs _ (by decide))).trans h.sn⟩

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

theorem top_side (L : Lay P) : ∀ k sg i u, top[k]? = some sg → i < nT P k → JT P m1 k i u →
    SGlueSides u (RcP P base) (WcP P) sg.al sg.wg sg.rg ∧ sg.As.map (·.denote u) = vsT P k i := by
  intro k sg i u hk hi h; lay_tac L
  seg_cases top k hk
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, h.1], by simp [vsT, SExpr.denote, h.1]⟩
  · simp only [nT, ↓reduceIte] at hi
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, h.2.1], by simp [vsT, SExpr.denote, h.2.1]⟩
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, spA, ROW, h.1.sp], by simp [vsT, SExpr.denote, h.1.sp]⟩

theorem top_step (L : Lay P) : ∀ k sg i u, top[k]? = some sg → i < nT P k → JT P m1 k i u →
    MemEq (sregions u sg.wg) u.mem (execAll sg.g u).mem → JT P m1 k (i + 1) (execAll sg.g u) ∧
      ∀ c, sg.br = some c → condPassed c (execAll sg.g u) = decide (i + 1 < nT P k) := by
  intro k sg i u hk hi h hm; lay_tac L
  seg_cases top k hk <;> dsimp only at hm ⊢
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    obtain ⟨h13, rfl, h0, h1, h2, h3⟩ := h
    have E := eff_run pre_ok u
    simp only [sregions, List.map, SExpr.denote, h13] at hm
    refine ⟨show ZI P u.mem 0 _ from ⟨⟨hm.mono (by mp_fp), ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun c hc => nomatch hc⟩
    · rw [E.reg 13 (by decide) (by decide)]; exact h13
    · simpa [spA, SExpr.denote, h13, h0] using E.rd (spA SD) (.reg0 0) (by decide)
    · simpa [spA, SExpr.denote, h13, h1] using E.rd (spA SA) (.reg0 1) (by decide)
    · simpa [spA, SExpr.denote, h13, h2] using E.rd (spA SB) (.reg0 2) (by decide)
    · simpa [spA, SExpr.denote, h13, h3] using E.rd (spA SN) (.reg0 3) (by decide)
    · rw [E.reg 0 (by decide) (by decide)]; simp [Eff.reg, preE, SExpr.denote, h0]
    · rw [E.reg 4 (by decide) (by decide)]; simp [Eff.reg, preE, SExpr.denote, h3, lsl1]
    · rw [E.reg 5 (by decide) (by decide)]; simp [Eff.reg, preE, SExpr.denote]
  · simp only [nT, ↓reduceIte] at hi
    obtain ⟨hf, h0, h4, h5, hz⟩ := h
    have E := eff_run zb_ok u
    simp only [sregions, List.map, SExpr.denote, h0] at hm
    have c := cnt hi (by omega)
    refine ⟨⟨Fr.step L hf hm (by mp_fp) (by mp_fp) (E.reg 13 (by decide) (by decide)), ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [E.reg 0 (by decide) (by decide)]
      show u.regs 0 + BitVec.ofNat 32 4 = _; rw [h0, add_ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
    · rw [E.reg 4 (by decide) (by decide)]; simpa [Eff.reg, zbE, SExpr.denote, h4] using c.1
    · rw [E.reg 5 (by decide) (by decide)]; exact h5
    · intro k hk
      rw [E.mem _ rfl]
      show wv (write32 u.mem (u.regs 0) (u.regs 5)) (P 0) k = 0
      rw [h0, h5, wv_write _ _ _ (L := 2 * nP) (by omega) hi k (by omega)]
      by_cases e : k = i
      · subst e; simp [upd]
      · rw [Ed25519Words.upd_ne _ _ e]; exact hz k (by omega)
    · rintro _ ⟨⟩
      rw [RoutineBranch.cond_ne, E.z _ rfl]; simpa [nT, SBool.denote, SExpr.denote, h4, c.1] using c.2
  · obtain rfl : i = 0 := by simp [nT] at hi; omega
    obtain ⟨hf, h0, h4, h5, hz⟩ := h
    have E := eff_run zp_ok u
    simp only [sregions, List.map, SExpr.denote, spA, hf.sp] at hm
    have hk : ∀ k < 2 * nP, wv (execAll zpost u).mem (P 0) k = 0 := fun k hk =>
      (wv_keep hm (by mp_fp)).trans (hz k hk)
    refine ⟨show Out P m1 0 _ from ⟨Fr.step L hf hm (by mp_fp) (by mp_fp)
      (E.reg 13 (by decide) (by decide)), ?_, mp_mul_start hk, fun k _ h => hk k h⟩, fun c hc => nomatch hc⟩
    simpa [spA, SExpr.denote, hf.sp, h4] using E.rd (spA ROW) (.reg0 4) (by decide)

theorem row_side (L : Lay P) {i : Nat} (hi : i < nP) : ∀ k sg j u, row[k]? = some sg → j < nR P i k →
    JR P m1 i k j u →
    SGlueSides u (RcP P base) (WcP P) sg.al sg.wg sg.rg ∧ sg.As.map (·.denote u) = vsR P i k j := by
  intro k sg j u hk hj h; lay_tac L
  seg_cases row k hk
  · obtain rfl : j = 0 := by simp [nR] at hj; omega
    obtain ⟨hf, hr, -, -⟩ := h
    have sp := hf.sp; have sa := hf.sa; have r := hr
    simp only [D, FRAME] at sp sa r
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, aiA, ldS, spA, SMem.denote, sp, sa, r, lsl2],
      by simp [vsR, aiA, ldS, spA, SExpr.denote, SMem.denote, hf.sp, hf.sa, hr, lsl2]⟩
  · simp only [nR, ↓reduceIte] at hj
    obtain ⟨-, -, -, -, h10, h11, -, -⟩ := h
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, h10, h11], by simp [vsR, SExpr.denote, h10, h11]⟩
  · obtain rfl : j = 0 := by simp [nR] at hj; omega
    obtain ⟨hf, -, -, -, -, h11, -, -⟩ := h
    exact ⟨by glue_tac [WcP, RcP, D, FRAME, spA, ROW, SN, hf.sp, h11], by simp [vsR, SExpr.denote, hf.sp, h11]⟩

theorem row_step (L : Lay P) {i : Nat} (hi : i < nP) : ∀ k sg j u, row[k]? = some sg → j < nR P i k →
    JR P m1 i k j u → MemEq (sregions u sg.wg) u.mem (execAll sg.g u).mem →
    JR P m1 i k (j + 1) (execAll sg.g u) ∧
      ∀ c, sg.br = some c → condPassed c (execAll sg.g u) = decide (j + 1 < nR P i k) := by
  intro k sg j u hk hj h hm; lay_tac L
  seg_cases row k hk <;> dsimp only at hm ⊢
  · obtain rfl : j = 0 := by simp [nR] at hj; omega
    obtain ⟨hf, hr, hs, hz⟩ := h
    have E := eff_run head_ok u
    have hv : (execAll head u).mem = u.mem := E.mem _ rfl
    simp only [sregions, List.map_nil] at hm
    have ha : read32 u.mem (P 1 + BitVec.ofNat 32 (4 * i)) = read32 m1 (P 1 + BitVec.ofNat 32 (4 * i)) :=
      hf.mem.read32 (by mp_fp)
    refine ⟨show II P m1 i 0 _ from ⟨Fr.step L hf hm (by mp_fp) (by mp_fp) (E.reg 13 (by decide) (by decide)),
      by rw [hv]; exact hr, ?_, ?_, ?_, ?_, ?_, fun k h1 h2 => by rw [hv]; exact hz k h1 h2⟩, fun c hc => nomatch hc⟩
    · rw [E.reg 8 (by decide) (by decide)]
      simp [Eff.reg, headE, aiA, ldS, spA, SExpr.denote, SMem.denote, hf.sp, hf.sa, hr, lsl2, ha]; rfl
    · rw [E.reg 9 (by decide) (by decide)]; simp [Eff.reg, headE, ldS, spA, SExpr.denote, SMem.denote, hf.sp, hf.sn]
    · rw [E.reg 10 (by decide) (by decide)]; simp [Eff.reg, headE, ldS, spA, SExpr.denote, SMem.denote, hf.sp, hf.sb]
    · rw [E.reg 11 (by decide) (by decide)]
      simp [Eff.reg, headE, ldS, spA, SExpr.denote, SMem.denote, hf.sp, hf.sd, hr, lsl2]
    · rw [E.reg 12 (by decide) (by decide), hv]; simp [Eff.reg, headE, SExpr.denote, hs]
  · simp only [nR, ↓reduceIte] at hj
    obtain ⟨hf, hr, h8, h9, h10, h11, he, hz⟩ := h
    have E := eff_run mac_ok u
    simp only [sregions, List.map, SExpr.denote, h11] at hm
    have c := cnt hj (by omega)
    have hs := mac_nat u
    rw [h8, h10, h11, hf.mem.read32 (a := P 2 + _) (by mp_fp)] at hs
    have hin := mp_mul_inner (D := wv u.mem (P 0)) he hj hi hs
    have hw := wv_write u.mem (P 0) (loM.denote u) (L := 2 * nP) (by omega) (i := i + j) (by omega)
    have hv : (execAll mac u).mem = write32 u.mem (P 0 + BitVec.ofNat 32 (4 * (i + j))) (loM.denote u) := by
      rw [E.mem _ rfl, ← h11]; rfl
    refine ⟨⟨Fr.step L hf hm (by mp_fp) (by mp_fp) (E.reg 13 (by decide) (by decide)),
      (hm.read32 (by mp_fp)).trans hr, by rw [E.reg 8 (by decide) (by decide)]; exact h8,
      ?_, ?_, ?_, ?_, fun k h1 h2 => ?_⟩, ?_⟩
    · rw [E.reg 9 (by decide) (by decide)]; simpa [Eff.reg, macE, SExpr.denote, h9] using c.1
    · rw [E.reg 10 (by decide) (by decide)]
      show u.regs 10 + BitVec.ofNat 32 4 = _; rw [h10, add_ofNat_add, show 4 * j + 4 = 4 * (j + 1) by omega]
    · rw [E.reg 11 (by decide) (by decide)]
      show u.regs 11 + BitVec.ofNat 32 4 = _; rw [h11, add_ofNat_add, show 4 * (i + j) + 4 = 4 * (i + (j + 1)) by omega]
    · rw [E.reg 12 (by decide) (by decide), hv, wsum_congr hw]; exact hin
    · rw [hv, hw k h2, Ed25519Words.upd_ne _ _ (by omega)]; exact hz k h1 h2
    · rintro _ ⟨⟩
      rw [RoutineBranch.cond_ne, E.z _ rfl]; simpa [nR, SBool.denote, SExpr.denote, h9, c.1] using c.2
  · obtain rfl : j = 0 := by simp [nR] at hj; omega
    obtain ⟨hf, hr, h8, h9, h10, h11, he, hz⟩ := h
    have E := eff_run tail_ok u
    simp only [sregions, List.map, SExpr.denote, spA, hf.sp, h11] at hm
    obtain ⟨m', hm'⟩ : ∃ m', m' = write32 u.mem (P 0 + BitVec.ofNat 32 (4 * (i + nP))) (u.regs 12) := ⟨_, rfl⟩
    have r1 : read32 m' (fP + BitVec.ofNat 32 ROW) = BitVec.ofNat 32 i := by
      rw [hm', MemEq.read32 (memEq_write32 _ _ _) (by mp_fp)]; exact hr
    have rn : read32 m' (fP + BitVec.ofNat 32 SN) = P 3 := by
      rw [hm', MemEq.read32 (memEq_write32 _ _ _) (by mp_fp)]; exact hf.sn
    have hv : (execAll tail u).mem = write32 m' (fP + BitVec.ofNat 32 ROW) (BitVec.ofNat 32 (i + 1)) := by
      rw [E.mem _ rfl]
      simp only [tailE, rowS, spA, cw, SMem.denote, SExpr.denote, h11, hf.sp, ← hm', r1, ← BitVec.ofNat_add]
    have hk : ∀ k < 2 * nP, wv (execAll tail u).mem (P 0) k = upd (wv u.mem (P 0)) (i + nP) (u.regs 12).toNat k :=
      fun k hk => by
        rw [hv, wv_keep (memEq_write32 _ _ _) (by mp_fp), hm']
        exact wv_write _ _ _ (by omega) (by omega) k hk
    refine ⟨show (Out P m1 (i + 1) _ ∧ _) from ⟨⟨Fr.step L hf hm (by mp_fp)
      (by mp_fp) (E.reg 13 (by decide) (by decide)),
      by rw [hv, M0Crypto.Armv6M.read32_write32_same], by rw [wsum_congr hk]; exact mp_mul_row he hi (hz _ (by omega) (by omega)),
      fun k h1 h2 => by rw [hk k h2, Ed25519Words.upd_ne _ _ (by omega)]; exact hz k (by omega) h2⟩, ?_⟩,
      fun c hc => nomatch hc⟩
    rw [RoutineBranch.cond_ne, E.z _ rfl]
    simp only [tailE, rowS, spA, cw, SBool.denote, SMem.denote, SExpr.denote, Sym.awc_not_true, h11, hf.sp, ← hm', r1,
      rn, ← BitVec.ofNat_add]
    exact cmp_ne hi

/-- `Fr` at `u.setReg 15 v`, in the form `simp [State.setReg]` leaves. -/
theorem Fr.pc_iff {u : State} {v : Word} :
    Fr P m1 { u with regs := fun i => if i = 15 then v else u.regs i } ↔ Fr P m1 u := by
  constructor <;> intro h <;> exact ⟨h.mem, by simpa [State.setReg] using h.sp, h.sd, h.sa, h.sb, h.sn⟩

/-- The decided layout checks of a build. -/
def mpOk (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Bool :=
  mpAt O B && seqAt B (oE O) post && segsOk (B := B) cs (oP O) D D top &&
  (segsOk (B := B) cs (oH O) D D row &&
    loopOk (B := B) cs (oH O) (oH O + segsSize row) D D (brImm8 (oH O + segsSize row) (oH O))) &&
  decide (oE O + seqSize post ≤ BS)

/-- The first failing check of `mpOk`, by name; `none` exactly when it holds. -/
def mpFailure (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] : Option String :=
  match RoutineDiagnose.piecesAtFailure B O (pieces O) with
  | some (k, off, _, why) => some s!"layout: piece {k} at byte {off}: {why}"
  | none => match segsFailure (B := B) cs (oP O) D D top with
    | some w => some s!"top: {w}"
    | none => match segsFailure (B := B) cs (oH O) D D row with
      | some w => some s!"row: {w}"
      | none => RoutineDiagnose.firstFalse
        [("post not at its offset", seqAt B (oE O) post),
         ("row loop branch (loopOk)", loopOk (B := B) cs (oH O) (oH O + segsSize row) D D (brImm8 (oH O + segsSize row) (oH O))),
         ("the function ends past the artifact", decide (oE O + seqSize post ≤ BS))]

theorem mpFailure_eq_none (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS] :
    mpFailure B BS = none ↔ mpOk B BS = true := by
  have h1 := RoutineDiagnose.piecesAtFailure_eq_none B O (pieces O)
  have h2 := segsFailure_eq_none (B := B) cs (oP O) D D top
  have h3 := segsFailure_eq_none (B := B) cs (oH O) D D row
  unfold mpFailure mpOk mpAt
  rcases e1 : RoutineDiagnose.piecesAtFailure B O (pieces O) with _ | ⟨_, _, _, _⟩ <;>
    rcases e2 : segsFailure (B := B) cs (oP O) D D top with _ | _ <;>
    rcases e3 : segsFailure (B := B) cs (oH O) D D row with _ | _ <;>
    simp_all [RoutineDiagnose.firstFalse_eq_none, and_assoc]

noncomputable def mp_te (hok : mpOk B BS = true) : mpR.TE mpPub mpE := by
  simp only [mpOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hL, hpo⟩, hT⟩, hR⟩, hbs⟩ := hok
  obtain ⟨hen, hL⟩ := piecesAt_cons hL
  refine frame_te (mask := 0) (k := FRAME / 4) (epi := oE O) (spP := fun P => P 4) (Ψ := mpTr)
    (Wd := fun _ P => Has [⟨P 0, 8 * nP⟩]) (by decide) hen hpo (by decide +kernel)
    ⟨by decide, by decide, Nat.le_trans (by decide +kernel) hbs, Nat.le_trans (by decide +kernel) hbs, by decide,
      by decide⟩ (fun _ _ => rfl) (fun base s e F t tpc t13 tr hm hc => ?_)
    (fun _ _ => by repeat (first | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_rep | apply segsTr_uniq | intro))
    (fun _ _ => by repeat (first | exact ⟨_, rfl⟩ | apply ex_cat | apply ex_segsTr | apply ex_rep | intro))
    (fun _ _ y ⟨r, hr, h⟩ => ⟨r, by simp only [List.mem_singleton] at hr; simp [hr], h⟩)
    (fun b P sp0 n U hroom hn hF hR => by
      rw [show 4 * nSaved 0 + 4 * (FRAME / 4) = D by decide]; exact body_gp b hroom hn hF fun y h hb => .inl (hR y h hb))
  generalize hP : mpPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 2 = P 2 ∧ s.regs 3 = P 3 ∧ s.regs 13 = P 4 := by
    subst hP; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨q0, q1, q2, q3, q4⟩ := q
  have L : Lay P := by
    obtain ⟨hn0, a0, a1, a2, dA, dB⟩ := e.pre
    have hsW := e.sepWr; have hsR := e.sepRd; have hroom := e.room; have hsp4 := e.sp4
    simp only [mpR, Routine.win, D, FRAME, q0, q1, q2, q3, q4] at hsW hsR hroom hsp4 hn0 a0 a1 a2 dA dB
    fp_simp at hsW hsR dA dB
    exact ⟨hn0, ⟨hroom, hsp4⟩, ⟨a0, a1, a2⟩, by omega, by omega, by omega, by simp only [D, FRAME]; omega,
      by simp only [D, FRAME]; omega, by simp only [D, FRAME]; omega⟩
  lay_tac L
  have hW : lowWin mpR 0 s :: mpR.wr s = WcP P := by subst hP; rfl
  rw [hW, q4] at F
  rw [hW, show mpR.RdP base s = Has (RcP P base) by subst hP; rfl, show mpR.SpP s = InStackWindow (P 4) D by rw [← q4]; rfl]
  have t13' : t.regs 13 = P 4 - BitVec.ofNat 32 D := by rw [t13, q4]; rfl
  trefine ReachFT.segs (d := D) F _ top (oP O) (JT P t.mem) (nT P) (vsT P) hL hT
    (fun k i u v h => by
      rcases k with _ | _ | _ | k <;> rcases i with _ | i <;> simpa [JT, ZI, Out, Zs, Fr.pc_iff, State.setReg] using h)
    (fun k sg hk => by seg_cases top k hk <;> simp [nT] <;> omega)
    (fun k sg i u hk hi h => top_side L k sg i u hk hi h) (top_step L)
    (fun k sg u hk h => by seg_cases top k hk <;> exact h) (fun t' hp hJ h13 hc' hl => ?_) t tpc
    ⟨t13', rfl, (tr 0 (by decide) (by decide)).trans q0, (tr 1 (by decide) (by decide)).trans q1,
      (tr 2 (by decide) (by decide)).trans q2, (tr 3 (by decide) (by decide)).trans q3⟩ t13' hc
  trefine ReachFT.segLoop (d := D) F [.seq post] row 1 (oH O) nP (Out P t.mem) (JR P t.mem) (nR P) (vsR P) hl
    (by rw [Bool.and_eq_true]; exact hR)
    (fun j u v h => by simpa [Out, Zs, Fr.pc_iff, State.setReg] using h)
    (fun j k i u v h => by
      rcases k with _ | _ | _ | k <;> rcases i with _ | i <;>
        simpa [JR, II, Out, Zs, Fr.pc_iff, cond_pc, State.setReg] using h)
    (fun j u _ h => h) (fun j k sg _ hk => by seg_cases row k hk <;> simp [nR] <;> omega)
    (fun j k sg i u hj hk hi h => row_side L hj k sg i u hk hi h) (fun j k sg i u hj => row_step L hj k sg i u)
    (fun j k sg u _ hk h => by seg_cases row k hk <;> exact h) (fun j u _ h => h)
    (fun u hp hI h13 _ _ => ReachT.done ⟨hp, by rw [h13, t13'], fun r h4 h11 _ hr =>
      absurd (Ed25519Routines.mem_hiRegs h4 h11) hr, ?_⟩) t' L.n0 hp hJ h13 hc'
  · show wsum (wv u.mem (s.regs 0)) (2 * (s.regs 3).toNat) =
      wsum (wv s.mem (s.regs 1)) (s.regs 3).toNat * wsum (wv s.mem (s.regs 2)) (s.regs 3).toNat
    rw [q0, q1, q2, q3, hI.2.2.1]
    simp only [saved, show nSaved 0 = 1 from rfl, q4] at hm
    rw [wsum_congr (fun k hk => wv_keep hm (by mp_fp)), wsum_congr (n := nP) (fun k hk => wv_keep hm (by mp_fp))]
end

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_mp_mul` in each build**, with its effect. -/
noncomputable def mp_mul_te (b : Build) : letI := b.codeBytes; mpR.TE mpPub mpE :=
  letI := b.codeBytes
  have hL : mpAt O b.bytes = true := by cases b; exact compact_at; exact fast_at
  have h : @mpOk b.bytes _ b.codeBytes = true := by
    simp only [mpOk, hL, Bool.true_and]; cases b <;> decide +kernel
  @mp_te _ _ b.codeBytes h

open M0Crypto.Release.Ed25519 (Build) in
theorem mp_mul_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => mpR) mpPub :=
  letI := b.codeBytes; ⟨(mp_mul_te b).T, fun _ => (mp_mul_te b).spec⟩

end M0Crypto.Release.Ed25519MpMul
