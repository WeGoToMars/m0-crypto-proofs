import M0Crypto.Release.Ed25519Lookup
import M0Crypto.Release.Ed25519GeField
import M0Crypto.Release.Ed25519ShaUpdate
import M0Crypto.Release.Ed25519ScReduceProg

set_option linter.unusedSimpArgs false

/-!
# `m0c_ge_lookup` with its effect

`lookE` is `m0c_ge_lookup`'s contract for every digit `d = r2`: word `n` of the selected entry is
the OR over the eight entries of their word `n` under the digit's masks (`gE`), with the identity
flag in words 0 and 8; the sign of `d` swaps the first two elements and negates the third. For
`-8 ≤ d ≤ 8` that is entry `|d|` (`gE_ent`). `look_te` is its call lemma with the byte effect of
its trace: it reads the row and writes the 128 bytes at `r0`. The run is `lookup_tspec`'s with
segments (`Seg`) for the blocks and the effect callees `fe_sub` and `cmov`. `lookAd` is the
adapter of the callee `lookS`, whose public values are `r0`, `r1` and `sp`.
-/

namespace M0Crypto.Release.Ed25519LookupTE

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Sym
open M0Crypto.Artifacts
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Release.Routine
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519WordLoop (wordR wordPub sel sel_zero sel_ones)
open M0Crypto.Release.Ed25519Lookup

/-! ## The contract for every digit -/

/-- The mask of entry `k` and the identity flag of the digit `d`. -/
def mW (k : Nat) (d : Word) : Word := (maskS k (.const d)).denote st0
def zW (d : Word) : Word := (zS (.const d)).denote st0

/-- Word `n` of the OR of the first `K` entries of the row words `w` under the masks of `d`. -/
def orV (w : Nat → Word) (d : Word) (n : Nat) : Nat → Word
  | 0 => 0
  | k + 1 => orV w d n k ||| (w (24 * k + n) &&& mW (k + 1) d)

/-- Word `n` of the selected entry. -/
def gE (w : Nat → Word) (d : Word) (n : Nat) : Word :=
  if n = 0 ∨ n = 8 then orV w d n 8 ||| zW d else orV w d n 8

/-- The number of the eight words `f`. -/
def wv (f : Nat → Word) : Nat := ((List.range 8).map fun i => (f i).toNat * 2 ^ (32 * i)).sum

/-- The words of the row at `a`. -/
def rw (m : Mem) (a : Word) (n : Nat) : Word := read32 m (a + BitVec.ofNat 32 (4 * n))

/-- The selected words `n` and `n + 8` (`n < 8`) in their order for the sign of `d`. -/
def gS (w : Nat → Word) (d : Word) (n : Nat) : Word := gE w d (if d.msb then n + 8 else n)
def gS' (w : Nat → Word) (d : Word) (n : Nat) : Word := gE w d (if d.msb then n else n + 8)
/-- The third element, negated for a negative `d`. -/
def gT (w : Nat → Word) (d : Word) : Int :=
  if d.msb then -(wv fun i => gE w d (16 + i) : Int) else (wv fun i => gE w d (16 + i) : Int)

/-- **`m0c_ge_lookup`** for every digit `r2`: `out = r0` (32 words, the last 8 scratch) receives
the entry `gE` of the row `r1` for `r2`, swapped and negated by its sign. -/
def lookE (o : Nat) (cs : List (Nat × Nat)) : Routine where
  entry := o
  code := cs
  stack := 64
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧
    Sep [⟨s.regs 0, 128⟩] [⟨s.regs 1, 768⟩]
  wr := fun s => [⟨s.regs 0, 128⟩]
  rd := fun s => [⟨s.regs 1, 768⟩, ⟨s.regs 0, 128⟩]
  Post := fun s m _ => (∀ i < 8,
      read32 m (s.regs 0 + BitVec.ofNat 32 (4 * i)) = gS (rw s.mem (s.regs 1)) (s.regs 2) i ∧
      read32 m (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) = gS' (rw s.mem (s.regs 1)) (s.regs 2) i) ∧
    ModP (feVal m (s.regs 0 + 64#32)) (gT (rw s.mem (s.regs 1)) (s.regs 2))
  clob := hiRegs

/-! ## Digit values -/

theorem sgn_val (d : Word) : (sgnS (.const d)).denote st0 = if d.msb then BitVec.allOnes 32 else 0 := by
  have h : d >>> 31 = if d.msb then 1#32 else 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.msb_eq_decide]
    have := d.isLt
    split <;> simp_all <;> omega
  simp only [sgnS, rsbS, kS, SExpr.denote, h]
  split <;> decide

theorem orV_congr {w w' : Nat → Word} {d : Word} {n : Nat} (h : ∀ k < 8, w (24 * k + n) = w' (24 * k + n)) :
    ∀ K ≤ 8, orV w d n K = orV w' d n K
  | 0, _ => rfl
  | K + 1, hK => by simp only [orV]; rw [orV_congr h K (by omega), h K (by omega)]

theorem gE_congr {w w' : Nat → Word} {d : Word} {n : Nat} (h : ∀ k < 8, w (24 * k + n) = w' (24 * k + n)) :
    gE w d n = gE w' d n := by
  simp only [gE, orV_congr h 8 (Nat.le_refl _)]

theorem wv_congr {f g : Nat → Word} (h : ∀ i < 8, f i = g i) : wv f = wv g := by
  unfold wv; congr 1; exact List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)]

theorem feVal_wv (m : Mem) (a : Word) : feVal m a = wv fun i => read32 m (a + BitVec.ofNat 32 (4 * i)) := rfl

/-- **The OR of a block's word `i`** at pass `j`: word `4 j + i` of the entry. -/
theorem orS_val {u : State} {d row : Word} {j i : Nat}
    (hm : ∀ k < 8, (ldS (oM + 4 * k)).denote u = mW (k + 1) d)
    (hrow : (blkS oRow).denote u = row + BitVec.ofNat 32 (16 * j)) :
    ∀ K ≤ 8, (orS i K).denote u = orV (rw u.mem row) d (4 * j + i) K
  | 0, _ => rfl
  | K + 1, hK => by
    simp only [orS, orV, SExpr.denote]
    rw [orS_val hm hrow K (by omega), hm K (by omega)]
    simp only [wS, kS, SExpr.denote, SMem.denote, hrow, rw]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * j + (96 * K + 4 * i) = 4 * (24 * K + (4 * j + i)) by omega]

/-! ## Entries for `-8 ≤ d ≤ 8` -/

theorem orV_ent {w : Nat → Word} {d : Word} (hd : (d + 8#32).toNat ≤ 16) (n : Nat) :
    ∀ K ≤ 8, orV w d n K = if 1 ≤ dIdx d ∧ dIdx d ≤ K then w (24 * (dIdx d - 1) + n) else 0
  | 0, _ => by simp [orV]; omega
  | K + 1, hK => by
    obtain ⟨m, hm, rfl⟩ := digit_of hd
    have e := (digit_facts m hm).2.2 K (by omega)
    simp only [orV, mW]
    rw [orV_ent hd n K (by omega), e]
    generalize dIdx (BitVec.ofNat 32 m - 8#32) = x
    by_cases h : x = K + 1
    · subst h
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(1 ≤ K + 1 ∧ K + 1 ≤ K) by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true (show 1 ≤ K + 1 ∧ K + 1 ≤ K + 1 by omega)),
        BitVec.and_allOnes, Nat.add_sub_cancel]; simp
    · have h1 : (1 ≤ x ∧ x ≤ K + 1) ↔ (1 ≤ x ∧ x ≤ K) := by omega
      simp only [h, h1, ite_false]; simp

/-- **For `-8 ≤ d ≤ 8`** the selected word `n < 24` is word `n` of entry `|d|` of the row at `row`. -/
theorem gE_ent {m : Mem} {row d : Word} (hd : (d + 8#32).toNat ≤ 16) (n : Nat) :
    gE (rw m row) d n = ent m row (dIdx d) n := by
  have dg := digit_exit hd
  have hz : zW d = if dIdx d = 0 then 1#32 else 0#32 := dg.1
  simp only [gE, orV_ent hd n 8 (Nat.le_refl _), hz, ent, rw]
  by_cases h0 : dIdx d = 0
  · simp only [h0]; split <;> simp
  · simp only [h0, show 1 ≤ dIdx d ∧ dIdx d ≤ 8 from ⟨by omega, dg.2.2⟩, and_self, ↓reduceIte,
      BitVec.or_zero, ite_self]
    rw [show 4 * (24 * (dIdx d - 1) + n) = 96 * (dIdx d - 1) + 4 * n by omega]

theorem msb_neg {d : Word} (hd : (d + 8#32).toNat ≤ 16) : d.msb = dNeg d := by
  obtain ⟨n, hn, rfl⟩ := digit_of hd
  revert n; decide +kernel

/-! ## The code -/

abbrev O : Nat := Ed25519Compact.ge_lookup

def r13k (n : Nat) : SExpr := .add (.reg0 13) (kS n)
def r0k (n : Nat) : SExpr := .add (.reg0 0) (kS n)

/-- The header writes the slots but the pad word at 20. -/
def sH : Seg := { g := sl 2 60, al := [(.reg0 13, 4)], wg := [(.reg0 13, 20), (r13k 24, 32)], As := [.reg0 13] }
/-- A block of the table pass. -/
def sP : Seg :=
  { g := sl 62 108, al := [(.reg0 13, 4), (blkS oRow, 4), (blkS oOut, 4)], wg := [(blkS oOut, 16)],
    rg := [(.reg0 13, 16), (r13k 24, 32), (blkS oRow, 688)], As := [.reg0 13, blkS oRow, blkS oOut] }
def sT : Seg := { g := sl 170 4, al := [(.reg0 13, 4)], wg := [(r13k 12, 4)], rg := [(r13k 12, 4)], As := [.reg0 13] }
def sF1 : Seg :=
  { g := sl 176 5, al := [(.reg0 13, 4), (ldS oOut, 4)], wg := [(ldS oOut, 4)],
    rg := [(.reg0 13, 4), (r13k 16, 4), (ldS oOut, 4)], As := [.reg0 13, ldS oOut] }
def sF2 : Seg := { g := sl 181 3, al := [(.reg0 0, 4)], wg := [(r0k 32, 4)], rg := [(r0k 32, 4)], As := [.reg0 0] }
def sF3 : Seg := { g := sl 184 2, al := [(.reg0 13, 4)], rg := [(r13k 8, 4)], As := [.reg0 13] }
def sS : Seg :=
  { g := sl 186 11, al := [(.reg0 0, 4)], wg := [(.reg0 0, 4), (r0k 32, 4)], rg := [(.reg0 0, 4), (r0k 32, 4)],
    As := [.reg0 0] }
def sN : Seg := { g := sl 198 2, al := [(.reg0 13, 4)], rg := [(.reg0 13, 4)], As := [.reg0 13] }
def sSub : Seg := { g := sl 201 3, al := [(.reg0 13, 4)], rg := [(.reg0 13, 4)], As := [.reg0 13] }
def sCm : Seg := { g := sl 205 6, al := [(.reg0 13, 4)], rg := [(.reg0 13, 4), (r13k 8, 4)], As := [.reg0 13] }

/-- The callees `m0c_fe_sub` and `m0c_cmov`. -/
abbrev subR : Routine := Ed25519GeField.fR Ed25519Compact.fe_sub Field25519AddSub.feSubBody (· - ·)
abbrev cmvR : Routine := wordR Ed25519Compact.cmov
  (seqSize (Ed25519WordLoop.wloop [] Ed25519WordLoop.cmovBody 0xf3)) 2 true true (fun _ => True) sel [4, 5, 6, 7]

def segAt (a : Nat) (s : Seg) : Bool :=
  sglueOk lookupCs s.g (O + off a) 60 64 s.al s.wg s.rg && traceOkE s.g s.As
def segL : List (Nat × Seg) :=
  [(2, sH), (62, sP), (170, sT), (176, sF1), (181, sF2), (184, sF3), (186, sS), (198, sN)]
theorem segs_ok : segL.all (fun p => segAt p.1 p.2) = true := by decide +kernel
theorem segOk (i a : Nat) (s : Seg) (hm : segL[i]? = some (a, s) := by rfl) : segAt a s = true :=
  List.all_eq_true.mp segs_ok _ (List.mem_of_getElem? hm)

section ok
variable (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS]

/-- The decided checks of a build. -/
structure Ok : Prop where
  code : seqAt B O code = true
  lk : lkOk lookupCs O Ed25519Compact.fe_sub (seqSize (Ed25519FeAddSub.wrap Field25519AddSub.feSubBody))
    Ed25519Compact.cmov (seqSize (Ed25519WordLoop.wloop [] Ed25519WordLoop.cmovBody 0xf3)) Ed25519Compact.ed_zero = true
  sub : siteOkE (BS := BS) lookupCs subR sSub (O + off 201) 60 64 (blOf 204) = true
  cm : siteOkE (BS := BS) lookupCs cmvR sCm (O + off 205) 60 64 (blOf 211) = true
end ok

open M0Crypto.Release.Ed25519 (Build)

theorem ok_b (b : Build) : @Ok _ _ b.codeBytes :=
  @Ok.mk _ _ b.codeBytes (code_at b) (lk_ok b) (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)

/-! ## The trace -/

section
variable (Ts Tc : Word → (Nat → Word) → List Event) (base : Word) (P : Nat → Word)

/-- The frame pointer. -/
def fpP : Word := P 2 - BitVec.ofNat 32 60
def bT (a : Nat) (s : Seg) (vs : List Word) : TrP := Tr.is (blockTrE s.g (base + BitVec.ofNat 32 (O + off a)) s.As vs)
/-- Pass `j` of the table: its block and the counter. -/
def pB (j : Nat) : TrP :=
  Tr.cat (bT base 62 sP [fpP P, P 1 + BitVec.ofNat 32 (16 * j), P 0 + BitVec.ofNat 32 (16 * j)])
    (Tr.cat (bT base 170 sT [fpP P]) (Tr.is []))
/-- Pass `j` of the swap. -/
def sB (j : Nat) : TrP := Tr.cat (bT base 186 sS [P 0 + BitVec.ofNat 32 (4 * j)]) (Tr.is [])
/-- The public values of the calls of `m0c_fe_sub` and `m0c_cmov`. -/
def pS : Nat → Word := pubOf [P 0 + 96#32, base + BitVec.ofNat 32 Ed25519Compact.ed_zero, P 0 + 64#32, fpP P]
def pC : Nat → Word := pubOf [P 0 + 64#32, P 0 + 96#32, 8#32, fpP P]
/-- After the swap: `-2dxy` and its selection by the sign. -/
def tlT : TrP :=
  Tr.cat (bT base 198 sN [fpP P]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + off 200), .ldrLit 1 7,
      [⟨.read, base + BitVec.ofNat 32 (litOff (O + off 200) 7), 4⟩]⟩])
    (Tr.cat (bT base 201 sSub [fpP P]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + off 201 + seqSize sSub.g),
      .bl (blOf 204), []⟩]) (Tr.cat (Tr.is (Ts base (pS base P)))
    (Tr.cat (bT base 205 sCm [fpP P]) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + off 205 + seqSize sCm.g),
      .bl (blOf 211), []⟩]) (Tr.cat (Tr.is (Tc base (pC P))) (Tr.is []))))))))
/-- From the block loop's exit: the identity flag, the swap and the tail. -/
def exT : TrP :=
  Tr.cat (bT base 176 sF1 [fpP P, P 0]) (Tr.cat (bT base 181 sF2 [P 0]) (Tr.cat (bT base 184 sF3 [fpP P])
    (Tr.rep (fun j => Tr.cat (sB base P j) (Tr.is [⟨base + BitVec.ofNat 32 (O + off 197), .bcond 1 (bcOf 197), []⟩]))
      0 8 (tlT Ts Tc base P))))
/-- **The body's trace**: a function of `base`, `r0`, `r1` and `sp`. -/
def lkTr : TrP :=
  Tr.cat (bT base 2 sH [fpP P])
    (Tr.rep (passTr base (pB base P) 6 (O + off 174) 0 (bcOf 174) (bOf 175)) 0 6 (exT Ts Tc base P))
end


/-! ## The run -/

/-- `m0c_ge_lookup` in the code it executes. -/
abbrev lkR : Routine := lookE O lookupCs

/-- The block loop's invariant before pass `j`: the counter slot holds `j`, and the output holds
the first `4 j` words of the OR of the entries. -/
def Jg (sp out row d : Word) (m1 m0 : Mem) (j : Nat) (u : State) : Prop :=
  MemEq [⟨sp + BitVec.ofNat 32 oBlk, 4⟩, ⟨out, 16 * j⟩] m1 u.mem ∧ read32 u.mem (sp + BitVec.ofNat 32 oBlk) = BitVec.ofNat 32 j ∧
  ∀ i < 4 * j, read32 u.mem (out + BitVec.ofNat 32 (4 * i)) = orV (rw m0 row) d i 8

/-- The end of the body. -/
def Qe (base : Word) (s t u : State) : Prop :=
  u.pc = base + BitVec.ofNat 32 (O + off 212) ∧ u.regs 13 = t.regs 13 ∧
  (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves 0 r → r ∉ lkR.clob → u.regs r = s.regs r) ∧ lkR.Post s u.mem (u.regs 0)

section
attribute [local irreducible] sl code
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {Ts Tc : Word → (Nat → Word) → List Event}

/-- The run's `ReachFT` from the entry `s`. -/
abbrev RL (base : Word) (s u : State) (Q : State → Prop) (Ψ : TrP) : Prop :=
  ReachFT base (lkR.PcP base) (lkR.RdP base s) (Has (⟨s.regs 13 - BitVec.ofNat 32 64, 60⟩ :: lkR.wr s)) (lkR.SpP s) u Q Ψ

/-- The context of the run: the checks, the entry and its frame, the public values `P`, and the
state `t` after the frame. -/
structure Cx (base : Word) (s t : State) (P : Nat → Word) : Prop where
  ok : Ok B BS
  e : lkR.Entry base s
  F : Caller base (s.regs 13) lkR.stack (⟨s.regs 13 - BitVec.ofNat 32 64, 60⟩ :: lkR.wr s)
  q0 : s.regs 0 = P 0
  q1 : s.regs 1 = P 1
  q13 : s.regs 13 = P 2
  s13 : (s.regs 13).toNat < 2 ^ 32
  t13 : t.regs 13 = s.regs 13 - BitVec.ofNat 32 60
  t0 : t.regs 0 = s.regs 0
  t1 : t.regs 1 = s.regs 1
  t2 : t.regs 2 = s.regs 2
  hm : MemEq [⟨s.regs 13 - BitVec.ofNat 32 4, 4⟩] s.mem t.mem

/-- The layout facts of the entry. -/
macro "lk_lay" C:term : tactic => `(tactic| (
  obtain ⟨h0a, h1a, hdj⟩ := ($C).e.pre
  have hroom := ($C).e.room; have hsp4 := ($C).e.sp4; have := ($C).s13
  have hsC := ($C).e.sepCode; have hsW := ($C).e.sepWr; have hsR := ($C).e.sepRd
  simp only [lookE, Routine.win, codeR] at hroom hsC hsW hsR
  fp_simp at hsC hsW hsR hdj))

theorem at1 (ok : Ok B BS) {a : Nat} {i : Instr} (h : sl a 1 = [i]) : instrAt B (O + off a) = some i :=
  instrAt_of_seqAt (h ▸ seqAt_sl ok.code _ 1)

theorem nx {u : State} {a n : Nat} {base : Word} (c : Nat) (hc : a + n = c)
    (h : u.pc = base + BitVec.ofNat 32 (O + off a + seqSize (sl a n))) : u.pc = base + BitVec.ofNat 32 (O + off c) := by
  rw [h, Nat.add_assoc, off_add, hc]

/-- A header slot but `BLK`, read through a frame that keeps it. -/
theorem slot_rd {t u : State} {s : State} (ht : t.regs 13 = s.regs 13 - BitVec.ofNat 32 60) {j k : Nat} {spec : SExpr}
    (hIm : MemEq [⟨s.regs 13 - 60#32 + BitVec.ofNat 32 oBlk, 4⟩, ⟨s.regs 0, 16 * j⟩] (execAll (sl 2 60) t).mem u.mem)
    (hk4 : k % 4 = 0) (hkB : k ≠ oBlk) (hk : k + 4 ≤ 56) (hj : j ≤ 6) (hd : (s.regs 0).toNat + 128 ≤ 2 ^ 32)
    (hsep : Sep [⟨s.regs 0, 128⟩] [⟨s.regs 13 - 64#32, 64⟩]) (h13 : 64 ≤ (s.regs 13).toNat)
    (h : rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS k))) = norm spec) :
    read32 u.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 k) = spec.denote t := by
  have hB : oBlk = 12 := rfl
  have := (s.regs 13).isLt
  fp_simp at hsep
  keep_simp; rw [← ht]; exact sym_rd hdr_ok.1 _ spec h t

/-- **Pass `j` of the block loop.** -/
theorem pass_run {base : Word} {s t : State} {P : Nat → Word} (C : Cx (B := B) base s t P) {j : Nat} {u : State}
    (hj : j < 6) (hpu : u.pc = base + BitVec.ofNat 32 (O + off 62))
    (hI : Jg (s.regs 13 - 60#32) (s.regs 0) (s.regs 1) (s.regs 2) (execAll (sl 2 60) t).mem t.mem j u)
    (h13u : u.regs 13 = s.regs 13 - BitVec.ofNat 32 60) (hcu : CodeAt u.mem base B)
    (h1 : MemEq [⟨s.regs 13 - BitVec.ofNat 32 60, 20⟩, ⟨s.regs 13 - BitVec.ofNat 32 60 + BitVec.ofNat 32 24, 32⟩]
      t.mem (execAll (sl 2 60) t).mem) :
    RL base s u (fun u' => u'.pc = base + BitVec.ofNat 32 (O + off 174) ∧ u'.regs 13 = s.regs 13 - BitVec.ofNat 32 60 ∧
      CodeAt u'.mem base B ∧ Jg (s.regs 13 - 60#32) (s.regs 0) (s.regs 1) (s.regs 2) (execAll (sl 2 60) t).mem t.mem
        (j + 1) u' ∧ condPassed 0 u' = decide (j + 1 = 6)) (pB base P j) := by
  lk_lay C
  have F := C.F; have hcode := C.ok.code; have hm := C.hm
  have hB12 : oBlk = 12 := rfl
  obtain ⟨hIm, hIc, hIw⟩ := hI
  unfold pB
  have sv' : ∀ k spec, rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS k))) = norm spec →
      k + 4 ≤ 56 → k % 4 = 0 → k ≠ oBlk → read32 u.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 k) = spec.denote t :=
    fun k spec h hk hk4 hkB => slot_rd C.t13 hIm hk4 hkB hk (by omega) (by fp_tac) (by fp_tac) (by fp_tac) h
  have hrow : (blkS oRow).denote u = s.regs 1 + BitVec.ofNat 32 (16 * j) := by
    simp only [blkS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13u]
    rw [sv' oRow (.reg0 1) hdr_ok.2.2.1 (by decide) (by decide) (by decide), hIc, shl4]
    simp only [SExpr.denote, C.t1]
  have hout : (blkS oOut).denote u = s.regs 0 + BitVec.ofNat 32 (16 * j) := by
    simp only [blkS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13u]
    rw [sv' oOut (.reg0 0) hdr_ok.2.1 (by decide) (by decide) (by decide), hIc, shl4]
    simp only [SExpr.denote, C.t0]
  obtain ⟨tP, fC2, zC2, mC2⟩ := pass_ok
  refine ReachFT.seg1 F sP (seqAt_sl hcode 62 108) (segOk 1 62 sP) hpu h13u hcu
    (by glue_tac [sP, r13k, kS, h13u, hrow, hout, lookE])
    (by simp only [sP, List.map, hrow, hout]; simp [SExpr.denote, h13u, C.q0, C.q1, C.q13, fpP]) fun hpA h13A hcA hmA => ?_
  dsimp only [sP] at hpA h13A hcA hmA ⊢
  refine ReachFT.seg1 F sT (seqAt_sl hcode 170 4) (segOk 2 170 sT) (nx 170 rfl hpA) h13A hcA
    (by glue_tac [sT, r13k, kS, h13A, lookE]) (by simp [sT, SExpr.denote, h13A, C.q13, fpP]) fun hpD h13D hcD hmD => ?_
  dsimp only [sT] at hpD h13D hcD hmD ⊢
  simp only [sregions, List.map, SExpr.denote, r13k, kS, hout, h13A] at hmA hmD
  have hcnt : read32 (execAll (sl 62 108) u).mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oBlk) =
      BitVec.ofNat 32 j := by keep_simp; exact hIc
  refine ReachT.done ⟨nx 174 rfl hpD, h13D, hcD, ⟨((hIm.trans hmA).trans hmD).mono
    (by simp only [List.cons_append, List.nil_append]; fp_tac), ?_,
    fun i hi => ?_⟩, ?_⟩
  · have m := sym_rd fC2 _ incS mC2 (execAll (sl 62 108) u)
    simp only [incS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, h13A, hcnt] at m
    rw [m, ← BitVec.ofNat_add]
  · keep_simp
    by_cases hij : i < 4 * j
    · keep_simp; exact hIw i hij
    obtain ⟨i', rfl⟩ : ∃ i', i = 4 * j + i' := ⟨i - 4 * j, by omega⟩
    have hmk : ∀ k < 8, (ldS (oM + 4 * k)).denote u = mW (k + 1) (s.regs 2) :=
      fun k hk => by
        simp only [ldS, kS, SExpr.denote, SMem.denote, h13u]
        rw [sv' _ _ (hdr_ok.2.2.2.2.2.2 k hk) (by simp only [oM]; omega) (by simp only [oM]; omega)
          (by simp only [oM, oBlk]; omega), maskS_reg, C.t2]; rfl
    have w := sym_rd blk_ok.1 _ _ (blk_ok.2 i' (by omega)) u
    simp only [SExpr.denote, kS, hout, ofNat_add_assoc] at w
    rw [show 4 * (4 * j + i') = 16 * j + 4 * i' by omega, w, orS_val (i := i') hmk hrow 8 (Nat.le_refl _)]
    refine orV_congr (fun k hk => ?_) 8 (Nat.le_refl _)
    have : 4 * (24 * k + (4 * j + i')) + 4 ≤ 768 := by omega
    simp only [rw]; keep_simp
  · have z := sym_z fC2 _ zC2 (execAll (sl 62 108) u)
    simp only [subS, incS, ldS, kS, SExpr.denote, SMem.denote, SBool.denote, add_flags, sub_flags,
      h13A, hcnt] at z
    rw [show ∀ v : State, condPassed 0 v = v.z from fun _ => rfl, z]
    have : ∀ j < 6, (BitVec.ofNat 32 j + BitVec.ofNat 32 1 - BitVec.ofNat 32 6 == 0#32) =
      decide (j + 1 = 6) := by decide
    exact this j hj

set_option maxHeartbeats 500000 in
/-- **The tail** after the swap: `out + 96 = -(out + 64)` by `fe_sub`, then `cmov` of it into
`out + 64` under the sign mask, from the words of the swapped entry at `x`. -/
theorem tail_run {base : Word} {s t : State} {P : Nat → Word} (C : Cx (B := B) base s t P)
    (hS : subR.SpecT fun b s => Tr.is (Ts b (Ed25519Leaf.leafPub [0, 1, 2] b s)))
    (hC : cmvR.SpecT fun b s => Tr.is (Tc b (wordPub 2 b s))) {x : State}
    (hpx : x.pc = base + BitVec.ofNat 32 (O + off 197 + 2)) (h13x : x.regs 13 = s.regs 13 - BitVec.ofNat 32 60)
    (hcx : CodeAt x.mem base B)
    (hO : read32 x.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oOut) = s.regs 0)
    (hN : read32 x.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oNeg) = if (s.regs 2).msb then BitVec.allOnes 32 else 0)
    (hX : ∀ i < 8, read32 x.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) = gS (rw s.mem (s.regs 1)) (s.regs 2) i ∧
      read32 x.mem (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) = gS' (rw s.mem (s.regs 1)) (s.regs 2) i)
    (hF : feVal x.mem (s.regs 0 + 64#32) = wv fun i => gE (rw s.mem (s.regs 1)) (s.regs 2) (16 + i)) :
    RL base s x (Qe base s t) (tlT Ts Tc base P) := by
  lk_lay C
  have F := C.F; have hcode := C.ok.code; have hm := C.hm; have q0 := C.q0; have q13 := C.q13
  have hok := C.ok.lk
  simp only [lkOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho4, hcs, hBS, -, -, -, -, -, -, -, -, -, -, hlit, -, -, hZ, hZ4, hZ0, hZl⟩ := hok
  obtain ⟨κ, hκκ⟩ : ∃ κ, (if (s.regs 2).msb then BitVec.allOnes 32 else 0) = κ := ⟨_, rfl⟩
  rw [hκκ] at hN
  unfold tlT
  obtain ⟨fN, rN⟩ := neg_ok
  have e1 : off 198 = off 197 + 2 ∧ off 201 = off 200 + 2 ∧ off 212 = off 205 + seqSize (sl 205 6) + 4 := by
    decide +kernel
  have hpx' : x.pc = base + BitVec.ofNat 32 (O + off 198) := by rw [hpx, e1.1, Nat.add_assoc]
  refine ReachFT.seg1 F sN (seqAt_sl hcode 198 2) (segOk 7 198 sN) hpx' h13x hcx
    (by glue_tac [sN, h13x, lookE]) (by simp [sN, SExpr.denote, h13x, q13, fpP]) fun hp4 h134 hc4 hm4 => ?_
  dsimp only [sN] at hp4 h134 hc4 hm4 ⊢
  have lOx : (ldS oOut).denote x = s.regs 0 := by
    simp only [ldS, kS, SExpr.denote, SMem.denote, h13x]; exact hO
  have r04 := sym_reg fN _ _ rN x
  simp only [SExpr.denote, SBool.denote, kS, add_flags, lOx] at r04
  have i200 := at1 C.ok (a := 200) (i := .ldrLit 1 7) (by decide +kernel)
  refine ReachFT.lit F 1 7 i200 (nx 200 rfl hp4) (Hi.self _) h134 hc4 (by simp only [codeR]; fp_tac)
    (fun y hy hp5 _ h135 hc5 => ?_) hlit
  have hp5' : y.pc = base + BitVec.ofNat 32 (O + off 201) := by rw [hp5, e1.2.1, Nat.add_assoc]
  have i204 := at1 C.ok (a := 204) (i := .bl (blOf 204)) (by decide +kernel)
  rw [← (off_add 201 3 : off 201 + seqSize (sl 201 3) = off 204), ← Nat.add_assoc] at i204
  rw [← codeWord_drop] at hZl
  have hz1 : Frame.codeWord (litOff (O + off 200) 7) + (base + BitVec.ofNat 32 (O + off 200 + 2) + 4#32) =
      base + BitVec.ofNat 32 Ed25519Compact.ed_zero := by
    rw [← hZl, e1.2.1, ← Nat.add_assoc, BitVec.ofNat_add (O + off 200 + 2) 4]
    generalize Frame.codeWord _ = cw; generalize BitVec.ofNat 32 (O + off 200 + 2) = p; ac_rfl
  have y0 : y.regs 0 = s.regs 0 + 96#32 := by
    rw [hy, ← r04]; simp only [litState, State.setReg, M0Crypto.Proofs.toReg_1]; rfl
  have y1 : y.regs 1 + (y.pc + 4#32) = base + BitVec.ofNat 32 Ed25519Compact.ed_zero := by
    rw [hp5, ← hz1, hy]; rfl
  have ym : y.mem = (execAll (sl 198 2) x).mem := by rw [hy, litState_mem]
  clear hy
  obtain ⟨sF, sR0, sR1, sR2, sR13⟩ := sub_ok
  have a0 := sym_reg sF _ _ sR0 y; have a1 := sym_reg sF _ _ sR1 y
  have a2 := sym_reg sF _ _ sR2 y; have a13 := sym_reg sF _ _ sR13 y
  have xm : (execAll (sl 198 2) x).mem = x.mem := funext fun a =>
    execAll_memEq (wg := []) x fN (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
  simp only [ldS, kS, SExpr.denote, SMem.denote, h13x] at lOx
  simp only [SExpr.denote, SBool.denote, SMem.denote, ldS, kS, add_flags, y0, ym, xm, h135, lOx] at a0 a1 a2 a13
  rw [show y.regs 15 = y.pc from rfl, y1] at a1
  have sp4 := F.sp4; have b4 := F.b4; have c32 := F.code32
  -- `fe_sub`: `out + 96 = 0 - out + 64`
  refine ReachFT.siteE hS F sSub (seqAt_sl hcode 201 3) i204 C.ok.sub hp5' (Hi.self _) h135 hc5 ?ss
    (by simp [sSub, SExpr.denote, h135, q13, fpP]) ?sp ?sΦ (fun u5 p5 _ s5 c5 m5 _ q5 => ?_)
  case ss =>
    simp only [SiteSidesE, SGlueSides, atCall, Routine.win, subR, Ed25519GeField.fR, Ed25519Leaf.leafR, sSub,
      sregions, Ed25519FeCanon.rg0, Ed25519FeEq.ab,
      SExpr.denote, List.map, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
      blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13,
      h135, lookE, codeR, oOut, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, List.mem_cons,
      forall_eq_or_imp, forall_eq, and_true]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> (try exact fun _ h => absurd h List.not_mem_nil) <;> fp_tac
  case sp =>
    simp only [subR, Ed25519GeField.fR, Ed25519Leaf.leafR, atCall, sSub, blState_regs (base := base) _ _ _ 0,
      blState_regs (base := base) _ _ _ 1, blState_regs (base := base) _ _ _ 2, a0, a1, a2]
    refine ⟨?_, ?_, ?_⟩ <;> fp_tac
  case sΦ =>
    simp only [Ed25519Leaf.leafPub, List.cons_append, List.nil_append, List.map_cons, List.map_nil, atCall, sSub,
      blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
      blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13, pS, fpP, q0, q13]
  have ex5 : (execAll (sl 201 3) y).mem = y.mem := funext fun a =>
    execAll_memEq (wg := []) y sF (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
  simp only [sregions, List.map, List.nil_append, atCall, Routine.win, subR, Ed25519GeField.fR, Ed25519Leaf.leafR,
    sSub, Ed25519FeCanon.rg0, Ed25519FeEq.ab,
    SExpr.denote, blState_mem, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
    blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, a0, a1, a2, a13,
    ex5, ym, xm] at m5 q5
  have e2 : off 205 = off 201 + seqSize (sl 201 3) + 4 := by decide +kernel
  have p5' : u5.pc = base + BitVec.ofNat 32 (O + off 205) := by
    dsimp only [sSub] at p5; rw [p5, e2, ← Nat.add_assoc, ← Nat.add_assoc]
  have i211 := at1 C.ok (a := 211) (i := .bl (blOf 211)) (by decide +kernel)
  rw [← (off_add 205 6 : off 205 + seqSize (sl 205 6) = off 211), ← Nat.add_assoc] at i211
  have l5 : read32 u5.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oOut) = s.regs 0 := by
    rw [← hO]; simp only [oOut]; keep_simp
  have κ5 : read32 u5.mem (s.regs 13 - 60#32 + BitVec.ofNat 32 oNeg) = κ := by
    rw [← hN]; simp only [oNeg]; keep_simp
  obtain ⟨cF, cR0, cR1, cR2, cR3, cR13⟩ := cmv_ok
  have b0 := sym_reg cF _ _ cR0 u5; have b1 := sym_reg cF _ _ cR1 u5; have b2 := sym_reg cF _ _ cR2 u5
  have b3 := sym_reg cF _ _ cR3 u5; have b13 := sym_reg cF _ _ cR13 u5
  simp only [SExpr.denote, SBool.denote, SMem.denote, ldS, kS, add_flags, s5, l5, κ5, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd] at b0 b1 b2 b3 b13
  -- `cmov`: `out + 64` takes `out + 96` under the sign
  refine ReachFT.siteE hC F sCm (seqAt_sl hcode 205 6) i211 C.ok.cm p5' (Hi.self _) s5 c5 ?cs
    (by simp [sCm, SExpr.denote, s5, q13, fpP]) ?cp ?cΦ (fun u6 p6 _ s6 c6 m6 _ q6 => ?_)
  case cs =>
    simp only [SiteSidesE, SGlueSides, atCall, Routine.win, cmvR, wordR, sCm, sregions, r13k, kS, ite_true,
      SExpr.denote, List.map, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
      blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, b0, b1, b2, b13,
      s5, lookE, codeR, oOut, oNeg, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      List.cons_append, List.nil_append, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul,
      List.mem_cons, forall_eq_or_imp, forall_eq, and_true]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> (try exact fun _ h => absurd h List.not_mem_nil) <;> fp_tac
  case cp =>
    simp only [cmvR, wordR, atCall, sCm, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
      blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 3, b0, b1, b2, b3, EqOrDisj,
      forall_const, and_true, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
    refine ⟨by simp only [Ed25519WordLoop.WordsOk]; decide, ?_, ?_, Or.inr ?_⟩ <;> fp_tac
  case cΦ =>
    simp only [wordPub, atCall, sCm, blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
      blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 13, b0, b1, b2, b13, pC, fpP, q0, q13]
  have ex6 : (execAll (sl 205 6) u5).mem = u5.mem := funext fun a =>
    execAll_memEq (wg := []) u5 cF (by decide +kernel) a fun ⟨_, h, _⟩ => by simp [regions] at h
  simp only [sregions, List.map, List.nil_append, atCall, Routine.win, cmvR, wordR, sCm, blState_mem,
    blState_regs (base := base) _ _ _ 0, blState_regs (base := base) _ _ _ 1,
    blState_regs (base := base) _ _ _ 2, blState_regs (base := base) _ _ _ 3,
    blState_regs (base := base) _ _ _ 13, b0, b1, b2, b3, b13, ex6, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.reduceMul] at m6 q6
  dsimp only [sCm] at p6
  refine ReachT.done ⟨by rw [p6, e1.2.2, ← Nat.add_assoc, ← Nat.add_assoc], by rw [s6, C.t13],
    fun r h4 h11 _ hK => absurd (mem_hiRegs h4 h11) hK, ?_⟩
  simp only [lookE]
  refine ⟨fun i hi => ?_, ?_⟩
  · have k0 : read32 u6.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) =
        read32 x.mem (s.regs 0 + BitVec.ofNat 32 (4 * i)) := by keep_simp
    have k8 : read32 u6.mem (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) =
        read32 x.mem (s.regs 0 + BitVec.ofNat 32 (32 + 4 * i)) := by keep_simp
    rw [k0, k8]; exact hX i hi
  · have z0 : feVal x.mem (base + BitVec.ofNat 32 Ed25519Compact.ed_zero) = 0 := feVal_zeroes fun i hi => by
      rw [ofNat_add_assoc, Frame.read32_code hcx _ (by omega), codeWord_zero hZ0 hi]
    rcases Bool.eq_false_or_eq_true (s.regs 2).msb with hn | hn
    · have f6 : feVal u6.mem (s.regs 0 + 64#32) = feVal u5.mem (s.regs 0 + 96#32) :=
        feVal_congr fun i hi => by rw [q6 i hi, ← hκκ]; simp only [hn, ↓reduceIte, sel_ones]
      have q := q5; rw [z0, hF] at q
      simp only [gT, hn, ↓reduceIte, f6]; simpa only [Int.natCast_zero, Int.zero_sub] using q
    · have f6 : feVal u6.mem (s.regs 0 + 64#32) = feVal x.mem (s.regs 0 + 64#32) :=
        feVal_congr fun i hi => by
          rw [q6 i hi, ← hκκ]; simp only [hn, Bool.false_eq_true, ↓reduceIte, sel_zero]; keep_simp
      simp only [gT, hn, Bool.false_eq_true, ↓reduceIte, f6, hF]; rfl

/-- **From the block loop's exit**: the identity flag into words 0 and 8, the masked swap of the
first two elements, and the tail. -/
theorem exit_run {base : Word} {s t : State} {P : Nat → Word} (C : Cx (B := B) base s t P)
    (hS : subR.SpecT fun b s => Tr.is (Ts b (Ed25519Leaf.leafPub [0, 1, 2] b s)))
    (hC : cmvR.SpecT fun b s => Tr.is (Tc b (wordPub 2 b s))) {w : State}
    (hpw : w.pc = base + BitVec.ofNat 32 (O + off 176))
    (hJ : Jg (s.regs 13 - 60#32) (s.regs 0) (s.regs 1) (s.regs 2) (execAll (sl 2 60) t).mem t.mem 6 w)
    (h13w : w.regs 13 = s.regs 13 - BitVec.ofNat 32 60) (hcw : CodeAt w.mem base B) :
    RL base s w (Qe base s t) (exT Ts Tc base P) := by
  lk_lay C
  have F := C.F; have hcode := C.ok.code; have hm := C.hm; have q0 := C.q0; have q13 := C.q13
  have hL : loopOk lookupCs (O + off 186) (O + off 197) 60 64 (bcOf 197) = true := by
    have hok := C.ok.lk
    simp only [lkOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
    exact hok.2.2.2.2.1
  obtain ⟨hWm, -, hWw⟩ := hJ
  have ld : ∀ k spec, rdW (normMem (symExec (sl 2 60) SState.init).mem) (norm (.add (.reg0 13) (kS k))) =
      norm spec → k + 4 ≤ 56 → k % 4 = 0 → k ≠ oBlk → (ldS k).denote w = spec.denote t :=
    fun k spec h hk hk4 hkB => by
      simp only [ldS, kS, SExpr.denote, SMem.denote, h13w]
      exact slot_rd C.t13 hWm hk4 hkB hk (Nat.le_refl _) (by fp_tac) (by fp_tac) (by fp_tac) h
  have lO : (ldS oOut).denote w = s.regs 0 := by
    rw [ld _ _ hdr_ok.2.1 (by decide) (by decide) (by decide)]; exact C.t0
  obtain ⟨fF, tF, mF, rF0, rF1, fF2, mF2, fF3, rF3, rF7⟩ := fix_ok
  unfold exT
  refine ReachFT.seg1 F sF1 (seqAt_sl hcode 176 5) (segOk 3 176 sF1) hpw h13w hcw
    (by glue_tac [sF1, r13k, kS, h13w, lO, lookE]) (by simp only [sF1, List.map, lO]; simp [SExpr.denote, h13w, q0, q13, fpP])
    fun hp1 h131 hc1 hm1 => ?_
  dsimp only [sF1] at hp1 h131 hc1 hm1 ⊢
  have r01 := sym_reg fF _ _ rF0 w; rw [lO] at r01
  refine ReachFT.seg1 F sF2 (seqAt_sl hcode 181 3) (segOk 4 181 sF2) (nx 181 rfl hp1) h131 hc1
    (by glue_tac [sF2, r0k, kS, r01, lookE]) (by simp [sF2, SExpr.denote, r01, q0]) fun hp2 h132 hc2 hm2 => ?_
  dsimp only [sF2] at hp2 h132 hc2 hm2 ⊢
  refine ReachFT.seg1 F sF3 (seqAt_sl hcode 184 2) (segOk 5 184 sF3) (nx 184 rfl hp2) h132 hc2
    (by glue_tac [sF3, r13k, kS, h132, lookE]) (by simp [sF3, SExpr.denote, h132, q13, fpP]) fun hp3 h133 hc3 hm3 => ?_
  dsimp only [sF3] at hp3 h133 hc3 hm3 ⊢
  simp only [sregions, List.map, SExpr.denote, r0k, kS, lO, r01, BitVec.add_zero] at hm1 hm2 hm3
  have hκ : (sgnS (.reg0 2)).denote t = if (s.regs 2).msb then BitVec.allOnes 32 else 0 := by
    rw [show (sgnS (.reg0 2)).denote t = (sgnS (.const (t.regs 2))).denote st0 from rfl, C.t2, sgn_val]
  obtain ⟨κ, hκκ⟩ : ∃ κ, (if (s.regs 2).msb then BitVec.allOnes 32 else 0) = κ := ⟨_, rfl⟩
  rw [hκκ] at hκ
  have i197 := at1 C.ok (a := 197) (i := .bcond 1 (bcOf 197)) (by decide +kernel)
  refine ReachFT.loop (o := O + off 186) (ob := O + off 197) (d := 60) F 1 (bcOf 197) i197 8
    (SwI (s.regs 0) κ (execAll (sl 184 2) (execAll (sl 181 3) (execAll (sl 176 5) w))).mem) (fun _ _ _ h => SwI_setReg h)
    ?sbody ?sexit hL 0 _ (by omega) (nx 186 rfl hp3) ?s0 h133 hc3
  case s0 =>
    refine ⟨?_, ?_, ?_, MemEq.rfl' _ _, fun i _ => by simp only [Nat.not_lt_zero, ↓reduceIte, and_self]⟩
    · rw [execAll_regs_other (sl 184 2) _ _ (by decide) (by decide +kernel),
        execAll_regs_other (sl 181 3) _ _ (by decide) (by decide +kernel), r01]; simp
    · rw [sym_reg fF3 _ _ rF3, ← hκ, ← ld _ _ hdr_ok.2.2.2.1 (by decide) (by decide) (by decide)]
      simp only [ldS, kS, SExpr.denote, SMem.denote, h132, h13w, oNeg]; keep_simp
    · rw [sym_reg fF3 _ _ rF7]; rfl
  case sbody =>
    rintro j v hj hpv ⟨r0, r3, r7, hmv, hwv⟩ h13v hcv
    unfold sB
    obtain ⟨fS, m0S, m32S, r0S, r3S, r7S, zS'⟩ := swap_ok
    refine ReachFT.seg1 F sS (seqAt_sl hcode 186 11) (segOk 6 186 sS) hpv h13v hcv
      (by glue_tac [sS, r0k, kS, r0, lookE]) (by simp [sS, SExpr.denote, r0, q0]) fun hpe h13e hce hme => ?_
    dsimp only [sS] at hpe h13e hce hme ⊢
    simp only [sregions, List.map, SExpr.denote, r0k, kS, r0, BitVec.add_zero] at hme
    refine ReachT.done ⟨nx 197 rfl hpe, h13e, hce, ⟨?_, ?_, ?_, (hmv.trans hme).mono
      (by simp only [List.cons_append, List.nil_append]; fp_tac), fun i hi => ?_⟩, ?_⟩
    · rw [sym_reg fS _ _ r0S]; simp only [SExpr.denote, SBool.denote, kS, add_flags, r0, ofNat_add_assoc]
      rw [show 4 * j + 4 = 4 * (j + 1) by omega]
    · rw [sym_reg fS _ _ r3S]; exact r3
    · rw [sym_reg fS _ _ r7S]; simp only [subS, SExpr.denote, SBool.denote, sub_flags, r7]
      have : ∀ j < 8, BitVec.ofNat 32 (8 - j) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (8 - (j + 1)) := by decide
      exact this j hj
    · by_cases hij : i = j
      · subst hij
        have e0 := sym_rd fS _ _ m0S v; have e32 := sym_rd fS _ _ m32S v
        simp only [swS, kS, SExpr.denote, SMem.denote, r0, r3, ofNat_add_assoc, Nat.add_zero,
          show 4 * i + 32 = 32 + 4 * i from Nat.add_comm _ _] at e0 e32
        rw [(hwv i hi).1, (hwv i hi).2] at e0 e32; simp only [Nat.lt_irrefl, ↓reduceIte] at e0 e32
        simp only [Nat.lt_succ_self, ↓reduceIte, sel, e0, e32, BitVec.xor_comm (read32 _ (_ + BitVec.ofNat 32 (32 + 4 * i)))]
        exact ⟨trivial, trivial⟩
      · keep_simp only [hme]
        have : (i < j + 1) = (i < j) := by simp only [eq_iff_iff]; omega
        simp only [this]; exact hwv i hi
    · have z := sym_z fS _ zS' v
      simp only [subS, SExpr.denote, SBool.denote, sub_flags, r7] at z
      rw [show ∀ v : State, condPassed 1 v = !v.z from fun _ => rfl, z]
      have : ∀ j < 8, (!(BitVec.ofNat 32 (8 - j) - BitVec.ofNat 32 1 == 0#32)) = decide (j + 1 < 8) := by
        decide
      exact this j hj
  case sexit =>
    rintro x hpx ⟨r0x, r3x, -, hmx, hwx⟩ h13x hcx
    have zw : (ldS oZ).denote w = zW (s.regs 2) := by
      rw [ld _ _ hdr_ok.2.2.2.2.1 (by decide) (by decide) (by decide)]
      show (zS (.const (t.regs 2))).denote st0 = _; rw [C.t2]; rfl
    have tw : ∀ n < 24, read32 w.mem (s.regs 0 + BitVec.ofNat 32 (4 * n)) =
        orV (rw s.mem (s.regs 1)) (s.regs 2) n 8 := by
      intro n hn
      rw [hWw n (by omega)]
      refine orV_congr (fun k hk => ?_) 8 (Nat.le_refl _)
      have : 4 * (24 * k + n) + 4 ≤ 768 := by omega
      simp only [rw]; keep_simp
    have M3w : ∀ n < 16, read32 (execAll (sl 184 2) (execAll (sl 181 3) (execAll (sl 176 5) w))).mem
        (s.regs 0 + BitVec.ofNat 32 (4 * n)) = gE (rw s.mem (s.regs 1)) (s.regs 2) n := by
      intro n hn
      have ew := tw n (by omega)
      rcases (by omega : n = 0 ∨ n = 8 ∨ (n ≠ 0 ∧ n ≠ 8)) with rfl | rfl | ⟨h0, h8⟩
      · have e := sym_rd fF _ _ mF w
        simp only [SExpr.denote, SMem.denote, kS, lO, zw, Nat.reduceMul, BitVec.add_zero] at e ew ⊢
        keep_simp
        rw [e, ew]; simp [gE]
      · have e := sym_rd fF2 _ _ mF2 (execAll (sl 176 5) w)
        have r1 := sym_reg fF _ _ rF1 w
        simp only [SExpr.denote, SMem.denote, kS, r01, r1, zw] at e
        simp only [Nat.reduceMul] at ew ⊢
        keep_simp; rw [e]; keep_simp; rw [ew]; simp [gE]
      · keep_simp; rw [ew]; simp [gE, h0, h8]
    refine tail_run C hS hC hpx h13x hcx ?_ ?_ (fun i hi => ?_) ?_
    · rw [← lO]; simp only [ldS, kS, SExpr.denote, SMem.denote, h13w, oOut]; keep_simp
    · rw [hκκ, ← hκ, ← ld _ _ hdr_ok.2.2.2.1 (by decide) (by decide) (by decide)]
      simp only [ldS, kS, SExpr.denote, SMem.denote, h13w, oNeg]; keep_simp
    · rw [(hwx i hi).1, (hwx i hi).2]
      simp only [hi, ↓reduceIte, show 32 + 4 * i = 4 * (i + 8) by omega, M3w i (by omega), M3w (i + 8) (by omega),
        ← hκκ, gS, gS']
      rcases Bool.eq_false_or_eq_true (s.regs 2).msb with hn | hn <;>
        simp only [hn, ↓reduceIte, Bool.false_eq_true, sel_zero, sel_ones, and_self]
    · rw [feVal_wv]; refine wv_congr fun i hi => ?_
      rw [ofNat_add_assoc, show 64 + 4 * i = 4 * (16 + i) by omega]; keep_simp
      rw [tw _ (by omega)]; simp only [gE, show ¬(16 + i = 0 ∨ 16 + i = 8) by omega, ↓reduceIte]

/-- **The body** from the state after the frame. -/
theorem look_run (ok : Ok B BS) (hS : subR.SpecT fun b s => Tr.is (Ts b (Ed25519Leaf.leafPub [0, 1, 2] b s)))
    (hC : cmvR.SpecT fun b s => Tr.is (Tc b (wordPub 2 b s))) {base : Word} {s : State} (e : lkR.Entry base s)
    (F : Caller base (s.regs 13) lkR.stack (lowWin lkR 0 s :: lkR.wr s)) (t : State)
    (tpc : t.pc = base + BitVec.ofNat 32 (lkR.entry + 4))
    (t13 : t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved 0 + 4 * 14))
    (tr : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) (hm : MemEq [saved 0 s] s.mem t.mem)
    (hc : CodeAt t.mem base B) :
    ReachFT base (lkR.PcP base) (lkR.RdP base s) (Has (lowWin lkR 0 s :: lkR.wr s)) (lkR.SpP s) t
      (Qe base s t) (lkTr Ts Tc base (lookupPub base s)) := by
  have hcode := ok.code
  have hok := ok.lk
  simp only [lkOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  have hJ := hok.2.2.2.1
  have eo2 : off 2 = 4 := by decide +kernel
  have hlw : lowWin lkR 0 s = ⟨s.regs 13 - BitVec.ofNat 32 64, 60⟩ := by simp only [lowWin, lookE]; rfl
  simp only [hlw] at F ⊢
  have C : Cx (B := B) base s t (lookupPub base s) := ⟨ok, e, F, rfl, rfl, rfl, (s.regs 13).isLt, t13,
    tr 0 (by decide) (by decide), tr 1 (by decide) (by decide), tr 2 (by decide) (by decide), hm⟩
  generalize lookupPub base s = P at C ⊢
  lk_lay C
  have t13' := C.t13
  have hpcH : t.pc = base + BitVec.ofNat 32 (O + off 2) := by rw [tpc, eo2]; rfl
  unfold lkTr
  refine ReachFT.seg1 F sH (seqAt_sl hcode 2 60) (segOk 0 2 sH) hpcH t13' hc (by glue_tac [sH, r13k, kS, t13', lookE])
    (by simp [sH, SExpr.denote, t13', C.q13, fpP]) fun hpc1 h131 hc1 hm1 => ?_
  dsimp only [sH] at hpc1 h131 hc1 hm1 ⊢
  simp only [sregions, List.map, SExpr.denote, r13k, kS, t13', BitVec.add_zero] at hm1
  have i174 := at1 ok (a := 174) (i := .bcond 0 (bcOf 174)) (by decide +kernel)
  have i175 := at1 ok (a := 175) (i := .b (bOf 175)) (by decide +kernel)
  have e175 : off 175 = off 174 + 2 := by decide +kernel
  rw [show O + off 175 = O + off 174 + 2 by omega] at i175
  refine loopJ (o := O + off 62) (ob := O + off 174) (ex := O + off 176) (d := 60) F 0 (bcOf 174)
    (bOf 175) i174 i175 6 (Jg (s.regs 13 - 60#32) (s.regs 0) (s.regs 1) (s.regs 2)
      (execAll (sl 2 60) t).mem t.mem) (fun _ _ _ h => h)
    (fun j u hj hpu hI h13u hcu => pass_run C hj hpu hI h13u hcu hm1)
    (fun w hpw hJw h13w hcw => exit_run C hS hC hpw hJw h13w hcw) hJ 0 (execAll (sl 2 60) t) (by omega)
    (nx 62 rfl hpc1) ?_ h131 hc1
  exact ⟨MemEq.rfl' _ _, by rw [← t13']; exact sym_rd hdr_ok.1 _ _ hdr_ok.2.2.2.2.2.1 t,
    fun i hi => absurd hi (by omega)⟩

end

/-! ## The byte effect -/

open M0Crypto.Release.StackEffect (Ef EffT frame_te GP SIR sir_pass above_sub reg_in reg_sub_above inRD_of
  site_gp InRD InR reg_split PassOk atomOf addrE_atom sir_quietC spExact spAfter)

/-- Windows at offsets: `(i, c, w)` is the `w` bytes from atom `i` plus `c`. -/
def winsChkO (As : List SExpr) (W : List (Nat × Nat × Nat)) (rs : List (SExpr × Nat)) : Bool :=
  rs.all fun r => match atomOf As r.1 with
    | some (i, d) => W.any fun w => w.1 == i && decide (w.2.1 ≤ d.toNat) &&
        decide (d.toNat + r.2 ≤ w.2.1 + w.2.2) && decide (w.2.1 + w.2.2 < 2 ^ 32)
    | none => false

section
variable {sp0 : Word} {n : Nat}

theorem inRD_winsO {pc y : Word} {As : List SExpr} {vs : List Word} {rs : List (SExpr × Nat)}
    {W : List (Nat × Nat × Nat)} (hl : vs.length = As.length) (hc : winsChkO As W rs = true)
    (hy : InRD (addrE pc As vs) rs y) :
    ∃ w ∈ W, ∃ v, vs[w.1]? = some v ∧ Region (v + BitVec.ofNat 32 w.2.1) w.2.2 y := by
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  have h := List.all_eq_true.mp hc r hr
  revert h; split
  · next i d ha =>
    intro h
    obtain ⟨w, hw, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨v, hv, e⟩ := addrE_atom (pc := pc) hl ha
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨w, hw, v, h1 ▸ hv, by rw [e]; simp only [Region]; bv_omega⟩
  · simp

/-- **A pass from windows at offsets**: its reads lie in the windows `Wr`, its writes in `Ww`. -/
theorem pass_ofO {sp : Word} {R : Word → Prop} {s : Seg} {pc : Word} {vs : List Word}
    {Wr Ww : List (Nat × Nat × Nat)} (hl : vs.length = s.As.length) (hr : winsChkO s.As Wr s.rg = true)
    (hw : winsChkO s.As Ww s.wg = true)
    (h1 : ∀ w ∈ Wr, ∀ v, vs[w.1]? = some v → ∀ y, Region (v + BitVec.ofNat 32 w.2.1) w.2.2 y →
      BelowEntry sp0 n y → R y)
    (h2 : ∀ w ∈ Ww, ∀ v, vs[w.1]? = some v → ∀ y, Region (v + BitVec.ofNat 32 w.2.1) w.2.2 y →
      BelowEntry sp0 n y → AtOrAboveSp sp0 sp y) :
    PassOk sp0 n sp R s (addrE pc s.As vs) :=
  ⟨fun y hy => let ⟨w, hw, v, hv, h⟩ := inRD_winsO hl hr hy; h1 w hw v hv y h,
   fun y hy => let ⟨w, hw, v, hv, h⟩ := inRD_winsO hl hw hy; h2 w hw v hv y h⟩

/-- **An event that only reads** bytes of `R` below the entry keeps `SIR sp R`. -/
theorem sir_rd {sp : Word} {R : Word → Prop} {e : Event} (hx : spExact e.instr = true)
    (hs : spAfter e.instr sp = sp) (hw : ∀ y, ¬ Writes e.accesses y)
    (hR : ∀ y, Reads e.accesses y → BelowEntry sp0 n y → R y) :
    GP sp0 n (SIR sp0 sp R) (Tr.is [e]) (SIR sp0 sp R) := by
  rintro q ⟨qs, qr, qa⟩ _ rfl
  refine ⟨⟨⟨hx, fun y hy hb => .inl ?_, fun y hy hb => qr y (hR y hy hb)⟩, trivial⟩,
    ⟨show spAfter e.instr q.sp = sp by rw [qs, hs], fun y hy => ⟨?_, .inl (qr y hy)⟩, fun y hy => ?_⟩⟩
  · rcases hy with hy | hy
    · rw [qs]; exact qa y (qr y (hR y hy hb))
    · exact absurd hy (hw y)
  · rw [qs, hs]; exact qa y (qr y hy)
  · have := hy.1; rwa [qs, hs] at this

theorem reg_in2 {a y : Word} {x c w N : Nat} (h : Region (a + BitVec.ofNat 32 x + BitVec.ofNat 32 c) w y)
    (hc : x + c + w ≤ N) (hN : N < 2 ^ 32) : Region a N y := by
  simp only [Region] at h ⊢; bv_omega

theorem reg_sh {a y : Word} {c w b N : Nat} (h : Region (a + BitVec.ofNat 32 c) w y) (h1 : b ≤ c)
    (h2 : c + w ≤ b + N) (hN : b + N < 2 ^ 32) : Region (a + BitVec.ofNat 32 b) N y := by
  simp only [Region] at h ⊢; bv_omega

/-- `passTr` keeps `SIR` from its body's GP. -/
theorem passTr_gp {base : Word} {Φb : Nat → TrP} {m ob : Nat} {c : BitVec 4} {i8 : BitVec 8} {i11 : BitVec 11}
    {j : Nat} {I : Ef → Prop} {sp : Word} {R : Word → Prop} (h : GP sp0 n I (Φb j) (SIR sp0 sp R)) :
    GP sp0 n I (passTr base Φb m ob c i8 i11 j) (SIR sp0 sp R) :=
  GP.cat h (GP.cat (sir_quietC rfl rfl rfl) (GP.cond (fun _ => GP.nil fun _ h => h) fun _ => sir_quietC rfl rfl rfl))
end

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The bytes `m0c_ge_lookup` accesses outside its stack: the code, the output and the row. -/
def lkFp (base : Word) (P : Nat → Word) : Word → Prop := Has [codeR base, ⟨P 0, 128⟩, ⟨P 1, 768⟩]
/-- The bytes it requires written: the code and the row. -/
def lkRq (base : Word) (P : Nat → Word) (y : Word) : Prop := Has [codeR base] y ∨ Region (P 1) 768 y
/-- The bytes it writes: the output. -/
def lkWd (P : Nat → Word) : Word → Prop := Region (P 0) 128
/-- **The effect of `m0c_ge_lookup`** at public values `P`. -/
def lkE (base : Word) (P : Nat → Word) : TrP := EffT 64 (lkFp base P) (lkRq base P) (lkWd P) (P 2)

/-- The GP's hypotheses at public values `P` (as `frame_te`'s), with the code's facts. -/
structure GH (base sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Prop where
  room : (sp0 - P 2).toNat + 64 ≤ n
  n32 : n < 2 ^ 32
  F : ∀ y, lkFp base P y → BelowEntry sp0 n y → AtOrAboveSp sp0 (P 2) y
  R : ∀ y, lkRq base P y → BelowEntry sp0 n y → U y
  lit : litOff (O + off 200) 7 + 4 ≤ BS
  zero : Ed25519Compact.ed_zero + 32 ≤ BS
end

section
variable {sp0 : Word} {n : Nat} {U : Word → Prop} {P : Nat → Word}

def R0 (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop := U y ∨ Region (P 2 - BitVec.ofNat 32 4) 4 y
/-- The header's slots. -/
def FW (P : Nat → Word) (y : Word) : Prop := Region (fpP P) 20 y ∨ Region (fpP P + BitVec.ofNat 32 24) 32 y
/-- Known written: the slots and the output's first `o` bytes. -/
def Kn (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (o : Nat) (y : Word) : Prop :=
  R0 U P y ∨ (FW P y ∨ Region (P 0) o y) ∧ BelowEntry sp0 n y
abbrev KS (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (o : Nat) : Ef → Prop :=
  SIR sp0 (fpP P) (Kn sp0 n U P o)
abbrev Jf (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Ef → Prop :=
  SIR sp0 (fpP P) fun y => R0 U P y ∨ lkWd P y ∧ BelowEntry sp0 n y

theorem Kn.fr {o c w : Nat} {y : Word} (hb : BelowEntry sp0 n y) (h : Region (fpP P + BitVec.ofNat 32 c) w y)
    (hc : c + w ≤ 20 ∨ 24 ≤ c ∧ c + w ≤ 56) : Kn sp0 n U P o y := by
  rcases hc with hc | hc
  · exact .inr ⟨.inl (.inl (reg_in h hc (by decide))), hb⟩
  · exact .inr ⟨.inl (.inr (reg_sh h hc.1 (by omega) (by decide))), hb⟩
theorem Kn.out1 {o c w : Nat} {y : Word} (hb : BelowEntry sp0 n y) (h : Region (P 0 + BitVec.ofNat 32 c) w y)
    (hc : c + w ≤ o) (ho : o < 2 ^ 32) : Kn sp0 n U P o y := .inr ⟨.inr (reg_in h hc ho), hb⟩
theorem Kn.out2 {o x c w : Nat} {y : Word} (hb : BelowEntry sp0 n y)
    (h : Region (P 0 + BitVec.ofNat 32 x + BitVec.ofNat 32 c) w y) (hc : x + c + w ≤ o) (ho : o < 2 ^ 32) :
    Kn sp0 n U P o y := .inr ⟨.inr (reg_in2 h hc ho), hb⟩

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

theorem GH.b60 (G : GH base sp0 n U P) : (sp0 - P 2).toNat + 60 < 2 ^ 32 := by
  have := G.room; have := G.n32; omega
theorem GH.r4 (G : GH base sp0 n U P) : (sp0 - fpP P).toNat + 4 ≤ n := by
  have := G.room; have := G.n32; have := G.b60; simp only [fpP]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega
theorem GH.up (G : GH base sp0 n U P) {y : Word} (h : AtOrAboveSp sp0 (P 2) y) : AtOrAboveSp sp0 (fpP P) y :=
  above_sub h G.b60
theorem GH.fr (G : GH base sp0 n U P) {y : Word} {c w : Nat} (h : Region (fpP P + BitVec.ofNat 32 c) w y)
    (hw : c + w ≤ 60) : AtOrAboveSp sp0 (fpP P) y :=
  reg_sub_above (d := 60) (reg_in h hw (by decide)) (Nat.le_refl _) G.b60
theorem GH.out1 (G : GH base sp0 n U P) {y : Word} {c w : Nat} (h : Region (P 0 + BitVec.ofNat 32 c) w y)
    (hw : c + w ≤ 128) (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 (fpP P) y :=
  G.up (G.F y ⟨_, .tail _ (.head _), Rgn.of_region (reg_in h hw (by decide))⟩ he)
theorem GH.out2 (G : GH base sp0 n U P) {y : Word} {x c w : Nat}
    (h : Region (P 0 + BitVec.ofNat 32 x + BitVec.ofNat 32 c) w y) (hw : x + c + w ≤ 128)
    (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 (fpP P) y :=
  G.up (G.F y ⟨_, .tail _ (.head _), Rgn.of_region (reg_in2 h hw (by decide))⟩ he)
theorem GH.row (G : GH base sp0 n U P) {y : Word} {x c w : Nat}
    (h : Region (P 1 + BitVec.ofNat 32 x + BitVec.ofNat 32 c) w y) (hw : x + c + w ≤ 768)
    (he : BelowEntry sp0 n y) : U y := G.R y (.inr (reg_in2 h hw (by decide))) he
theorem GH.cd (G : GH base sp0 n U P) {y : Word} {c w : Nat} (h : Region (base + BitVec.ofNat 32 c) w y)
    (hw : c + w ≤ BS) (he : BelowEntry sp0 n y) : U y :=
  G.R y (.inl ⟨_, .head _, Rgn.of_region (reg_in h hw CodeBytes.lt)⟩) he
theorem GH.cdF (G : GH base sp0 n U P) {y : Word} {c w : Nat} (h : Region (base + BitVec.ofNat 32 c) w y)
    (hw : c + w ≤ BS) (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 (fpP P) y :=
  G.up (G.F y ⟨_, .head _, Rgn.of_region (reg_in h hw CodeBytes.lt)⟩ he)

/-- **The header's GP**: it writes the slots. -/
theorem GH.hd (G : GH base sp0 n U P) :
    GP sp0 n (SIR sp0 (fpP P) (R0 U P)) (bT base 2 sH [fpP P]) (KS sp0 n U P 0) := by
  refine GP.post (sir_pass (by decide +kernel) (pass_ofO (vs := [fpP P]) (Wr := []) (Ww := [(0, 0, 56)]) rfl
    (by decide) (by decide +kernel) (by simp) (by pass_tac []; exact fun y h _ => G.fr (c := 0) (w := 56) h (by omega))))
    fun q h => h.mono fun y hy => ?_
  rcases hy with hy | ⟨(h | h) | h, hb⟩
  · exact .inl hy
  · exact .inr ⟨inRD_of (vs := [fpP P]) (r := (.reg0 13, 20)) (i := 0) (d := 0#32) rfl (.head _) (by decide) rfl
      (by rw [BitVec.add_zero]; exact h), hb⟩
  · exact .inr ⟨inRD_of (vs := [fpP P]) (r := (r13k 24, 32)) (i := 0) (d := 24#32) rfl (.tail _ (.head _)) (by decide +kernel) rfl h, hb⟩
  · exact absurd h (by simp [Region])

/-- **Pass `j` of the block loop's GP**: the output's next 16 bytes join the written set. -/
theorem GH.pass (G : GH base sp0 n U P) {j : Nat} (hj : j < 6) :
    GP sp0 n (KS sp0 n U P (16 * j)) (passTr base (pB base P) 6 (O + off 174) 0 (bcOf 174) (bOf 175) j)
      (KS sp0 n U P (16 * (j + 1))) := by
  refine passTr_gp (GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO
      (vs := [fpP P, P 1 + BitVec.ofNat 32 (16 * j), P 0 + BitVec.ofNat 32 (16 * j)])
      (Wr := [(0, 0, 16), (0, 24, 32), (1, 0, 688)]) (Ww := [(2, 0, 16)]) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact ⟨fun y h hb => Kn.fr (c := 0) (w := 16) hb h (by omega), fun y h hb => Kn.fr (c := 24) (w := 32) hb h (by omega),
        fun y h hb => .inl (.inl (G.row (x := 16 * j) (c := 0) (w := 688) h (by omega) hb))⟩)
      (by pass_tac []; exact fun y h hb => G.out2 (x := 16 * j) (c := 0) (w := 16) h (by omega) hb))) fun q h => h.mono fun y hy => ?_)
    (GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P (16 * (j + 1))) (vs := [fpP P]) (Wr := [(0, 12, 4)]) (Ww := [(0, 12, 4)])
      rfl (by decide +kernel) (by decide +kernel) (by pass_tac []; exact fun y h hb => Kn.fr (c := 12) (w := 4) hb h (by omega))
      (by pass_tac []; exact fun y h _ => G.fr (c := 12) (w := 4) h (by omega)))) fun q h => h.mono fun y hy => .inl hy)
      (GP.nil fun _ h => h)))
  rcases hy with hy | ⟨h | h, hb⟩
  · exact .inl (.inl hy)
  · exact .inl (.inr ⟨.inl h, hb⟩)
  · rw [show 16 * (j + 1) = 16 * j + 16 by omega] at h
    rcases reg_split h with h | h
    · exact .inl (.inr ⟨.inr h, hb⟩)
    · exact .inr ⟨inRD_of (vs := [fpP P, P 1 + BitVec.ofNat 32 (16 * j), P 0 + BitVec.ofNat 32 (16 * j)])
        (r := (blkS oOut, 16)) (i := 2) (d := 0#32) rfl (List.mem_singleton_self _) (by decide +kernel) rfl
        (by rw [BitVec.add_zero]; exact h), hb⟩

variable {Ts Tc : Word → (Nat → Word) → List Event}

/-- **The tail's GP**: `fe_sub` writes the scratch element and `cmov` rewrites the third. -/
theorem GH.tl (G : GH base sp0 n U P) (hbS : ∀ b p, Ed25519GeField.fE Ed25519Compact.fe_sub b p (Ts b p))
    (hbC : ∀ b p, Ed25519WordLoop.wloopE true true b p (Tc b p)) :
    GP sp0 n (KS sp0 n U P 96) (tlT Ts Tc base P) (Jf sp0 n U P) := by
  have e8 : 8 * ((pC P 2).toNat / 2) = 32 := by simp [pC, pubOf]
  refine GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 96) (vs := [fpP P])
      (Wr := [(0, 0, 4)]) (Ww := []) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact fun y h hb => Kn.fr (c := 0) (w := 4) hb h (by omega)) (by simp)))
      fun q h => h.mono fun y hy => .inl hy) (GP.cat (sir_rd (R := Kn sp0 n U P 96) rfl rfl ?nw ?rd) ?sub)
  case nw => rintro y ⟨a, ha, hk, -⟩; simp only [List.mem_singleton] at ha; subst ha; cases hk
  case rd =>
    rintro y ⟨a, ha, -, k, hk, rfl⟩ hb
    simp only [List.mem_singleton] at ha; subst ha
    exact .inl (.inl (G.cd (c := litOff (O + off 200) 7) (w := 4) (Region.mk hk rfl) G.lit hb))
  refine site_gp (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 96) (vs := [fpP P])
      (Wr := [(0, 0, 4)]) (Ww := []) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact fun y h hb => Kn.fr (c := 0) (w := 4) hb h (by omega)) (by simp)))
      fun q h => h.mono fun y hy => .inl hy) rfl rfl rfl
    (show EffT 4 _ _ _ (fpP P) _ from hbS base (pS base P)) G.r4 G.n32 ?F1 ?R1
    (GP.pre (fun q h => h.mono (R' := Kn sp0 n U P 128) fun y hy => ?_) (site_gp (GP.post (sir_pass
      (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 128) (vs := [fpP P]) (Wr := [(0, 0, 4), (0, 8, 4)]) (Ww := [])
      rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact ⟨fun y h hb => Kn.fr (c := 0) (w := 4) hb h (by omega),
        fun y h hb => Kn.fr (c := 8) (w := 4) hb h (by omega)⟩) (by simp)))
      fun q h => h.mono fun y hy => .inl hy) rfl rfl rfl
      (show EffT 4 _ _ _ (fpP P) _ from hbC base (pC P)) G.r4 G.n32 ?F2 ?R2 (GP.nil fun q h => h.mono fun y hy => ?_)))
  case F1 =>
    rintro y ⟨r, hr, o, ho, rfl⟩ hb
    simp only [Ed25519FeCanon.rg0, Ed25519FeEq.ab, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact G.out1 (c := 96) (w := 32) (Region.mk ho rfl) (by omega) hb
    · exact G.cdF (c := Ed25519Compact.ed_zero) (w := 32) (Region.mk ho rfl) G.zero hb
    · exact G.out1 (c := 64) (w := 32) (Region.mk ho rfl) (by omega) hb
  case R1 =>
    rintro y ⟨r, hr, o, ho, rfl⟩ hb
    simp only [Ed25519FeEq.ab, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (.inl (G.cd (c := Ed25519Compact.ed_zero) (w := 32) (Region.mk ho rfl) G.zero hb))
    · exact Kn.out1 (c := 64) (w := 32) hb (Region.mk ho rfl) (by omega) (by decide)
  case F2 =>
    intro y h hb
    rcases h with h | ⟨-, h⟩ <;> rw [e8] at h
    · exact G.out1 (c := 64) (w := 32) h (by omega) hb
    · exact G.out1 (c := 96) (w := 32) h (by omega) hb
  case R2 =>
    intro y h hb
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [e8] at h
    · exact Kn.out1 (c := 64) (w := 32) hb h (by omega) (by decide)
    · exact Kn.out1 (c := 96) (w := 32) hb h (by omega) (by decide)
  · rcases hy with hy | ⟨h | h, hb⟩
    · exact .inl (.inl hy)
    · exact .inl (.inr ⟨.inl h, hb⟩)
    · rcases reg_split (x := 96) (w := 32) h with h | h
      · exact .inl (.inr ⟨.inr h, hb⟩)
      · obtain ⟨o, ho, rfl⟩ := Region.exists h
        exact .inr ⟨⟨_, List.mem_singleton_self _, o, ho, rfl⟩, hb⟩
  · rcases hy with hy | ⟨h, hb⟩
    · exact .inl (.inl hy)
    · exact .inl (.inr ⟨.inr h, hb⟩)

/-- **From the block loop's exit**: the fixes and the swap read and write the output's first 96 bytes. -/
theorem GH.ex (G : GH base sp0 n U P) (hbS : ∀ b p, Ed25519GeField.fE Ed25519Compact.fe_sub b p (Ts b p))
    (hbC : ∀ b p, Ed25519WordLoop.wloopE true true b p (Tc b p)) :
    GP sp0 n (KS sp0 n U P 96) (exT Ts Tc base P) (Jf sp0 n U P) := by
  refine GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 96) (vs := [fpP P, P 0])
      (Wr := [(0, 0, 4), (0, 16, 4), (1, 0, 4)]) (Ww := [(1, 0, 4)]) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact ⟨fun y h hb => Kn.fr (c := 0) (w := 4) hb h (by omega),
        fun y h hb => Kn.fr (c := 16) (w := 4) hb h (by omega),
        fun y h hb => Kn.out1 (c := 0) (w := 4) hb h (by omega) (by decide)⟩)
      (by pass_tac []; exact fun y h hb => G.out1 (c := 0) (w := 4) h (by omega) hb)))
      fun q h => h.mono fun y hy => .inl hy) ?_
  refine GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 96) (vs := [P 0])
      (Wr := [(0, 32, 4)]) (Ww := [(0, 32, 4)]) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact fun y h hb => Kn.out1 (c := 32) (w := 4) hb h (by omega) (by decide))
      (by pass_tac []; exact fun y h hb => G.out1 (c := 32) (w := 4) h (by omega) hb)))
      fun q h => h.mono fun y hy => .inl hy) ?_
  refine GP.cat (GP.post (sir_pass (by decide +kernel) (pass_ofO (R := Kn sp0 n U P 96) (vs := [fpP P])
      (Wr := [(0, 8, 4)]) (Ww := []) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact fun y h hb => Kn.fr (c := 8) (w := 4) hb h (by omega)) (by simp)))
      fun q h => h.mono fun y hy => .inl hy) ?_
  refine GP.rep (G.tl hbS hbC) 8 0 fun i hi => GP.cat (GP.cat (GP.post (sir_pass (by decide +kernel)
    (pass_ofO (R := Kn sp0 n U P 96) (vs := [P 0 + BitVec.ofNat 32 (4 * i)]) (Wr := [(0, 0, 4), (0, 32, 4)])
      (Ww := [(0, 0, 4), (0, 32, 4)]) rfl (by decide +kernel) (by decide +kernel)
      (by pass_tac []; exact ⟨fun y h hb => Kn.out2 (x := 4 * i) (c := 0) (w := 4) hb h (by omega) (by decide),
        fun y h hb => Kn.out2 (x := 4 * i) (c := 32) (w := 4) hb h (by omega) (by decide)⟩)
      (by pass_tac []; exact ⟨fun y h hb => G.out2 (x := 4 * i) (c := 0) (w := 4) h (by omega) hb,
        fun y h hb => G.out2 (x := 4 * i) (c := 32) (w := 4) h (by omega) hb⟩)))
      fun q h => h.mono fun y hy => .inl hy) (GP.nil fun _ h => h)) (sir_quietC rfl rfl rfl)

/-- **The body's GP**: from the entry's `R0`, the row and the code read, the output written. -/
theorem GH.lk (G : GH base sp0 n U P) (hbS : ∀ b p, Ed25519GeField.fE Ed25519Compact.fe_sub b p (Ts b p))
    (hbC : ∀ b p, Ed25519WordLoop.wloopE true true b p (Tc b p)) :
    GP sp0 n (SIR sp0 (fpP P) (R0 U P)) (lkTr Ts Tc base P) (Jf sp0 n U P) :=
  GP.cat G.hd (GP.repI (I := fun j => KS sp0 n U P (16 * j)) 6 0 (fun _ _ hj => G.pass (by omega)) (G.ex hbS hbC))
end
end

/-! ## The routine's TE -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **`m0c_ge_lookup`'s call lemma with its effect**, from its callees'. -/
noncomputable def look_te (ok : Ok B BS)
    (hs : subR.TE (Ed25519Leaf.leafPub [0, 1, 2]) (Ed25519GeField.fE Ed25519Compact.fe_sub))
    (hc : cmvR.TE (wordPub 2) (Ed25519WordLoop.wloopE true true)) : lkR.TE lookupPub lkE := by
  have hok := ok.lk
  simp only [lkOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨-, -, hBS, -, -, -, -, -, -, -, -, -, -, hlit, -, -, hZ, -, -, -⟩ := hok
  have hl : litOff (O + off 200) 7 + 4 ≤ BS := by
    simp only [litOk, Bool.and_eq_true, decide_eq_true_eq] at hlit; exact hlit.1.1.2
  have eo : off 0 = 0 ∧ off 212 % 2 = 0 ∧ off 212 + 4 ≤ 432 := by decide +kernel
  have hO : O % 2 = 0 := by decide
  have hchk : O % 2 = 0 ∧ (O + off 212) % 2 = 0 ∧ O + off 212 + 4 ≤ BS ∧ O + 4 ≤ BS ∧ 14 < 128 ∧
      4 * nSaved 0 + 4 * 14 ≤ 64 := by
    obtain ⟨-, h1, h2⟩ := eo
    generalize off 212 = k at h1 h2 ⊢
    generalize O = o at hO hBS ⊢
    exact ⟨hO, by omega, by omega, by omega, by decide, by decide⟩
  refine frame_te (f := lkR) (pub := lookupPub) (mask := 0) (k := 14) (epi := O + off 212) (spP := fun p => p 2)
    (Ψ := fun b p => lkTr hs.T hc.T b p) (Fp := lkFp) (Rq := lkRq) (Wd := fun _ p => lkWd p) (by decide)
    ?en ?po (by decide +kernel) hchk (fun _ _ => rfl)
    (fun _ _ e F t tpc t13 tr hm hc' => look_run ok hs.spec hc.spec e F t tpc t13 tr hm hc')
    (fun _ _ => by simp only [lkTr, exT, tlT, bT, pB, sB, passTr]; uniq_tac)
    (fun _ _ => by simp only [lkTr, exT, tlT, bT, pB, sB, passTr]; ex_tac)
    (fun _ p y h => ⟨_, .tail _ (.head _), Rgn.of_region h⟩)
    (fun b p sp0 n U hroom hn hF hR => by
      rw [show 4 * nSaved 0 + 4 * 14 = 60 by decide, show 4 * nSaved 0 = 4 by decide]
      exact GH.lk ⟨hroom, hn, hF, hR, hl, hZ⟩ hs.eff hc.eff)
  case en =>
    have := seqAt_sl ok.code 0 2
    rw [eo.1, Nat.add_zero, show sl 0 2 = [.push 0 true, .subSp (BitVec.ofNat 7 14)] by decide +kernel] at this
    exact this
  case po =>
    have := seqAt_sl ok.code 212 2
    rwa [show sl 212 2 = [.addSp (BitVec.ofNat 7 14), .pop 0 true] by decide +kernel] at this
end

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_ge_lookup` in each build**, with its effect. -/
noncomputable def lookup_te (b : Build) : letI := b.codeBytes; lkR.TE lookupPub (@lkE _ b.size b.codeBytes) :=
  letI := b.codeBytes
  look_te (ok_b b) (Ed25519GeField.sub_te b) (Ed25519WordLoop.cmov_te b)

/-! ## The adapter -/

section
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519ScReduceProg (dW word_dW)

/-- `m0c_ge_lookup`'s interface: the 128 bytes at `r0` (the entry's three elements and scratch),
the 768-byte row at `r1`, the secret digit in `r2`. -/
def ioLook : Iface :=
  { ins := [(1, 0, .raw (.k 768)), (2, 0, .view .rw)], outs := [(0, 0, .fe), (0, 32, .fe), (0, 64, .fe)],
    wr := [⟨0, 0, .k 128⟩], rd := [⟨1, 0, .k 768⟩, ⟨0, 0, .k 128⟩], al := [0, 1],
    apt := [(⟨0, 0, .k 128⟩, ⟨1, 0, .k 768⟩)] }

/-- The callee: its public values are `r0`, `r1` and `sp`; the digit is not one. -/
def lookS : CalleeS := calleeAt O ioLook [0, 1]

/-- The selected entry's elements from the row bytes `l` and the digit `d`. -/
def lookV : List V → List V
  | [.b l, .w d] => [.f (wv (gS (dW l) d)), .f (wv (gS' (dW l) d)), .f (gT (dW l) d)]
  | _ => [.none, .none, .none]

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The routine's effect is the callee's. -/
theorem look_eff {base : Word} {p : Nat → Word} {tr : List Event} (h : lkE base p tr) : lookS.Eff p base tr := by
  refine EffT.mono h (by decide +kernel) (fun y hy => ?_) (fun y hy => ?_) fun y hy => ?_
  · show Has (codeR base :: [⟨p 1 + 0#32, 768⟩, ⟨p 0 + 0#32, 128⟩] ++ [⟨p 0 + 0#32, 128⟩]) y
    simp only [BitVec.add_zero]
    obtain ⟨r, hr, hy⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, hy⟩
    · exact ⟨_, .tail _ (.tail _ (.head _)), hy⟩
    · exact ⟨_, .tail _ (.head _), hy⟩
  · rcases hy with hy | hy
    · exact .inl hy
    · exact .inr ⟨_, .head _, show Region (p 1 + BitVec.ofNat 32 0) 768 y by rwa [BitVec.add_zero]⟩
  · obtain ⟨x, hx, hy⟩ := hy
    simp only [lookS, calleeAt, ioLook, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact reg_in (c := 0) (w := 32) hy (by omega) (by decide)
    · exact reg_in (c := 32) (w := 32) hy (by omega) (by decide)
    · exact reg_in (c := 64) (w := 32) hy (by omega) (by decide)
end

/-- **`m0c_ge_lookup`'s adapter** in build `b`: the entry of the row `r1` for the secret digit
`r2`, its trace a function of `r0`, `r1` and `sp`. -/
noncomputable def lookAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) lookS :=
  letI := b.codeBytes
  Ad.ofTSpec { lkR with code := footprint O } rfl rfl (by show 64 = stackOf O; decide +kernel)
    ((lookup_te b).code _ (by decide +kernel)) (fun _ _ _ h => look_eff h) lookV
    (fun _ _ _ st _ hg hv _ => by
      refine ⟨hg.1 0 (by simp [lookS, calleeAt, ioLook]), hg.1 1 (by simp [lookS, calleeAt, ioLook]), ?_⟩
      have h := hv.2.2 (⟨0, 0, .k 128⟩, ⟨1, 0, .k 768⟩) (List.mem_singleton_self _)
      change Sep [⟨st.regs 0 + 0#32, 128⟩] [⟨st.regs 1 + 0#32, 768⟩] at h
      simpa only [BitVec.add_zero] using h)
    (fun st => by
      show ([⟨st.regs 0, 128⟩] : List Rgn) = [⟨st.regs 0 + 0#32, 128⟩]; rw [BitVec.add_zero])
    (fun st => by
      show ([⟨st.regs 1, 768⟩, ⟨st.regs 0, 128⟩] : List Rgn) = [⟨st.regs 1 + 0#32, 768⟩, ⟨st.regs 0 + 0#32, 128⟩]
      simp only [BitVec.add_zero])
    fun _ _ st m _ vs _ hi hp => by
      rcases vs with _ | ⟨l | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | d | _, _ | _⟩⟩ <;>
        simp only [InsRel, All2, lookS, calleeAt, ioLook, Rel, In.kd, ALen.val, and_true, and_false,
          false_and] at hi
      simp only [BitVec.add_zero] at hi
      obtain ⟨rfl, rfl⟩ := hi
      have hw : ∀ n < 192, rw st.mem (st.regs 1) n = dW (bytesAt st.mem (st.regs 1) 768) n :=
        fun n hn => word_dW (n := 192) _ _ hn
      have hg : ∀ n < 24, gE (rw st.mem (st.regs 1)) (st.regs 2) n = gE (dW (bytesAt st.mem (st.regs 1) 768)) (st.regs 2) n :=
        fun n hn => gE_congr fun k hk => hw _ (by omega)
      obtain ⟨h8, hT⟩ := hp
      simp only [OutsRel, All2, lookS, calleeAt, ioLook, lookV, Rel, BitVec.add_zero, and_true]
      refine ⟨?_, ?_, ?_⟩
      · rw [feVal_wv, wv_congr (g := gS (dW (bytesAt st.mem (st.regs 1) 768)) (st.regs 2)) fun i hi => ?_]
        · exact ModP.refl _
        rw [(h8 i hi).1]; unfold gS; exact hg _ (by split <;> omega)
      · rw [feVal_wv, wv_congr (g := gS' (dW (bytesAt st.mem (st.regs 1) 768)) (st.regs 2)) fun i hi => ?_]
        · exact ModP.refl _
        rw [ofNat_add_assoc, (h8 i hi).2]; unfold gS'; exact hg _ (by split <;> omega)
      · have e : gT (rw st.mem (st.regs 1)) (st.regs 2) = gT (dW (bytesAt st.mem (st.regs 1) 768)) (st.regs 2) := by
          unfold gT; rw [wv_congr fun i hi => hg (16 + i) (by omega)]
        rw [← e]; exact hT
end

end M0Crypto.Release.Ed25519LookupTE
