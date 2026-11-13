import M0Crypto.Release.X25519SlotEnv
import M0Crypto.Release.X25519LadderBit
import M0Crypto.Release.X25519Ladder

set_option linter.unusedSectionVars false

/-!
One Montgomery-ladder step of `m0c_x25519` (`X25519EntryCode.stepAt`, plan phase 9, step 3).

`step_w` runs the step: the four sums and differences, the scalar-bit block `bitL`, the two
selects with mask `-(swap ^ bit)`, and the thirteen remaining operations. `StepOut` gives the
slot values as `X25519Ladder.StepSlots` with `sw = swap ^ bit`, the new swap word, and keeps
every frame byte outside the slots `X2..D` and the swap word. The addition, subtraction and
select lemmas are hypotheses here; the call operations come from `X25519OpRun`.
-/

namespace M0Crypto.Release.X25519LadderStep
open M0Crypto.Armv6M (Word State Mem read32 write32 rorC)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun
open M0Crypto.Release.X25519SlotEnv
open M0Crypto.Release.X25519Ladder (StepSlots)

/-! ## Words of the frame -/

/-- The ladder bit index. -/
def tWord (c : X25519.Ctx) (m : Mem) : Word := read32 m (slotAt c lvT)

/-- The swap word. -/
def swWord (c : X25519.Ctx) (m : Mem) : Word := read32 m (slotAt c lvSwap)

/-- Bit `t` of the clamped scalar, as `bitL` computes it. -/
def bitWord (c : X25519.Ctx) (m : Mem) : Word :=
  (rorC (read32 m (slotAt c sK + ((tWord c m >>> 3) &&& 28#32))) ((tWord c m).toNat % 256)
    ((tWord c m).getLsbD 2)).1 &&& 1#32

theorem region_add {a x y : Word} {n k : Nat} (hx : x.toNat + n ≤ k) (h : Region (a + x) n y) :
    Region a k y := by
  show (y - a).toNat < k
  have h' : (y - (a + x)).toNat < n := h
  simp only [BitVec.toNat_sub, BitVec.toNat_add] at h' ⊢
  have := a.isLt; have := y.isLt; have := x.isLt
  omega

theorem idx_le (w : Word) : ((w >>> 3) &&& 28#32).toNat ≤ 28 := by
  rw [BitVec.toNat_and]
  exact Nat.le_trans Nat.and_le_right (by decide)

/-- The three words depend only on the bytes from `S_K` to the end of the frame. -/
theorem hi_congr {c : X25519.Ctx} (hv : X25519.Valid c) {m m' : Mem}
    (h : ∀ y, Region (slotAt c sK) (LFRAME - sK) y → m y = m' y) :
    tWord c m = tWord c m' ∧ swWord c m = swWord c m' ∧ bitWord c m = bitWord c m' := by
  have ht : tWord c m = tWord c m' :=
    read32_congr' fun y hy => h y (band_sub hv (by decide) (by decide) (by decide) hy)
  refine ⟨ht, read32_congr' fun y hy => h y (band_sub hv (by decide) (by decide) (by decide) hy), ?_⟩
  unfold bitWord
  rw [ht, read32_congr' (m := m) (m' := m')
    (a := slotAt c sK + ((tWord c m' >>> 3) &&& 28#32)) fun y hy =>
      h y (region_add (by have := idx_le (tWord c m'); simp only [LFRAME, sK]; omega) hy)]

/-! ## Masks -/

theorem word_le_one {x : Word} (h : x.toNat ≤ 1) : x = 0#32 ∨ x = 1#32 := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
  · exact .inl (BitVec.eq_of_toNat_eq (by simpa using h))
  · exact .inr (BitVec.eq_of_toNat_eq (by simpa using h))

theorem xor_le_one {x y : Word} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) : (x ^^^ y).toNat ≤ 1 := by
  rcases word_le_one hx with rfl | rfl <;> rcases word_le_one hy with rfl | rfl <;> decide

theorem and_one_le (x : Word) : (x &&& 1#32).toNat ≤ 1 := by
  rw [BitVec.toNat_and]
  exact Nat.le_trans Nat.and_le_right (by decide)

theorem mask_if {x : Word} (hx : x.toNat ≤ 1) {α : Type} (a b : α) :
    (if 0#32 - x = 0 then a else b) = if x.toNat = 1 then b else a := by
  rcases word_le_one hx with rfl | rfl
  · rfl
  · rfl

theorem mask_ok {x : Word} (hx : x.toNat ≤ 1) : 0#32 - x = 0#32 ∨ 0#32 - x = BitVec.allOnes 32 := by
  rcases word_le_one hx with rfl | rfl
  · exact .inl (by decide)
  · exact .inr (by decide)

/-! ## The step -/

def sels : List Op := [sel sX2 sA sC, sel sZ2 sB sD]

def ladderRest : List Op :=
  [mul sD sD sA, mul sC sC sB, add sX3 sD sC, sqr sX3 sX3, sub sZ3 sD sC, sqr sZ3 sZ3,
   mul sZ3 sX1 sZ3, sqr sA sX2, sqr sB sZ2, mul sX2 sA sB, sub sA sA sB, mulc sC sA sB,
   mul sZ2 sA sC]

theorem ops2_split : ladderOps2 = sels ++ ladderRest := rfl

/-- The effect of one ladder step from `s` to `t`. -/
structure StepOut (c : X25519.Ctx) (s t : State) : Prop where
  slots : ∃ A B C D SA SB DA CB X3s Z3d Z3s AA BB E T : Int,
    StepSlots (env c s.mem sX1) (env c s.mem sX2) (env c s.mem sZ2) (env c s.mem sX3)
      (env c s.mem sZ3) (swWord c s.mem ^^^ bitWord c s.mem).toNat A B C D SA SB DA CB X3s
      (env c t.mem sX3) Z3d Z3s (env c t.mem sZ3) AA BB (env c t.mem sX2) E T (env c t.mem sZ2)
  swap : swWord c t.mem = bitWord c s.mem
  keep : ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sX2) (sK - sX2) y →
    ¬ Region (slotAt c lvSwap) 4 y → t.mem y = s.mem y

theorem step_w (hAdd : OpW .add) (hSub : OpW .sub) (hSel : OpW .sel)
    {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
    {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : X25519Op.PcOk c.base lo hi Pc)
    {s : State} {Q : State → Prop} {o : Nat}
    (hseq : seqAt B o (stepAt o) = true) (ho : o % 2 = 0) (hlo : lo ≤ o)
    (hend : o + seqSize (stepAt o) ≤ hi)
    (hpc : s.pc = c.base + BitVec.ofNat 32 o) (hs : Body c m1 s) (hsw : (swWord c s.mem).toNat ≤ 1)
    (k : ∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (stepAt o)) → Body c m1 t →
      StepOut c s t → ReachW c.base Pc Wr t Q) :
    ReachW c.base Pc Wr s Q := by
  have hW := nonsel_w hAdd hSub
  -- code layout
  have hst : stepAt o = (opsAt o ladderOps1 ++ bitL) ++
      (opsAt (o + seqSize (opsAt o ladderOps1 ++ bitL)) sels ++
        opsAt (o + seqSize (opsAt o ladderOps1 ++ bitL) +
          seqSize (opsAt (o + seqSize (opsAt o ladderOps1 ++ bitL)) sels)) ladderRest) := by
    simp only [stepAt, ops2_split, opsAt_append]
  generalize ho2 : o + seqSize (opsAt o ladderOps1 ++ bitL) = o2 at hst
  generalize ho3 : o2 + seqSize (opsAt o2 sels) = o3 at hst
  rw [seqSize_append] at ho2
  have hsz : o + seqSize (stepAt o) = o3 + seqSize (opsAt o3 ladderRest) := by
    rw [hst, seqSize_append, seqSize_append, seqSize_append]; omega
  rw [hst, seqAt_append, seqAt_append, seqAt_append, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hseq
  rw [hsz] at hend k
  obtain ⟨⟨hs1, hsb⟩, hs2, hs3⟩ := hseq
  rw [seqSize_append, ho2] at hs2
  rw [seqSize_append, ho2, ho3] at hs3
  have he1 := seqSize_even (opsAt o ladderOps1)
  have heb : seqSize bitL = 26 := by decide
  have he2 := seqSize_even (opsAt o2 sels)
  have he3 := seqSize_even (opsAt o3 ladderRest)
  -- ops 1
  refine opsAt_w hv hcode hWr hPO ladderOps1 o s
    (fun p hp => ⟨hW _ (nonsel_of (by decide) p hp), nonsel_of (by decide) p hp⟩) (by decide)
    hs1 ho hlo (by omega) hpc hs ?_
  intro u1 pc1 E1
  have hb1 := E1.body hs
  have hK1 := opsEff_keep hv (lo := sX2) (hi := sK) (by decide) E1 (by decide)
  have hhi : ∀ y, Region (slotAt c sK) (LFRAME - sK) y → u1.mem y = s.mem y := fun y h =>
    hK1 y (band_frame hv (by decide) h) (band_disj hv (by decide) (by decide) (by decide) h)
  obtain ⟨-, hsw1, hbit1⟩ := hi_congr hv hhi
  -- scalar bit
  refine X25519LadderBit.bit_w hv hWr hPO hsb (by omega) (by omega) (by omega) pc1 hb1 ?_
  intro u2 pc2 hb2 tW w b r7 mem2
  have hr7 : u2.regs 7 = 0#32 - (swWord c s.mem ^^^ bitWord c s.mem) := by
    rw [← hsw1, ← hbit1]; exact r7
  have hx : (swWord c s.mem ^^^ bitWord c s.mem).toNat ≤ 1 := xor_le_one hsw (and_one_le _)
  have hbr : ∀ e, SlotOk e → env c u2.mem e = env c u1.mem e := by
    intro e he
    refine congrArg (fun n : Nat => (n : Int)) (feVal_congr fun y hy => ?_)
    rw [mem2]
    refine X25519LadderBit.write32_out (band_disj hv ?_ he.2 (by decide) hy)
    have := he.1; have := he.2; simp only [LFRAME, lvSwap] at *; omega
  -- selects
  refine selsAt_w hv hcode hWr hPO hSel sels o2 u2 (by decide) (by decide) hs2 (by omega) (by omega)
    (by omega) (by rw [pc2, ← ho2, Nat.add_assoc]) hb2
    (fun _ => by rw [hr7]; exact mask_ok hx) ?_
  intro u3 pc3 E3 r73
  have hb3 := E3.body hb2
  -- the rest
  refine opsAt_w hv hcode hWr hPO ladderRest o3 u3
    (fun p hp => ⟨hW _ (nonsel_of (by decide) p hp), nonsel_of (by decide) p hp⟩) (by decide)
    hs3 (by omega) (by omega) hend (by rw [pc3, ho3]) hb3 ?_
  intro t pc4 E4
  have hbt := E4.body hb3
  have hKt : ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c sX2) (sK - sX2) y →
      t.mem y = u2.mem y := fun y h1 h2 =>
    (opsEff_keep hv (lo := sX2) (hi := sK) (by decide) E4 (by decide) y h1 h2).trans
      (opsEff_keep hv (lo := sX2) (hi := sK) (by decide) E3 (by decide) y h1 h2)
  refine k t pc4 hbt ⟨?_, ?_, ?_⟩
  · -- slot values
    have V1 := opsEff_val hv (u2.regs 7) E1 (by decide) (nonsel_of (by decide))
    have V3 := (selsEff_val hv E3 (by decide) (by decide)).1
    have V4 := opsEff_val hv (u2.regs 7) E4 (by decide) (nonsel_of (by decide))
    simp only [OpsVal, ladderOps1, sels, ladderRest, Op.step, add, sub, sel, mul, sqr, mulc,
      Fn.rel, Option.getD_some] at V1 V3 V4
    obtain ⟨τ1, ⟨r1, k1⟩, τ2, ⟨r2, k2⟩, τ3, ⟨r3, k3⟩, τ4, ⟨r4, k4⟩, e1⟩ := V1
    obtain ⟨σ1, ⟨q1, j1⟩, σ2, ⟨q2, j2⟩, e3⟩ := V3
    obtain ⟨ρ1, ⟨p1, i1⟩, ρ2, ⟨p2, i2⟩, ρ3, ⟨p3, i3⟩, ρ4, ⟨p4, i4⟩, ρ5, ⟨p5, i5⟩,
      ρ6, ⟨p6, i6⟩, ρ7, ⟨p7, i7⟩, ρ8, ⟨p8, i8⟩, ρ9, ⟨p9, i9⟩, ρ10, ⟨p10, i10⟩,
      ρ11, ⟨p11, i11⟩, ρ12, ⟨p12, i12⟩, ρ13, ⟨p13, i13⟩, e4⟩ := V4
    subst e1 e3 e4
    rw [hr7, mask_if hx] at q1 q2
    refine ⟨τ1 sA, τ2 sB, τ3 sC, env c u1.mem sD, σ1 sX2, env c u3.mem sZ2, ρ1 sD, ρ2 sC,
      ρ3 sX3, ρ5 sZ3, ρ6 sZ3, ρ8 sA, ρ9 sB, ρ11 sA, ρ12 sC, ?_⟩
    simp (disch := decide) only [k1, k2, k3, k4, hbr, j1, j2, i1, i2, i3, i4, i5, i6, i7, i8,
      i9, i10, i11, i12, i13] at r1 r2 r3 r4 q1 q2 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 ⊢
    exact ⟨r1, r2, r3, r4, q1, q2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩
  · -- swap word
    have e : swWord c t.mem = swWord c u2.mem := read32_congr' fun y h =>
      hKt y (band_frame hv (by decide) h) (band_disj hv (by decide) (by decide) (by decide) h)
    rw [e, ← hbit1]
    show read32 u2.mem (slotAt c lvSwap) = _
    rw [mem2, M0Crypto.Armv6M.read32_write32_same]
    rfl
  · -- other frame bytes
    intro y h1 h2 h3
    rw [hKt y h1 h2, mem2, X25519LadderBit.write32_out h3]
    exact hK1 y h1 h2

end M0Crypto.Release.X25519LadderStep
