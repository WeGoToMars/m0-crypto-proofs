import M0Crypto.Release.X25519OpRun

set_option linter.unusedSectionVars false

/-!
Slot values through runs of operations (plan `x25519-proofs.md`, phase 9).

`env c m e` is the field value of the slot at frame offset `e`. `Op.step` is what one operation
does to these values: the destination is related to the operands by `Fn.rel` and every other
slot keeps its value. `OpsVal` chains steps over a list; `opsEff_val` and `selsEff_val` obtain it
from the memory-level `OpsEff`. `opsEff_keep` keeps the frame bytes outside a band of slots, and
`selsAt_w` runs a list of `select` operations, which keep their mask.
-/

namespace M0Crypto.Release.X25519SlotEnv
open M0Crypto.Armv6M (Word State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW Region B)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun

/-! ## Bytes of the frame -/

/-- A field value depends only on its 32 bytes. -/
theorem feVal_congr {m m' : Mem} {a : Word} (h : ∀ y, Region a 32 y → m y = m' y) :
    feVal m a = feVal m' a := by
  unfold feVal
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have e : read32 m (a + BitVec.ofNat 32 (4 * i)) = read32 m' (a + BitVec.ofNat 32 (4 * i)) :=
    Frame.read32_congr (m := m') (m' := m) fun k hk => h _ (by
      show (a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k - a).toNat < 32
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := a.isLt
      omega)
  rw [e]

/-- A word depends only on its four bytes. -/
theorem read32_congr' {m m' : Mem} {a : Word} (h : ∀ y, Region a 4 y → m y = m' y) :
    read32 m a = read32 m' a :=
  Frame.read32_congr (m := m') (m' := m) fun k hk => h _ (by
    show (a + BitVec.ofNat 32 k - a).toNat < 4
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    omega)

/-- A band `[i, i + n)` of the frame inside the band `[j, j + m)`. -/
theorem band_sub {c : X25519.Ctx} (hv : X25519.Valid c) {i n j m : Nat} (hj : j ≤ i)
    (hin : i + n ≤ j + m) (hm : j + m ≤ LFRAME) {y : Word} (h : Region (slotAt c i) n y) :
    Region (slotAt c j) m y := by
  have ei := E_add hv (d := i) (by simp only [LFRAME, SAVED] at *; omega)
  have ej := E_add hv (d := j) (by simp only [LFRAME, SAVED] at *; omega)
  have eT := E_add hv (d := LFRAME + SAVED) (Nat.le_refl _)
  have := (E c + BitVec.ofNat 32 (LFRAME + SAVED)).isLt
  simp only [slotAt, LFRAME, SAVED] at *
  exact region_sub (by omega) (by omega) (by omega) h

/-- Disjoint bands of the frame. -/
theorem band_disj {c : X25519.Ctx} (hv : X25519.Valid c) {i n j m : Nat}
    (hd : i + n ≤ j ∨ j + m ≤ i) (hi : i + n ≤ LFRAME) (hj : j + m ≤ LFRAME) {y : Word}
    (h : Region (slotAt c i) n y) : ¬ Region (slotAt c j) m y := by
  have ei := E_add hv (d := i) (by simp only [LFRAME, SAVED] at *; omega)
  have ej := E_add hv (d := j) (by simp only [LFRAME, SAVED] at *; omega)
  have eT := E_add hv (d := LFRAME + SAVED) (Nat.le_refl _)
  have := (E c + BitVec.ofNat 32 (LFRAME + SAVED)).isLt
  simp only [slotAt, LFRAME, SAVED] at *
  rw [region_iff (by omega), ei] at h
  rw [region_iff (by omega), ej]
  omega

/-- A band of the frame is in the frame. -/
theorem band_frame {c : X25519.Ctx} (hv : X25519.Valid c) {i n : Nat} (hi : i + n ≤ LFRAME)
    {y : Word} (h : Region (slotAt c i) n y) : Region (E c) LFRAME y := by
  have := band_sub hv (j := 0) (m := LFRAME) (Nat.zero_le _) (by omega) (Nat.le_refl _) h
  simpa [slotAt] using this

/-! ## Slot values -/

/-- The value of the slot at frame offset `e`. -/
def env (c : X25519.Ctx) (m : Mem) (e : Nat) : Int := feVal m (slotAt c e)

/-- One operation on slot values, with mask `w` for `select`. -/
def _root_.M0Crypto.Release.X25519EntryCode.Op.step (p : Op) (w : Word) (σ τ : Nat → Int) : Prop :=
  p.fn.rel w (τ p.d) (σ p.a) (σ (p.b.getD p.a)) ∧ ∀ e, SlotOk e → e ≠ p.d → τ e = σ e

/-- Steps over a list of operations, with one mask. -/
def OpsVal (w : Word) : List Op → (Nat → Int) → (Nat → Int) → Prop
  | [], σ, υ => υ = σ
  | p :: ps, σ, υ => ∃ τ, p.step w σ τ ∧ OpsVal w ps τ υ

theorem OpsVal.append {w : Word} : ∀ {xs ys : List Op} {σ τ υ : Nat → Int},
    OpsVal w xs σ τ → OpsVal w ys τ υ → OpsVal w (xs ++ ys) σ υ
  | [], _, _, _, _, h1, h2 => by
    simp only [OpsVal] at h1; subst h1; exact h2
  | _ :: _, _, _, _, _, ⟨τ', h, h1⟩, h2 => ⟨τ', h, OpsVal.append h1 h2⟩

theorem eff_step {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} {p : Op} {s t : State}
    (h : Eff c m1 p s t) (hok : p.ok = true) :
    p.step (s.regs 7) (env c s.mem) (env c t.mem) := by
  obtain ⟨hd, -, -, hbn⟩ := ok_parts hok
  refine ⟨?_, fun e he hne => ?_⟩
  · have hv' := h.val
    obtain ⟨fn, d, a, b⟩ := p
    cases b with
    | some b =>
      have e1 : env c t.mem d = feVal t.mem (slotAt c d) := rfl
      have e2 : env c s.mem a = feVal s.mem (slotAt c a) := rfl
      have e3 : env c s.mem ((some b).getD a) = feVal s.mem (bAddr (E c) (s.regs 2) (some b)) := rfl
      simp only at hv' ⊢
      rw [e1, e2, e3]; exact hv'
    | none =>
      have := hbn rfl
      simp only at this; subst this
      have e1 : env c t.mem d = feVal t.mem (slotAt c d) := rfl
      have e2 : env c s.mem a = feVal s.mem (slotAt c a) := rfl
      simp only [Fn.rel] at hv' ⊢
      rw [e1, e2]; exact hv'
  · unfold env
    congr 1
    refine feVal_congr fun y hy => h.keep y (band_frame hv he.2 hy) (band_disj hv ?_ he.2 hd.2 hy)
    have := he.1; have := hd.1
    omega

/-- The relation of a function other than `select` does not depend on the mask. -/
theorem rel_mask {fn : Fn} (h : fn ≠ .sel) {m w : Word} {x a b : Int} (hr : fn.rel m x a b) :
    fn.rel w x a b := by
  cases fn
  case sel => exact absurd rfl h
  all_goals exact hr

theorem opsEff_val {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (w : Word) :
    ∀ {ops : List Op} {s t : State}, OpsEff c m1 ops s t → ops.all Op.ok = true →
    (∀ p ∈ ops, p.fn ≠ .sel) → OpsVal w ops (env c s.mem) (env c t.mem)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons (p := p) he hr, hok, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have := eff_step hv he hok.1
    exact ⟨_, ⟨rel_mask (hs p List.mem_cons_self) this.1, this.2⟩,
      opsEff_val hv w hr hok.2 fun q hq => hs q (List.mem_cons_of_mem _ hq)⟩

theorem selsEff_val {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} :
    ∀ {ops : List Op} {s t : State}, OpsEff c m1 ops s t → ops.all Op.ok = true →
    (∀ p ∈ ops, p.fn = .sel) →
    OpsVal (s.regs 7) ops (env c s.mem) (env c t.mem) ∧ t.regs 7 = s.regs 7
  | _, _, _, .nil _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .cons (p := p) he hr, hok, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hm := he.mask (hs p List.mem_cons_self)
    obtain ⟨h1, h2⟩ := selsEff_val hv hr hok.2 fun q hq => hs q (List.mem_cons_of_mem _ hq)
    rw [hm] at h1 h2
    exact ⟨⟨_, eff_step hv he hok.1, h1⟩, h2⟩

/-- Operations writing only slots in the band `[lo, hi)` keep the other frame bytes. -/
theorem opsEff_keep {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} {lo hi : Nat}
    (hhi : hi ≤ LFRAME) :
    ∀ {ops : List Op} {s t : State}, OpsEff c m1 ops s t →
    (∀ p ∈ ops, lo ≤ p.d ∧ p.d + 32 ≤ hi) →
    ∀ y, Region (E c) LFRAME y → ¬ Region (slotAt c lo) (hi - lo) y → t.mem y = s.mem y
  | _, _, _, .nil _, _, _, _, _ => rfl
  | _, _, _, .cons (p := p) he hr, hd, y, h1, h2 => by
    rw [opsEff_keep hv hhi hr (fun q hq => hd q (List.mem_cons_of_mem _ hq)) y h1 h2]
    have := hd p List.mem_cons_self
    exact he.keep y h1 fun h3 => h2 (band_sub hv this.1 (by omega) (by omega) h3)

theorem _root_.M0Crypto.Release.X25519OpRun.OpsEff.body {c : X25519.Ctx} {m1 : Mem} :
    ∀ {ops : List Op} {s t : State}, OpsEff c m1 ops s t → Body c m1 s → Body c m1 t
  | _, _, _, .nil _, h => h
  | _, _, _, .cons he hr, _ => M0Crypto.Release.X25519OpRun.OpsEff.body hr he.body

/-! ## Code of operation lists -/

theorem opsAt_append : ∀ (o : Nat) (xs ys : List Op),
    opsAt o (xs ++ ys) = opsAt o xs ++ opsAt (o + seqSize (opsAt o xs)) ys
  | o, [], ys => by simp [opsAt, seqSize]
  | o, p :: xs, ys => by
    simp only [List.cons_append, opsAt]
    rw [opsAt_append, seqSize_append, List.append_assoc, Nat.add_assoc]

/-- Every function other than `select`, from its five lemmas. -/
theorem nonsel_w (hAdd : OpW .add) (hSub : OpW .sub) : ∀ fn : Fn, fn ≠ .sel → OpW fn
  | .add, _ => hAdd
  | .sub, _ => hSub
  | .mul, _ => mul_opW
  | .sqr, _ => sqr_opW
  | .mulc, _ => mulc_opW
  | .sel, h => absurd rfl h

theorem nonsel_of {ops : List Op} (h : (ops.all fun p => p.fn != .sel) = true) :
    ∀ p ∈ ops, p.fn ≠ .sel := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simpa using this

/-- A list of `select` operations; the mask stays in `r7`. -/
theorem selsAt_w {c : X25519.Ctx} (hv : X25519.Valid c) {m1 : Mem} (hcode : CodeAt m1 c.base B)
    {Wr : Word → Prop} (hWr : ∀ y, Region c.fp X25519.stackBytes y → Wr y)
    {Pc : Word → Prop} {lo hi : Nat} (hPO : PcOk c.base lo hi Pc) {Q : State → Prop}
    (hSel : OpW .sel) :
    ∀ (ops : List Op) (o : Nat) (s : State), (∀ p ∈ ops, p.fn = .sel) →
    ops.all Op.ok = true →
    seqAt B o (opsAt o ops) = true → o % 2 = 0 → lo ≤ o →
    o + seqSize (opsAt o ops) ≤ hi →
    s.pc = c.base + BitVec.ofNat 32 o → Body c m1 s → MaskOk .sel s →
    (∀ t, t.pc = c.base + BitVec.ofNat 32 (o + seqSize (opsAt o ops)) → OpsEff c m1 ops s t →
      t.regs 7 = s.regs 7 → ReachW c.base Pc Wr t Q) →
    ReachW c.base Pc Wr s Q
  | [], o, s, _, _, _, _, _, _, hpc, _, _, k => k s (by simpa [opsAt, seqSize] using hpc) (.nil s) rfl
  | p :: ps, o, s, hW, hok, hseq, ho, hlo, hend, hpc, hs, hm, k => by
    obtain ⟨fn, d, a, b⟩ := p
    have hf : fn = .sel := hW _ List.mem_cons_self
    subst hf
    simp only [opsAt] at hseq hend k
    rw [seqAt_append, Bool.and_eq_true] at hseq
    rw [seqSize_append] at hend
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have h1 : o + seqSize (opAt o ⟨.sel, d, a, b⟩) ≤ hi := by omega
    refine hSel hv hcode hWr hPO hseq.1 ho hlo h1 hpc hs hok.1 hm ?_
    intro u upc ue
    have he := seqSize_even (opAt o ⟨.sel, d, a, b⟩)
    have hr7 : u.regs 7 = s.regs 7 := ue.mask rfl
    refine selsAt_w hv hcode hWr hPO hSel ps _ u (fun q hq => hW q (List.mem_cons_of_mem _ hq)) hok.2
      hseq.2 (by omega) (by omega) (by omega) upc ue.body (fun h => by rw [hr7]; exact hm h)
      fun t tpc te tr => k t ?_ (.cons ue te) (tr.trans hr7)
    rw [tpc, seqSize_append, Nat.add_assoc]

end M0Crypto.Release.X25519SlotEnv
