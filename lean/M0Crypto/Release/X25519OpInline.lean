import M0Crypto.Release.X25519OpRun
import M0Crypto.Release.X25519InlAdd
import M0Crypto.Release.X25519InlSub
import M0Crypto.Release.X25519InlSel

set_option linter.unusedSimpArgs false

/-!
The three inline slot operations of `m0c_x25519` (plan `x25519-proofs.md`, phase 9): `OpW .add`,
`OpW .sub` and `OpW .sel`.

`InlRun fn bd` is the shape of an inline body lemma: run from any site with `r0 = dst`,
`r1 = a`, `r2 = b`, relate `dst` to the operands by `fn.rel`, write only `dst`, keep `sp` and,
for `select`, the mask. `inl_opW` runs the operand prefix `opPre` and then the body, at any
operation placed in the entry; the three instances come from the `X25519Inl` run lemmas.
-/

namespace M0Crypto.Release.X25519OpInline
open M0Crypto.Armv6M (Word Reg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region B)
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.X25519Block (Runs Runs.reg)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519Op
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519OpRun

/-- An inline body run at any site, `r0 = dst`, `r1 = a`, `r2 = b`. -/
def InlRun (fn : Fn) (bd : List Instr) : Prop :=
  ∀ {base : Word} (_ : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {t : State} {off : Nat}
    {dst a b : Word},
    seqAt B off bd = true → off % 2 = 0 → t.pc = base + BitVec.ofNat 32 off →
    InRegion Pc base off (seqSize bd) → t.regs 0 = dst → t.regs 1 = a → t.regs 2 = b →
    MaskOk fn t → dst.toNat % 4 = 0 → a.toNat % 4 = 0 → b.toNat % 4 = 0 →
    dst.toNat + 32 ≤ 2 ^ 32 → (a = dst ∨ Disj a 32 dst 32) → (b = dst ∨ Disj b 32 dst 32) →
    (∀ j < 32, Wr (dst + BitVec.ofNat 32 j)) → ∀ {Q : State → Prop},
    (∀ t', t'.pc = base + BitVec.ofNat 32 (off + seqSize bd) →
      fn.rel (t.regs 7) (feVal t'.mem dst) (feVal t.mem a) (feVal t.mem b) →
      (∀ y, ¬ Region dst 32 y → t'.mem y = t.mem y) →
      t'.regs 13 = t.regs 13 → (fn = .sel → t'.regs 7 = t.regs 7) →
      ReachW base Pc Wr t' Q) →
    ReachW base Pc Wr t Q

theorem add_inl : InlRun .add X25519Inl.feAddBody := by
  intro base hb Pc Wr t off dst a b hseq ho hpc hr h0 h1 h2 _ hd ha hbb hf _ _ hW Q k
  exact X25519Inl.feAdd_run_w hb hseq ho hpc hr h0 h1 h2 hd ha hbb hf hW fun t' p v m r =>
    k t' p v m (r 13 (by decide) (by decide)) fun h => nomatch h

theorem sub_inl : InlRun .sub X25519Inl.feSubBody := by
  intro base hb Pc Wr t off dst a b hseq ho hpc hr h0 h1 h2 _ hd ha hbb hf _ _ hW Q k
  exact X25519Inl.feSub_run_w hb hseq ho hpc hr h0 h1 h2 hd ha hbb hf hW fun t' p v m r =>
    k t' p v m (r 13 (by decide) (by decide)) fun h => nomatch h

theorem sel_inl : InlRun .sel X25519Inl.selBody := by
  intro base hb Pc Wr t off dst a b hseq ho hpc hr h0 h1 h2 hm hd ha hbb hf hda hdb hW Q k
  exact X25519Inl.sel_run_w hb hseq ho hpc hr h0 h1 h2 (hm rfl) hd ha hbb hf hda hdb hW
    fun t' p v m r => k t' p (by show ((feVal t'.mem dst : Nat) : Int) = _; rw [v]; split <;> rfl) m
      (r 13 (by decide) (by decide)) fun _ => r 7 (by decide) (by decide)

/-- An inline operation placed in the entry has its effect. -/
theorem inl_opW {fn : Fn} {bd : List Instr} (hrun : InlRun fn bd)
    (hat : ∀ o d a b, opAt o ⟨fn, d, a, b⟩ = opPre d a b ++ bd) (hfn : fn ≠ .sqr) : OpW fn := by
  intro c hv m1 hcode Wr hWr Pc lo hi hPO s Q o d a b hseq ho hlo hend hpc hs hok hmk k
  have hb0 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨hd, ha, hb, hbn⟩ := ok_parts hok
  obtain ⟨x, rfl⟩ : ∃ x, b = some x := by
    cases b with
    | some x => exact ⟨x, rfl⟩
    | none => exact absurd (hbn rfl) hfn
  have hx := hb x rfl
  rw [hat] at hseq hend k
  rw [seqAt_append, Bool.and_eq_true] at hseq
  obtain ⟨hP, hBd⟩ := hseq
  rw [seqSize_append] at hend k
  have hendS := Nat.le_trans hend hPO.hile
  have hxl := hPO.xlo
  have hE := E_toNat hv
  have hF := fp_toNat hv
  have hsp := hv.spLo
  have hs4 := hv.sp4
  have hsl := size_lt
  have hev := opPre_even d a (some x)
  have hps := opPre_size d a (some x)
  have hbe : seqSize bd % 2 = 0 := seqSize_even bd
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hx1, hx2⟩ := hx
  simp only [X25519.stackBytes, X25519.wipeBytes, SAVED, LFRAME, CALLEE, Disj] at *
  have hdd : d % 4 = 0 ∧ d < 1024 := ⟨by omega, by omega⟩
  have haa : a % 4 = 0 ∧ a < 1024 := ⟨by omega, by omega⟩
  have hbb : ∀ y, some x = some y → y % 4 = 0 ∧ y < 1024 := fun y hy => by
    cases hy; exact ⟨by omega, by omega⟩
  have hreg := opPre_reg d a (some x)
  refine X25519Block.ReachW.blockRuns hb0 (opPre d a (some x)) o hpc ho hP (opPre_falls d a (some x))
    (Runs.reg (Q := fun u => u = execAll (opPre d a (some x)) s) hreg.1 hreg.2 rfl)
    (hPO.inE hlo (by omega)) ?_
  rintro u upc rfl
  obtain ⟨u0, u1, u2, um, ur⟩ := opPre_exec s d a (some x) hdd haa hbb
  have hsp' : s.sp = E c := hs.sp
  rw [hsp'] at u0 u1 u2
  have u13 : (execAll (opPre d a (some x)) s).regs 13 = E c := by
    rw [ur 13 (by decide) (by decide)]; exact hs.sp
  have u7 : (execAll (opPre d a (some x)) s).regs 7 = s.regs 7 := ur 7 (by decide) (by decide)
  generalize execAll (opPre d a (some x)) s = u at u0 u1 u2 um ur u13 u7 upc
  simp only [bAddr] at u2
  have eD : (E c + BitVec.ofNat 32 d).toNat = (E c).toNat + d :=
    E_add hv (by simp only [SAVED, LFRAME]; omega)
  have eA : (E c + BitVec.ofNat 32 a).toNat = (E c).toNat + a :=
    E_add hv (by simp only [SAVED, LFRAME]; omega)
  have eX : (E c + BitVec.ofNat 32 x).toNat = (E c).toNat + x :=
    E_add hv (by simp only [SAVED, LFRAME]; omega)
  have hD : ∀ y, Region (E c + BitVec.ofNat 32 d) 32 y → Region c.fp 480 y := fun y h =>
    region_sub (by omega) (by omega) (by omega) h
  have hRw : ∀ y, Region c.fp 480 y → Region c.fp 516 y := fun y h =>
    region_sub (by omega) (Nat.le_refl _) (by omega) h
  have hdis : ∀ z, z % 32 = 0 → z + 32 ≤ 332 → (E c + BitVec.ofNat 32 z).toNat = (E c).toNat + z →
      E c + BitVec.ofNat 32 z = E c + BitVec.ofNat 32 d ∨
        Disj (E c + BitVec.ofNat 32 z) 32 (E c + BitVec.ofNat 32 d) 32 := fun z h1 h2 ez => by
    by_cases e : z = d
    · exact Or.inl (by rw [e])
    · right; simp only [Disj]; omega
  have hW : ∀ j < 32, Wr (E c + BitVec.ofNat 32 d + BitVec.ofNat 32 j) := fun j hj =>
    hWr _ (hRw _ (hD _ (by
      have := Frame.toNat_add_ofNat (E c + BitVec.ofNat 32 d) j (by omega)
      rw [region_iff (by omega)]; omega)))
  refine hrun hb0 hBd (by omega) upc
    (hPO.inE (by omega) (by omega))
    u0 u1 u2 (fun h => by rw [u7]; exact hmk h) (by rw [eD]; omega) (by rw [eA]; omega)
    (by rw [eX]; omega) (by omega) (hdis a ha1 ha2 eA) (hdis x hx1 hx2 eX) hW ?_
  intro t tp tv tm t13 t7
  rw [Nat.add_assoc] at tp
  refine k t tp ⟨⟨by rw [t13, u13], fun y hy => ?_⟩, ?_, fun y _ hy => by rw [tm y hy, um],
    fun h => by rw [t7 h, u7]⟩
  · rw [tm y fun h => hy (hD y h), um]; exact hs.keep y hy
  · rw [u7, um] at tv; exact tv

theorem add_opW : OpW .add := inl_opW add_inl (fun _ _ _ _ => rfl) (by decide)
theorem sub_opW : OpW .sub := inl_opW sub_inl (fun _ _ _ _ => rfl) (by decide)
theorem sel_opW : OpW .sel := inl_opW sel_inl (fun _ _ _ _ => rfl) (by decide)

end M0Crypto.Release.X25519OpInline
