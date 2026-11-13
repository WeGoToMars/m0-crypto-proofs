import M0Crypto.Release.X25519FeSteps
import M0Crypto.Release.X25519MulcEnds

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
The contract of `m0c_fe_sqr`:
`X25519Routines.SqrSpec feSqr feSqrSize`.

The routine (`X25519Macros.feSqrList`) is `body` followed by `pop {pc}`. `body_runs` runs the
body as one block (`Runs`) over the same 37-slot frame as `m0c_fe_mul` (`X25519FeSteps`):
`L = aL^2` into slots 0-7, `H = aH^2` into slots 8-15, `|aL - aH|` into slots 24-27, its square
into slots 16-23 and `r0`, `r1`, then `combine_reduce` (always subtracting) writes `dst`. The
value is `X25519Kara.cross_sq` and `kara_split`; `combineReduce_exec` gives the congruence.
-/

namespace M0Crypto.Release.X25519FeSqr
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region)
open M0Crypto.Release.Frame (Disj InFrame toNat_add_ofNat sub_ofNat_toNat)
open M0Crypto.Release.X25519Block
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519Comb (coff cregs)
open M0Crypto.Release.X25519Macros (sl SFRAME SP_ SH SPP SDA SN SDST SA sqr128 diff256
  combineReduce feSqrList feSqr_at feSqr_size)
open M0Crypto.Release.X25519Mul128 (opv lt128)
open M0Crypto.Release.X25519Slot (ld)
open M0Crypto.Release.X25519W4 (w4 mask w4_lt)
open M0Crypto.Release.X25519FeCommon
open M0Crypto.Release.X25519FeSteps
open M0Crypto.Release.X25519CR (YOk NOk CRPost pval combineReduce_acc combineReduce_exec)
open M0Crypto.Release.X25519Routines (Call Pre Post SqrSpec feVal mulFrame)
open M0Crypto.Thumb.ReleaseCheck.X25519 (feSqr feSqrSize)
open M0Crypto.Release.X25519MulcFacts (pop_at inReg inReg1 region_ne reachW_runUntil)
open M0Crypto.Release.X25519MulcEnds (pop_run_w)

/-- The routine's writes: its stack bytes and `dst`. -/
abbrev Wr (c : Call) : Word → Prop := fun y => Region (fp c) mulFrame y ∨ Region c.dst 32 y

/-- The routine without its last instruction, `pop {pc}`. -/
def body : List Instr :=
  .push 0 true :: .subSp (BitVec.ofNat 7 SFRAME) :: .strSp 0 (sl SDST) :: .strSp 1 (sl SA) ::
  (sqr128 SP_ false ++ (.ldrSp 1 (sl SA) :: .addImm8 1 16 ::
  (sqr128 SH false ++ (diff256 SA SDA ++ (.addRdSp 1 (sl SDA) ::
  (sqr128 SPP true ++ (combineReduce true ++ [.addSp (BitVec.ofNat 7 SFRAME)])))))))

theorem split : feSqrList = body ++ [.pop 0 true] := by
  simp only [feSqrList, body, List.append_assoc, List.cons_append, List.nil_append]

/-- The state before `pop {pc}`. -/
def Out (c : Call) (t : State) : Prop :=
  t.regs 13 = c.sp0 - 4#32 ∧ read32 t.mem (c.sp0 - 4#32) = c.regs0 14 ∧
    X25519Congr.ModP (feVal t.mem c.dst : Int) ((feVal c.m0 c.a : Int) * feVal c.m0 c.a) ∧
    ∀ y, ¬ Region (fp c) mulFrame y → ¬ Region c.dst 32 y → t.mem y = c.m0 y

theorem body_runs (c : Call) (s : State) (hp : Pre feSqr feSqrSize mulFrame false c s) :
    Runs (AccOk (Wr c)) body s (Out c) := by
  have hlo := hp.spLo
  have h4 := hp.sp4
  have hfit := fp_fits c hlo
  have hP := fp_al c h4 hlo
  have wS : ∀ k q, k < 37 → q < 4 → Wr c (slot (fp c) k + BitVec.ofNat 32 q) :=
    fun k q hk hq => Or.inl (wr_slot c hk hq)
  have wB : ∀ k j, 4 * k + j < 148 → Wr c (slot (fp c) k + BitVec.ofNat 32 j) :=
    fun k j h => Or.inl (by rw [slot_byte]; exact wr_fp c h)
  have aS : Disj c.a 32 (fp c) (4 * 37) := hp.aS
  have tS : ∀ k, k < 37 → (slot (fp c) k).toNat = (fp c).toNat + 4 * k :=
    fun k hk => toNat_add_ofNat _ _ (by omega)
  have tA : (c.a + BitVec.ofNat 32 16).toNat = c.a.toNat + 16 :=
    toNat_add_ofNat _ _ (by have := aS.1; omega)
  -- disjointness from the frame
  have DS : ∀ {p : Word} {n : Nat} (k : Nat), k + 8 ≤ 37 → p.toNat + n ≤ 2 ^ 32 →
      (p.toNat + n ≤ (fp c).toNat ∨ (fp c).toNat + 148 ≤ p.toNat) → Disj p n (slot (fp c) k) 32 :=
    fun k hk h1 h2 => by unfold Disj; rw [tS k (by omega)]; omega
  have DF : ∀ {p : Word} {n : Nat}, p.toNat + n ≤ 2 ^ 32 →
      (p.toNat + n ≤ (fp c).toNat ∨ (fp c).toNat + 148 ≤ p.toNat) → Disj p n (fp c) (4 * 37) :=
    fun h1 h2 => by unfold Disj; omega
  have aS' := aS.2.2; have aS1 := aS.1
  -- push {lr}; sub sp, #144; str r0, r1
  refine enter_step c s (by rw [hp.regs, hp.sp]) hp.mem h4 hlo (fun y h => Or.inl h)
    fun s2 sp2 fr2 o2 => ?_
  refine str_step s2 0 (k := SDST) (by decide) sp2 fr2 hP (fun q hq => wS _ _ (by decide) hq)
    fun s3 sp3 fr3 o3 => ?_
  refine str_step s3 1 (k := SA) (by decide) sp3 fr3 hP (fun q hq => wS _ _ (by decide) hq)
    fun s5 sp5 fr5 o5 => ?_
  have e0 : s2.reg 0 = c.dst := by
    show s2.regs 0 = _; rw [o2 0 (by decide) (by decide), hp.regs, hp.r0]
  have e1 : s3.reg 1 = c.a := by
    show s3.regs 1 = _; rw [o3 1 (by decide), o2 1 (by decide) (by decide), hp.regs, hp.r1]
  have a5 : s5.regs 1 = c.a := by rw [o5 1 (by decide)]; exact e1
  have lr : s.regs 14 = c.regs0 14 := by rw [hp.regs]
  rw [e0, e1, lr] at fr5
  generalize hF5 : upd (upd (upd (fun i => read32 c.m0 (slot (fp c) i)) 36 [c.regs0 14]) SDST
    [c.dst]) SA [c.a] = F5 at fr5
  have f5 : F5 SDST = c.dst ∧ F5 SA = c.a ∧ F5 36 = c.regs0 14 := by
    subst hF5; simp [upd, SDST, SA]
  clear hF5
  -- L = aL^2
  refine sqr_step s5 false (k := SP_) (by decide) sp5 fr5 hP (by rw [a5]; exact hp.al.2.1)
    (by rw [a5]; exact DS _ (by decide) (by omega) (by omega))
    (fun j hj => wB _ _ (by simp only [SP_]; omega))
    fun s6 F6 l0 l1 sp6 fr6 ag6 f60 f61 fc6 v6 => ?_
  rw [a5, opv_frame fr5 (DF (n := 16) (by omega) (by omega))] at v6
  have hL : w8F F6 SP_ = opv c.m0 c.a * opv c.m0 c.a := by rw [w8F_lo f60 f61 fc6, v6]
  clear v6 fc6 f60 f61
  -- the high half
  refine ldr_step s6 1 (k := SA) (by decide) sp6 fr6 hP fun s7 sp7 fr7 r17 o7 => ?_
  refine cons (one _ s7 rfl rfl) fun s10 e10 => ?_
  have F6A : F6 SA = c.a := by rw [ag6 SA (.inr (by decide))]; exact f5.2.1
  have a10 : s10.regs 1 = c.a + BitVec.ofNat 32 16 := by
    rw [e10]
    show ((Instr.addImm8 1 16).next s7).regs (LowReg.toReg 1) = _
    have r17' : s7.regs 1 = c.a := r17.trans F6A
    rw [regs_addImm8_16]; exact congrArg (· + _) r17'
  have sp10 : s10.sp = fp c := by
    show s10.regs 13 = _
    rw [e10, X25519Mem.regs_addImm8 _ _ _ _ (by decide), if_neg (by decide)]; exact sp7
  have fr10 : FrameOk (fp c) 37 c.m0 F6 s10.mem := by rw [e10]; exact fr7
  clear e10 o7 r17 fr7 sp7
  -- H = aH^2
  refine sqr_step s10 false (k := SH) (by decide) sp10 fr10 hP
    (by rw [a10, tA]; have := hp.al.2.1; omega)
    (by rw [a10]; exact DS _ (by decide) (by rw [tA]; omega) (by rw [tA]; omega))
    (fun j hj => wB _ _ (by simp only [SH]; omega))
    fun s11 F11 h0 h1 sp11 fr11 ag11 f110 f111 fc11 v11 => ?_
  rw [a10, opv_frame fr10 (DF (p := c.a + BitVec.ofNat 32 16) (n := 16) (by rw [tA]; omega)
    (by rw [tA]; omega))] at v11
  have hH : w8F F11 SH = opv c.m0 (c.a + BitVec.ofNat 32 16) * opv c.m0 (c.a + BitVec.ofNat 32 16) := by
    rw [w8F_lo f110 f111 fc11, v11]
  clear v11 fc11 f110 f111
  have F11A : F11 SA = c.a := by rw [ag11 SA (.inr (by decide)), F6A]
  -- |aL - aH|
  refine diff_step s11 SA SDA (by decide) (by decide) sp11 fr11 hP (by rw [F11A]; exact hp.al.2.1)
    (fun j hj => wB _ _ (by simp only [SDA]; omega)) fun s12 sp12 fr12 d12 dv12 df12 => ?_
  rw [F11A, opv_frame fr11 (DF (p := c.a) (n := 16) (by omega) (by omega)),
    opv_frame fr11 (DF (p := c.a + BitVec.ofNat 32 16) (n := 16) (by rw [tA]; omega)
      (by rw [tA]; omega))] at d12 dv12
  -- add r1, sp, #SDA
  refine cons (one _ s12 rfl rfl) fun s13 e13 => ?_
  have r113 : s13.regs 1 = slot (fp c) SDA := by
    rw [e13, X25519Mem.regs_addRdSp _ _ _ _ (by decide), if_pos (show (1 : Reg) = LowReg.toReg 1 from rfl),
      sp12, sl_slot _ (by decide)]
  have sp13 : s13.sp = fp c := by
    show s13.regs 13 = _
    rw [e13, X25519Mem.regs_addRdSp _ _ _ _ (by decide), if_neg (by decide)]; exact sp12
  generalize hF13 : upd F11 SDA [s12.regs 4, s12.regs 5, s12.regs 6, s12.regs 7] = F13 at fr12
  have fr13 : FrameOk (fp c) 37 c.m0 F13 s13.mem := by rw [e13]; exact fr12
  have F13v : (∀ i, i < 16 ∨ (36 ≤ i) → F13 i = F11 i) ∧
      F13 SDA = s12.regs 4 ∧ F13 (SDA + 1) = s12.regs 5 ∧ F13 (SDA + 2) = s12.regs 6 ∧
      F13 (SDA + 3) = s12.regs 7 ∧ F13 SDST = F11 SDST := by
    subst hF13
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [upd_out _ _ (by simp [SDA]; omega)]
    · simp [upd, SDA, SDST]
  clear hF13 e13 fr11 fr12
  obtain ⟨F13o, fa0, fa1, fa2, fa3, F13D⟩ := F13v
  -- the middle square |aL - aH|^2
  refine sqr_step s13 true (k := SPP) (by decide) sp13 fr13 hP
    (by rw [r113, tS _ (by decide)]; simp only [SDA]; omega)
    (by rw [r113]; unfold Disj; rw [tS _ (by decide), tS _ (by decide)]; simp only [SDA, SPP]; omega)
    (fun j hj => wB _ _ (by simp only [SPP]; omega))
    fun s21 F21 p0 p1 sp21 fr21 ag21 f210 f211 fc21 v21 => ?_
  rw [r113, opv_slot fr13 (k := SDA) (by decide), fa0, fa1, fa2, fa3] at v21
  obtain ⟨q4, q5, q6, q7⟩ := w4F_hi fc21
  have hPv : pval s21 = w4 (s12.regs 4) (s12.regs 5) (s12.regs 6) (s12.regs 7) *
      w4 (s12.regs 4) (s12.regs 5) (s12.regs 6) (s12.regs 7) := by
    unfold pval X25519CR.fr
    rw [sp21, fr21.slots _ (by decide), fr21.slots _ (by decide), fr21.slots _ (by decide),
      fr21.slots _ (by decide), fr21.slots _ (by decide), fr21.slots _ (by decide), f210, f211,
      q4, q5, q6, q7, ← v21]
    unfold w4; omega
  clear v21 q4 q5 q6 q7 fc21 f210 f211
  have F21o : ∀ i, (i < 16 ∨ 36 ≤ i) → F21 i = F11 i := fun i hi => by
    rw [ag21 i (by simp only [SPP]; omega), F13o i hi]
  have hdst : X25519CR.fr s21.mem s21.sp SDST = c.dst := by
    unfold X25519CR.fr
    rw [sp21, fr21.slots _ (by decide), ag21 SDST (.inr (by decide)), F13D, ag11 SDST (.inr (by decide)),
      ag6 SDST (.inr (by decide))]
    exact f5.1
  have hL' : X25519CR.w8 s21.mem s21.sp SP_ = opv c.m0 c.a * opv c.m0 c.a := by
    rw [sp21, w8_eq fr21 (by decide), ← hL]
    exact w8F_congr fun i h1 h2 => by
      rw [F21o i (by simp only [SP_] at h2; omega), ag11 i (by simp only [SP_, SH] at h2 ⊢; omega)]
  have hH' : X25519CR.w8 s21.mem s21.sp SH =
      opv c.m0 (c.a + BitVec.ofNat 32 16) * opv c.m0 (c.a + BitVec.ofNat 32 16) := by
    rw [sp21, w8_eq fr21 (by decide), ← hH]
    exact w8F_congr fun i h1 h2 => F21o i (by simp only [SH] at h2; omega)
  -- the Karatsuba middle term
  have bAL := w4_lt (ld c.m0 c.a 0) (ld c.m0 c.a 1) (ld c.m0 c.a 2) (ld c.m0 c.a 3)
  have bAH := w4_lt (ld c.m0 (c.a + BitVec.ofNat 32 16) 0) (ld c.m0 (c.a + BitVec.ofNat 32 16) 1)
    (ld c.m0 (c.a + BitVec.ofNat 32 16) 2) (ld c.m0 (c.a + BitVec.ofNat 32 16) 3)
  change opv c.m0 c.a < 2 ^ 128 at bAL
  change opv c.m0 (c.a + BitVec.ofNat 32 16) < 2 ^ 128 at bAH
  have fa := feVal_halves c.m0 c.a
  generalize opv c.m0 c.a = AL at *
  generalize opv c.m0 (c.a + BitVec.ofNat 32 16) = AH at *
  generalize w4 (s12.regs 4) (s12.regs 5) (s12.regs 6) (s12.regs 7) = DA at *
  have kc := X25519Kara.cross_sq AL AH DA (if AL < AH then 1 else 0)
    (by by_cases h : AL < AH <;> simp [h] at dv12 ⊢ <;> exact dv12) (by split <;> omega)
  have l1 := lt128 bAL bAH; have l2 := lt128 bAH bAL
  have hN : NOk true s21 true := by simp [NOk]
  have hY : YOk s21 true (AL * AH + AH * AL) := by
    unfold YOk
    rw [hL', hH', hPv]
    refine ⟨?_, by omega⟩
    simp only [if_true]; omega
  have hD : Disj (X25519CR.fr s21.mem s21.sp SDST) 32 s21.sp (4 * (SH + 8)) := by
    rw [hdst, sp21]; have : Disj c.dst 32 (fp c) 148 := hp.dstS
    unfold Disj at this ⊢; simp only [SH] at this ⊢; omega
  -- combine_reduce
  refine Runs.append ⟨combineReduce_acc s21 true (by rw [sp21]; exact hP) (by rw [hdst]; exact hp.al.1)
    (fun j hj => by rw [sp21]; exact wB _ _ (by simp only [SH]; omega))
    (fun j hj => by
      rw [hdst]
      exact Or.inr (by
        show (c.dst + BitVec.ofNat 32 j - c.dst).toNat < 32
        rw [sub_ofNat_toNat _ _ (by omega)]; exact hj)), rfl⟩ fun t ht => ?_
  obtain ⟨g0, g1, g2, g3, o0, o1, o2, o3, o4, o5, o6, o7, tm, tv, tr⟩ :=
    combineReduce_exec s21 true _ _ hN hY hD
  subst ht
  generalize execAll (combineReduce true) s21 = t at tm tv tr ⊢
  rw [hL', hH'] at tv
  rw [hdst, sp21] at tm
  have frH := fr21.storeWords [g0, g1, g2, g3] (k := SH) (by simp [SH])
  -- add sp, #144
  refine cons (one _ t rfl rfl) fun u eu => ⟨accAll_nil _ _, ?_⟩
  have um : u.mem = t.mem := by rw [eu]; simp [Instr.next, Instr.exec, State.setReg, State.sp]
  have t13 : t.regs 13 = fp c := by rw [tr 13 (by decide) (by decide)]; exact sp21
  refine ⟨?_, ?_, ?_, fun y h1 h2 => ?_⟩
  · rw [eu]
    show ((Instr.addSp (BitVec.ofNat 7 SFRAME)).next t).regs 13 = _
    rw [regs_addSp _ _ _ (by decide), if_pos rfl, t13, fp_add]
  · rw [show execAll [] u = u from rfl, um, tm, ← slot36 c, read_store_disj _ (by
      have : Disj c.dst 32 (fp c) 148 := hp.dstS
      unfold Disj at this ⊢; rw [tS _ (by decide)]
      simp only [List.length_cons, List.length_nil]; omega), frH.slots _ (by decide),
      upd_out _ _ (by simp [SH]), F21o _ (by decide), ag11 _ (.inr (by decide)), ag6 _ (.inr (by decide))]
    exact f5.2.2
  · rw [show execAll [] u = u from rfl, um, tm, feVal_store8]
    have hn : AL * AL + 2 ^ 128 * (AL * AH + AH * AL) + 2 ^ 256 * (AH * AH) =
        feVal c.m0 c.a * feVal c.m0 c.a := by
      rw [fa, X25519Kara.kara_split]
    rw [hn] at tv
    have e : ((feVal c.m0 c.a * feVal c.m0 c.a : Nat) : Int) = (feVal c.m0 c.a : Int) * feVal c.m0 c.a := by
      push_cast; rfl
    rw [← e]; exact tv
  · rw [show execAll [] u = u from rfl, um, tm, store8_out _ (by simp) (hp.dstS.1) h2]
    exact frH.out y (not_inFrame c h1)

/-- The routine's code bytes, where every executed PC lies. -/
abbrev Pc (c : Call) : Word → Prop := Region (c.base + BitVec.ofNat 32 feSqr) feSqrSize

theorem body_at : seqAt B feSqr body = true ∧ seqAt B (feSqr + seqSize body) [.pop 0 true] = true := by
  have h := feSqr_at
  rw [split, seqAt_append, Bool.and_eq_true] at h
  exact h

theorem body_size : seqSize body + 2 = feSqrSize := by
  have h : seqSize [Instr.pop 0 true] = 2 := by decide
  rw [← feSqr_size, split, seqSize_append, h]

theorem body_falls : body.all Instr.falls = true := by decide +kernel

/-- `m0c_fe_sqr` from entry to its return, inside its code and writing only its frame and `dst`. -/
theorem run (c : Call) (s : State) (hp : Pre feSqr feSqrSize mulFrame false c s) :
    ReachW c.base (Pc c) (Wr c) s fun t => t.pc = c.ret ∧ Post mulFrame (fun a _ => a * a) c t := by
  have hb : c.base.toNat % 2 = 0 := by have := hp.base4; omega
  have hpc0 : s.pc = c.base + BitVec.ofNat 32 feSqr := by
    show s.regs 15 = _; rw [hp.regs, hp.pc]
  obtain ⟨hat, hpat⟩ := body_at
  have hsz := body_size
  have e0 : feSqr % 2 = 0 := by decide
  have e1 : feSqrSize % 2 = 0 := by decide
  have e2 : feSqr + feSqrSize < 2 ^ 32 := by decide
  refine ReachW.blockRuns hb body feSqr hpc0 e0 hat body_falls (body_runs c s hp)
    (inReg ⟨Nat.le_refl _, by omega, e2⟩) ?_
  intro x pcx hx
  obtain ⟨x13, xlr, xv, xm⟩ := hx
  obtain ⟨hpop, hpsz⟩ := pop_at hpat
  have sp_al : (c.sp0 - 4#32).toNat % 4 = 0 := by
    have h1 : mulFrame ≤ c.sp0.toNat := hp.spLo
    have h2 := hp.sp4
    simp only [mulFrame] at h1
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine pop_run_w hb hpop hpsz (by omega) pcx (inReg1 ⟨by omega, by omega, e2⟩)
    (by rw [x13]; exact sp_al) (by rw [x13, xlr]; exact hp.thumb) ?_
  intro t pct spt mt
  rw [x13, xlr] at pct
  exact ⟨pct, pct, by rw [spt, x13, BitVec.sub_add_cancel], by rw [mt]; exact xv,
    fun y h1 h2 => by rw [mt]; exact xm y h1 h2⟩

/-- `m0c_fe_sqr` meets its contract: `dst ≡ a * a (mod p)`, SP restored, writes only to its
stack frame and `dst`. -/
theorem sqr_spec : SqrSpec feSqr feSqrSize := by
  intro c s hp
  have hc : CodeAt s.mem c.base B := by rw [hp.mem]; exact hp.code
  refine reachW_runUntil hc ?_ hp.retOut (run c s hp)
  intro y hy i hi
  rw [B_len] at hi
  rcases hy with h | h
  · exact region_ne hp.codeS h i hi
  · exact region_ne hp.codeD h i hi

end M0Crypto.Release.X25519FeSqr
