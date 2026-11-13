import M0Crypto.Release.X25519MulcFacts

set_option linter.unusedSimpArgs false

/-!
The contract of `m0c_fe_mulc_add`:
`X25519Routines.MulcAddSpec feMulcAdd feMulcAddSize`.

The run (`run`) chains the piece lemmas: `pre` (push, `r12 = dst`, the literal `60833`
read from the code bytes, `r6 = 0`), word 7 (`mulcWord 7 none 3 4 5`), `fold`, the seven
chain steps (`chain_step_w`), `fin` (word 7 stored) and `pop {pc}`. The value comes from
`X25519Reduce.mulc_add_nat`. `dst = a` or `dst = b` is covered by `Ok.dstA` / `Ok.dstB`
(`X25519MulcChain.read_src`).

Writes go to the pushed word and to `dst` only (`Wr`). The return address lies outside the
routine's bytes (`Pre.retOut`), which is where `reachW_runUntil` needs it: every executed
PC lies inside the routine (`Pc`).
-/

namespace M0Crypto.Release.X25519MulcAdd
open M0Crypto.Armv6M (Word Reg LowReg State Mem addWithCarry read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region)
open M0Crypto.Release.Frame (Disj InFrame toNat_add_ofNat sub_ofNat_toNat)
open M0Crypto.Release.X25519Frame (FrameOk upd slot_byte)
open M0Crypto.Release.X25519MulcWord (wAddr kVal mulcWord_run_w)
open M0Crypto.Release.X25519MulcStep (sAddr)
open M0Crypto.Release.X25519MulcEnds (pre_run_w fold_run_w fin_run_w pop_run_w)
open M0Crypto.Release.X25519MulcChain
open M0Crypto.Release.X25519MulcFacts
open M0Crypto.Release.X25519Routines (Call Pre Post MulcAddSpec feVal mulcFrame)
open M0Crypto.Release.X25519Carry (adc_nat)
open M0Crypto.Thumb.ReleaseCheck.X25519 (feMulcAdd feMulcAddSize)

/-- The routine's PCs. -/
abbrev Pc (c : Call) : Word → Prop := Region (c.base + BitVec.ofNat 32 feMulcAdd) feMulcAddSize

/-- The routine's writes: the pushed word and `dst`. -/
abbrev Wr (c : Call) : Word → Prop := fun y => Region (c.fp mulcFrame) mulcFrame y ∨ Region c.dst 32 y

/-- Memory after `push {lr}`. -/
abbrev m1 (c : Call) : Mem := write32 c.m0 (c.sp0 - 4#32) (c.regs0 14)

/-- The chain's data. -/
def ctx (c : Call) (r8 : Word) : Ctx := ⟨c.dst, c.a, c.b, c.m0, m1 c, r8, c.sp0 - 4#32⟩

section
variable {c : Call} {s : State} (hp : Pre feMulcAdd feMulcAddSize mulcFrame true c s)
include hp

theorem ctx_ok (r8 : Word) : Ok (ctx c r8) where
  a4 := hp.al.2.1
  b4 := hp.al.2.2 rfl
  dst4 := hp.al.1
  fits := hp.codeD.2.1
  dstA := hp.dstA
  dstB := hp.dstB rfl
  ra := fun _ hi => read32_write32_disj _ _ (disj_slot hp.aS hi)
  rb := fun _ hi => read32_write32_disj _ _ (disj_slot (hp.bS rfl) hi)

omit hp in
theorem wr_dst : ∀ i < 8, ∀ q < 4, Wr c (slot c.dst i + BitVec.ofNat 32 q) := fun i hi q hq =>
  Or.inr (by
    show ((slot c.dst i + BitVec.ofNat 32 q) - c.dst).toNat < 32
    rw [slot_byte, sub_ofNat_toNat _ _ (by omega)]; omega)

omit hp in
theorem wr_push : ∀ q < 4, Wr c (c.sp0 - 4#32 + BitVec.ofNat 32 q) := fun q hq =>
  Or.inl (by
    show ((c.sp0 - 4#32 + BitVec.ofNat 32 q) - (c.sp0 - 4#32)).toNat < 4
    rw [sub_ofNat_toNat _ _ (by omega)]; exact hq)

theorem wr_code : ∀ y, Wr c y → ∀ i < B.length, y ≠ c.base + BitVec.ofNat 32 i := by
  intro y hy i hi
  rw [B_len] at hi
  rcases hy with h | h
  · exact region_ne hp.codeS h i hi
  · exact region_ne hp.codeD h i hi

theorem sp_al : (c.sp0 - 4#32).toNat % 4 = 0 := by
  have h1 : 4 ≤ c.sp0.toNat := hp.spLo
  have h2 := hp.sp4
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit hp in
/-- Bytes outside the pushed word and `dst` keep their entry values. -/
theorem post_mem {F : Nat → Word} {m : Mem} (h : FrameOk c.dst 8 (m1 c) F m) (y : Word)
    (h1 : ¬ Region (c.fp mulcFrame) mulcFrame y) (h2 : ¬ Region c.dst 32 y) : m y = c.m0 y := by
  have hf : ¬ InFrame c.dst 8 y := fun ⟨o, ho, e⟩ => h2 (by
    subst e
    show (c.dst + BitVec.ofNat 32 o - c.dst).toNat < 32
    rw [sub_ofNat_toNat _ _ (by omega)]; omega)
  rw [h.out y hf]
  apply M0Crypto.Armv6M.write32_other
  intro k hk e
  apply h1
  subst e
  show (c.sp0 - 4#32 + BitVec.ofNat 32 k - (c.sp0 - 4#32)).toNat < 4
  rw [sub_ofNat_toNat _ _ (by omega)]; exact hk

/-- The pushed word still holds the entry `lr`. -/
theorem ret_word {F : Nat → Word} {m : Mem} (h : FrameOk c.dst 8 (m1 c) F m) :
    read32 m (c.sp0 - 4#32) = c.regs0 14 := by
  have hd : Disj c.dst 32 (c.sp0 - 4#32) 4 := hp.dstS
  obtain ⟨d1, d2, d3⟩ := hd
  have ho : ∀ q < 4, ¬ InFrame c.dst 8 (c.sp0 - 4#32 + BitVec.ofNat 32 q) := fun q hq ⟨o, ho, e⟩ => by
    have := congrArg BitVec.toNat e
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
    omega
  rw [h.read_out ho]
  exact M0Crypto.Armv6M.read32_write32_same _ _ _

end

/-- The final value: `dst` after the store of word 7. -/
theorem fin_val {dst : Word} {m1 m : Mem} {F : Nat → Word} {V : Word}
    (h : FrameOk dst 8 m1 (upd F 7 [V]) m) :
    feVal m dst = psum (fun i => (F i).toNat) 7 + 2 ^ 224 * V.toNat := by
  rw [feVal_psum]
  have e : ∀ i < 8, (read32 m (slot dst i)).toNat = (upd F 7 [V] i).toNat := fun i hi => by
    rw [h.slots i hi]
  rw [psum_congr e]
  show psum _ 7 + 2 ^ 224 * _ = _
  have e7 : psum (fun i => (upd F 7 [V] i).toNat) 7 = psum (fun i => (F i).toNat) 7 :=
    psum_congr fun i hi => by
      simp only [upd, List.length_singleton]; rw [ite_eq_right_iff.mpr (fun h => by omega)]
  rw [e7]
  simp [upd]

/-- The routine's run, as a `ReachW` judgment over its own PCs. -/
theorem run (c : Call) (s : State) (hp : Pre feMulcAdd feMulcAddSize mulcFrame true c s) :
    ReachW c.base (Pc c) (Wr c) s fun t =>
      t.pc = c.ret ∧ Post mulcFrame (fun a b => 121666 * a + b) c t := by
  have hb : c.base.toNat % 2 = 0 := by have := hp.base4; omega
  obtain ⟨cPre, cW, cFold, s0, s1, s2, s3, s4, s5, s6, cFin, cPop⟩ := pieces
  have hpc0 : s.pc = c.base + BitVec.ofNat 32 feMulcAdd := by
    show s.regs 15 = _; rw [hp.regs, hp.pc]
  have h13 : s.regs 13 = c.sp0 := by rw [hp.regs, hp.sp]
  obtain ⟨lv, la⟩ := lit_val (sp := c.sp0) (c.regs0 14) hp.code hp.base4 hp.codeS
  -- push {lr}; mov r12, r0; ldr r7, =60833; movs r6, #0
  refine pre_run_w hb cPre (by decide) hpc0 (inReg (by decide)) (by rw [h13]; exact hp.sp4)
    (fun q hq => by rw [h13]; exact wr_push q hq) la ?_
  intro x1 pc1 m1e r13 r12 r6 r7 o1
  have em1 : x1.mem = m1 c := by rw [m1e, hp.mem, h13, hp.regs]; rfl
  have r7' : x1.reg 7 = 60833#32 := by rw [r7, hp.mem, h13, hp.regs]; exact lv
  have e1 : x1.reg 1 = c.a := by
    show x1.regs 1 = c.a
    rw [o1 1 (by decide) (by decide) (by decide) (by decide) (by decide), hp.regs, hp.r1]
  have e2 : x1.reg 2 = c.b := by
    show x1.regs 2 = c.b
    rw [o1 2 (by decide) (by decide) (by decide) (by decide) (by decide), hp.regs, hp.r2 rfl]
  have e12 : x1.regs 12 = c.dst := by rw [r12, hp.regs, hp.r0]
  have e13 : x1.regs 13 = c.sp0 - 4#32 := by rw [r13, h13]
  -- word 7
  refine mulcWord_run_w hb (by unfold X25519MulcWord.Dist; decide)
    (show X25519MulcWord.KOk 3 4 5 none from trivial) cW (by decide) pc1
    (inReg (by decide)) (by rw [e1]; exact hp.al.2.1) (by rw [e2]; exact hp.al.2.2 rfl) r6 r7' ?_
  intro x2 pc2 v2 m2 o2
  have ra : ∀ i < 8, read32 (m1 c) (slot c.a i) = read32 c.m0 (slot c.a i) := (ctx_ok hp 0#32).ra
  have rb : ∀ i < 8, read32 (m1 c) (slot c.b i) = read32 c.m0 (slot c.b i) := (ctx_ok hp 0#32).rb
  have hk : kVal x1 none = 0 := rfl
  rw [wAddr_slot x1 1 7 (by omega), wAddr_slot x1 2 7 (by omega), e1, e2, em1, hk, Nat.add_zero,
    ra 7 (by omega), rb 7 (by omega)] at v2
  have hA7 := (read32 c.m0 (slot c.a 7)).isLt
  have hB7 := (read32 c.m0 (slot c.b 7)).isLt
  have hh : (x2.reg 3).toNat < 2 ^ 26 := by omega
  -- fold
  refine fold_run_w hb cFold (by decide) pc2 (inReg (by decide)) hh ?_
  intro x3 pc3 v3 v8 m3 o3
  have k1 : x3.reg 1 = c.a := by
    show x3.regs 1 = c.a
    rw [o3 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 1 (by decide) (by decide) (by decide) (by decide)]; exact e1
  have k2 : x3.reg 2 = c.b := by
    show x3.regs 2 = c.b
    rw [o3 2 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 2 (by decide) (by decide) (by decide) (by decide)]; exact e2
  have k6 : x3.reg 6 = 0#32 := by
    show x3.regs 6 = 0#32
    rw [o3 6 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 6 (by decide) (by decide) (by decide) (by decide)]; exact r6
  have k7 : x3.reg 7 = 60833#32 := by
    show x3.regs 7 = 60833#32
    rw [o3 7 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 7 (by decide) (by decide) (by decide) (by decide)]; exact r7'
  have k12 : x3.regs 12 = c.dst := by
    rw [o3 12 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 12 (by decide) (by decide) (by decide) (by decide)]; exact e12
  have k13 : x3.regs 13 = c.sp0 - 4#32 := by
    rw [o3 13 (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 13 (by decide) (by decide) (by decide) (by decide)]; exact e13
  have hc := ctx_ok hp (x3.regs 8)
  have i0 : Inv (ctx c (x3.regs 8)) (x3.reg 3).toNat 0 3 x3 :=
    ⟨k1, k2, k6, k7, rfl, k12, k13, fun i => read32 (m1 c) (slot c.dst i),
      ⟨by have := hp.codeD.2.1; show c.dst.toNat + 4 * 8 ≤ 2 ^ 32; omega, fun i _ => by rw [m3, m2, em1]; rfl,
        fun y _ => by rw [m3, m2, em1]; rfl⟩,
      fun _ _ _ => rfl, by simp [psum]⟩
  -- the chain, words 0 to 6
  have hd30 : X25519MulcStep.SDist 3 0 := by unfold X25519MulcStep.SDist; decide
  have hd03 : X25519MulcStep.SDist 0 3 := by unfold X25519MulcStep.SDist; decide
  refine chain_step_w hb hc hd30 (by decide) s0 (by decide) pc3 (inReg (by decide)) (wr_dst) i0 ?_
  intro y1 p1 i1
  refine chain_step_w hb hc hd03 (by decide) s1 (by decide) p1 (inReg (by decide)) (wr_dst) i1 ?_
  intro y2 p2 i2
  refine chain_step_w hb hc hd30 (by decide) s2 (by decide) p2 (inReg (by decide)) (wr_dst) i2 ?_
  intro y3 p3 i3
  refine chain_step_w hb hc hd03 (by decide) s3 (by decide) p3 (inReg (by decide)) (wr_dst) i3 ?_
  intro y4 p4 i4
  refine chain_step_w hb hc hd30 (by decide) s4 (by decide) p4 (inReg (by decide)) (wr_dst) i4 ?_
  intro y5 p5 i5
  refine chain_step_w hb hc hd03 (by decide) s5 (by decide) p5 (inReg (by decide)) (wr_dst) i5 ?_
  intro y6 p6 i6
  refine chain_step_w hb hc hd30 (by decide) s6 (by decide) p6 (inReg (by decide)) (wr_dst) i6 ?_
  intro y p7 i7
  obtain ⟨-, -, -, -, r8, r12', r13', F, hF, -, hv⟩ := i7
  have sa : sAddr y 7 = slot c.dst 7 := by rw [sAddr_slot y 7 (by omega), r12']; rfl
  -- fin: word 7
  refine fin_run_w hb cFin (by decide) p7 (inReg (by decide)) (by rw [r12']; exact hp.al.1)
    (by rw [sa]; exact wr_dst 7 (by omega)) ?_
  intro x8 pc8 m8 o8
  have hF8 : FrameOk c.dst 8 (m1 c) (upd F 7 [(addWithCarry (y.regs 8) (y.reg 0) false).1]) x8.mem := by
    rw [m8, sa]; exact hF.write (by omega) _
  -- the value
  have fa : feVal c.m0 c.a = psum (ctx c (x3.regs 8)).A 8 := feVal_psum _ _
  have fb : feVal c.m0 c.b = psum (ctx c (x3.regs 8)).B 8 := feVal_psum _ _
  obtain ⟨pa1, pa2⟩ := psum8 (ctx c (x3.regs 8)).A (fun _ => BitVec.isLt _)
  obtain ⟨pb1, pb2⟩ := psum8 (ctx c (x3.regs 8)).B (fun _ => BitVec.isLt _)
  have hv' : psum (fun i => (F i).toNat) 7 + 2 ^ 224 * (y.reg 0).toNat =
      121666 * psum (ctx c (x3.regs 8)).A 7 + psum (ctx c (x3.regs 8)).B 7 + (x3.reg 3).toNat := hv
  have hm := X25519Reduce.mulc_add_nat (feVal c.m0 c.a) (feVal c.m0 c.b) (x2.reg 4).toNat
    (x2.reg 3).toNat (psum (fun i => (F i).toNat) 7) (y.reg 0).toNat (feVal_lt _ _) (feVal_lt _ _)
    (by rw [fa, fb, pa1, pb1]; exact v2) (by rw [fa, fb, pa2, pb2, ← v3]; exact hv')
    (psum_lt (fun _ => BitVec.isLt _) 7)
  have hV : (addWithCarry (y.regs 8) (y.reg 0) false).1.toNat = (x2.reg 4).toNat % 2 ^ 31 + (y.reg 0).toNat := by
    have ha := adc_nat (y.regs 8) (y.reg 0) false
    have e8 : (y.regs 8).toNat = (x2.reg 4).toNat % 2 ^ 31 := by rw [r8]; exact v8
    have := (addWithCarry (y.regs 8) (y.reg 0) false).1.isLt
    simp only [Bool.toNat_false, Nat.add_zero] at ha
    omega
  have fv := fin_val hF8
  rw [hV] at fv
  -- pop {pc}
  have x8sp : x8.regs 13 = c.sp0 - 4#32 := by
    rw [o8 13 (by decide) (by decide) (by decide)]; exact r13'
  have rw8 : read32 x8.mem (c.sp0 - 4#32) = c.regs0 14 := ret_word hp hF8
  obtain ⟨hat, hsz⟩ := pop_at cPop
  refine pop_run_w hb hat hsz (by decide) pc8 (inReg1 (by decide)) (by rw [x8sp]; exact sp_al hp)
    (by rw [x8sp, rw8]; exact hp.thumb) ?_
  intro t pct spt mt
  rw [x8sp, rw8] at pct
  refine ⟨pct, pct, by rw [spt, x8sp, BitVec.sub_add_cancel], ?_, fun y h1 h2 => by
    rw [mt]; exact post_mem hF8 y h1 h2⟩
  have e1 : ((121666 * feVal c.m0 c.a + feVal c.m0 c.b : Nat) : Int) =
      121666 * (feVal c.m0 c.a : Int) + (feVal c.m0 c.b : Int) := by omega
  show X25519Congr.ModP (feVal t.mem c.dst : Int) (121666 * (feVal c.m0 c.a : Int) + feVal c.m0 c.b)
  rw [mt, fv, ← e1]
  exact hm.2

/-- `m0c_fe_mulc_add` meets its contract: `dst ≡ 121666 * a + b (mod p)`, SP restored, writes
only to the pushed word and `dst`. -/
theorem mulcAdd_spec : MulcAddSpec feMulcAdd feMulcAddSize := by
  intro c s hp
  have hc : CodeAt s.mem c.base B := by rw [hp.mem]; exact hp.code
  exact reachW_runUntil hc (wr_code hp) hp.retOut (run c s hp)

end M0Crypto.Release.X25519MulcAdd
