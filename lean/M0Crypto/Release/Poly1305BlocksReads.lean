import M0Crypto.Release.AeadReadSites
import M0Crypto.Release.Poly1305BlocksCorrect
import M0Crypto.Release.Poly1305One

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Read bounds of the `m0c_poly1305_blocks` message loads

`RdP`-judgments for the block loop: every message load of a block reads the 16 bytes at the
message pointer, which the caller's hypothesis places in `Rd`. All other instructions of the
function sit at pcs without a read site.
-/

namespace M0Crypto.Release.Poly1305Blocks
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Aead (RdP SiteRd NoSite rdSiteB firstReadSite no_readSite polySiteB rdP_of_free inRegion_noSite pc_noSite)

/-- Instructions whose reads are single bytes at `r6 + k`, `k < 16`, or that read nothing. -/
def okR6 (i : Instr) : Bool :=
  match i with
  | .memImm op _ n imm => op == .ldrb && n == 6 && decide (imm.toNat < 16)
  | .lslImm .. => true
  | .dp .. => true
  | _ => false

theorem okR6_reads (i : Instr) (h : okR6 i = true) (x : State) (y : Word)
    (hy : Reads (i.accesses x) y) : ∃ o < 16, y = x.regs 6 + BitVec.ofNat 32 o := by
  cases i <;> simp [okR6] at h <;> simp [Instr.accesses, Reads] at hy
  obtain ⟨⟨rfl, rfl⟩, h2⟩ := h
  obtain ⟨_, k, hk, rfl⟩ := hy
  simp [MemOp.width] at hk
  subst hk
  exact ⟨_, h2, by simp [MemOp.width, M0Crypto.Armv6M.State.reg, BitVec.add_assoc]; rfl⟩

theorem trace_r6 : ∀ (is : List Instr) (u : State), is.all okR6 = true →
    is.all (fun i => !(i.dsts.contains 6)) = true →
    ∀ e ∈ traceAll is u, ∀ y, Reads e.accesses y → ∃ o < 16, y = u.regs 6 + BitVec.ofNat 32 o
  | [], _, _, _, e, he => by cases he
  | i :: is, u, h1, h2, e, he => by
    simp only [List.all_cons, Bool.and_eq_true] at h1 h2
    simp only [traceAll, List.mem_cons] at he
    rcases he with rfl | he
    · intro y hy; exact okR6_reads i h1.1 u y hy
    · have hd : (6 : Reg).val ∉ i.dsts := by
        have h := h2.1
        simp only [List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not] at h
        exact h
      have hr : (i.next u).regs 6 = u.regs 6 := next_regs_other u 6 (by decide) hd
      intro y hy
      obtain ⟨o, ho, e'⟩ := trace_r6 is (i.next u) h1.2 h2.2 e he y hy
      exact ⟨o, ho, by rw [e', hr]⟩

theorem loadU_eq : loadU = loadU.dropLast ++ [.addImm8 6 16] := by decide +kernel

theorem loadU_ok (base : Word) (Rd : Word → Prop) (u : State)
    (h : ∀ o < 16, Rd (u.regs 6 + BitVec.ofNat 32 o)) : BlockOk (RdP base Rd) loadU u := by
  have := (blockOk_events_iff (p := fun e => Aead.SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y)
    loadU u).mpr ?_
  · exact this
  intro e he _ y hy
  rw [loadU_eq, traceAll_append] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨o, ho, rfl⟩ := trace_r6 _ u (by decide +kernel) (by decide +kernel) e he y hy
    exact h o ho
  · simp [traceAll] at he
    subst he
    simp [Instr.accesses, Reads] at hy

theorem loadA_ok (base : Word) (Rd : Word → Prop) (u : State)
    (h : ∀ o < 16, Rd (u.regs 6 + BitVec.ofNat 32 o)) : BlockOk (RdP base Rd) loadA u := by
  have := (blockOk_events_iff (p := fun e => Aead.SiteRd base e.pc → ∀ y, Reads e.accesses y → Rd y)
    loadA u).mpr ?_
  · exact this
  intro e he _ y hy
  simp [loadA, traceAll] at he
  subst he
  obtain ⟨a, ha, _, k, hk, rfl⟩ := hy
  simp [Instr.accesses, wordAccesses, bitCount] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  have hl : (listRegs 15#8).length = 4 := by decide +kernel
  rw [hl] at hi
  dsimp only at hk
  have := h (4 * i + k) (by omega)
  have e6 : u.reg 6 = u.regs 6 := rfl
  show Rd (u.reg 6 + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 k)
  rw [e6, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact this

/-- Program counters of the function that are not read sites. -/
abbrev FreePc (base : Word) : Word → Prop := fun pc => BlkPc base pc ∧ Aead.NoSite base pc

theorem freeP (base : Word) (Rd : Word → Prop) :
    ∀ x e, RegionWrites (FreePc base) (fun _ => True) x e → RdP base Rd x e :=
  fun x e h => rdP_of_free (fun _ h => h.2) x e h

theorem free_region {base : Word} {off n : Nat} (h1 : entryAt ≤ off) (h2 : off + n ≤ popAt + 2)
    (hs : firstReadSite off n = none) : InRegion (FreePc base) base off n :=
  inRegion_noSite (Pc := BlkPc base) (fun _ h => h) h1 h2 (by decide +kernel) (no_readSite hs)

theorem free_pc {base : Word} (off : Nat) (h1 : entryAt ≤ off) (h2 : off < popAt + 2)
    (hs : rdSiteB off = false) : FreePc base (base + BitVec.ofNat 32 off) :=
  pc_noSite (Pc := BlkPc base) (fun _ h => h) h1 h2 (by decide +kernel) hs

theorem load_run_r {base : Word} (hb : base.toNat % 4 = 0) (Rd : Word → Prop) (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hR : ∀ o < 16, Rd (read32 s.mem (slot (s.regs 13) slotMsg) + BitVec.ofNat 32 o)) :
    ReachS base (RdP base Rd) s (fun t => t = loadState s) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  refine ReachS.blockW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
    (free_region (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 hp (by decide)
    segments_at.1 (by decide) (stable_aligned _ _ (by decide) hs hc) (fun _ _ _ _ => trivial) ?_
  let t := execAll testAlign s
  have pt : t.pc = base + BitVec.ofNat 32 alignBrAt := by
    dsimp [t]; rw [execAll_pc _ _ (by decide), hp, ofNat_add_assoc]; rfl
  have tr : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 6 → r.val ≠ 15 → t.regs r = s.regs r := by
    intro r h4 h6 h15
    exact execAll_regs_other _ _ _ h15 (by simp [testAlign, Instr.dsts]; omega)
  have tz : t.z = ((t.regs 6).toNat % 4 == 0) := by
    rw [(test_regs s).2, and3_zero, (test_regs s).1]
  have t6 : t.regs 6 = read32 s.mem (slot (s.regs 13) slotMsg) := (test_regs s).1
  refine ReachS.bcondW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
    (free_pc alignBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 loadUAt 1
    (brImm8 alignBrAt loadUAt) pt (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro hT
    have hz : t.z = false := by
      have h := hT; simp [condPassed] at h; exact h
    have hna : ¬ (t.regs 6).toNat % 4 = 0 := by
      rw [tz] at hz; simpa using hz
    let u := t.setReg 15 (base + BitVec.ofNat 32 loadUAt)
    have u6 : u.regs 6 = t.regs 6 := setReg_regs_ne _ 15 6 _ (by decide)
    refine ReachS.block hb2 loadU loadUAt u (by rfl) (by decide) segments_at.2.2.1 (by decide)
      (stable_aligned _ _ (by decide)
        (by simpa [u, M0Crypto.Armv6M.State.setReg, tr 13 (by decide) (by decide) (by decide)] using hs)
        (by simpa [u, M0Crypto.Armv6M.State.setReg, tr 7 (by decide) (by decide) (by decide)] using hc))
      (loadU_ok base Rd u (by rw [u6, t6]; exact hR)) ?_
    apply ReachS.done
    simp only [loadState, show execAll testAlign s = t from rfl, hna, ite_false]
    congr 2
    rw [hp, BitVec.add_assoc]; rfl
  · intro hF
    have hz : t.z = true := by
      have h := hF; simp [condPassed] at h; exact h
    have ha : (t.regs 6).toNat % 4 = 0 := by
      rw [tz] at hz; simpa using hz
    let u := t.setReg 15 (base + BitVec.ofNat 32 loadAAt)
    have u6 : u.regs 6 = t.regs 6 := setReg_regs_ne _ 15 6 _ (by decide)
    refine ReachS.block hb2 loadA loadAAt u (by rfl) (by decide) segments_at.2.1 (by decide) ?_
      (loadA_ok base Rd u (by rw [u6, t6]; exact hR)) ?_
    · have ha' : (t.regs (LowReg.toReg 6)).toNat % 4 = 0 := ha
      simp (config := { decide := true }) [bitCount, listRegs, List.range_succ, alignedAll, loadA, Instr.accesses, wordAccesses, List.range_succ, bitCount,
        Access.aligned, M0Crypto.Armv6M.State.reg, M0Crypto.Armv6M.State.setReg, u, BitVec.toNat_add]
      omega
    let v := execAll loadA u
    have pv : v.pc = base + BitVec.ofNat 32 skipBrAt := by
      dsimp [v]; rw [execAll_pc _ _ (by decide)]; change base + _ + _ = _
      rw [ofNat_add_assoc]; exact pc_congr (by decide +kernel)
    refine ReachS.bW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
      (free_pc skipBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 bodyAt
      (brImm11 skipBrAt bodyAt) pv (by decide) (by decide) (by decide) (by decide) ?_
    apply ReachS.done
    simp only [loadState, show execAll testAlign s = t from rfl, ha, ite_true]
    dsimp [v, u]
    rw [hp, BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem body_run_r {base : Word} (hb : base.toNat % 4 = 0) (Rd : Word → Prop) (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 bodyAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0) :
    ReachS base (RdP base Rd) s (fun t => t = execAll body s) :=
  ReachS.blockW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
    (free_region (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by omega) hp
    (by decide +kernel) segments_at.2.2.2.1 body_falls (stable_aligned body s body_stable hs hc)
    (fun _ _ _ _ => trivial) (ReachS.done rfl)

theorem one_run_r {base : Word} (hb : base.toNat % 4 = 0) (Rd : Word → Prop) (s : State)
    (hp : s.pc = base + BitVec.ofNat 32 testAt)
    (hs : (s.regs 13).toNat % 4 = 0) (hc : (s.regs 7).toNat % 4 = 0)
    (hR : ∀ o < 16, Rd (mp s + BitVec.ofNat 32 o)) :
    ReachS base (RdP base Rd) s (fun t => t = oneBlock s) := by
  apply ReachS.bind
  apply (load_run_r hb Rd s hp hs hc hR).mono (fun _ _ h => h)
  intro t ht; subst t
  obtain ⟨l7, _, l13, _⟩ := load_props s
  have lp : (loadState s).pc = base + BitVec.ofNat 32 bodyAt := by
    rw [load_pc, hp, ofNat_add_assoc]; rfl
  apply ReachS.bind
  apply (body_run_r hb Rd _ lp (by rw [l13]; exact hs) (by rw [l7]; exact hc)).mono (fun _ _ h => h)
  intro t ht; subst t
  have bsp := (body_regs (loadState s)).2.2.trans l13
  refine ReachS.blockW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
    (free_region (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by omega) ?_
    (by decide +kernel) segments_at.2.2.2.2.1 (by decide)
    (stable_aligned _ _ (by decide) (by rw [bsp]; exact hs)
      (by rw [(body_regs _).1, l7]; exact hc))
    (fun _ _ _ _ => trivial) (ReachS.done rfl)
  rw [execAll_pc _ _ body_falls, lp, ofNat_add_assoc]; exact pc_congr (by decide +kernel)

theorem loop_run_r {base : Word} (hb : base.toNat % 4 = 0) (Rd : Word → Prop) :
    ∀ (n : Nat), 0 < n → n < 2^32 → ∀ s : State,
    s.pc = base + BitVec.ofNat 32 testAt →
    (s.regs 13).toNat % 4 = 0 → (s.regs 7).toNat % 4 = 0 →
    read32 s.mem (slot (s.regs 13) slotCount) = BitVec.ofNat 32 n →
    (∀ o < 16 * n, Rd (mp s + BitVec.ofNat 32 o)) →
    ReachS base (RdP base Rd) s (fun t => t = loopState base n s ∧
      t.pc = base + BitVec.ofNat 32 publishAt ∧ t.regs 7 = s.regs 7 ∧
      t.regs 12 = s.regs 12 ∧ t.regs 13 = s.regs 13 ∧
      read32 t.mem (slot (s.regs 13) slotCount) = 0#32)
  | 0, hn, _, _, _, _, _, _, _ => by omega
  | n+1, _, hn, s, hp, hs, hc, hcount, hR => by
    have hb2 : base.toNat % 2 = 0 := by omega
    apply ReachS.bind
    apply (one_run_r hb Rd s hp hs hc (fun o ho => hR o (by omega))).mono (fun _ _ h => h)
    intro t ht; subst t
    obtain ⟨r7, r12, r13, pc, count, z⟩ := one_props s
    have pc' : (oneBlock s).pc = base + BitVec.ofNat 32 countBrAt := by
      rw [pc, hp, ofNat_add_assoc]; rfl
    have sub : BitVec.ofNat 32 (n+1) - 1#32 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    have c' : read32 (oneBlock s).mem (slot (s.regs 13) slotCount) = BitVec.ofNat 32 n := by
      rw [count, hcount, sub]
    have z' : (oneBlock s).z = (BitVec.ofNat 32 n == 0#32) := by
      rw [z, hcount, sub]
    refine ReachS.bcondW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
      (free_pc countBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 publishAt 0
      (brImm8 countBrAt publishAt) pc' (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) ?_ ?_
    · intro hT
      have n0 : n = 0 := by
        have hz : BitVec.ofNat 32 n = 0#32 := by simpa [condPassed, z'] using hT
        have := congrArg BitVec.toNat hz; simp at this; omega
      apply ReachS.done
      refine ⟨by simp [loopState, n0], rfl, ?_, ?_, ?_, ?_⟩
      · simpa [M0Crypto.Armv6M.State.setReg] using r7
      · simpa [M0Crypto.Armv6M.State.setReg] using r12
      · simpa [M0Crypto.Armv6M.State.setReg] using r13
      · simpa [n0] using c'
    · intro hF
      have nn : n ≠ 0 := by
        intro hz; simp [condPassed, z', hz] at hF
      let u := (oneBlock s).setReg 15 (base + BitVec.ofNat 32 (countBrAt + 2))
      refine ReachS.bW (Pn := FreePc base) (Wr := fun _ => True) (freeP base Rd)
        (free_pc backBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 testAt
        (brImm11 backBrAt testAt) (by rfl) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) ?_
      let v := u.setReg 15 (base + BitVec.ofNat 32 testAt)
      have v7 : v.regs 7 = s.regs 7 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r7
      have v12 : v.regs 12 = s.regs 12 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r12
      have v13 : v.regs 13 = s.regs 13 := by simpa [v, u, M0Crypto.Armv6M.State.setReg] using r13
      have vc : read32 v.mem (slot (v.regs 13) slotCount) = BitVec.ofNat 32 n := by rw [v13]; exact c'
      have vmp : mp v = mp s + 16#32 := by
        rw [← one_mp]
        simp only [mp, v, u, M0Crypto.Armv6M.State.setReg, v13, r13]
        rfl
      have hR2 : ∀ o < 16 * n, Rd (mp v + BitVec.ofNat 32 o) := by
        intro o ho
        have h := hR (16 + o) (by omega)
        have e : mp s + 16#32 + BitVec.ofNat 32 o = mp s + BitVec.ofNat 32 (16 + o) := by
          rw [BitVec.add_assoc, BitVec.ofNat_add]
        rw [vmp, e]; exact h
      apply (loop_run_r hb Rd n (by omega) (by omega) v rfl (by rw [v13]; exact hs)
        (by rw [v7]; exact hc) vc hR2).mono (fun _ _ h => h)
      intro t ht
      obtain ⟨eq, pt, t7, t12, t13, tc⟩ := ht
      refine ⟨?_, pt, t7.trans v7, t12.trans v12, t13.trans v13, ?_⟩
      · rw [eq, loopState, ite_eq_right nn]
        change loopState base n (((oneBlock s).setReg 15 _).setReg 15 _) = _
        rw [setPc_twice]
      · rw [← v13]; exact tc

attribute [local irreducible] body loadState oneBlock loopState

theorem blocks_reach_r (c : BCtx) (hv : BValid c) (Rd : Word → Prop) (s : State) (he : BEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hR : ∀ o < 16 * c.count.toNat, Rd (c.msg + BitVec.ofNat 32 o)) :
    ReachS c.base (RdP c.base Rd) s (BResult c s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hn : ∀ pc, FreePc c.base pc → ¬ Aead.SiteRd c.base pc := fun _ h => h.2
  have rg : ∀ {off n : Nat}, entryAt ≤ off → off + n ≤ popAt + 2 →
      firstReadSite off n = none → InRegion (FreePc c.base) c.base off n :=
    fun h1 h2 hs => free_region h1 h2 hs
  apply ReachS.bind
  apply ((prologue_run_g c (Pn := FreePc c.base)
    (rg (by decide +kernel) (by decide +kernel) (by decide +kernel)) hv s he).toRd hn).mono
    (fun _ _ h => h)
  intro p hp; subst p
  let p := execAll prologue s
  obtain ⟨pm, ps, p0, p1, p2, p3, pz⟩ := prologue_effect c s he
  have pp : p.pc = c.base + BitVec.ofNat 32 enterBrAt := by
    dsimp [p]; rw [execAll_pc _ _ (by decide)]
    change s.pc + _ = _
    have entrypc : s.pc = c.base + BitVec.ofNat 32 entryAt := by show s.regs 15 = _; rw [he.regs, he.pc]
    rw [entrypc, ofNat_add_assoc]; rfl
  change p.z = (c.count == 0#32) at pz
  have pmS : Saved c p.mem := by rw [pm]; exact mP_saved c hv
  refine ReachS.bcondW (Pn := FreePc c.base) (Wr := fun _ => True) (freeP c.base Rd)
    (free_pc enterBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 setupAt 1
    (brImm8 enterBrAt setupAt) pp (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro hn'
    have hzf : p.z = false := by
      have h := hn'; simp [condPassed] at h; exact h
    have cn : c.count ≠ 0#32 := by rw [pz] at hzf; simpa using hzf
    let q := p.setReg 15 (c.base + BitVec.ofNat 32 setupAt)
    have qs : q.regs 13 = c.fp := ps
    have q0 : q.regs 0 = c.ctx := p0
    have q1 : q.regs 1 = c.msg := p1
    have q2 : q.regs 2 = c.count := p2
    apply ReachS.bind
    apply ((setup_run_g (Pn := FreePc c.base) (Wr := fun _ => True)
      (rg (by decide +kernel) (by decide +kernel) (by decide +kernel)) hv.base4 q rfl
      (by rw [qs]; exact fp4 hv) (by rw [q0]; exact hv.ctx4) (fun _ _ => trivial)).toRd hn).mono
      (fun _ _ h => h)
    intro u hu; subst u
    let u := execAll setup q
    obtain ⟨u7, u12, us, um⟩ := setup_effect q
    have us' : u.regs 13 = c.fp := us.trans qs
    have u7' : u.regs 7 = c.ctx := u7.trans q0
    have up : u.pc = c.base + BitVec.ofNat 32 testAt := by
      dsimp [u]; rw [execAll_pc _ _ (by decide)]; change (c.base + _) + _ = _
      rw [ofNat_add_assoc]; rfl
    have uc : read32 u.mem (slot (u.regs 13) slotCount) = BitVec.ofNat 32 c.count.toNat := by
      rw [us, um, M0Crypto.Armv6M.read32_write32_same, q2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have umsg : mp u = c.msg := by
      rw [mp, us, um, M0Crypto.Armv6M.read32_write32_slot _ _ _ slotCount slotMsg (by decide) (by decide),
        ite_eq_right (by decide), M0Crypto.Armv6M.read32_write32_same, q1]
    have uS : Saved c u.mem := setup_saved c q qs pmS
    apply ReachS.bind
    apply (loop_run_r hv.base4 Rd c.count.toNat (by have := c.count.isLt; have hz := cn; bv_omega)
      c.count.isLt u up (by rw [us']; exact fp4 hv) (by rw [u7']; exact hv.ctx4) uc
      (by rw [umsg]; exact hR)).mono (fun _ _ h => h)
    intro v hv'
    obtain ⟨veq, vp, v7, v12, vs, _⟩ := hv'
    have vs' : v.regs 13 = c.fp := vs.trans us'
    have v7' : v.regs 7 = c.ctx := v7.trans u7'
    have vS : Saved c v.mem := by rw [veq]; exact loop_saved c _ u us' uS
    apply ReachS.bind
    apply ((publish_run_g (Pn := FreePc c.base)
      (rg (by decide +kernel) (by decide +kernel) (by decide +kernel)) hv.base4 v vp
      (by rw [vs']; exact fp4 hv) (by rw [v7']; exact hv.ctx4)).toRd hn).mono (fun _ _ h => h)
    intro w hw; subst w
    have wp : (execAll publish v).pc = c.base + BitVec.ofNat 32 epilogueAt := by
      rw [execAll_pc _ _ (by decide), vp, ofNat_add_assoc]; exact pc_congr (by decide +kernel)
    apply ((blocks_ret_g c hv (Pn := FreePc c.base) (fun _ => True) _
      (rg (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (free_pc popAt (by decide +kernel) (by decide +kernel) (by decide +kernel))
      wp ((publish_effect v).2.2.trans vs')
      (publish_saved c hv v vs' v7' vS) hlr).toRd hn).mono (fun _ _ h => h)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
    · intro r hr
      rw [ht.2.2.2.1 r hr]
      change _ = (afterBlocks c s).regs r
      rw [afterBlocks, ite_eq_right cn]
      change _ = (execAll publish (loopState c.base c.count.toNat u)).regs r
      rw [veq]
    · rw [ht.2.2.2.2, afterBlocks, ite_eq_right cn]
      change _ = (execAll publish (loopState c.base c.count.toNat u)).mem
      rw [veq]
  · intro hz
    have hzt : p.z = true := by
      have h := hz; simp [condPassed] at h; exact h
    have cz : c.count = 0#32 := by rw [pz] at hzt; simpa using hzt
    let q := p.setReg 15 (c.base + BitVec.ofNat 32 retBrAt)
    refine ReachS.bW (Pn := FreePc c.base) (Wr := fun _ => True) (freeP c.base Rd)
      (free_pc retBrAt (by decide +kernel) (by decide +kernel) (by decide +kernel)) hb2 epilogueAt
      (brImm11 retBrAt epilogueAt) (by rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) ?_
    let u := q.setReg 15 (c.base + BitVec.ofNat 32 epilogueAt)
    apply ((blocks_ret_g c hv (Pn := FreePc c.base) (fun _ => True) u
      (rg (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (free_pc popAt (by decide +kernel) (by decide +kernel) (by decide +kernel))
      rfl ps pmS hlr).toRd hn).mono (fun _ _ h => h)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
    · intro r hr
      rw [ht.2.2.2.1 r hr, afterBlocks, ite_eq_left cz]
      have hr15 : r ≠ 15 := by
        intro h
        have hv15 : r.val = 15 := congrArg Fin.val h
        omega
      change (((p.setReg 15 _).setReg 15 _).regs r) = p.regs r
      rw [setReg_regs_ne _ 15 r _ hr15, setReg_regs_ne _ 15 r _ hr15]
    · rw [ht.2.2.2.2, afterBlocks, ite_eq_left cz]
      rfl

end M0Crypto.Release.Poly1305Blocks
