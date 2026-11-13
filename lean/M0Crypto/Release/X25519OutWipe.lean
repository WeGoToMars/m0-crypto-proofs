import M0Crypto.Release.X25519OpRun

set_option linter.unusedSimpArgs false

/-!
The stack wipe of `m0c_x25519`.

`wipe` is `sub sp, #CALLEE; movs r1-r5, #0; add r0, sp, #0` and `(LFRAME + CALLEE) / 20`
copies of `stm r0!, {r1-r5}` (`X25519EntryCode.wipe`). `zeros_run_w` runs `n` copies of the
`stm` by induction on `n`: the `20 n` bytes from `r0` become zero and nothing else is written.
`wipe_run_w` is the whole segment, generic in its SP: the `wipeBytes` bytes from
`SP - CALLEE` are zero afterwards.
-/

namespace M0Crypto.Release.X25519OutWipe
open M0Crypto.Armv6M (Word Reg LowReg State Mem write32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region B)
open M0Crypto.Release.Frame (toNat_add_ofNat)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode
open M0Crypto.Release.X25519Block (AccAll AccOk accAll_cons accAll_nil wordAccesses_ok)

/-! ## Zero stores -/

/-- A zero word store zeroes its four bytes. -/
theorem write32_zero (m : Mem) (a y : Word) :
    write32 m a 0#32 y = if Region a 4 y then 0#8 else m y := by
  have hr : Region a 4 y ↔ (y = a ∨ y = a + 1#32 ∨ y = a + 2#32 ∨ y = a + 3#32) := by
    show (y - a).toNat < 4 ↔ _
    constructor <;> intro h <;> bv_omega
  by_cases h : Region a 4 y
  · simp only [h, ite_true]
    rcases hr.mp h with e | e | e | e <;> simp [write32, e]
  · simp only [h, ite_false]
    have := mt hr.mpr h
    simp only [not_or] at this
    simp [write32, this.1, this.2.1, this.2.2.1, this.2.2.2]

/-- `Region a (4 + n) y` splits at `a + 4`, when the bytes do not wrap. -/
theorem region_split {a y : Word} {k n : Nat} (h : a.toNat + k + n ≤ 2 ^ 32) :
    Region a (k + n) y ↔ Region a k y ∨ Region (a + BitVec.ofNat 32 k) n y := by
  by_cases hn : n = 0
  · subst hn; simp [Region]
  have ek : (a + BitVec.ofNat 32 k).toNat = a.toNat + k := toNat_add_ofNat _ _ (by omega)
  rw [X25519Op.region_iff (by omega), X25519Op.region_iff (by omega), X25519Op.region_iff (by omega), ek]
  omega

/-- `k` zero words from `a`. -/
theorem storeWords_zero : ∀ (k : Nat) (m : Mem) (a y : Word), a.toNat + 4 * k ≤ 2 ^ 32 →
    storeWords m a (List.replicate k 0#32) y = if Region a (4 * k) y then 0#8 else m y
  | 0, m, a, y, _ => by simp [storeWords, Region]
  | k + 1, m, a, y, h => by
    simp only [List.replicate_succ, storeWords]
    rw [storeWords_zero k _ _ _ (by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; have := (a + 4#32).isLt; omega
      · rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, toNat_add_ofNat _ _ (by omega)]; omega),
      write32_zero, show 4 * (k + 1) = 4 + 4 * k by omega]
    have hs := region_split (a := a) (y := y) (k := 4) (n := 4 * k) (by omega)
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl]
    by_cases h1 : Region (a + BitVec.ofNat 32 4) (4 * k) y <;> by_cases h2 : Region a 4 y <;>
      simp only [h1, h2, hs, or_true, true_or, or_false, ite_true, ite_false]

/-! ## `stm r0!, {r1-r5}` repeated -/

/-- One wipe store. -/
abbrev stmZ : Instr := .stm 0 0x3e

theorem listRegs_3e : listRegs (0x3e : BitVec 8) = [1, 2, 3, 4, 5] := by decide

theorem listRegs_62 : listRegs 62#8 = [1, 2, 3, 4, 5] := by decide

theorem bitCount_62 : bitCount 62#8 = 5 := by decide

theorem bitCount_3e : bitCount (0x3e : BitVec 8) = 5 := by decide

/-- Registers `r1`-`r5`. -/
def Z5 (s : State) : Prop := ∀ r : Reg, 1 ≤ r.val → r.val ≤ 5 → s.regs r = 0#32

theorem stmZ_exec (s : State) (hz : Z5 s) :
    (stmZ.next s).mem = storeWords s.mem (s.regs 0) (List.replicate 5 0#32) ∧
      (stmZ.next s).regs 0 = s.regs 0 + BitVec.ofNat 32 20 ∧
      (∀ r : Reg, r ≠ 0 → r.val ≠ 15 → (stmZ.next s).regs r = s.regs r) ∧
      (stmZ.next s).pc = s.pc + BitVec.ofNat 32 stmZ.size := by
  have z1 := hz 1 (by decide) (by decide)
  have z2 := hz 2 (by decide) (by decide)
  have z3 := hz 3 (by decide) (by decide)
  have z4 := hz 4 (by decide) (by decide)
  have z5 := hz 5 (by decide) (by decide)
  refine ⟨?_, ?_, fun r h0 h15 => ?_, ?_⟩
  · simp [Instr.next, Instr.exec, listRegs_3e, listRegs_62, State.setReg, State.reg, LowReg.toReg]
    refine congrArg _ ?_
    simp only [List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> first | rfl | exact hz _ (by decide) (by decide)
  · simp [Instr.next, Instr.exec, bitCount_3e, bitCount_62, State.setReg, State.reg, X25519Mem.toReg0]
  · have h15' : r ≠ 15 := fun e => h15 (by rw [e]; rfl)
    simp [Instr.next, Instr.exec, State.setReg, X25519Mem.toReg0, h0, h15']
  · exact execAll_pc [stmZ] s rfl

theorem replicate_falls (n : Nat) : (List.replicate n stmZ).all Instr.falls = true := by
  simp [List.all_replicate, Instr.falls]

/-- **The wipe stores**, by induction on the count: `n` copies of `stm r0!, {r1-r5}` with
`r1`-`r5` zero and `r0 = a` zero the `20 n` bytes from `a`, write nothing else, advance `r0`
by `20 n` and change no other register. -/
theorem zeros_run_w {base : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {Q : State → Prop} :
    ∀ (n off : Nat) (s : State) (a : Word), seqAt B off (List.replicate n stmZ) = true →
    off % 2 = 0 → s.pc = base + BitVec.ofNat 32 off → s.regs 0 = a → a.toNat % 4 = 0 →
    a.toNat + 20 * n < 2 ^ 32 → Z5 s → (∀ y, Region a (20 * n) y → Wr y) →
    InRegion Pc base off (seqSize (List.replicate n stmZ)) →
    (∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize (List.replicate n stmZ)) →
      t.regs 0 = a + BitVec.ofNat 32 (20 * n) →
      (∀ r : Reg, r ≠ 0 → r.val ≠ 15 → t.regs r = s.regs r) →
      (∀ y, Region a (20 * n) y → t.mem y = 0#8) →
      (∀ y, ¬ Region a (20 * n) y → t.mem y = s.mem y) →
      ReachW base Pc Wr t Q) →
    ReachW base Pc Wr s Q
  | 0, off, s, a, _, _, hpc, h0, _, _, _, _, _, k =>
    k s (by simpa [seqSize] using hpc) (by simpa using h0) (fun _ _ _ => rfl)
      (fun y hy => absurd hy (by simp [Region])) (fun _ _ => rfl)
  | n + 1, off, s, a, hseq, ho, hpc, h0, ha, hn, hz, hw, hr, k => by
    rw [List.replicate_succ] at hseq hr k
    have hseq' : seqAt B off ([stmZ] ++ List.replicate n stmZ) = true := hseq
    rw [seqAt_append, Bool.and_eq_true] at hseq'
    have hs1 : seqSize [stmZ] = 2 := rfl
    have hsz : seqSize (stmZ :: List.replicate n stmZ) = 2 + seqSize (List.replicate n stmZ) :=
      seqSize_append [stmZ] _
    rw [hsz] at hr k
    rw [hs1] at hseq'
    have hwa : ∀ y, Region a 20 y → Wr y := fun y hy =>
      hw y (by show (y - a).toNat < _; have : (y - a).toNat < 20 := hy; omega)
    refine X25519Block.ReachW.blockAcc hb [stmZ] off hpc ho hseq'.1 rfl
      (accAll_cons (fun x hx => ?_) (accAll_nil _ _)) (hr.prefix (by omega)) ?_
    · simp only [Instr.accesses, bitCount_3e, State.reg, X25519Mem.toReg0, h0] at hx
      refine wordAccesses_ok ha (fun _ i hi q hq => hwa _ ?_) x hx
      rw [ofNat_add_assoc]
      show ((a + BitVec.ofNat 32 (4 * i + q)) - a).toNat < 20
      rw [Frame.sub_ofNat_toNat _ _ (by omega)]; omega
    · obtain ⟨m1, r0, ro, pc1⟩ := stmZ_exec s hz
      have e20 : (a + BitVec.ofNat 32 20).toNat = a.toNat + 20 := toNat_add_ofNat _ _ (by omega)
      have hu : execAll [stmZ] s = stmZ.next s := rfl
      rw [hu]
      refine zeros_run_w hb n (off + 2) _ (a + BitVec.ofNat 32 20) hseq'.2 (by omega)
        (by rw [pc1, hpc, ofNat_add_assoc]; rfl) (by rw [r0, h0]) (by rw [e20]; omega)
        (by rw [e20]; omega)
        (fun r h1 h5 => by
          rw [ro r (fun e => by rw [e] at h1; exact absurd h1 (by decide)) (by omega)]; exact hz r h1 h5)
        (fun y hy => hw y (by
          rw [show 20 * (n + 1) = 20 + 20 * n by omega, region_split (by omega)]; exact Or.inr hy))
        (hr.sub (by omega)) ?_
      intro t tpc t0 treg tz toth
      refine k t (by rw [tpc, Nat.add_assoc]) ?_ (fun r h0' h15 => by rw [treg r h0' h15, ro r h0' h15])
        (fun y hy => ?_) (fun y hy => ?_)
      · rw [t0, ofNat_add_assoc]; congr 2; omega
      · rw [show 20 * (n + 1) = 20 + 20 * n by omega, region_split (by omega)] at hy
        by_cases h2 : Region (a + BitVec.ofNat 32 20) (20 * n) y
        · exact tz y h2
        · rw [toth y h2, m1, h0, storeWords_zero 5 _ _ _ (by omega)]
          rcases hy with hy | hy
          · simp only [show 4 * 5 = 20 from rfl, hy, ite_true]
          · exact absurd hy h2
      · rw [show 20 * (n + 1) = 20 + 20 * n by omega, region_split (by omega), not_or] at hy
        rw [toth y hy.2, m1, h0, storeWords_zero 5 _ _ _ (by omega)]
        simp only [show 4 * 5 = 20 from rfl, hy.1, ite_false]

/-! ## The segment -/

/-- `sub sp, #CALLEE; movs r1-r5, #0; add r0, sp, #0`. -/
def wipePre : List Instr :=
  [.subSp (BitVec.ofNat 7 (CALLEE / 4)), .movImm 1 0, .movImm 2 0, .movImm 3 0, .movImm 4 0,
    .movImm 5 0, .addRdSp 0 0]

/-- Number of wipe stores. -/
def nWipe : Nat := (LFRAME + CALLEE) / 20

theorem wipe_eq : wipe = wipePre ++ List.replicate nWipe stmZ := rfl

theorem nWipe_bytes : 20 * nWipe = X25519.wipeBytes := by decide

theorem callee_off : (BitVec.ofNat 7 (CALLEE / 4)).toNat * 4 = CALLEE := by decide

theorem wipePre_exec (s : State) :
    (execAll wipePre s).regs 13 = s.regs 13 - BitVec.ofNat 32 CALLEE ∧
    (execAll wipePre s).regs 0 = s.regs 13 - BitVec.ofNat 32 CALLEE ∧
    Z5 (execAll wipePre s) ∧
    (∀ r : Reg, 6 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → (execAll wipePre s).regs r = s.regs r) := by
  have hc : (37 : Nat) = CALLEE / 4 := rfl
  refine ⟨?_, ?_, fun r h1 h5 => ?_, fun r h6 h13 h15 => ?_⟩
  · simp [wipePre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
      X25519Mem.toReg1, X25519Mem.toReg2, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5, CALLEE]
  · simp [wipePre, execAll, Instr.next, Instr.exec, State.setReg, State.sp, X25519Mem.toReg0,
      X25519Mem.toReg1, X25519Mem.toReg2, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5, CALLEE]
  · have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
      rcases r with ⟨v, hv⟩
      simp only at h1 h5
      rcases (by omega : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5) with rfl | rfl | rfl | rfl | rfl <;>
        simp [Fin.ext_iff]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [wipePre, execAll, Instr.next, Instr.exec, State.setReg, X25519Mem.toReg0, X25519Mem.toReg1,
        X25519Mem.toReg2, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5]
  · have ne : ∀ k : Reg, k.val < 6 → r ≠ k := fun k hk e => by
      rw [e] at h6; omega
    have n13 : r ≠ 13 := fun e => h13 (by rw [e]; rfl)
    have n15 : r ≠ 15 := fun e => h15 (by rw [e]; rfl)
    simp [wipePre, execAll, Instr.next, Instr.exec, State.setReg, X25519Mem.toReg0, X25519Mem.toReg1,
      X25519Mem.toReg2, X25519Mem.toReg3, X25519Mem.toReg4, X25519Mem.toReg5,
      ne 0 (by decide), ne 1 (by decide), ne 2 (by decide), ne 3 (by decide), ne 4 (by decide),
      ne 5 (by decide), n13, n15]

/-- **`wipe`**: from `pc = base + off`, with `lo = SP - CALLEE` aligned and the `wipeBytes`
bytes from `lo` not wrapping, the segment zeroes those bytes, writes nothing else, leaves SP at
`lo` and `r1`-`r5` zero, and changes no register from `r6` up other than SP. -/
theorem wipe_run_w {base lo : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop} {s : State}
    {off : Nat} (hseq : seqAt B off wipe = true) (ho : off % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (hlo : s.regs 13 - BitVec.ofNat 32 CALLEE = lo)
    (hal : lo.toNat % 4 = 0) (hn : lo.toNat + X25519.wipeBytes < 2 ^ 32)
    (hw : ∀ y, Region lo X25519.wipeBytes y → Wr y) (hr : InRegion Pc base off (seqSize wipe))
    {Q : State → Prop}
    (cont : ∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize wipe) → t.regs 13 = lo → Z5 t →
      (∀ r : Reg, 6 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      (∀ y, Region lo X25519.wipeBytes y → t.mem y = 0#8) →
      (∀ y, ¬ Region lo X25519.wipeBytes y → t.mem y = s.mem y) →
      ReachW base Pc Wr t Q) :
    ReachW base Pc Wr s Q := by
  rw [wipe_eq] at hseq hr cont
  rw [seqAt_append, Bool.and_eq_true] at hseq
  rw [seqSize_append] at hr cont
  have hpre : seqSize wipePre = 14 := rfl
  refine ReachW.block hb wipePre off hpc ho hseq.1 rfl (X25519Mul.alignedAll_regOnly _ _ rfl)
    (WritesTo.of_noWritesMem _ _ rfl Wr) (hr.prefix (by omega)) ?_
  obtain ⟨u13, u0, uz, uo⟩ := wipePre_exec s
  have um : (execAll wipePre s).mem = s.mem := execAll_mem _ _ rfl
  have upc : (execAll wipePre s).pc = base + BitVec.ofNat 32 (off + seqSize wipePre) := by
    rw [execAll_pc _ _ rfl, hpc, ofNat_add_assoc]
  rw [hlo] at u13 u0
  rw [← nWipe_bytes] at hn hw cont
  refine zeros_run_w hb nWipe (off + seqSize wipePre) _ lo hseq.2 (by omega) upc u0 hal hn uz hw
    (hr.sub (by omega)) ?_
  intro t tpc _ treg tz toth
  refine cont t (by rw [tpc, Nat.add_assoc]) (by rw [treg 13 (by decide) (by decide), u13])
    (fun r h1 h5 => by
      rw [treg r (fun e => by rw [e] at h1; exact absurd h1 (by decide)) (by omega)]; exact uz r h1 h5)
    (fun r h6 h13 h15 => by
      rw [treg r (fun e => by rw [e] at h6; exact absurd h6 (by decide)) h15, uo r h6 h13 h15])
    tz (fun y hy => by rw [toth y hy, um])

end M0Crypto.Release.X25519OutWipe
