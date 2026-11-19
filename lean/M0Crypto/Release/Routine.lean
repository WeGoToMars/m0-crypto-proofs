import M0Crypto.Release.Footprint
import M0Crypto.Release.ReachInv
import M0Crypto.Release.Call
import M0Crypto.Release.SymReach
import M0Crypto.Release.SymReadChk
import M0Crypto.Release.TraceSpec
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.ReachTrace

set_option linter.unusedSimpArgs false

/-!
# Routines and calls

`ReachF base Pc Rd Wr Sp s Q`: a Harvard run of the release bytes from `s` reaches `Q`, and every
step runs at a pc in `Pc`, reads only in `Rd`, writes only in `Wr` and has `sp` in `Sp`.

A `Routine` states once what a call lemma is. It supplies its entry offset, the code it runs,
its stack size, its own entry conditions `Pre`, its write and read footprints outside its stack
window (`wr`, `rd`) and its result `Post` (on the memory and `r0` at return). `Routine.Spec`
adds the common part: from an `Entry` (code present, `sp` aligned with room, `lr` a Thumb
address, footprints apart from the code and the window) the routine returns to `lr` with `sp`
and `r4`-`r11` restored, running only its code, writing only its window and `wr`, reading only
the code, its window and `rd`, and keeping `sp` in its window. Memory outside the write
footprint is unchanged: that follows from the judgment (`ReachF.memEq`), so no routine states it.

`ReachFT.call` is the call rule: one `bl`, the callee's `Spec` from the state the `bl` leaves,
and the continuation from the return, which receives the callee's `Post`, the frame fact
`MemEq`, the code and the caller's high registers (`Hi`).

Each rule is proved once in its trace form (`ReachFT`, the judgment with a condition on the
trace, `ReachTrace.lean`), and the `ReachF` rule follows with the trivial condition. A rule's
trace form takes the trace of its own instructions as an equation `traceAll g t = G` and the
callee's trace condition as `Φf base c = Φc`: for `ReachF` both are `rfl`, and a constant-time
proof rewrites them into public values. `Routine.TSpec` is the constant-time call lemma: the
trace of a call is a function of the code's base and the call's public values.
-/

namespace M0Crypto.Release.Routine

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow)
open M0Crypto.Release.ConstantTime (PCBetween)

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-! ## The judgment -/

/-- The instruction is at a pc in `Pc`, writes only in `Wr`, reads only in `Rd`, and runs with
`sp` in `Sp`. -/
def Step (Pc Rd Wr Sp : Word → Prop) (x : State) (e : Event) : Prop :=
  Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧ (∀ y, Reads e.accesses y → Rd y) ∧ Sp (x.regs 13)

abbrev ReachF (base : Word) (Pc Rd Wr Sp : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachS base (Step Pc Rd Wr Sp) s Q

/-- `ReachF` whose trace satisfies `Φ`. -/
abbrev ReachFT (base : Word) (Pc Rd Wr Sp : Word → Prop) (s : State) (Q : State → Prop)
    (Φ : TrP) : Prop :=
  ReachT base (Step Pc Rd Wr Sp) s Q Φ

variable {base : Word} {Pc Rd Wr Sp : Word → Prop}

theorem ReachF.done {s : State} {Q : State → Prop} (h : Q s) : ReachF base Pc Rd Wr Sp s Q :=
  ReachS.done h

theorem ReachF.mono {Pc' Rd' Wr' Sp' : Word → Prop} {s : State} {Q Q' : State → Prop}
    (h : ReachF base Pc Rd Wr Sp s Q) (hp : ∀ y, Pc y → Pc' y) (hr : ∀ y, Rd y → Rd' y)
    (hw : ∀ y, Wr y → Wr' y) (hs : ∀ y, Sp y → Sp' y) (hq : ∀ t, Q t → Q' t) :
    ReachF base Pc' Rd' Wr' Sp' s Q' :=
  ReachS.mono h (fun _ _ h => ⟨hp _ h.1, fun y hy => hw y (h.2.1 y hy),
    fun y hy => hr y (h.2.2.1 y hy), hs _ h.2.2.2⟩) hq

theorem ReachFT.mono {Pc' Rd' Wr' Sp' : Word → Prop} {s : State} {Q Q' : State → Prop}
    {Φ Φ' : TrP} (h : ReachFT base Pc Rd Wr Sp s Q Φ) (hp : ∀ y, Pc y → Pc' y)
    (hr : ∀ y, Rd y → Rd' y) (hw : ∀ y, Wr y → Wr' y) (hs : ∀ y, Sp y → Sp' y)
    (hq : ∀ t, Q t → Q' t) (hΦ : ∀ tr, Φ tr → Φ' tr) : ReachFT base Pc' Rd' Wr' Sp' s Q' Φ' :=
  ReachT.mono h (fun _ _ h => ⟨hp _ h.1, fun y hy => hw y (h.2.1 y hy),
    fun y hy => hr y (h.2.2.1 y hy), hs _ h.2.2.2⟩) hq hΦ

theorem ReachF.bind {s : State} {Q : State → Prop}
    (h : ReachF base Pc Rd Wr Sp s fun t => ReachF base Pc Rd Wr Sp t Q) :
    ReachF base Pc Rd Wr Sp s Q :=
  ReachS.bind h

/-- One instruction, with its event `ev`. -/
theorem ReachFT.step {s s1 : State} {Q : State → Prop} {Ψ : TrP} {ev : Event} {off : Nat}
    (hb : base.toNat % 2 = 0)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hr : Pc (base + BitVec.ofNat 32 off)) (hw : ∀ y, Writes (i.accesses s) y → Wr y)
    (hrd : ∀ y, Reads (i.accesses s) y → Rd y) (hsp : Sp (s.regs 13))
    (hev : (⟨s.pc, i, i.accesses s⟩ : Event) = ev)
    (hq : ReachFT base Pc Rd Wr Sp s1 Q Ψ) : ReachFT base Pc Rd Wr Sp s Q (Tr.cat (Tr.is [ev]) Ψ) :=
  hev ▸ ReachT.step hb off i hpc ho hi hsz ha hex ⟨by rw [hpc]; exact hr, hw, hrd, hsp⟩ hq

/-- One instruction. -/
theorem ReachF.step {s s1 : State} {Q : State → Prop} {off : Nat} (hb : base.toNat % 2 = 0)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hr : Pc (base + BitVec.ofNat 32 off)) (hw : ∀ y, Writes (i.accesses s) y → Wr y)
    (hrd : ∀ y, Reads (i.accesses s) y → Rd y) (hsp : Sp (s.regs 13))
    (hq : ReachF base Pc Rd Wr Sp s1 Q) : ReachF base Pc Rd Wr Sp s Q :=
  ReachS.step hb off i hpc ho hi hsz ha hex ⟨by rw [hpc]; exact hr, hw, hrd, hsp⟩ hq

theorem ReachF.bcond {s : State} {Q : State → Prop} {off : Nat} (hb : base.toNat % 2 = 0)
    (tgt : Nat) (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hi : instrAt B off = some (.bcond cond imm))
    (hsz : off + 2 ≤ BS)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off)) (hsp : Sp (s.regs 13))
    (hT : condPassed cond s = true →
      ReachF base Pc Rd Wr Sp (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false →
      ReachF base Pc Rd Wr Sp (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachF base Pc Rd Wr Sp s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y),
      fun y hy => absurd hy (reads_nil y), hsp⟩ hT hF

/-- A conditional branch with outcome `b`: the trace is that of the branch taken. -/
theorem ReachFT.bcond {s : State} {Q : State → Prop} {ΨT ΨF : TrP} {b : Bool} {off : Nat}
    (hb : base.toNat % 2 = 0) (tgt : Nat) (cond : BitVec 4) (imm : BitVec 8)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ BS)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off)) (hsp : Sp (s.regs 13)) (hc : condPassed cond s = b)
    (hT : condPassed cond s = true →
      ReachFT base Pc Rd Wr Sp (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q ΨT)
    (hF : condPassed cond s = false →
      ReachFT base Pc Rd Wr Sp (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q ΨF) :
    ReachFT base Pc Rd Wr Sp s Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 off, .bcond cond imm, []⟩]) (Tr.cond b ΨT ΨF)) :=
  ReachT.bcond hb off tgt cond imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y),
      fun y hy => absurd hy (reads_nil y), hsp⟩ hc hT hF

/-! ## Straight-line blocks -/

/-- The regions `(r, k, n)` of a symbolic check, at the state `s`. -/
def regions (s : State) (rg : List (Reg × Word × Nat)) : List Rgn :=
  rg.map fun p => ⟨s.regs p.1 + p.2.1, p.2.2⟩

theorem has_regions {s : State} {rg : List (Reg × Word × Nat)} {p : Reg × Word × Nat}
    (hp : p ∈ rg) {o : Nat} (ho : o < p.2.2) :
    Has (regions s rg) (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o) :=
  ⟨⟨s.regs p.1 + p.2.1, p.2.2⟩, List.mem_map.mpr ⟨p, hp, rfl⟩, o, ho, rfl⟩

/-- No instruction of the block writes `sp`. -/
def keepsSp (is : List Instr) : Bool := is.all fun i => !(i.dsts.contains 13)

theorem blockOk_keepsSp {p : Event → Prop} :
    ∀ (is : List Instr) (s : State), keepsSp is = true → (∀ e ∈ traceAll is s, p e) →
      BlockOk (fun x e => p e ∧ x.regs 13 = s.regs 13) is s
  | [], _, _, _ => trivial
  | i :: is, s, hk, hp => by
    simp only [keepsSp, List.all_cons, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hk
    refine ⟨⟨hp _ (by simp [traceAll]), rfl⟩, ?_⟩
    have h13 : (i.next s).regs 13 = s.regs 13 := next_regs_other s 13 (by decide) hk.1
    have := blockOk_keepsSp is (i.next s) (by simpa [keepsSp] using hk.2)
      (fun e he => hp e (by simp [traceAll, he]))
    rw [h13] at this
    exact this

/-- **A straight-line block**, with its alignment, write and read side conditions discharged by
the symbolic checks: the caller only shows that the checked regions lie in `Wr` and `Rd`. -/
theorem ReachFT.block {s : State} {Q : State → Prop} {Ψ : TrP} {G : List Event}
    (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true) (hk : keepsSp is = true)
    (hr : InRegion Pc base off (seqSize is))
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat))
    (ha : Sym.alignChk al is = true) (hwc : Sym.writeChk wg is = true)
    (hrc : Sym.readChk (fun _ => true) rg is = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hw : ∀ y, Has (regions s wg) y → Wr y) (hrd : ∀ y, Has (regions s rg) y → Rd y)
    (hsp : Sp (s.regs 13)) (hG : traceAll is s = G)
    (hq : ReachFT base Pc Rd Wr Sp (execAll is s) Q Ψ) :
    ReachFT base Pc Rd Wr Sp s Q (Tr.cat (Tr.is G) Ψ) := by
  rw [← hG]
  refine ReachT.block hb is off s hpc ho hseq hf
    (Sym.alignChk_sound al is (Sym.sound_all hf) s hal ha) ?_ hq
  refine BlockOk.mono (fun x e h => ⟨h.1.1, h.1.2.1, h.1.2.2, by rw [h.2]; exact hsp⟩) is s
    (blockOk_keepsSp (p := fun e => Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧
      ∀ y, Reads e.accesses y → Rd y) is s hk ?_)
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  refine ⟨?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hep, hpc, ofNat_add_assoc]; exact hr j hj
  · obtain ⟨p, hp, o, ho', rfl⟩ := Sym.writeChk_sound wg is (Sym.sound_all hf) s hwc e he y hy
    exact hw _ (has_regions hp ho')
  · obtain ⟨p, hp, o, ho', rfl⟩ :=
      Sym.readChk_sound (fun _ => true) rg is (Sym.sound_all hf) s hrc e he rfl y hy
    exact hrd _ (has_regions hp ho')

theorem ReachF.block {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true) (hk : keepsSp is = true)
    (hr : InRegion Pc base off (seqSize is))
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat))
    (ha : Sym.alignChk al is = true) (hwc : Sym.writeChk wg is = true)
    (hrc : Sym.readChk (fun _ => true) rg is = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hw : ∀ y, Has (regions s wg) y → Wr y) (hrd : ∀ y, Has (regions s rg) y → Rd y)
    (hsp : Sp (s.regs 13)) (hq : ReachF base Pc Rd Wr Sp (execAll is s) Q) :
    ReachF base Pc Rd Wr Sp s Q :=
  ReachT.toS (ReachFT.block hb is off hpc ho hseq hf hk hr al wg rg ha hwc hrc hal hw hrd hsp rfl
    (ReachS.toT hq))

/-- A block changes memory only at the bytes its trace writes. -/
theorem execAll_mem_other : ∀ (is : List Instr) (s : State) (y : Word),
    (∀ e ∈ traceAll is s, ¬ Writes e.accesses y) → (execAll is s).mem y = s.mem y
  | [], _, _, _ => rfl
  | i :: is, s, y, h => by
    have h1 : (i.next s).mem y = s.mem y := by
      unfold Instr.next
      split
      · rename_i s' hex
        exact exec_mem_other i s s' hex y (h ⟨s.pc, i, i.accesses s⟩ (by simp [traceAll]))
      · rfl
    show (execAll is (i.next s)).mem y = s.mem y
    rw [execAll_mem_other is _ y (fun e he => h e (by simp [traceAll, he])), h1]

/-- The frame of a checked block: memory outside its write regions is unchanged. -/
theorem execAll_memEq {is : List Instr} {wg : List (Reg × Word × Nat)} (s : State)
    (hf : is.all Instr.falls = true) (hwc : Sym.writeChk wg is = true) :
    MemEq (regions s wg) s.mem (execAll is s).mem := fun y hy =>
  execAll_mem_other is s y fun e he hw => by
    obtain ⟨p, hp, o, ho, rfl⟩ := Sym.writeChk_sound wg is (Sym.sound_all hf) s hwc e he y hw
    exact hy (has_regions hp ho)

/-- One fall-through instruction that may move `sp` (a `push`, a `sub sp`). -/
theorem ReachF.sym1 {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (i : Instr)
    (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off [i] = true) (hf : [i].all Instr.falls = true)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat))
    (ha : Sym.alignChk al [i] = true) (hwc : Sym.writeChk wg [i] = true)
    (hrc : Sym.readChk (fun _ => true) rg [i] = true)
    (hal : ∀ p ∈ al, (s.regs p.1).toNat % p.2 = 0)
    (hw : ∀ y, Has (regions s wg) y → Wr y) (hrd : ∀ y, Has (regions s rg) y → Rd y)
    (hsp : Sp (s.regs 13)) (hq : ReachF base Pc Rd Wr Sp (i.next s) Q) :
    ReachF base Pc Rd Wr Sp s Q := by
  refine ReachS.block hb [i] off s hpc ho hseq hf
    (Sym.alignChk_sound al [i] (Sym.sound_all hf) s hal ha) ⟨⟨by rw [hpc]; exact hr, ?_, ?_, hsp⟩,
      trivial⟩ hq
  · intro y hy
    obtain ⟨p, hp, o, ho', rfl⟩ := Sym.writeChk_sound wg [i] (Sym.sound_all hf) s hwc
      ⟨s.pc, i, i.accesses s⟩ (by simp [traceAll]) y hy
    exact hw _ (has_regions hp ho')
  · intro y hy
    obtain ⟨p, hp, o, ho', rfl⟩ := Sym.readChk_sound (fun _ => true) rg [i] (Sym.sound_all hf) s
      hrc ⟨s.pc, i, i.accesses s⟩ (by simp [traceAll]) rfl y hy
    exact hrd _ (has_regions hp ho')

/-! ## The caller's high registers -/

/-- `r4`-`r11` and `sp` hold `R`: one equation per register, so that `simp [h]` rewrites with
each. -/
abbrev Hi (R : Reg → Word) (t : State) : Prop :=
  t.regs 4 = R 4 ∧ t.regs 5 = R 5 ∧ t.regs 6 = R 6 ∧ t.regs 7 = R 7 ∧ t.regs 8 = R 8 ∧
    t.regs 9 = R 9 ∧ t.regs 10 = R 10 ∧ t.regs 11 = R 11 ∧ t.regs 13 = R 13

theorem Hi.of_forall {R : Reg → Word} {t : State}
    (h : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 13 → r.val ≠ 12 → t.regs r = R r) : Hi R t :=
  ⟨h 4 (by decide) (by decide) (by decide), h 5 (by decide) (by decide) (by decide),
    h 6 (by decide) (by decide) (by decide), h 7 (by decide) (by decide) (by decide),
    h 8 (by decide) (by decide) (by decide), h 9 (by decide) (by decide) (by decide),
    h 10 (by decide) (by decide) (by decide), h 11 (by decide) (by decide) (by decide),
    h 13 (by decide) (by decide) (by decide)⟩

theorem Hi.get {R : Reg → Word} {t : State} (h : Hi R t) (r : Reg) (h4 : 4 ≤ r.val)
    (h13 : r.val ≤ 13) (h12 : r.val ≠ 12) : t.regs r = R r := by
  obtain ⟨e4, e5, e6, e7, e8, e9, e10, e11, e13⟩ := h
  obtain ⟨v, hv⟩ := r
  simp only at h4 h13 h12
  rcases (by omega : v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 13)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- No instruction of the block writes `r4`-`r11` or `sp`. -/
def keepsHi (is : List Instr) : Bool :=
  [4, 5, 6, 7, 8, 9, 10, 11, 13].all fun r => is.all fun i => !(i.dsts.contains r)

theorem Hi.execAll {R : Reg → Word} {t : State} {is : List Instr} (h : Hi R t)
    (hk : keepsHi is = true) : Hi R (execAll is t) := Hi.of_forall fun r h4 h13 h12 => by
  have hm : r.val ∈ [4, 5, 6, 7, 8, 9, 10, 11, 13] := by simp; omega
  rw [execAll_regs_other is t r (by omega) (List.all_eq_true.mp hk _ hm)]
  exact h.get r h4 h13 h12

theorem Hi.self (t : State) : Hi t.regs t := Hi.of_forall fun _ _ _ _ => rfl

theorem Hi.r (h : Hi R t) (r : Reg) (hr : 4 ≤ r.val ∧ r.val ≤ 13 ∧ r.val ≠ 12 := by decide) :
    t.regs r = R r :=
  h.get r hr.1 hr.2.1 hr.2.2

/-- `r4`-`r11` and `sp` hold `R`, except the registers `K`: the caller's high registers after a
call to a routine that changes `K`. -/
def HiK (K : List Reg) (R : Reg → Word) (t : State) : Prop :=
  t.regs 13 = R 13 ∧ ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → r ∉ K → t.regs r = R r

theorem HiK.hi {R : Reg → Word} {t : State} (h : HiK [] R t) : Hi R t :=
  Hi.of_forall fun r h4 h13 h12 => by
    by_cases e : r.val = 13
    · obtain rfl : r = 13 := Fin.ext e
      exact h.1
    · exact h.2 r h4 (by omega) List.not_mem_nil

/-- The registers other than `sp` and `pc`, one equation each. -/
abbrev Lo (R : Reg → Word) (t : State) : Prop :=
  t.regs 0 = R 0 ∧ t.regs 1 = R 1 ∧ t.regs 2 = R 2 ∧ t.regs 3 = R 3 ∧ t.regs 4 = R 4 ∧
    t.regs 5 = R 5 ∧ t.regs 6 = R 6 ∧ t.regs 7 = R 7 ∧ t.regs 8 = R 8 ∧ t.regs 9 = R 9 ∧
    t.regs 10 = R 10 ∧ t.regs 11 = R 11 ∧ t.regs 12 = R 12 ∧ t.regs 14 = R 14

theorem Lo.of_forall {R : Reg → Word} {t : State}
    (h : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = R r) : Lo R t :=
  ⟨h 0 (by decide) (by decide), h 1 (by decide) (by decide), h 2 (by decide) (by decide),
    h 3 (by decide) (by decide), h 4 (by decide) (by decide), h 5 (by decide) (by decide),
    h 6 (by decide) (by decide), h 7 (by decide) (by decide), h 8 (by decide) (by decide),
    h 9 (by decide) (by decide), h 10 (by decide) (by decide), h 11 (by decide) (by decide),
    h 12 (by decide) (by decide), h 14 (by decide) (by decide)⟩

/-! ## Calls -/

/-- The state a `bl` at offset `o` to offset `tgt` leaves. -/
def blState (base : Word) (s : State) (o tgt : Nat) : State :=
  (s.setReg 14 ((base + BitVec.ofNat 32 (o + 4)) ||| 1#32)).setReg 15 (base + BitVec.ofNat 32 tgt)

@[simp] theorem blState_regs (s : State) (o tgt : Nat) (r : Reg) (h14 : r.val ≠ 14 := by decide)
    (h15 : r.val ≠ 15 := by decide) : (blState base s o tgt).regs r = s.regs r := by
  have a14 : r ≠ 14 := by rintro rfl; exact h14 rfl
  have a15 : r ≠ 15 := by rintro rfl; exact h15 rfl
  simp [blState, State.setReg, a14, a15]

@[simp] theorem blState_mem (s : State) (o tgt : Nat) : (blState base s o tgt).mem = s.mem := rfl

theorem blState_pc (s : State) (o tgt : Nat) :
    (blState base s o tgt).pc = base + BitVec.ofNat 32 tgt := by
  simp [blState, State.setReg, State.pc]

theorem blState_lr (s : State) (o tgt : Nat) :
    ((blState base s o tgt).regs 14).getLsbD 0 = true := by
  simp [blState, State.setReg, BitVec.getLsbD_or]

theorem blState_ret (s : State) (o tgt : Nat) (hb : base.toNat % 2 = 0) (ho : o % 2 = 0) :
    (blState base s o tgt).regs 14 &&& ~~~1#32 = base + BitVec.ofNat 32 (o + 4) := by
  have : (blState base s o tgt).regs 14 = (base + BitVec.ofNat 32 (o + 4)) ||| 1#32 := by
    simp [blState, State.setReg]
  rw [this]
  apply lr_mask
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The pcs of the offset ranges `[lo, hi)` of `cs`. -/
def PcIn (base : Word) (cs : List (Nat × Nat)) (y : Word) : Prop :=
  ∃ p ∈ cs, PCBetween base p.1 p.2 y

/-- Every range of `cs` lies in a range of `ds`. -/
def rangesSub (cs ds : List (Nat × Nat)) : Bool :=
  cs.all fun p => ds.any fun q => q.1 ≤ p.1 && p.2 ≤ q.2

theorem PcIn.mono {cs ds : List (Nat × Nat)} (h : rangesSub cs ds = true) {y : Word}
    (hy : PcIn base cs y) : PcIn base ds y := by
  obtain ⟨p, hp, k, h1, h2, rfl⟩ := hy
  have := List.all_eq_true.mp h p hp
  obtain ⟨q, hq, hpq⟩ := List.any_eq_true.mp this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpq
  exact ⟨q, hq, k, by omega, by omega, rfl⟩

theorem PcIn.at {cs : List (Nat × Nat)} {lo hi off : Nat} (hm : (lo, hi) ∈ cs) (h1 : lo ≤ off)
    (h2 : off < hi) : PcIn base cs (base + BitVec.ofNat 32 off) :=
  ⟨(lo, hi), hm, off, h1, h2, rfl⟩

theorem PcIn.region {cs : List (Nat × Nat)} {lo hi off n : Nat} (hm : (lo, hi) ∈ cs)
    (h1 : lo ≤ off) (h2 : off + n ≤ hi) : InRegion (PcIn base cs) base off n :=
  fun j hj => ⟨(lo, hi), hm, off + j, by omega, by omega, rfl⟩

/-- Offset `x` lies outside the ranges `cs`, none of which passes `2 ^ 32`. -/
def outside (cs : List (Nat × Nat)) (x : Nat) : Bool :=
  cs.all fun p => decide (p.2 ≤ 2 ^ 32) && (decide (x < p.1) || decide (p.2 ≤ x))

theorem not_pcIn {cs : List (Nat × Nat)} {x : Nat} (h : outside cs x = true) (hx : x < 2 ^ 32) :
    ¬ PcIn base cs (base + BitVec.ofNat 32 x) := by
  rintro ⟨p, hp, j, h1, h2, he⟩
  have hc := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  have : BitVec.ofNat 32 x = BitVec.ofNat 32 j := by
    have := congrArg (· - base) he; simpa using this
  have := congrArg BitVec.toNat this
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem instrAt_of_seqAt {off : Nat} {i : Instr} {is : List Instr} (h : seqAt B off (i :: is) = true) :
    instrAt B off = some i := by
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

/-- The artifact. -/
def codeR [CodeBytes B BS] (base : Word) : Rgn := ⟨base, BS⟩

/-- **A routine**: what a call lemma states beyond the common part. -/
structure Routine where
  /-- Offset of the entry. -/
  entry : Nat
  /-- The code it runs, its own and its callees', as offset ranges `[lo, hi)`. -/
  code : List (Nat × Nat)
  /-- Bytes of stack it uses below the entry `sp`. -/
  stack : Nat
  /-- Its own entry conditions. -/
  Pre : Word → State → Prop
  /-- What it writes outside its stack window, from the entry state. -/
  wr : State → List Rgn
  /-- What it reads outside its stack window and the code, from the entry state. -/
  rd : State → List Rgn
  /-- Its result, from the entry state, on the memory and `r0` at the return. -/
  Post : State → Mem → Word → Prop
  /-- The registers among `r4`-`r11` it may change: none for a routine that follows the AAPCS. -/
  clob : List Reg := []

namespace Routine

variable (f : Routine)

/-- The stack window: `f.stack` bytes below the entry `sp`. -/
def win (s : State) : Rgn := ⟨s.regs 13 - BitVec.ofNat 32 f.stack, f.stack⟩

structure Entry [CodeBytes B BS] (base : Word) (s : State) : Prop where
  pc : s.pc = base + BitVec.ofNat 32 f.entry
  base4 : base.toNat % 4 = 0
  code : CodeAt s.mem base B
  sp4 : (s.regs 13).toNat % 4 = 0
  room : f.stack ≤ (s.regs 13).toNat
  lr : (s.regs 14).getLsbD 0 = true
  sepCode : Sep [codeR base] (f.win s :: f.wr s)
  sepWr : Sep (f.wr s) [f.win s]
  sepRd : Sep (f.rd s) [f.win s]
  /-- The return address is outside the code it runs. -/
  ret : ¬ PcIn base f.code (s.regs 14 &&& ~~~1#32)
  pre : f.Pre base s

structure Ret (s t : State) : Prop where
  pc : t.pc = s.regs 14 &&& ~~~1#32
  sp : t.regs 13 = s.regs 13
  keep : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → r ∉ f.clob → t.regs r = s.regs r
  post : f.Post s t.mem (t.regs 0)

/-- The pcs it runs at, the bytes it writes and reads, and the stack pointers it runs with. -/
abbrev PcP (base : Word) : Word → Prop := PcIn base f.code
abbrev WrP (s : State) : Word → Prop := Has (f.win s :: f.wr s)
abbrev RdP (base : Word) (s : State) : Word → Prop := Has (codeR base :: f.win s :: f.rd s)
abbrev SpP (s : State) : Word → Prop := InStackWindow (s.regs 13) f.stack

/-- **The call lemma of a routine.** -/
def Spec : Prop :=
  ∀ base s, f.Entry base s → ReachF base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)

/-- The call lemma with the trace condition `Φ base s`. -/
def SpecT (Φ : Word → State → TrP) : Prop :=
  ∀ base s, f.Entry base s →
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s) (Φ base s)

theorem Spec.specT {f : Routine} (h : f.Spec) : f.SpecT fun _ _ _ => True :=
  fun base s e => ReachS.toT (h base s e)

theorem SpecT.spec {f : Routine} {Φ : Word → State → TrP} (h : f.SpecT Φ) : f.Spec :=
  fun base s e => ReachT.toS (h base s e)

end Routine

/-- **The constant-time call lemma** of the routines `f i`: the trace of a call is a function of
the code's base and the call's public values `pub base s`, the same for every `i`. -/
def Routine.TSpec {ι α : Type} (f : ι → Routine) (pub : Word → State → α) : Prop :=
  ∃ T : Word → α → List Event, ∀ i, (f i).SpecT fun base s => Tr.is (T base (pub base s))

/-- The trace of a constant-time routine as a function of `base` and its public values. -/
noncomputable def Routine.TSpec.T {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    (h : Routine.TSpec f pub) : Word → α → List Event := h.choose

/-- A constant-time routine's call lemma with its trace: callers name the callee's trace by the
closed term `h.T`, so no hypothesis about it enters their context. -/
theorem Routine.TSpec.specT {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    (h : Routine.TSpec f pub) (i : ι) : (f i).SpecT fun base s => Tr.is (h.T base (pub base s)) :=
  h.choose_spec i

/-- Public values given as a list, read by index: `pubOf [a, b] 1 = b` by `rfl`. -/
def pubOf (l : List Word) (i : Nat) : Word := l.getD i 0

/-- A trace condition of the public values that admits one trace gives `TSpec`. -/
theorem Routine.tspec_of {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    (Φ : Word → α → TrP) (hu : ∀ b p, Tr.Uniq (Φ b p))
    (h : ∀ i, (f i).SpecT fun base s => Φ base (pub base s)) : Routine.TSpec f pub := by
  classical
  refine ⟨fun b p => if hx : ∃ tr, Φ b p tr then hx.choose else [], fun i base s e => ?_⟩
  obtain ⟨n, t, tr, hr, hok, hq, hΦ⟩ := h i base s e
  have hx : ∃ tr, Φ base (pub base s) tr := ⟨tr, hΦ⟩
  refine ⟨n, t, tr, hr, hok, hq, ?_⟩
  show tr = if hx : ∃ tr, Φ base (pub base s) tr then hx.choose else []
  rw [dite_eq_left hx]
  exact hu _ _ _ _ hΦ hx.choose_spec

/-- `tspec_of` with the trace condition left to unification: `trefine Routine.tspec_by (fun _ base
s e => ?_) (fun _ _ => ?_)` leaves the run, whose proof fixes `Φ`, then its uniqueness. -/
theorem Routine.tspec_by {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    {Φ : Word → α → TrP}
    (h : ∀ i base s, (f i).Entry base s → ReachFT base ((f i).PcP base) ((f i).RdP base s)
      ((f i).WrP s) ((f i).SpP s) s ((f i).Ret s) (Φ base (pub base s)))
    (hu : ∀ b p, Tr.Uniq (Φ b p)) : Routine.TSpec f pub :=
  Routine.tspec_of Φ hu h

/-- The call lemma of a constant-time routine. -/
theorem Routine.TSpec.spec {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    (h : Routine.TSpec f pub) (i : ι) : (f i).Spec :=
  (h.choose_spec i).spec

/-- A callee's trace condition at public values `p` equal to its `pub`. -/
theorem Routine.tr_pub {α : Type} {T : Word → α → List Event} {pub : Word → State → α}
    {base : Word} {c : State} {p : α} (h : pub base c = p) :
    Tr.is (T base (pub base c)) = Tr.is (T base p) := by rw [h]

/-- The write footprint misses the code. -/
theorem Routine.Entry.wr_not_code {f : Routine} {s : State} (e : f.Entry base s) :
    ∀ y, f.WrP s y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i := fun y hy i hi he =>
  Sep.not_has e.sepCode ⟨codeR base, List.mem_singleton.mpr rfl, i,
    by simp only [codeR]; rw [← B_len]; exact hi, he⟩ hy

/-! ## The frame of a judgment -/

theorem runH_mem_other : ∀ {n : Nat} {s t : State} {tr : List Event} {P : State → Event → Prop}
    {W : Word → Prop}, runH B base n s = .ok (t, tr) → StepsOk base P n s →
    (∀ x e, P x e → ∀ y, Writes e.accesses y → W y) → ∀ y, ¬ W y → t.mem y = s.mem y
  | 0, s, t, tr, _, _, hr, _, _, y, _ => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at hr
    rw [hr.1]
  | n + 1, s, t, tr, P, W, hr, hok, hP, y, hy => by
    obtain ⟨s1, e, tr', hs, hr', -⟩ := runH_succ_ok hr
    obtain ⟨hp, hok'⟩ := hok.uncons hs
    rw [runH_mem_other hr' hok' hP y hy, stepH_mem_other hs y (fun hw => hy (hP _ _ hp y hw))]

theorem ReachFT.memEq {s : State} {Q : State → Prop} {Φ : TrP}
    (h : ReachFT base Pc Rd Wr Sp s Q Φ) :
    ReachFT base Pc Rd Wr Sp s (fun t => Q t ∧ ∀ y, ¬ Wr y → t.mem y = s.mem y) Φ := by
  obtain ⟨n, t, tr, hr, hok, hq, hΦ⟩ := h
  exact ⟨n, t, tr, hr, hok, ⟨hq, runH_mem_other hr hok (fun _ _ h => h.2.1)⟩, hΦ⟩

/-- **Memory outside the write bound is unchanged.** -/
theorem ReachF.memEq {s : State} {Q : State → Prop} (h : ReachF base Pc Rd Wr Sp s Q) :
    ReachF base Pc Rd Wr Sp s fun t => Q t ∧ ∀ y, ¬ Wr y → t.mem y = s.mem y := by
  obtain ⟨n, t, tr, hr, hok, hq⟩ := h
  exact ⟨n, t, tr, hr, hok, hq, runH_mem_other hr hok (fun _ _ h => h.2.1)⟩

/-- A window `d` bytes further down, of `M` bytes, lies in a window of `N ≥ d + M` bytes. -/
theorem sp_sub {sp0 sp : Word} {d M N : Nat} (h : sp = sp0 - BitVec.ofNat 32 d) (hd : d + M ≤ N) :
    ∀ y, InStackWindow sp M y → InStackWindow sp0 N y := by
  rintro y ⟨o, ho, rfl⟩
  exact ⟨d + o, by omega, by rw [h, BitVec.ofNat_add]; bv_omega⟩

/-- **The call rule.** A `bl` at offset `o` to the routine `f`, from a caller whose footprints
are `Rc` and `Wc`. The side conditions are those of `f`'s entry that depend on the call site;
the continuation receives the return state with `f`'s result and frame, and the caller's high
registers other than those `f` changes (`f.clob`). The trace is the `bl`, the callee's, and the
continuation's. -/
theorem ReachFT.callK {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf)
    {Pc Sp : Word → Prop} {Rc Wc : List Rgn}
    {R : Reg → Word} {t : State} {Q : State → Prop} {Ψ : TrP} {o : Nat} {imm : BitVec 25}
    (hb4 : base.toNat % 4 = 0) (hpc : t.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0)
    (hi : instrAt B o = some (.bl imm)) (hsz : o + 4 ≤ BS)
    (ht : BitVec.ofNat 32 o + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 f.entry)
    (hr : Pc (base + BitVec.ofNat 32 o)) (hsp : Sp (t.regs 13)) (hcode : CodeAt t.mem base B)
    (hR : Hi R t) (hcodeW : Sep [codeR base] Wc)
    (hP : ∀ y, PcIn base f.code y → Pc y) (hout : outside f.code (o + 4) = true)
    (hS : ∀ y, InStackWindow (t.regs 13) f.stack y → Sp y)
    (hsp4 : (t.regs 13).toNat % 4 = 0) (hroom : f.stack ≤ (t.regs 13).toNat)
    (hW : Sub (f.win (blState base t o f.entry) :: f.wr (blState base t o f.entry)) Wc)
    (hRd : Sub (codeR base :: f.win (blState base t o f.entry) :: f.rd (blState base t o f.entry)) Rc)
    (hsw : Sep (f.wr (blState base t o f.entry)) [f.win (blState base t o f.entry)])
    (hsr : Sep (f.rd (blState base t o f.entry)) [f.win (blState base t o f.entry)])
    (hpre : f.Pre base (blState base t o f.entry))
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + 4) → HiK f.clob R u → CodeAt u.mem base B →
      MemEq (f.win (blState base t o f.entry) :: f.wr (blState base t o f.entry)) t.mem u.mem →
      f.Post (blState base t o f.entry) u.mem (u.regs 0) →
      ReachFT base Pc (Has Rc) (Has Wc) Sp u Q Ψ) :
    ReachFT base Pc (Has Rc) (Has Wc) Sp t Q (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .bl imm, []⟩])
      (Tr.cat (Φf base (blState base t o f.entry)) Ψ)) := by
  have hb2 : base.toNat % 2 = 0 := by omega
  have : BS < 2 ^ 32 := CodeBytes.lt
  generalize hc : blState base t o f.entry = c at hW hRd hsw hsr hpre k ⊢
  have c13 : c.regs 13 = t.regs 13 := by rw [← hc]; exact blState_regs t o _ 13
  have he : f.Entry base c :=
    { pc := by rw [← hc]; exact blState_pc t o _
      base4 := hb4
      code := by rw [← hc]; exact hcode
      sp4 := by rw [c13]; exact hsp4
      room := by rw [c13]; exact hroom
      lr := by rw [← hc]; exact blState_lr t o _
      sepCode := (hW.sep hcodeW.symm).symm
      sepWr := hsw
      sepRd := hsr
      ret := by rw [← hc, blState_ret t o _ hb2 ho]; exact not_pcIn hout (by omega)
      pre := hpre }
  refine ReachT.bl hb2 o f.entry imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, fun y hy => absurd hy (writes_nil y),
      fun y hy => absurd hy (reads_nil y), hsp⟩ ?_
  rw [show (t.setReg 14 ((base + BitVec.ofNat 32 (o + 4)) ||| 1#32)).setReg 15
    (base + BitVec.ofNat 32 f.entry) = c from hc]
  refine ReachT.seq (ReachT.mono (ReachFT.memEq (hf base c he)) (fun _ _ h => ⟨hP _ h.1,
    fun y hy => hW.has (h.2.1 y hy), fun y hy => hRd.has (h.2.2.1 y hy),
    hS _ (by rw [← c13]; exact h.2.2.2)⟩) (fun _ h => h) fun _ h => h) fun u ⟨hu, hm⟩ => ?_
  have hmem : MemEq (f.win c :: f.wr c) t.mem u.mem := by
    intro y hy; rw [hm y hy, ← hc]; rfl
  refine k u ?_ ?_ ?_ hmem hu.post
  · rw [hu.pc, ← hc, blState_ret t o _ hb2 ho]
  · refine ⟨by rw [hu.sp, c13]; exact hR.r 13, fun r h4 h11 hK => ?_⟩
    rw [hu.keep r h4 h11 hK, ← hc, blState_regs t o _ r (by omega) (by omega)]
    exact hR.get r h4 (by omega) (by omega)
  · intro i hi
    have hn : ¬ Has (f.win c :: f.wr c) (base + BitVec.ofNat 32 i) :=
      Sep.not_has he.sepCode ⟨codeR base, List.mem_singleton.mpr rfl, i,
        by simp only [codeR]; rw [← B_len]; exact hi, rfl⟩
    rw [hmem _ hn]; exact hcode i hi

/-- **The call rule** for a routine that keeps `r4`-`r11` (`ReachFT.callK`). -/
theorem ReachFT.call {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf)
    {Pc Sp : Word → Prop} {Rc Wc : List Rgn}
    {R : Reg → Word} {t : State} {Q : State → Prop} {Ψ : TrP} {o : Nat} {imm : BitVec 25}
    (hb4 : base.toNat % 4 = 0) (hpc : t.pc = base + BitVec.ofNat 32 o) (ho : o % 2 = 0)
    (hi : instrAt B o = some (.bl imm)) (hsz : o + 4 ≤ BS)
    (ht : BitVec.ofNat 32 o + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 f.entry)
    (hr : Pc (base + BitVec.ofNat 32 o)) (hsp : Sp (t.regs 13)) (hcode : CodeAt t.mem base B)
    (hR : Hi R t) (hcodeW : Sep [codeR base] Wc)
    (hP : ∀ y, PcIn base f.code y → Pc y) (hout : outside f.code (o + 4) = true)
    (hS : ∀ y, InStackWindow (t.regs 13) f.stack y → Sp y)
    (hsp4 : (t.regs 13).toNat % 4 = 0) (hroom : f.stack ≤ (t.regs 13).toNat)
    (hW : Sub (f.win (blState base t o f.entry) :: f.wr (blState base t o f.entry)) Wc)
    (hRd : Sub (codeR base :: f.win (blState base t o f.entry) :: f.rd (blState base t o f.entry)) Rc)
    (hsw : Sep (f.wr (blState base t o f.entry)) [f.win (blState base t o f.entry)])
    (hsr : Sep (f.rd (blState base t o f.entry)) [f.win (blState base t o f.entry)])
    (hpre : f.Pre base (blState base t o f.entry))
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + 4) → Hi R u → CodeAt u.mem base B →
      MemEq (f.win (blState base t o f.entry) :: f.wr (blState base t o f.entry)) t.mem u.mem →
      f.Post (blState base t o f.entry) u.mem (u.regs 0) →
      ReachFT base Pc (Has Rc) (Has Wc) Sp u Q Ψ)
    (hcl : f.clob = [] := by rfl) :
    ReachFT base Pc (Has Rc) (Has Wc) Sp t Q (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .bl imm, []⟩])
      (Tr.cat (Φf base (blState base t o f.entry)) Ψ)) :=
  ReachFT.callK hf hb4 hpc ho hi hsz ht hr hsp hcode hR hcodeW hP hout hS hsp4 hroom hW hRd hsw hsr
    hpre fun u a h c d e => k u a (hcl ▸ h).hi c d e

/-! ## Call sites -/

/-- The caller's facts that hold at all its call sites: `base` word-aligned, the entry `sp0`
word-aligned with `N` bytes below it, and the write footprint `Wc` apart from the code. -/
structure Caller [CodeBytes B BS] (base sp0 : Word) (N : Nat) (Wc : List Rgn) : Prop where
  b4 : base.toNat % 4 = 0
  sp4 : sp0.toNat % 4 = 0
  room : N ≤ sp0.toNat
  codeW : Sep [codeR base] Wc
  code32 : base.toNat + BS ≤ 2 ^ 32

/-- The side conditions of a glue block at `t`: its aligned registers are aligned and its
accesses lie in the caller's footprints. -/
def GlueSides (t : State) (Rc Wc : List Rgn) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) : Prop :=
  (∀ p ∈ al, (t.regs p.1).toNat % p.2 = 0) ∧ Sub (regions t wg) Wc ∧ Sub (regions t rg) Rc

/-- The decided checks of a glue block `g` at `o`: it falls through, keeps `sp`, lies in the
caller's code `cs`, and has its accesses aligned (`al`) and inside `wg` and `rg`. -/
def glueOk (cs : List (Nat × Nat)) (g : List Instr) (o d N : Nat) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) : Bool :=
  o % 2 == 0 && g.all Instr.falls && keepsSp g && Sym.alignChk al g && Sym.writeChk wg g &&
  Sym.readChk (fun _ => true) rg g && rangesSub [(o, o + seqSize g)] cs && decide (d ≤ N)

theorem codeAt_execAll {Wc : List Rgn} {g : List Instr} {wg : List (Reg × Word × Nat)} {t : State}
    (hcW : Sep [codeR base] Wc) (hw : Sub (regions t wg) Wc) (hfa : g.all Instr.falls = true)
    (hwc : Sym.writeChk wg g = true) (hcode : CodeAt t.mem base B) :
    CodeAt (execAll g t).mem base B := fun i hi => by
  rw [execAll_memEq t hfa hwc (base + BitVec.ofNat 32 i) fun h => Sep.not_has hcW
    ⟨codeR base, List.mem_singleton.mpr rfl, i, by simp only [codeR]; rw [← B_len]; exact hi, rfl⟩
    (hw.has h)]
  exact hcode i hi

/-- `codeAt_execAll` from the block's write check `hw`. -/
theorem codeAt_execAll_has {Wc : List Rgn} {g : List Instr} {wg : List (Reg × Word × Nat)}
    {t : State} (hcW : Sep [codeR base] Wc) (hw : ∀ y, Has (regions t wg) y → Has Wc y)
    (hfa : g.all Instr.falls = true) (hwc : Sym.writeChk wg g = true)
    (hcode : CodeAt t.mem base B) : CodeAt (execAll g t).mem base B := fun i hi => by
  rw [execAll_memEq t hfa hwc (base + BitVec.ofNat 32 i) fun h => Sep.not_has hcW
    ⟨codeR base, List.mem_singleton.mpr rfl, i, by simp only [codeR]; rw [← B_len]; exact hi, rfl⟩
    (hw _ h)]
  exact hcode i hi

/-- The code stays in memory across a frame fact whose footprint lies apart from it. -/
theorem CodeAt.of_memEq {f : List Rgn} {m m' : Mem} (hc : CodeAt m base B) (h : MemEq f m m')
    (hs : Sep [codeR base] f) : CodeAt m' base B := fun i hi => by
  rw [h (base + BitVec.ofNat 32 i) fun hy => Sep.not_has hs
    ⟨codeR base, List.mem_singleton.mpr rfl, i, by simp only [codeR]; rw [← B_len]; exact hi, rfl⟩ hy]
  exact hc i hi

/-- A byte store changes only its byte. -/
theorem MemEq.write8 (m : Mem) (a v : Word) : MemEq [⟨a, 1⟩] m (Thumb.write8 m a v) :=
  fun y hy => by
    have : y ≠ a := fun h => hy ⟨⟨a, 1⟩, List.mem_singleton.mpr rfl, 0, Nat.one_pos, by simp [h]⟩
    simp [Thumb.write8, this]

/-- **A glue block** between calls, at the caller's `sp` offset `d`, with trace `G`. -/
theorem ReachFT.glue {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {t : State} {Q : State → Prop} {Ψ : TrP} {G : List Event} {o d : Nat}
    (F : Caller base sp0 N Wc) (g : List Instr)
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) (hseq : seqAt B o g = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : GlueSides t Rc Wc al wg rg) (hG : traceAll g t = G)
    (k : (execAll g t).pc = base + BitVec.ofNat 32 (o + seqSize g) →
      (execAll g t).regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt (execAll g t).mem base B →
      MemEq (regions t wg) t.mem (execAll g t).mem →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) (execAll g t) Q Ψ)
    (hok : glueOk cs g o d N al wg rg = true := by decide) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) Ψ) := by
  simp only [glueOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho, hfa, hks, ha, hwc, hrc, hcs, hd⟩ := hok
  obtain ⟨hal, hw, hrd⟩ := hs
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  refine ReachFT.block hb2 g o hpc ho hseq hfa hks
    (fun j hj => PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega))) al wg rg ha
    hwc hrc hal (fun _ h => hw.has h) (fun _ h => hrd.has h) ⟨d, hd, h13⟩ hG ?_
  refine k (by rw [execAll_pc _ _ hfa, hpc, ofNat_add_assoc]) ?_
    (codeAt_execAll F.codeW hw hfa hwc hcode) (execAll_memEq t hfa hwc)
  rw [execAll_regs_other g t 13 (by decide) hks, h13]

/-- **A glue block** between calls, at the caller's `sp` offset `d`. -/
theorem ReachF.glue {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn} {t : State}
    {Q : State → Prop} {o d : Nat} (F : Caller base sp0 N Wc) (g : List Instr)
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) (hseq : seqAt B o g = true)
    (hpc : t.pc = base + BitVec.ofNat 32 o)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : GlueSides t Rc Wc al wg rg)
    (k : (execAll g t).pc = base + BitVec.ofNat 32 (o + seqSize g) →
      (execAll g t).regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt (execAll g t).mem base B →
      MemEq (regions t wg) t.mem (execAll g t).mem →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) (execAll g t) Q)
    (hok : glueOk cs g o d N al wg rg = true := by decide) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q :=
  ReachT.toS (ReachFT.glue F g al wg rg hseq hpc h13 hcode hs rfl
    (fun a b c d => ReachS.toT (k a b c d)) hok)

/-- The code offset that `ldr rt, [pc, #imm * 4]` at offset `o` reads. -/
def litOff (o : Nat) (imm : BitVec 8) : Nat := (o + 4) / 4 * 4 + imm.toNat * 4

/-- The decided checks of a literal load at `o`: it lies in the caller's code, its word lies in
the artifact, and it loads `r0`-`r3`. -/
def litOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o d N : Nat) (rt : LowReg) (imm : BitVec 8) : Bool :=
  o % 2 == 0 && rangesSub [(o, o + 2)] cs && decide (litOff o imm + 4 ≤ BS) &&
  decide (d ≤ N) && decide (rt.val < 4)

/-- The state after `ldr rt, [pc, #imm * 4]` at `o`, which loads the code word `v`. -/
def litState (base : Word) (t : State) (o : Nat) (rt : LowReg) (v : Word) : State :=
  (t.setReg 15 (base + BitVec.ofNat 32 (o + 2))).setReg rt.toReg v

@[simp] theorem litState_mem (t : State) (o : Nat) (rt : LowReg) (v : Word) :
    (litState base t o rt v).mem = t.mem := rfl

/-- **A literal-pool load**: `rt` receives the code word at `litOff o imm`. -/
theorem ReachFT.lit {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {R : Reg → Word} {t : State} {Q : State → Prop} {Ψ : TrP} {o d : Nat} (F : Caller base sp0 N Wc)
    (rt : LowReg) (imm : BitVec 8) (hi : instrAt B o = some (.ldrLit rt imm))
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B) (hrd : Sub [codeR base] Rc)
    (k : ∀ u, u = litState base t o rt (Frame.codeWord (litOff o imm)) →
      u.pc = base + BitVec.ofNat 32 (o + 2) → Hi R u → u.regs 13 = sp0 - BitVec.ofNat 32 d →
      CodeAt u.mem base B → ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ)
    (hok : litOk cs o d N rt imm = true := by decide) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 o, .ldrLit rt imm,
        [⟨.read, base + BitVec.ofNat 32 (litOff o imm), 4⟩]⟩]) Ψ) := by
  simp only [litOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho, hcs, hsz, hd, hrt⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have := F.code32
  have hl : litOff o imm % 4 = 0 := by simp only [litOff]; omega
  have hsz' : o + 2 ≤ BS := by simp only [litOff] at hsz; omega
  have : BS < 2 ^ 32 := CodeBytes.lt
  have ha : ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4) =
      base + BitVec.ofNat 32 (litOff o imm) := by
    rw [hpc, Frame.lit_addr base F.b4 o imm.toNat (by simp only [litOff] at hsz; omega)]; rfl
  have hal : (base + BitVec.ofNat 32 (litOff o imm)).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := F.b4; omega
  have hR' : Hi R (litState base t o rt (Frame.codeWord (litOff o imm))) :=
    Hi.of_forall fun r h4 h13 h12 => by
      have : r ≠ rt.toReg := fun he => by rw [he] at h4; simp [LowReg.toReg] at h4; omega
      have : r ≠ 15 := fun he => by rw [he] at h13; exact absurd h13 (by decide)
      simp only [litState, State.setReg, ‹r ≠ rt.toReg›, ‹r ≠ 15›, ite_false]
      exact hR.get r h4 h13 h12
  refine ReachFT.step hb2 (.ldrLit rt imm) hpc ho hi (by rw [B_len]; simp [Instr.size]; omega)
    (by simp only [Instr.accesses]; rw [ha]; simp [Access.aligned, hal]; have := F.b4; omega) ?_
    (PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by simp [Instr.size]))) ?_ ?_
    ⟨d, hd, h13⟩ (by show (⟨t.pc, _, [⟨.read, ((t.pc + 4#32) &&& ~~~3#32) +
      BitVec.ofNat 32 (imm.toNat * 4), 4⟩]⟩ : Event) = _; rw [ha, hpc]) (k _ rfl (by
      have h : (15 : Reg) ≠ rt.toReg := fun he => by
        have : (rt.toReg).val < 8 := rt.isLt
        rw [← he] at this; exact absurd this (by decide)
      simp [litState, State.setReg, State.pc, h]) hR'
      (by rw [hR'.r 13, ← hR.r 13, h13]) (by simp only [litState, State.setReg]; exact hcode))
  · rw [show (Instr.ldrLit rt imm).exec t = .ok ((t.setReg 15 (t.pc + BitVec.ofNat 32 2)).setReg
      rt.toReg (read32 t.mem (((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4))))
      from rfl, ha, Frame.read32_code hcode _ hsz, hpc, ofNat_add_assoc]
    rfl
  · intro y hy; simp [Instr.accesses, Writes] at hy
  · rintro y ⟨a, ha', -, j, hj, rfl⟩
    simp only [Instr.accesses, List.mem_singleton] at ha'
    subst ha'
    refine hrd.has ⟨_, List.mem_singleton_self _, litOff o imm + j, by simp only [codeR] at *; omega,
      by rw [ha, ofNat_add_assoc]; rfl⟩

/-- **A literal-pool load**: `rt` receives the code word at `litOff o imm`. -/
theorem ReachF.lit {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {R : Reg → Word} {t : State} {Q : State → Prop} {o d : Nat} (F : Caller base sp0 N Wc)
    (rt : LowReg) (imm : BitVec 8) (hi : instrAt B o = some (.ldrLit rt imm))
    (hpc : t.pc = base + BitVec.ofNat 32 o) (hR : Hi R t) (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d)
    (hcode : CodeAt t.mem base B) (hrd : Sub [codeR base] Rc)
    (k : ∀ u, u = litState base t o rt (Frame.codeWord (litOff o imm)) →
      u.pc = base + BitVec.ofNat 32 (o + 2) → Hi R u → u.regs 13 = sp0 - BitVec.ofNat 32 d →
      CodeAt u.mem base B → ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q)
    (hok : litOk cs o d N rt imm = true := by decide) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q :=
  (ReachFT.lit F rt imm hi hpc hR h13 hcode hrd
    (fun u hu hp hR h13 hc => ReachS.toT (k u hu hp hR h13 hc)) hok).toS

/-- A pc at offset `a` is at offset `b = a`, decided. -/
theorem pc_at {t : State} {a b : Nat} (h : t.pc = base + BitVec.ofNat 32 a)
    (he : a = b := by decide) : t.pc = base + BitVec.ofNat 32 b := he ▸ h

/-- The state at the entry of `f` after the glue `g` at `o` and the `bl` after it. -/
def atCall (base : Word) (f : Routine) (g : List Instr) (o : Nat) (t : State) : State :=
  blState base (execAll g t) (o + seqSize g) f.entry

/-- The side conditions of a call site: the glue's, and the callee's footprints inside the
caller's and apart from the callee's window. -/
def SiteSides (f : Routine) (base : Word) (g : List Instr) (o : Nat) (t : State)
    (Rc Wc : List Rgn) (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) : Prop :=
  GlueSides t Rc Wc al wg rg ∧
  Sub (f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) Wc ∧
  Sub (codeR base :: f.win (atCall base f g o t) :: f.rd (atCall base f g o t)) Rc ∧
  Sep (f.wr (atCall base f g o t)) [f.win (atCall base f g o t)] ∧
  Sep (f.rd (atCall base f g o t)) [f.win (atCall base f g o t)]

/-- The decided checks of a call site: the glue `g` at `o` falls through, keeps `r4`-`r11` and
`sp`, and has its accesses aligned (`al`) and inside `wg` and `rg`; the `bl` after it reaches
`f`; glue, `bl` and `f`'s code lie in the caller's code `cs`; the return offset lies outside
`f`'s code; `f`'s window fits in the caller's `N` bytes below its `sp` offset `d`. -/
def siteOk [CodeBytes B BS] (cs : List (Nat × Nat)) (f : Routine) (g : List Instr) (o d N : Nat) (imm : BitVec 25)
    (al : List (Reg × Nat)) (wg rg : List (Reg × Word × Nat)) : Bool :=
  o % 2 == 0 && (o + seqSize g) % 2 == 0 && g.all Instr.falls && keepsHi g &&
  Sym.alignChk al g && Sym.writeChk wg g && Sym.readChk (fun _ => true) rg g &&
  rangesSub [(o, o + seqSize g + 4)] cs && rangesSub f.code cs &&
  outside f.code (o + seqSize g + 4) && decide (o + seqSize g + 4 ≤ BS) &&
  decide (BitVec.ofNat 32 (o + seqSize g) + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 f.entry) &&
  decide (d + f.stack ≤ N) && d % 4 == 0

/-- **The call-site rule**: a glue block `g` that keeps `r4`-`r11` and `sp`, and a `bl` to `f`.
The caller gives the side conditions `SiteSides` (footprint arithmetic) and `f`'s `Pre`; the
continuation receives the return state with `sp`, the caller's high registers other than `f.clob`,
the code, the frame of glue and call, and `f`'s `Post`. The trace is the glue's (`G`), the `bl`,
the callee's (`Φc`) and the continuation's. -/
theorem ReachFT.siteK {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf)
    {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat}
    {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop} {Ψ Φc : TrP}
    {G : List Event} {o d : Nat}
    {imm : BitVec 25} (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hseq : seqAt B o g = true)
    (hi : instrAt B (o + seqSize g) = some (.bl imm)) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (hG : traceAll g t = G) (hΦ : Φf base (atCall base f g o t) = Φc)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → HiK f.clob R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B → MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ)
    (hok : siteOk cs f g o d N imm al wg rg = true := by first | decide +kernel | rfl) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize g), .bl imm, []⟩])
        (Tr.cat Φc Ψ))) := by
  simp only [siteOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨ho, ho', hfa, hk, ha, hwc, hrc, hcs, hfc, hout, hsz, ht, hd, hd4⟩ := hok
  obtain ⟨⟨hal, hw, hrd⟩, hW, hRd, hsw, hsr⟩ := hs
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have hks : keepsSp g = true := List.all_eq_true.mp hk 13 (by simp)
  have hR13 : R 13 = t.regs 13 := (hR.r 13).symm
  have hsp4 : (sp0 - BitVec.ofNat 32 d).toNat % 4 = 0 := by
    have := F.sp4; have := F.room
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hroom : f.stack ≤ (sp0 - BitVec.ofNat 32 d).toNat := by
    have := F.room
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [← hΦ]
  refine ReachFT.block hb2 g o hpc ho hseq hfa hks
    (fun j hj => PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega))) al wg rg ha
    hwc hrc hal (fun _ h => hw.has h) (fun _ h => hrd.has h) ⟨d, by omega, h13⟩ hG ?_
  have hx13 : (execAll g t).regs 13 = sp0 - BitVec.ofNat 32 d := by
    rw [(hR.execAll hk).r 13, hR13, h13]
  exact ReachFT.callK hf F.b4 (o := o + seqSize g) (by rw [execAll_pc _ _ hfa, hpc, ofNat_add_assoc])
    ho' hi hsz ht (PcIn.mono hcs (PcIn.at List.mem_cons_self (by omega) (by omega)))
    ⟨d, by omega, hx13⟩ (codeAt_execAll F.codeW hw hfa hwc hcode) (hR.execAll hk) F.codeW
    (fun _ h => PcIn.mono hfc h) hout (by rw [hx13]; exact sp_sub rfl hd) (by rw [hx13]; exact hsp4)
    (by rw [hx13]; exact hroom) hW hRd hsw hsr hpre fun u hu hRu hcu hm hp =>
      k u hu hRu (by rw [hRu.1, hR13, h13]) hcu ((execAll_memEq t hfa hwc).trans hm) hp

/-- **The call-site rule** for a routine that keeps `r4`-`r11` (`ReachFT.siteK`). -/
theorem ReachFT.site {f : Routine} {Φf : Word → State → TrP} (hf : f.SpecT Φf)
    {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat}
    {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop} {Ψ Φc : TrP}
    {G : List Event} {o d : Nat}
    {imm : BitVec 25} (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hseq : seqAt B o g = true)
    (hi : instrAt B (o + seqSize g) = some (.bl imm)) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (hG : traceAll g t = G) (hΦ : Φf base (atCall base f g o t) = Φc)
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → Hi R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B → MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q Ψ)
    (hok : siteOk cs f g o d N imm al wg rg = true := by first | decide +kernel | rfl)
    (hcl : f.clob = [] := by rfl) :
    ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
      (Tr.cat (Tr.is G) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (o + seqSize g), .bl imm, []⟩])
        (Tr.cat Φc Ψ))) :=
  ReachFT.siteK hf F g al wg rg hseq hi hpc hR h13 hcode hs hpre hG hΦ
    (fun u a h c d e f => k u a (hcl ▸ h).hi c d e f) hok

/-- **The call-site rule** without the trace (`ReachFT.site`). -/
theorem ReachF.site {f : Routine} (hf : f.Spec) {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat}
    {Rc Wc : List Rgn} {R : Reg → Word} {t : State} {Q : State → Prop} {o d : Nat}
    {imm : BitVec 25} (F : Caller base sp0 N Wc) (g : List Instr) (al : List (Reg × Nat))
    (wg rg : List (Reg × Word × Nat)) (hseq : seqAt B o g = true)
    (hi : instrAt B (o + seqSize g) = some (.bl imm)) (hpc : t.pc = base + BitVec.ofNat 32 o)
    (hR : Hi R t)
    (h13 : t.regs 13 = sp0 - BitVec.ofNat 32 d) (hcode : CodeAt t.mem base B)
    (hs : SiteSides f base g o t Rc Wc al wg rg) (hpre : f.Pre base (atCall base f g o t))
    (k : ∀ u, u.pc = base + BitVec.ofNat 32 (o + seqSize g + 4) → Hi R u →
      u.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt u.mem base B → MemEq (regions t wg ++ f.win (atCall base f g o t) :: f.wr (atCall base f g o t)) t.mem u.mem →
      f.Post (atCall base f g o t) u.mem (u.regs 0) →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) u Q)
    (hok : siteOk cs f g o d N imm al wg rg = true := by first | decide +kernel | rfl)
    (hcl : f.clob = [] := by rfl) :
    ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q :=
  ReachT.toS (ReachFT.site hf.specT F g al wg rg hseq hi hpc hR h13 hcode hs hpre rfl rfl
    (fun u a b c d e f => ReachS.toT (k u a b c d e f)) hok hcl)

/-- `site_simp [h, ...]` evaluates the glue and the `bl` of a call site, unfolds the footprints
and rewrites with the given register facts. -/
syntax "site_simp" " [" term,* "]" (Lean.Parser.Tactic.location)? : tactic

/-- `site_simpa [h, ...] using e`: `site_simp` at `e` and the goal, then `e`. -/
syntax "site_simpa" " [" term,* "]" " using " term : tactic

/-- The result of an add with carry in: `subs` after its operand is folded to a literal. -/
theorem addWithCarry_true_fst (x y : Word) :
    (M0Crypto.Armv6M.addWithCarry x y true).1 = x + y + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_add, Bool.toNat_true]
  omega

/-- Constant offsets added in turn are one offset. -/
theorem add_add_ofNat (a : Word) (x y : Nat) :
    a + BitVec.ofNat 32 x + BitVec.ofNat 32 y = a + BitVec.ofNat 32 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The four bytes of a word store, at its address. -/
theorem bytesAt_write32_self (m : Mem) (a v : Word) :
    Footprint.bytesAt (M0Crypto.Armv6M.write32 m a v) a 4 =
      [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8] := by
  have h1 : a + 1#32 ≠ a := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h2 : a + 2#32 ≠ a := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h3 : a + 3#32 ≠ a := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h21 : a + 2#32 ≠ a + 1#32 := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h31 : a + 3#32 ≠ a + 1#32 := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  have h32 : a + 3#32 ≠ a + 2#32 := by intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_add] at this; omega
  refine bytesAt_eq_list rfl fun k hk => ?_
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [M0Crypto.Armv6M.write32, h1, h2, h3, h21, h31, h32]

/-- A word store at `a - x` leaves the bytes at `a - y` apart from it. -/
theorem write32_sub_other (m : Mem) (a v : Word) (x y i : Nat) (hx : x < 2 ^ 32)
    (hy : y + 4 ≤ 2 ^ 32) (hi : i ≤ y) (h : x + 1 ≤ y - i ∨ y - i + 4 ≤ x) :
    M0Crypto.Armv6M.write32 m (a - BitVec.ofNat 32 x) v (a - BitVec.ofNat 32 y + BitVec.ofNat 32 i) =
      m (a - BitVec.ofNat 32 y + BitVec.ofNat 32 i) :=
  M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => by
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    have := a.isLt
    omega

/-- A word store at `a - x` leaves the word at `a - y` apart from it. -/
theorem read32_write32_sub (m : Mem) (a v : Word) (x y : Nat) (hx : x < 2 ^ 32)
    (hy : y + 4 ≤ 2 ^ 32) (h4 : 4 ≤ y) (h : x + 4 ≤ y ∨ y + 4 ≤ x) :
    read32 (M0Crypto.Armv6M.write32 m (a - BitVec.ofNat 32 x) v) (a - BitVec.ofNat 32 y) =
      read32 m (a - BitVec.ofNat 32 y) := by
  have e := fun i (hi : i < 4) => write32_sub_other m a v x y i hx hy (by omega) (by omega)
  have e0 := e 0 (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e0
  simp only [read32, e0]
  rw [show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, e 1 (by omega), e 2 (by omega), e 3 (by omega)]

/-- A word store at `a - x` leaves the `n` bytes at `a - y` apart from it. -/
theorem bytesAt_write32_sub (m : Mem) (a v : Word) (x y n : Nat) (hx : x < 2 ^ 32)
    (hy : y + 4 ≤ 2 ^ 32) (hn : n ≤ y) (h : x + n ≤ y ∨ y + 4 ≤ x) :
    Footprint.bytesAt (M0Crypto.Armv6M.write32 m (a - BitVec.ofNat 32 x) v) (a - BitVec.ofNat 32 y) n =
      Footprint.bytesAt m (a - BitVec.ofNat 32 y) n :=
  Footprint.bytesAt_congr fun i hi => write32_sub_other m a v x y i hx hy (by omega) (by omega)

/-- A word store at `a + x` leaves the byte at `a + z` apart from it. -/
theorem write32_add_other (m : Mem) (a v : Word) (x z : Nat) (hx : x + 4 ≤ 2 ^ 32)
    (hz : z < 2 ^ 32) (h : z + 1 ≤ x ∨ x + 4 ≤ z) :
    M0Crypto.Armv6M.write32 m (a + BitVec.ofNat 32 x) v (a + BitVec.ofNat 32 z) =
      m (a + BitVec.ofNat 32 z) :=
  M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => by
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := a.isLt
    omega

/-- A word store at `a + x` leaves the word at `a + y` apart from it. -/
theorem read32_write32_add (m : Mem) (a v : Word) (x y : Nat) (hx : x + 4 ≤ 2 ^ 32)
    (hy : y + 4 ≤ 2 ^ 32) (h : y + 4 ≤ x ∨ x + 4 ≤ y) :
    read32 (M0Crypto.Armv6M.write32 m (a + BitVec.ofNat 32 x) v) (a + BitVec.ofNat 32 y) =
      read32 m (a + BitVec.ofNat 32 y) := by
  have e := fun i (hi : i < 4) => write32_add_other m a v x (y + i) hx (by omega) (by omega)
  simp only [read32]
  rw [show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, add_add_ofNat, add_add_ofNat, add_add_ofNat,
    e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  have e0 := e 0 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0]

/-- `read32_write32_add` at `a` itself. -/
theorem read32_write32_add0 (m : Mem) (a v : Word) (x : Nat) (hx : x + 4 ≤ 2 ^ 32) (h4 : 4 ≤ x) :
    read32 (M0Crypto.Armv6M.write32 m (a + BitVec.ofNat 32 x) v) a = read32 m a := by
  have := read32_write32_add m a v x 0 hx (by omega) (by omega)
  simpa using this

/-- A word store at `a + x` leaves the `n` bytes at `a + y` apart from it. -/
theorem bytesAt_write32_add (m : Mem) (a v : Word) (x y n : Nat) (hx : x + 4 ≤ 2 ^ 32)
    (hy : y + n ≤ 2 ^ 32) (h : y + n ≤ x ∨ x + 4 ≤ y) :
    Footprint.bytesAt (M0Crypto.Armv6M.write32 m (a + BitVec.ofNat 32 x) v) (a + BitVec.ofNat 32 y) n =
      Footprint.bytesAt m (a + BitVec.ofNat 32 y) n :=
  Footprint.bytesAt_congr fun i hi => by
    rw [add_add_ofNat]; exact write32_add_other m a v x (y + i) hx (by omega) (by omega)

/-- `read32_write32_add` for a store at `a` itself. -/
theorem read32_write32_base (m : Mem) (a v : Word) (y : Nat) (hy : y + 4 ≤ 2 ^ 32) (h4 : 4 ≤ y) :
    read32 (M0Crypto.Armv6M.write32 m a v) (a + BitVec.ofNat 32 y) = read32 m (a + BitVec.ofNat 32 y) := by
  have := read32_write32_add m a v 0 y (by omega) hy (by omega)
  simpa using this

/-- `bytesAt_write32_add` for a store at `a` itself. -/
theorem bytesAt_write32_base (m : Mem) (a v : Word) (y n : Nat) (hy : y + n ≤ 2 ^ 32) (h4 : 4 ≤ y) :
    Footprint.bytesAt (M0Crypto.Armv6M.write32 m a v) (a + BitVec.ofNat 32 y) n =
      Footprint.bytesAt m (a + BitVec.ofNat 32 y) n := by
  have := bytesAt_write32_add m a v 0 y n (by omega) hy (by omega)
  simpa using this

open Lean in
def siteSimpArgs (ts : Syntax.TSepArray `term ",") :
    MacroM (Array (TSyntax [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
      ``Lean.Parser.Tactic.simpLemma])) := do
  let base ← [``atCall, ``Routine.win, ``regions, ``codeR, ``execAll, ``Instr.next, ``Instr.exec,
    ``State.setReg, ``State.sp, ``State.reg, ``lslC, ``blState, ``Hi, ``litState,
    ``sub_sub_ofNat, ``sub_add_ofNat, ``addFlags, ``State.setNZCV, ``State.setNZ,
    ``M0Crypto.Proofs.addWithCarry_fst, ``Instr.exec.memOp, ``M0Crypto.Thumb.read8, ``addWithCarry_true_fst, ``add_add_ofNat,
    ``read32_write32_sub, ``bytesAt_write32_sub, ``read32_write32_add, ``read32_write32_add0,
    ``bytesAt_write32_add, ``read32_write32_base, ``bytesAt_write32_base,
    ``M0Crypto.Armv6M.read32_write32_same, ``bytesAt_write32_self].mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let extra ← ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  return (base.toArray ++ extra).map fun t => ⟨t.raw⟩

macro_rules
  | `(tactic| site_simp [$ts,*] $[$loc]?) => do
    let args ← siteSimpArgs ts
    `(tactic| simp [$args,*] $[$loc]?)
  | `(tactic| site_simpa [$ts,*] using $e) => do
    let args ← siteSimpArgs ts
    `(tactic| simpa [$args,*] using $e)

/-- `sides_tac [h, ...]` closes one side condition: `site_simp`, then `fp_tac`. -/
macro "sides_tac" " [" ts:term,* "]" : tactic => `(tactic| first
  | done
  | ((try site_simp [$ts,*]) <;> fp_tac))

/-- `site_tac [h, ...]` closes the `SiteSides` or `GlueSides` of a call site or glue block. -/
macro "site_tac" " [" ts:term,* "]" : tactic => `(tactic|
  (simp only [SiteSides, GlueSides]; repeat' apply And.intro) <;> sides_tac [$ts,*])

/-- `tr_glue pc [h, ...]` proves `traceAll g t = G` for a glue block `g` whose pcs and addresses
read only the pc, or the pc and `sp`: `G` is `blockTr` of `t`'s pc (`pc : t.pc = …`) and `sp`,
rewritten by `site_simp [h, ...]`. `tr_glue_regs L pc [h, ...]` names the registers `L`. -/
macro "tr_glue " pc:term:max " [" ts:term,* "]" : term =>
  `(by first
    | exact traceAll_blockTr (L := []) (vs := []) (by first | decide | rfl)
        (by first | decide +kernel | rfl) $pc rfl
    | exact traceAll_blockTr (L := [13]) (by first | decide | rfl)
        (by first | decide +kernel | rfl) $pc (by site_simp [$ts,*] <;> rfl))

/-- `tr_glue` with the registers `L` the block's addresses read. -/
macro "tr_glue_regs " L:term:max pc:term:max " [" ts:term,* "]" : term =>
  `(traceAll_blockTr (L := $L) (by first | decide | rfl) (by first | decide +kernel | rfl) $pc
    (by site_simp [$ts,*] <;> rfl))

/-- `tr_call [h, ...]` proves `Φf base (atCall …) = Φc` for a callee with a `TSpec`: its public
values at the call, rewritten by `site_simp [h, ...]`. -/
macro "tr_call" " [" ts:term,* "]" : term =>
  `(Routine.tr_pub (by site_simp [$ts,*] <;> rfl))

/-! ## The outermost call -/

/-- The run of a call from an entry is the model's `runUntil` to the return address. -/
theorem Routine.runUntil_of {f : Routine} {s t : State} {n : Nat} {tr : List Event}
    (e : f.Entry base s) (hr : runH B base n s = .ok (t, tr))
    (hok : StepsOk base (Step (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s)) n s)
    (hq : f.Ret s t) :
    ∀ fuel, n ≤ fuel → Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) := by
  have hwc := e.wr_not_code
  have hev := (stepsOk_events_iff (p := fun ev => ev.pc ≠ s.regs 14 &&& ~~~1#32 ∧
      ∀ y, Writes ev.accesses y → f.WrP s y) hr).mp
    (hok.mono fun _ _ h => ⟨fun he => e.ret (he ▸ h.1), h.2.1⟩)
  intro fuel hfu
  apply runUntil_of_runH n fuel s t tr e.code hr _ _ hq.pc hfu
  · intro ev he i hi hwr
    exact hwc _ ((hev ev he).2 _ hwr) i hi rfl
  · intro ev he
    exact (hev ev he).1

/-- **A call lemma gives the model's run.** At the outermost call, with the return address
outside the routine's code, the judgment is the model's `runUntil` to the return address, with
its writes in the write footprint and its reads in the read footprint. -/
theorem Routine.runUntil {f : Routine} (hf : f.Spec) {s : State} (e : f.Entry base s) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr) ∧
      f.Ret s t ∧ WritesTo (f.WrP s) tr ∧ ReadsFrom (f.RdP base s) tr := by
  obtain ⟨n, t, tr, hr, hok, hQ⟩ := hf base s e
  have hev := (stepsOk_events_iff (p := fun e => (∀ y, Writes e.accesses y → f.WrP s y) ∧
      ∀ y, Reads e.accesses y → f.RdP base s y) hr).mp (hok.mono fun _ _ h => ⟨h.2.1, h.2.2.1⟩)
  exact ⟨n, fun fuel hfu => ⟨t, tr, Routine.runUntil_of e hr hok hQ fuel hfu, hQ,
    fun e he y hy => (hev e he).1 y hy, fun e he y hy => (hev e he).2 y hy⟩⟩

/-- **A constant-time call lemma from a relational one**: two entries with equal public values
return to the same address with the same trace, for every fuel. -/
theorem Routine.tspec_of_ct {ι α : Type} {f : ι → Routine} {pub : Word → State → α}
    (hf : ∀ i, (f i).Spec)
    (hct : ∀ i j base s₁ s₂, (f i).Entry base s₁ → (f j).Entry base s₂ →
      pub base s₁ = pub base s₂ → s₂.regs 14 = s₁.regs 14 ∧
        ∀ fuel, (Thumb.runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₁).map Prod.snd =
          (Thumb.runUntil (s₁.regs 14 &&& ~~~1#32) fuel s₂).map Prod.snd) :
    Routine.TSpec f pub := by
  refine Routine.tspec_of (fun b p tr => ∃ i s, (f i).Entry b s ∧ pub b s = p ∧ ∃ n, ∀ fuel,
    n ≤ fuel → ∃ t, Thumb.runUntil (s.regs 14 &&& ~~~1#32) fuel s = .ok (t, tr)) ?_ ?_
  · rintro b p tr tr' ⟨i, s₁, e₁, h₁, n₁, hn₁⟩ ⟨j, s₂, e₂, h₂, n₂, hn₂⟩
    obtain ⟨hlr, hc⟩ := hct i j b s₁ s₂ e₁ e₂ (h₁.trans h₂.symm)
    obtain ⟨t₁, r₁⟩ := hn₁ (max n₁ n₂) (Nat.le_max_left _ _)
    obtain ⟨t₂, r₂⟩ := hn₂ (max n₁ n₂) (Nat.le_max_right _ _)
    have h := hc (max n₁ n₂)
    rw [r₁, ← hlr, r₂] at h
    simpa [Except.map] using h
  · intro i base s e
    obtain ⟨n, t, tr, hr, hok, hq⟩ := hf i base s e
    exact ⟨n, t, tr, hr, hok, hq, i, s, e, rfl, n, fun fuel h => ⟨t, Routine.runUntil_of e hr hok hq fuel h⟩⟩

/-! ## Read bounds from the model's run -/

theorem StepsOk.and {P1 P2 : State → Event → Prop} :
    ∀ {n : Nat} {s : State}, StepsOk base P1 n s → StepsOk base P2 n s →
      StepsOk base (fun x e => P1 x e ∧ P2 x e) n s
  | 0, _, _, _ => trivial
  | _ + 1, _, h1, h2 => fun s1 e hs =>
    ⟨⟨(h1 s1 e hs).1, (h2 s1 e hs).1⟩, StepsOk.and (h1 s1 e hs).2 (h2 s1 e hs).2⟩

/-- A judgment to a stop address `ret` that its steps avoid, with a read bound on the model's run
to `ret`, has that read bound at every step. -/
theorem ReachS.withReads {P : State → Event → Prop} {Rd W : Word → Prop} {s : State} {ret : Word}
    {Q : State → Prop} (hc : CodeAt s.mem base B)
    (hP : ∀ x e, P x e → e.pc ≠ ret ∧ ∀ y, Writes e.accesses y → W y)
    (hwc : ∀ y, W y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hrd : ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil ret fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom Rd tr)
    (h : ReachS base P s fun t => t.pc = ret ∧ Q t) :
    ReachS base (fun x e => P x e ∧ ∀ y, Reads e.accesses y → Rd y) s fun t => t.pc = ret ∧ Q t := by
  obtain ⟨n, t, tr, hr, hok, hq⟩ := h
  obtain ⟨m, hm⟩ := hrd
  have hev := (stepsOk_events_iff (p := fun e => e.pc ≠ ret ∧ ∀ y, Writes e.accesses y → W y)
    hr).mp (hok.mono fun x e h => hP x e h)
  have hru := runUntil_of_runH n (max n m) s t tr hc hr
    (fun e he i hi hw => hwc _ ((hev e he).2 _ hw) i hi rfl) (fun e he => (hev e he).1) hq.1
    (Nat.le_max_left _ _)
  obtain ⟨t', tr', hru', hR⟩ := hm (max n m) (Nat.le_max_right _ _)
  have htr := (ConstantTime.runUntil_success_unique hru hru').2
  have hrs : StepsOk base (fun _ e => ∀ y, Reads e.accesses y → Rd y) n s :=
    (stepsOk_events_iff (p := fun e => ∀ y, Reads e.accesses y → Rd y) hr).mpr
      (fun e he => hR e (htr ▸ he))
  exact ⟨n, t, tr, hr, StepsOk.and hok hrs, hq⟩

/-- **A functional judgment as a `ReachF` judgment**: its steps run in `Pc`, which misses the
stop address `ret`, write in `Wr`, which misses the code, and keep `sp` in `Sp`; the model's run
to `ret` reads in `Rd`. -/
theorem ReachS.toReachF {P : State → Event → Prop} {s : State} {ret : Word} {Q : State → Prop}
    (hc : CodeAt s.mem base B)
    (hP : ∀ x e, P x e → Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧ Sp (x.regs 13))
    (hret : ¬ Pc ret) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hrd : ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil ret fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom Rd tr)
    (h : ReachS base P s fun t => t.pc = ret ∧ Q t) :
    ReachF base Pc Rd Wr Sp s fun t => t.pc = ret ∧ Q t :=
  (ReachS.withReads hc (fun x e h => ⟨fun he => hret (by rw [← he]; exact (hP x e h).1), (hP x e h).2.1⟩) hwc hrd
    h).mono (fun x e h => ⟨(hP x e h.1).1, (hP x e h.1).2.1, h.2, (hP x e h.1).2.2⟩) fun _ h => h

/-- The steps of a Harvard run from a state reachable before `stop`, none at `stop` and none
writing the code, are from states reachable before `stop`. -/
theorem _root_.M0Crypto.Release.StepsOk.beforeStop {P : State → Event → Prop} {stop : Word}
    {s0 : State} (hP : ∀ x e, P x e → e.pc ≠ stop ∧ MissesCode B base e.accesses) :
    ∀ {n : Nat} {s : State}, CodeAt s.mem base B → ConstantTime.BeforeStop stop s0 s →
      StepsOk base P n s →
      StepsOk base (fun x e => P x e ∧ ConstantTime.BeforeStop stop s0 x ∧ e.pc = x.pc) n s
  | 0, _, _, _, _ => trivial
  | _ + 1, s, hc, hb, h => fun s1 e hs => by
    obtain ⟨hp, h'⟩ := h s1 e hs
    have hst := step_of_stepH hc hs
    have hne : s.pc ≠ stop := by rw [← stepH_pc hs]; exact (hP _ _ hp).1
    exact ⟨⟨hp, hb, stepH_pc hs⟩, StepsOk.beforeStop hP (codeAt_step hc hst (hP _ _ hp).2)
      (ConstantTime.BeforeStop.next hb hne hst) h'⟩

/-- **A functional judgment with a pc bound as a `ReachF` judgment**: its steps run in `Pc`,
which misses the stop address `ret`, and write in `Wr`, which misses the code; every state
reachable before `ret` has `sp` in `Sp`; the model's run to `ret` reads in `Rd`. -/
theorem ReachS.toReachF_sp {P : State → Event → Prop} {s : State} {ret : Word} {Q : State → Prop}
    (hc : CodeAt s.mem base B) (hP : ∀ x e, P x e → Pc e.pc ∧ ∀ y, Writes e.accesses y → Wr y)
    (hret : ¬ Pc ret) (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hS : ∀ u, ConstantTime.BeforeStop ret s u → u.pc ≠ ret → Sp (u.regs 13))
    (hrd : ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil ret fuel s = .ok (t, tr) ∧
      TraceSpec.ReadsFrom Rd tr)
    (h : ReachS base P s fun t => t.pc = ret ∧ Q t) :
    ReachF base Pc Rd Wr Sp s fun t => t.pc = ret ∧ Q t := by
  obtain ⟨n, t, tr, hr, hok, hq⟩ := h
  have hne : ∀ x e, P x e → e.pc ≠ ret := fun x e h he => hret (he ▸ (hP x e h).1)
  refine ReachS.toReachF hc (fun x e h => ⟨(hP x e h.1).1, (hP x e h.1).2,
    hS x h.2.1 (by rw [← h.2.2]; exact hne x e h.1)⟩) hret hwc hrd ⟨n, t, tr, hr,
    StepsOk.beforeStop (fun x e h => ⟨hne x e h, fun i hi hw => hwc _ ((hP x e h).2 _ hw) i hi rfl⟩)
      hc ConstantTime.BeforeStop.initial hok, hq⟩

/-! ## The frame of a routine

A routine with the shape `push {mask, lr}; sub sp, #4k; … ; add sp, #4k; pop {mask, pc}` (mask a
subset of `r4`-`r7`) meets its `Spec` when its body does (`Routine.spec_of_frame`). The body
runs from the state after the `sub` to the `add`. It may write the window below the saved
registers and the routine's write footprint, must return with `sp` where it found it and keep
`r4`-`r11` other than the saved ones, and establishes `Post`. The saved registers and `lr` come
back from the stack: the body's write bound misses them, so they are intact at the `pop`.
-/


/-- Words pushed by `push {mask, lr}`. -/
def nSaved (mask : BitVec 8) : Nat := bitCount mask + 1

/-- `push {mask, lr}` saves `r`. -/
def Saves (mask : BitVec 8) (r : Reg) : Prop := ∃ x ∈ listRegs mask, x.toReg = r

instance (mask : BitVec 8) (r : Reg) : Decidable (Saves mask r) := by
  unfold Saves; infer_instance

@[simp] theorem nSaved_0 : nSaved 0 = 1 := rfl
@[simp] theorem nSaved_10 : nSaved 0x10 = 2 := rfl
@[simp] theorem nSaved_70 : nSaved 0x70 = 4 := rfl
@[simp] theorem nSaved_F0 : nSaved 0xF0 = 5 := rfl
@[simp] theorem bitCount_0 : bitCount (BitVec.ofNat 8 0) = 0 := rfl
@[simp] theorem bitCount_10 : bitCount (BitVec.ofNat 8 0x10) = 1 := rfl
@[simp] theorem bitCount_70 : bitCount (BitVec.ofNat 8 0x70) = 3 := rfl
@[simp] theorem bitCount_F0 : bitCount (BitVec.ofNat 8 0xF0) = 4 := rfl

/-- The pushed words. -/
def saved (mask : BitVec 8) (s : State) : Rgn :=
  ⟨s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask), 4 * nSaved mask⟩

/-- The window below the pushed words. -/
def lowWin (f : Routine) (mask : BitVec 8) (s : State) : Rgn :=
  ⟨s.regs 13 - BitVec.ofNat 32 f.stack, f.stack - 4 * nSaved mask⟩

theorem bitCount_le (l : BitVec 8) : bitCount l ≤ 8 := by
  unfold bitCount listRegs
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem listRegs_nodup (l : BitVec 8) : ((listRegs l).map LowReg.toReg).Nodup :=
  List.Pairwise.map LowReg.toReg (fun _ _ h he => h (Fin.ext (show _ from congrArg (fun r : Reg => r.val) he)))
    (List.Pairwise.filter _ (List.nodup_finRange 8))

/-- `loadRegs` over distinct registers: each gets its word. -/
theorem loadRegs_at (s : State) : ∀ (a : Word) (rs : List Reg), rs.Nodup → ∀ i (hi : i < rs.length),
    (loadRegs s a rs).regs rs[i] = read32 s.mem (a + BitVec.ofNat 32 (4 * i))
  | _, [], _, i, hi => absurd hi (by simp)
  | a, r :: rs, hn, 0, _ => by
    simp only [loadRegs, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero]
    rw [loadRegs_regs_ne _ _ _ _ (List.nodup_cons.mp hn).1]
    simp [State.setReg]
  | a, r :: rs, hn, i + 1, hi => by
    simp only [loadRegs, List.getElem_cons_succ]
    rw [loadRegs_at _ (a + 4#32) rs (List.nodup_cons.mp hn).2 i (by simpa using hi)]
    simp only [setReg_mem]
    congr 1
    rw [show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_assoc]
    congr 2; omega

theorem words_writes {k : Kind} {a y : Word} {n : Nat} (h : Writes (wordAccesses k a n) y) :
    ∃ o < 4 * n, y = a + BitVec.ofNat 32 o := by
  obtain ⟨acc, hm, _, j, hj, rfl⟩ := h
  simp only [wordAccesses, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  exact ⟨4 * i + j, by simp at hj; omega, by simp only; rw [ofNat_add_assoc]⟩

theorem words_reads {k : Kind} {a y : Word} {n : Nat} (h : Reads (wordAccesses k a n) y) :
    ∃ o < 4 * n, y = a + BitVec.ofNat 32 o := by
  obtain ⟨acc, hm, _, j, hj, rfl⟩ := h
  simp only [wordAccesses, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  exact ⟨4 * i + j, by simp at hj; omega, by simp only; rw [ofNat_add_assoc]⟩

theorem words_no_reads {a y : Word} {n : Nat} : ¬ Reads (wordAccesses .write a n) y := by
  rintro ⟨acc, hm, hk, _⟩
  simp only [wordAccesses, List.mem_map, List.mem_range] at hm
  obtain ⟨_, _, rfl⟩ := hm; cases hk

theorem words_no_writes {a y : Word} {n : Nat} : ¬ Writes (wordAccesses .read a n) y := by
  rintro ⟨acc, hm, hk, _⟩
  simp only [wordAccesses, List.mem_map, List.mem_range] at hm
  obtain ⟨_, _, rfl⟩ := hm; cases hk

theorem words_aligned (k : Kind) (a : Word) (n : Nat) (ha : a.toNat % 4 = 0) :
    (wordAccesses k a n).all Access.aligned = true := by
  simp only [wordAccesses, List.all_eq_true, List.mem_map, List.mem_range, Access.aligned]
  rintro _ ⟨i, _, rfl⟩
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, beq_iff_eq]
  have := a.isLt
  omega

/-! ## The four frame instructions -/

section steps
variable (s : State) (l : BitVec 8) (i7 : BitVec 7)

theorem push_exec : (Instr.push l true).exec s = .ok ((Instr.push l true).next s) := rfl

theorem push_sp :
    ((Instr.push l true).next s).regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved l) := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, nSaved]

theorem push_pc : ((Instr.push l true).next s).pc = s.pc + 2#32 := by
  simp [Instr.next, Instr.exec, State.setReg, State.pc, Instr.size]

theorem push_regs (r : Reg) (h13 : r ≠ 13) (h15 : r ≠ 15) :
    ((Instr.push l true).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, h13, h15]

theorem push_mem : ((Instr.push l true).next s).mem = storeWords s.mem
    (s.regs 13 - BitVec.ofNat 32 (4 * nSaved l)) ((listRegs l).map (fun x => s.regs x.toReg) ++ [s.regs 14]) := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp, State.reg, nSaved]

theorem subSp_exec : (Instr.subSp i7).exec s = .ok ((Instr.subSp i7).next s) := rfl
theorem addSp_exec : (Instr.addSp i7).exec s = .ok ((Instr.addSp i7).next s) := rfl

theorem subSp_sp : ((Instr.subSp i7).next s).regs 13 = s.regs 13 - BitVec.ofNat 32 (i7.toNat * 4) := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp]

theorem addSp_sp : ((Instr.addSp i7).next s).regs 13 = s.regs 13 + BitVec.ofNat 32 (i7.toNat * 4) := by
  simp [Instr.next, Instr.exec, State.setReg, State.sp]

theorem subSp_pc : ((Instr.subSp i7).next s).pc = s.pc + 2#32 := by
  simp [Instr.next, Instr.exec, State.setReg, State.pc, Instr.size]

theorem addSp_pc : ((Instr.addSp i7).next s).pc = s.pc + 2#32 := by
  simp [Instr.next, Instr.exec, State.setReg, State.pc, Instr.size]

theorem subSp_regs (r : Reg) (h13 : r ≠ 13) (h15 : r ≠ 15) :
    ((Instr.subSp i7).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, h13, h15]

theorem addSp_regs (r : Reg) (h13 : r ≠ 13) (h15 : r ≠ 15) :
    ((Instr.addSp i7).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, h13, h15]

theorem subSp_mem : ((Instr.subSp i7).next s).mem = s.mem := rfl
theorem addSp_mem : ((Instr.addSp i7).next s).mem = s.mem := rfl

/-- The state `pop {l, pc}` leaves. -/
def popState : State :=
  ((loadRegs (s.setReg 15 (s.pc + 2#32)) s.sp ((listRegs l).map LowReg.toReg)).setReg 13
    (s.sp + BitVec.ofNat 32 (4 * nSaved l))).setReg 15
    (read32 s.mem (s.sp + BitVec.ofNat 32 (4 * bitCount l)) &&& ~~~1#32)

theorem pop_exec (h : (read32 s.mem (s.regs 13 + BitVec.ofNat 32 (4 * bitCount l))).getLsbD 0 = true) :
    (Instr.pop l true).exec s = .ok (popState s l) := by
  simp only [Instr.exec, State.sp] at h ⊢
  simp only [h, ite_true]
  rfl

theorem popState_pc : (popState s l).pc = read32 s.mem (s.regs 13 + BitVec.ofNat 32 (4 * bitCount l)) &&& ~~~1#32 := by
  simp [popState, State.pc, State.setReg, State.sp]

theorem popState_sp : (popState s l).regs 13 = s.regs 13 + BitVec.ofNat 32 (4 * nSaved l) := by
  simp [popState, State.setReg, State.sp]

theorem popState_mem : (popState s l).mem = s.mem := by
  simp [popState, loadRegs_mem]

theorem toReg_lt (x : LowReg) : (x.toReg).val < 8 := x.isLt

theorem popState_saved (i : Nat) (hi : i < (listRegs l).length) :
    (popState s l).regs ((listRegs l)[i]).toReg = read32 s.mem (s.regs 13 + BitVec.ofNat 32 (4 * i)) := by
  have hv : ((listRegs l)[i]).toReg.val < 8 := ((listRegs l)[i]).isLt
  have h13 : ((listRegs l)[i]).toReg ≠ 13 := fun h => by rw [h] at hv; exact absurd hv (by decide)
  have h15 : ((listRegs l)[i]).toReg ≠ 15 := fun h => by rw [h] at hv; exact absurd hv (by decide)
  have := loadRegs_at (s.setReg 15 (s.pc + 2#32)) s.sp _ (listRegs_nodup l) i (by rw [List.length_map]; exact hi)
  simp only [List.getElem_map] at this
  rw [popState, setReg_regs_ne _ _ _ _ h15, setReg_regs_ne _ _ _ _ h13, this]; rfl

/-- A saved register gets back the value `R` gives it, when the stack holds those values. -/
theorem popState_saves (R : Reg → Word) (hm : ∀ i (hi : i < (listRegs l).length),
      read32 s.mem (s.regs 13 + BitVec.ofNat 32 (4 * i)) = R ((listRegs l)[i]).toReg)
    (r : Reg) (hs : Saves l r) : (popState s l).regs r = R r := by
  obtain ⟨x, hx, rfl⟩ := hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [popState_saved s l i hi, hm i hi]

theorem popState_other (r : Reg) (h13 : r ≠ 13) (h15 : r ≠ 15) (hs : ¬ Saves l r) :
    (popState s l).regs r = s.regs r := by
  simp only [popState, State.setReg, h13, h15, ite_false]
  rw [loadRegs_regs_ne _ _ _ _ (fun hm => hs (by
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm; exact ⟨x, hx, he⟩))]
  simp [State.setReg, h15]

end steps

theorem ne13 {r : Reg} (h : r.val ≠ 13) : r ≠ 13 := fun he => h (by rw [he]; rfl)
theorem ne15 {r : Reg} (h : r.val ≠ 15) : r ≠ 15 := fun he => h (by rw [he]; rfl)

theorem win_has {f : Routine} {s : State} {d o : Nat} (hd : d ≤ f.stack) (ho : o < d) :
    (f.win s).Has (s.regs 13 - BitVec.ofNat 32 d + BitVec.ofNat 32 o) := by
  have := (s.regs 13).isLt
  refine ⟨f.stack - d + o, by simp only [Routine.win]; omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [Routine.win, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem pc_add {s : State} {o : Nat} (h : s.pc = base + BitVec.ofNat 32 o) :
    s.pc + 2#32 = base + BitVec.ofNat 32 (o + 2) := by
  rw [h, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_assoc]

theorem rangesSub_trans {cs ds es : List (Nat × Nat)} (h1 : rangesSub cs ds = true)
    (h2 : rangesSub ds es = true) : rangesSub cs es = true := by
  simp only [rangesSub, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  intro p hp
  obtain ⟨q, hq, a, b⟩ := h1 p hp
  obtain ⟨r, hr, c, d⟩ := h2 q hq
  exact ⟨r, hr, by omega, by omega⟩

/-- **A routine from its `push {mask, lr}` … `pop {mask, pc}` frame**, for a routine that may
change the registers `f.clob`. -/
theorem ReachFT.push_popK {f : Routine} {mask : BitVec 8} {epi : Nat} {s : State} {sp : Word}
    {Ψ : TrP}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hpop : instrAt B epi = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hent : f.entry + 2 ≤ BS)
    (hepi : epi + 2 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 2), (epi, epi + 2)] f.code = true)
    (hst : 4 * nSaved mask ≤ f.stack)
    (e : f.Entry base s) (hsp : s.regs 13 = sp)
    (body : ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 2) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ f.clob → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) Ψ) :
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 f.entry, .push mask true,
          wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 epi, .pop mask true,
          wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))) := by
  subst hsp
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hb8 := bitCount_le mask
  have hns : nSaved mask = bitCount mask + 1 := rfl
  have hroom := e.room
  have hsp4 := e.sp4
  have hsplt := (s.regs 13).isLt
  have hcodeW := e.sepCode
  have hwr : ∀ {d o}, d ≤ f.stack → o < d →
      f.WrP s (s.regs 13 - BitVec.ofNat 32 d + BitVec.ofNat 32 o) :=
    fun hd ho => ⟨f.win s, List.mem_cons_self, win_has hd ho⟩
  have hrd : ∀ {d o}, d ≤ f.stack → o < d →
      f.RdP base s (s.regs 13 - BitVec.ofNat 32 d + BitVec.ofNat 32 o) :=
    fun hd ho => ⟨f.win s, List.mem_cons_of_mem _ List.mem_cons_self, win_has hd ho⟩
  have hspw : ∀ {d}, d ≤ f.stack → f.SpP s (s.regs 13 - BitVec.ofNat 32 d) :=
    fun hd => ⟨_, hd, rfl⟩
  -- `push {mask, lr}`
  let vals := (listRegs mask).map (fun x => s.regs x.toReg) ++ [s.regs 14]
  have hvl : vals.length = nSaved mask := by simp [vals, nSaved, bitCount]
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = (Instr.push mask true).next s := ⟨_, rfl⟩
  refine ReachFT.step (s1 := s1) hb2 (.push mask true) e.pc he2 hpush
    (by rw [B_len]; simp [Instr.size]; omega)
    (by simp only [Instr.accesses]
        exact words_aligned _ _ _ (by
          simp only [State.sp, BitVec.toNat_sub, BitVec.toNat_ofNat, Bool.toNat_true]; omega))
    (by rw [hs1]; exact push_exec s mask)
    (PcIn.mono hcode (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega))) ?_ ?_
    ⟨0, Nat.zero_le _, by simp⟩ (by rw [e.pc]; simp [Instr.accesses, State.sp, nSaved]) ?_
  · intro y hy
    simp only [Instr.accesses, State.sp, Bool.toNat_true] at hy
    obtain ⟨o, ho, rfl⟩ := words_writes hy
    exact hwr (by omega) ho
  · intro y hy; simp only [Instr.accesses] at hy; exact absurd hy words_no_reads
  have s1_13 : s1.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask) := by
    rw [hs1]; exact push_sp s mask
  have s1_pc : s1.pc = base + BitVec.ofNat 32 (f.entry + 2) := by
    rw [hs1, push_pc]; exact pc_add e.pc
  have s1_r : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → s1.regs r = s.regs r := fun r h13 h15 => by
    rw [hs1, push_regs _ _ _ (ne13 h13) (ne15 h15)]
  have s1_m : s1.mem = storeWords s.mem (s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask)) vals := by
    rw [hs1]; exact push_mem s mask
  -- the body
  have hm1 : MemEq [saved mask s] s.mem s1.mem := by
    intro y hy
    rw [s1_m]
    apply storeWords_other
    intro i j hi hj he
    apply hy
    refine ⟨saved mask s, List.mem_singleton.mpr rfl, 4 * i + j, ?_, ?_⟩
    · rw [hvl] at hi; simp only [saved]; omega
    · rw [he, ofNat_add_assoc]; rfl
  have hsavedSep : Sep [codeR base] [saved mask s] := by
    have h := hcodeW (codeR base) (List.mem_singleton.mpr rfl) (f.win s) List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := h
    simp only [codeR, Routine.win, BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 h2 h3
    fp_simp
    simp only [codeR, saved, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hcode1 : CodeAt s1.mem base B := fun i hi =>
    (hm1 _ (Sep.not_has hsavedSep
      ⟨codeR base, List.mem_singleton.mpr rfl, i, by simp only [codeR]; rw [← B_len]; exact hi, rfl⟩)).trans
      (e.code i hi)
  have hb := (body s1 s1_pc s1_13 s1_r hm1 hcode1).memEq
  refine ReachT.seq (ReachFT.mono hb (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h) (fun _ h => h)
    fun _ h => h) fun v hv => ?_
  · intro y ⟨r, hr, hy⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨o, ho, rfl⟩ := hy
      exact hwr (d := f.stack) (Nat.le_refl _) (by simp only [lowWin] at ho; omega)
    · exact ⟨r, List.mem_cons_of_mem _ hr, hy⟩
  obtain ⟨⟨vpc, v13, vkeep, vpost⟩, vmem⟩ := hv
  -- the saved words are intact
  have hsv : ∀ i (hi : i < vals.length),
      read32 v.mem (v.regs 13 + BitVec.ofNat 32 (4 * i)) = vals[i] := by
    intro i hi
    rw [v13, s1_13, Frame.read32_congr (m := s1.mem) (fun j hj => ?_), s1_m]
    · exact Frame.read32_storeWords_same _ _ _ _ hi (by rw [hvl]; omega)
    apply vmem
    rintro ⟨r, hr, o, ho, he⟩
    have he' := congrArg BitVec.toNat he
    rw [hvl] at hi
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [lowWin, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at ho he'
      omega
    · obtain ⟨h1, h2, h3⟩ := e.sepWr r hr (f.win s) (List.mem_singleton.mpr rfl)
      simp only [Routine.win, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at he' h2 h3
      have := r.a.isLt
      omega
  -- `pop {mask, pc}`
  have v13' : v.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask) := by rw [v13, s1_13]
  have hlr : read32 v.mem (v.regs 13 + BitVec.ofNat 32 (4 * bitCount mask)) = s.regs 14 := by
    rw [hsv _ (by rw [hvl]; omega)]
    simp [vals, List.getElem_append_right, bitCount]
  have hva : (v.regs 13).toNat % 4 = 0 := by
    rw [v13']; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ReachT.mono (ReachFT.step (s1 := popState v mask) hb2 (.pop mask true) vpc hep2 hpop
    (by rw [B_len]; simp [Instr.size]; omega)
    (by simp only [Instr.accesses]; exact words_aligned _ _ _ hva)
    (pop_exec _ _ (by rw [hlr]; exact e.lr))
    (PcIn.mono hcode (PcIn.at (List.mem_cons_of_mem _ List.mem_cons_self) (Nat.le_refl _) (by omega)))
    (fun y hy => by simp only [Instr.accesses] at hy; exact absurd hy words_no_writes)
    ?_ (by rw [v13']; exact hspw (by omega))
    (by rw [vpc]; simp [Instr.accesses, State.sp, v13', nSaved]) (ReachT.done ⟨?_, ?_, ?_, ?_⟩))
    (fun _ _ h => h) (fun _ h => h) Tr.cat_nil
  · intro y hy
    simp only [Instr.accesses, State.sp, Bool.toNat_true] at hy
    obtain ⟨o, ho, rfl⟩ := words_reads hy
    rw [v13']; exact hrd (by omega) (by omega)
  · rw [popState_pc, hlr]
  · rw [popState_sp, v13', BitVec.sub_add_cancel]
  · intro r h4 h11 hK
    by_cases hs : Saves mask r
    · refine popState_saves v mask s.regs (fun i hi => ?_) r hs
      rw [hsv i (by rw [hvl, hns, ← bitCount_listRegs]; omega)]
      simp [vals, List.getElem_append_left, hi]
    · rw [popState_other _ _ r (ne13 (by omega)) (ne15 (by omega)) hs]
      exact vkeep r h4 h11 hs hK
  · have hs0 : ¬ Saves mask 0 := by
      rintro ⟨x, hx, he⟩
      have := hmask x hx
      have := congrArg Fin.val he
      simp [LowReg.toReg] at this; omega
    rw [popState_other _ _ 0 (by decide) (by decide) hs0, popState_mem]
    exact vpost

/-- **A routine from its `push {mask, lr}` … `pop {mask, pc}` frame** (`ReachFT.push_popK`). -/
theorem ReachFT.push_pop {f : Routine} {mask : BitVec 8} {epi : Nat} {s : State} {sp : Word}
    {Ψ : TrP}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hpop : instrAt B epi = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hent : f.entry + 2 ≤ BS)
    (hepi : epi + 2 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 2), (epi, epi + 2)] f.code = true)
    (hst : 4 * nSaved mask ≤ f.stack)
    (e : f.Entry base s) (hsp : s.regs 13 = sp)
    (body : ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 2) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) Ψ) :
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 f.entry, .push mask true,
          wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 epi, .pop mask true,
          wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))) :=
  ReachFT.push_popK hmask hpush hpop he2 hep2 hent hepi hcode hst e hsp fun t a b c d e' =>
    ReachT.mono (body t a b c d e') (fun _ _ h => h) (fun _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, fun r h4' h11 hs _ => h3 r h4' h11 hs, h4⟩) fun _ h => h

theorem Routine.spec_of_push_pop {f : Routine} {mask : BitVec 8} {epi : Nat}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hpop : instrAt B epi = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hent : f.entry + 2 ≤ BS)
    (hepi : epi + 2 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 2), (epi, epi + 2)] f.code = true)
    (hst : 4 * nSaved mask ≤ f.stack)
    (body : ∀ base s, f.Entry base s → ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 2) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachF base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) :
    f.Spec := fun base s e =>
  ReachT.toS (ReachFT.push_pop hmask hpush hpop he2 hep2 hent hepi hcode hst e rfl
    fun t a b c d e' => ReachS.toT (body base s e t a b c d e'))

/-- **A routine from its frame** `push {mask, lr}; sub sp, #4k; … ; add sp, #4k; pop {mask, pc}`, for a
routine that may change the registers `f.clob`. -/
theorem ReachFT.frameK {f : Routine} {mask : BitVec 8} {k epi : Nat} {s : State} {sp : Word}
    {Ψ : TrP}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hsub : instrAt B (f.entry + 2) = some (.subSp (BitVec.ofNat 7 k)))
    (hadd : instrAt B epi = some (.addSp (BitVec.ofNat 7 k)))
    (hpop : instrAt B (epi + 2) = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hepi : epi + 4 ≤ BS)
    (hent : f.entry + 4 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 4), (epi, epi + 4)] f.code = true)
    (hk : k < 128) (hst : 4 * nSaved mask + 4 * k ≤ f.stack)
    (e : f.Entry base s) (hsp : s.regs 13 = sp)
    (body : ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 4) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ f.clob → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) Ψ) :
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 f.entry, .push mask true,
          wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (f.entry + 2), .subSp (BitVec.ofNat 7 k), []⟩])
            (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 epi, .addSp (BitVec.ofNat 7 k), []⟩])))
          (Tr.is [⟨base + BitVec.ofNat 32 (epi + 2), .pop mask true,
            wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))) := by
  refine ReachFT.push_popK (epi := epi + 2) hmask hpush hpop he2 (by omega) (by omega)
    (by omega) (rangesSub_trans (ds := [(f.entry, f.entry + 4), (epi, epi + 4)])
      (by simp [rangesSub]) hcode) (by omega) e hsp ?_
  intro t tpc t13 tr hm hc
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hk7 : (BitVec.ofNat 7 k).toNat = k := by simp; omega
  have hroom := e.room
  have hpc : ∀ off, (f.entry ≤ off ∧ off < f.entry + 4) ∨ (epi ≤ off ∧ off < epi + 4) →
      f.PcP base (base + BitVec.ofNat 32 off) := by
    rintro off (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact PcIn.mono hcode (PcIn.at List.mem_cons_self h1 h2)
    · exact PcIn.mono hcode (PcIn.at (List.mem_cons_of_mem _ List.mem_cons_self) h1 h2)
  -- `sub sp, #4k`
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = (Instr.subSp (BitVec.ofNat 7 k)).next t := ⟨_, rfl⟩
  refine ReachFT.step (s1 := t0) hb2 (.subSp (BitVec.ofNat 7 k)) tpc (by omega) hsub
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [ht0]; exact subSp_exec _ _)
    (hpc _ (Or.inl ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, t13⟩ (by rw [tpc]; rfl) ?_
  have t0_13 : t0.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) := by
    rw [ht0, subSp_sp, t13, hk7, sub_sub_ofNat, Nat.mul_comm k 4]
  have t0_pc : t0.pc = base + BitVec.ofNat 32 (f.entry + 4) := by
    rw [ht0, subSp_pc]; exact pc_add tpc
  have t0_r : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t0.regs r = s.regs r := fun r h13 h15 => by
    rw [ht0, subSp_regs _ _ _ (ne13 h13) (ne15 h15), tr r h13 h15]
  have t0_m : t0.mem = t.mem := by rw [ht0, subSp_mem]
  refine ReachT.seq (body t0 t0_pc t0_13 t0_r (t0_m ▸ hm) (t0_m ▸ hc)) fun v hv => ?_
  obtain ⟨vpc, v13, vkeep, vpost⟩ := hv
  -- `add sp, #4k`
  have hspv : v.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) := by rw [v13, t0_13]
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = (Instr.addSp (BitVec.ofNat 7 k)).next v := ⟨_, rfl⟩
  refine ReachT.mono (ReachFT.step (s1 := v1) hb2 (.addSp (BitVec.ofNat 7 k)) vpc hep2 hadd
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [hv1]; exact addSp_exec _ _)
    (hpc _ (Or.inr ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, hspv⟩ (by rw [vpc]; rfl)
    (ReachT.done ⟨?_, ?_, ?_, ?_⟩)) (fun _ _ h => h) (fun _ h => h) Tr.cat_nil
  · rw [hv1, addSp_pc]; exact pc_add vpc
  · rw [hv1, addSp_sp, hspv, hk7, sub_add_ofNat _ _ _ (by omega), t13]; congr 2; omega
  · intro r h4 h11 hs hK
    rw [hv1, addSp_regs _ _ _ (ne13 (by omega)) (ne15 (by omega))]
    exact vkeep r h4 h11 hs hK
  · rw [hv1, addSp_regs _ _ _ (by decide) (by decide), addSp_mem]
    exact vpost

/-- **A routine from its frame** `push {mask, lr}; sub sp, #4k; … ; add sp, #4k; pop {mask, pc}`
(`ReachFT.frameK`). -/
theorem ReachFT.frame {f : Routine} {mask : BitVec 8} {k epi : Nat} {s : State} {sp : Word}
    {Ψ : TrP}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hsub : instrAt B (f.entry + 2) = some (.subSp (BitVec.ofNat 7 k)))
    (hadd : instrAt B epi = some (.addSp (BitVec.ofNat 7 k)))
    (hpop : instrAt B (epi + 2) = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hepi : epi + 4 ≤ BS)
    (hent : f.entry + 4 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 4), (epi, epi + 4)] f.code = true)
    (hk : k < 128) (hst : 4 * nSaved mask + 4 * k ≤ f.stack)
    (e : f.Entry base s) (hsp : s.regs 13 = sp)
    (body : ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 4) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) Ψ) :
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 f.entry, .push mask true,
          wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (f.entry + 2), .subSp (BitVec.ofNat 7 k), []⟩])
            (Tr.cat Ψ (Tr.is [⟨base + BitVec.ofNat 32 epi, .addSp (BitVec.ofNat 7 k), []⟩])))
          (Tr.is [⟨base + BitVec.ofNat 32 (epi + 2), .pop mask true,
            wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))) :=
  ReachFT.frameK hmask hpush hsub hadd hpop he2 hep2 hepi hent hcode hk hst e hsp fun t a b c d e' =>
    ReachT.mono (body t a b c d e') (fun _ _ h => h) (fun _ ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, fun r h4' h11 hs _ => h3 r h4' h11 hs, h4⟩) fun _ h => h

theorem Routine.spec_of_frame {f : Routine} {mask : BitVec 8} {k epi : Nat}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hsub : instrAt B (f.entry + 2) = some (.subSp (BitVec.ofNat 7 k)))
    (hadd : instrAt B epi = some (.addSp (BitVec.ofNat 7 k)))
    (hpop : instrAt B (epi + 2) = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hepi : epi + 4 ≤ BS)
    (hent : f.entry + 4 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 4), (epi, epi + 4)] f.code = true)
    (hk : k < 128) (hst : 4 * nSaved mask + 4 * k ≤ f.stack)
    (body : ∀ base s, f.Entry base s → ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 4) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachF base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) :
    f.Spec := fun base s e =>
  ReachT.toS (ReachFT.frame hmask hpush hsub hadd hpop he2 hep2 hepi hent hcode hk hst e rfl
    fun t a b c d e' => ReachS.toT (body base s e t a b c d e'))

/-- **A routine's entry gives the caller facts** of its body: the write footprint is the low
window below the pushed words and `wr`. -/
theorem Caller.of_entry {f : Routine} {mask : BitVec 8} {s : State} (e : f.Entry base s) :
    Caller base (s.regs 13) f.stack (lowWin f mask s :: f.wr s) := by
  have hc := e.sepCode
  have hcw := hc _ (List.mem_singleton_self _) _ List.mem_cons_self
  refine ⟨e.base4, e.sp4, e.room, (Sub.sep (g := f.win s :: f.wr s) ?_ hc.symm).symm, hcw.1⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨f.win s, List.mem_cons_self, by simp [lowWin, Routine.win],
      by simp only [lowWin, Routine.win]; omega, hcw.2.1⟩
  · exact ⟨r, List.mem_cons_of_mem _ hr, Nat.le_refl _, Nat.le_refl _,
      (e.sepWr r hr _ (List.mem_singleton_self _)).1⟩

/-- `frame_intro R mask` opens the body of `Routine.spec_of_frame` or `spec_of_push_pop` for the
routine `R` with frame `push {mask, lr}`. It names the body's arguments (`base s e t tpc t13 tr
hm0 hc`), the low registers at its start (`tl`), the layout facts of the entry in `toNat` form
(`hroom`, `hsp4`, `hsC`, `hsW`, `hsR`), the caller facts of the body (`F`) and the frame fact
that the push wrote only the window (`w0`). `frame_intro R mask [a, b]` also unfolds the
definitions `a`, `b` that `R`'s footprints use. `frame_body R mask` is the same for the body
of `ReachFT.frame` or `ReachFT.push_pop`, whose `base s e` are already named. -/
syntax "frame_intro " ident term:max (" [" ident,* "]")? : tactic
/-- `frame_intro` without `intro base s e` (see there). -/
syntax "frame_body " ident term:max (" [" ident,* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| frame_intro $R:ident $mask:term $[[$ts,*]]?) => do
    let ts : Array Lean.Ident := (ts.map (·.getElems)).getD #[]
    `(tactic| (intro base s e; frame_body $R $mask [$ts,*]))
  | `(tactic| frame_body $R:ident $mask:term $[[$ts,*]]?) => do
    let ts : Array Lean.Ident := (ts.map (·.getElems)).getD #[]
    `(tactic| (
      intro t tpc t13 tr hm0 hc
      have tl := Lo.of_forall tr
      have hroom := e.room
      have hsp4 := e.sp4
      have := (s.regs 13).isLt
      have hsC := e.sepCode
      have hsW := e.sepWr
      have hsR := e.sepRd
      simp only [$R:ident, Routine.win, codeR, $[$ts:ident],*] at hroom hsC hsW hsR
      fp_simp at hsC hsW hsR
      have F := Caller.of_entry (mask := $mask) e
      have w0 : MemEq [($R).win s] s.mem t.mem := hm0.mono (by
        simp [Routine.win, saved, nSaved]; fp_tac)))

/-- **The registers a frame does not save are restored**, given the caller's high registers
after a first glue block `g` that does not write them. -/
theorem keep_of_hi {mask : BitVec 8} {g : List Instr} {s t u : State}
    (h : Hi (execAll g t).regs u) (tr : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r)
    (hg : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r →
      g.all (fun i => !(i.dsts.contains r.val)) = true := by decide) :
    ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r :=
  fun r h4 h11 hs => by
    rw [h.get r h4 (by omega) (by omega), execAll_regs_other g t r (by omega) (hg r h4 h11 hs),
      tr r (by omega) (by omega)]

/-- `keep_of_hi` across a second glue block `g2` that writes saved registers, at a state `u`
reached from the first with the same high registers. -/
theorem keep_of_hi₂ {mask : BitVec 8} {g g2 : List Instr} {s t u v : State}
    (h : Hi (execAll g2 u).regs v) (hu : Hi (execAll g t).regs u)
    (tr : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r)
    (hg : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r →
      g.all (fun i => !(i.dsts.contains r.val)) = true := by decide)
    (hg2 : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r →
      g2.all (fun i => !(i.dsts.contains r.val)) = true := by decide) :
    ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → v.regs r = s.regs r :=
  fun r h4 h11 hs => by
    rw [h.get r h4 (by omega) (by omega), execAll_regs_other g2 u r (by omega) (hg2 r h4 h11 hs)]
    exact keep_of_hi hu tr hg r h4 h11 hs

/-- `keep_of_hi` one glue block `g` further: the kept registers at `u` stay kept at `v`. Chains
across any number of glue blocks and calls. -/
theorem keep_step {mask : BitVec 8} {g : List Instr} {s u v : State}
    (h : Hi (execAll g u).regs v)
    (hu : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → u.regs r = s.regs r)
    (hg : ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r →
      g.all (fun i => !(i.dsts.contains r.val)) = true := by decide) :
    ∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → v.regs r = s.regs r :=
  fun r h4 h11 hs => by
    rw [h.get r h4 (by omega) (by omega), execAll_regs_other g u r (by omega) (hg r h4 h11 hs)]
    exact hu r h4 h11 hs

/-! ## Counted loops -/

/-- The decided checks of a loop's back branch at `ob`: it lies in the caller's code `cs` and in
the artifact, and it returns to `o`. -/
def loopOk [CodeBytes B BS] (cs : List (Nat × Nat)) (o ob d N : Nat) (imm : BitVec 8) : Bool :=
  ob % 2 == 0 && rangesSub [(ob, ob + 2)] cs && decide (ob + 2 ≤ BS) &&
  decide (BitVec.ofNat 32 ob + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 o) &&
  decide (d ≤ N)

/-- **A counted loop**: a body from `o` to the branch `b<cond>` at `ob`, which returns to `o`.
`I j` holds before pass `j` and does not depend on the pc. Pass `j` reaches the branch with
`I (j + 1)`, and the branch is taken exactly while `j + 1 < n`. After pass `n - 1` the loop
falls through to `ob + 2` with `I n`. -/
theorem ReachFT.loop {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {Φb : Nat → TrP} {Ψx : TrP} {o ob d : Nat} (F : Caller base sp0 N Wc) (cond : BitVec 4)
    (imm : BitVec 8) (hbr : instrAt B ob = some (.bcond cond imm)) (n : Nat)
    (I : Nat → State → Prop) (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v))
    (hbody : ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t (fun u =>
        u.pc = base + BitVec.ofNat 32 ob ∧ u.regs 13 = sp0 - BitVec.ofNat 32 d ∧
        CodeAt u.mem base B ∧ I (j + 1) u ∧ condPassed cond u = decide (j + 1 < n)) (Φb j))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (ob + 2) → I n t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q Ψx)
    (hok : loopOk cs o ob d N imm = true := by decide) :
    ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (fun j => Tr.cat (Φb j) (Tr.is [⟨base + BitVec.ofNat 32 ob, .bcond cond imm, []⟩]))
          j (n - j) Ψx) := by
  simp only [loopOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hob, hcs⟩, hsz⟩, ht⟩, hd⟩ := hok
  have hb2 : base.toNat % 2 = 0 := by have := F.b4; omega
  have hpc15 : ∀ (u : State) (v : Word), (u.setReg 15 v).pc = v := fun _ _ => by
    simp [State.setReg, State.pc]
  have h15 : ∀ (u : State) (v : Word), (u.setReg 15 v).regs 13 = u.regs 13 := fun _ _ => by
    simp [State.setReg]
  suffices H : ∀ rem j t, rem + j + 1 = n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachFT base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q
        (Tr.rep (fun j => Tr.cat (Φb j) (Tr.is [⟨base + BitVec.ofNat 32 ob, .bcond cond imm, []⟩]))
          j (rem + 1) Ψx) from
    fun j t hj => by rw [show n - j = (n - j - 1) + 1 by omega]; exact H (n - j - 1) j t (by omega)
  intro rem
  induction rem with
  | zero =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := false) hb2 ob o cond imm hpu hob hbr hsz ht
        ⟨by rw [hpu]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega)),
          fun y hy => absurd hy (writes_nil y),
          fun y hy => absurd hy (reads_nil y), by rw [hu13]; exact ⟨d, hd, rfl⟩⟩
        (by rw [hcp]; simp; omega) (ΨT := Ψx) (fun hT => absurd (hcp ▸ hT) (by simp; omega))
        fun _ => hexit _ (hpc15 _ _) (by rw [show n = j + 1 by omega]; exact hpcI _ _ _ hIu)
          (by rw [h15]; exact hu13) hcu) (fun _ _ h => h) (fun _ h => h) fun tr h => ?_
    exact Tr.cat_assoc tr (Tr.cat_mono (fun _ h => h) (Tr.cat_mono (fun _ h => h)
      fun _ h => h.2 rfl) tr h)
  | succ rem ih =>
    intro j t hn hpc hI h13 hc
    refine ReachT.mono (ReachT.seq (hbody j t (by omega) hpc hI h13 hc) fun u ⟨hpu, hu13, hcu, hIu, hcp⟩ =>
      ReachT.bcond (b := true) hb2 ob o cond imm hpu hob hbr hsz ht
        ⟨by rw [hpu]; exact PcIn.mono hcs (PcIn.at List.mem_cons_self (Nat.le_refl _) (by omega)),
          fun y hy => absurd hy (writes_nil y),
          fun y hy => absurd hy (reads_nil y), by rw [hu13]; exact ⟨d, hd, rfl⟩⟩
        (by rw [hcp]; simp; omega) (ΨF := Ψx)
        (fun _ => ih (j + 1) _ (by omega) (hpc15 _ _) (hpcI _ _ _ hIu) (by rw [h15]; exact hu13) hcu)
        fun hF => absurd (hcp ▸ hF) (by simp; omega)) (fun _ _ h => h) (fun _ h => h) fun tr h => ?_
    exact Tr.cat_assoc tr (Tr.cat_mono (fun _ h => h) (Tr.cat_mono (fun _ h => h)
      fun _ h => h.1 rfl) tr h)

/-- **A counted loop**: a body from `o` to the branch `b<cond>` at `ob`, which returns to `o`.
`I j` holds before pass `j` and does not depend on the pc. Pass `j` reaches the branch with
`I (j + 1)`, and the branch is taken exactly while `j + 1 < n`. After pass `n - 1` the loop
falls through to `ob + 2` with `I n`. -/
theorem ReachF.loop {cs : List (Nat × Nat)} {sp0 : Word} {N : Nat} {Rc Wc : List Rgn}
    {Q : State → Prop} {o ob d : Nat} (F : Caller base sp0 N Wc) (cond : BitVec 4)
    (imm : BitVec 8) (hbr : instrAt B ob = some (.bcond cond imm)) (n : Nat)
    (I : Nat → State → Prop) (hpcI : ∀ j t v, I j t → I j (t.setReg 15 v))
    (hbody : ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t fun u =>
        u.pc = base + BitVec.ofNat 32 ob ∧ u.regs 13 = sp0 - BitVec.ofNat 32 d ∧
        CodeAt u.mem base B ∧ I (j + 1) u ∧ condPassed cond u = decide (j + 1 < n))
    (hexit : ∀ t, t.pc = base + BitVec.ofNat 32 (ob + 2) → I n t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q)
    (hok : loopOk cs o ob d N imm = true := by decide) :
    ∀ j t, j < n → t.pc = base + BitVec.ofNat 32 o → I j t →
      t.regs 13 = sp0 - BitVec.ofNat 32 d → CodeAt t.mem base B →
      ReachF base (PcIn base cs) (Has Rc) (Has Wc) (InStackWindow sp0 N) t Q :=
  fun j t hj hpc hI h13 hc => ReachT.toS (ReachFT.loop (Φb := fun _ _ => True) F cond imm hbr n I hpcI
    (fun j t a b c d e => ReachS.toT (hbody j t a b c d e))
    (fun t a b c d => ReachS.toT (hexit t a b c d)) hok j t hj hpc hI h13 hc)

end M0Crypto.Release.Routine
