import M0Crypto.Release.Reach
import M0Crypto.Thumb.SeqScan

/-! Reachability with instruction-sensitive byte-access policies. -/
namespace M0Crypto.Release.CT
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release

/-- Every accessed byte obeys a condition on its source instruction and kind. -/
def EventAccessesTo (allowed : Word → Kind → Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k)

/-- Program counters in a bounded, base-relative prefix of an artifact. -/
def PCBefore (base : Word) (upper : Nat) (pc : Word) : Prop :=
  ∃ off < upper, pc = base + BitVec.ofNat 32 off

/-- All accesses in a fall-through block inherit its instruction-PC bound. -/
theorem traceAll_pcBefore (base : Word) (upper off : Nat) (is : List Instr) (s : State)
    (hf : is.all Instr.falls = true) (hp : s.pc = base + BitVec.ofNat 32 off)
    (hb : off + seqSize is ≤ upper) :
    EventAccessesTo (fun pc _ _ => PCBefore base upper pc) (traceAll is s) := by
  intro e he a ha k hk
  obtain ⟨j, hj, hpc⟩ := traceAll_pc_offset is s hf e he
  refine ⟨off + j, by omega, ?_⟩
  rw [hpc, hp, ofNat_add_assoc]

/-- Program counters in a bounded base-relative instruction interval. -/
def PCBetween (base : Word) (lower upper : Nat) (pc : Word) : Prop :=
  ∃ off, lower ≤ off ∧ off < upper ∧ pc = base + BitVec.ofNat 32 off

/-- Every access in a fall-through block lies within its instruction interval. -/
theorem traceAll_pcBetween (base : Word) (lower upper off : Nat) (is : List Instr) (s : State)
    (hf : is.all Instr.falls = true) (hp : s.pc = base + BitVec.ofNat 32 off)
    (hl : lower ≤ off) (hu : off + seqSize is ≤ upper) :
    EventAccessesTo (fun pc _ _ => PCBetween base lower upper pc) (traceAll is s) := by
  intro e he a ha k hk
  obtain ⟨j, hj, hpc⟩ := traceAll_pc_offset is s hf e he
  refine ⟨off + j, by omega, by omega, ?_⟩
  rw [hpc, hp, ofNat_add_assoc]

def ReachEvents (base : Word) (allowed : Word → Kind → Word → Prop)
    (s : State) (Q : State → Prop) : Prop :=
  ∃ n t tr, runH B base n s = .ok (t, tr) ∧ EventAccessesTo allowed tr ∧ Q t

/-- A trace satisfying a specific access policy also satisfies any weaker policy. -/
theorem EventAccessesTo.mono {allowed allowed' : Word → Kind → Word → Prop}
    {tr : List Event} (h : EventAccessesTo allowed tr)
    (himp : ∀ pc kind addr, allowed pc kind addr → allowed' pc kind addr) :
    EventAccessesTo allowed' tr := by
  intro e he a ha k hk
  exact himp e.pc a.kind _ (h e he a ha k hk)

/-- Weaken the access policy and strengthen the postcondition of a reachability proof. -/
theorem ReachEvents.mono {base : Word} {allowed allowed' : Word → Kind → Word → Prop}
    {s : State} {Q Q' : State → Prop} (h : ReachEvents base allowed s Q)
    (himp : ∀ pc kind addr, allowed pc kind addr → allowed' pc kind addr)
    (hq : ∀ t, Q t → Q' t) : ReachEvents base allowed' s Q' := by
  obtain ⟨n, t, tr, hr, ha, ht⟩ := h
  exact ⟨n, t, tr, hr, ha.mono himp, hq t ht⟩

theorem ReachEvents.done {base : Word} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (h : Q s) : ReachEvents base allowed s Q := by
  exact ⟨0, s, [], rfl, by simp [EventAccessesTo], h⟩

theorem ReachEvents.bind {base : Word} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop}
    (h : ReachEvents base allowed s (fun t => ReachEvents base allowed t Q)) :
    ReachEvents base allowed s Q := by
  obtain ⟨n, t, tr, hr, ha, m, u, tail, ht, hb, hq⟩ := h
  refine ⟨n + m, u, tr ++ tail, ?_, ?_, hq⟩
  · rw [runH_add, hr]; simp only [ht]
  · intro e he a hacc k hk
    rcases List.mem_append.mp he with he | he
    · exact ha e he a hacc k hk
    · exact hb e he a hacc k hk

/-- Combine independently proved policies for the same trace. -/
theorem EventAccessesTo.and {a b : Word → Kind → Word → Prop} {tr : List Event}
    (ha : EventAccessesTo a tr) (hb : EventAccessesTo b tr) :
    EventAccessesTo (fun pc kind y => a pc kind y ∧ b pc kind y) tr := by
  intro e he access hacc k hk
  exact ⟨ha e he access hacc k hk, hb e he access hacc k hk⟩

/-- Ignoring instruction PCs recovers ordinary whole-trace read bounds. -/
theorem EventAccessesTo.readsFrom {allowed : Word → Kind → Word → Prop}
    {tr : List Event} {Rd : Word → Prop} (h : EventAccessesTo allowed tr)
    (hread : ∀ pc y, allowed pc .read y → Rd y) : ReadsFrom Rd tr := by
  intro e he y ⟨a, ha, hk, k, hbound, hy⟩
  rw [hy]
  apply hread e.pc
  simpa [hk] using h e he a ha k hbound

/-- Ignoring instruction PCs recovers ordinary whole-trace write bounds. -/
theorem EventAccessesTo.writesTo {allowed : Word → Kind → Word → Prop}
    {tr : List Event} {Wr : Word → Prop} (h : EventAccessesTo allowed tr)
    (hwrite : ∀ pc y, allowed pc .write y → Wr y) : WritesTo Wr tr := by
  intro e he y ⟨a, ha, hk, k, hbound, hy⟩
  rw [hy]
  apply hwrite e.pc
  simpa [hk] using h e he a ha k hbound

theorem ReachEvents.block {base : Word} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off)
    (ho : off % 2 = 0) (hseq : seqAt B off is = true)
    (hf : is.all Instr.falls = true) (ha : alignedAll is s = true)
    (hacc : EventAccessesTo allowed (traceAll is s))
    (hq : ReachEvents base allowed (execAll is s) Q) : ReachEvents base allowed s Q := by
  obtain ⟨n, u, tr, hr, ht, hq⟩ := hq
  refine ⟨is.length + n, u, traceAll is s ++ tr, ?_, ?_, hq⟩
  · rw [runH_block hb (by rw [B_len]; decide) is off s hpc ho hseq hf ha, hr]
  · intro e he a ha k hk
    rcases List.mem_append.mp he with he | he
    · exact hacc e he a ha k hk
    · exact ht e he a ha k hk

/-- A PC-sensitive execution yields an ordinary write-bounded execution. -/
theorem ReachEvents.toReach {base : Word} {allowed : Word → Kind → Word → Prop}
    {Wr : Word → Prop} {s : State} {Q : State → Prop} (h : ReachEvents base allowed s Q)
    (hw : ∀ pc y, allowed pc .write y → Wr y) : Reach base Wr s Q := by
  obtain ⟨n, t, tr, hr, ha, hq⟩ := h
  exact ⟨n, t, tr, hr, ha.writesTo hw, hq⟩

/-- Policy corresponding to an ordinary write-only reachability bound. -/
def writeOnlyPolicy (Wr : Word → Prop) (_ : Word) (kind : Kind) (y : Word) : Prop :=
  kind = .read ∨ Wr y

/-- Write-bounded traces satisfy the corresponding access policy. -/
theorem WritesTo.toEventAccesses {Wr : Word → Prop} {tr : List Event} (h : WritesTo Wr tr) :
    EventAccessesTo (writeOnlyPolicy Wr) tr := by
  intro e he a ha k hk
  cases hkind : a.kind with
  | read => exact Or.inl rfl
  | write => exact Or.inr (h e he _ ⟨a, ha, hkind, k, hk, rfl⟩)

/-- Lift an ordinary write-bounded execution to its equivalent access policy. -/
theorem Reach.toReachEvents {base : Word} {Wr : Word → Prop} {s : State} {Q : State → Prop}
    (h : Reach base Wr s Q) : ReachEvents base (writeOnlyPolicy Wr) s Q := by
  obtain ⟨n, t, tr, hr, hw, hq⟩ := h
  refine ⟨n, t, tr, hr, ?_, hq⟩
  intro e he a ha k hk
  cases hkind : a.kind with
  | read => exact Or.inl rfl
  | write => exact Or.inr (hw e he _ ⟨a, ha, hkind, k, hk, rfl⟩)

/-- Execute one instruction under a program-counter-sensitive access policy. -/
theorem ReachEvents.step {base : Word} {allowed : Word → Kind → Word → Prop}
    {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hacc : ∀ a ∈ i.accesses s, ∀ k < a.width,
      allowed s.pc a.kind (a.addr + BitVec.ofNat 32 k))
    (hq : ReachEvents base allowed s1 Q) : ReachEvents base allowed s Q := by
  obtain ⟨n, u, tr, hr, ht, hq⟩ := hq
  have hs := stepH_of_instr hb (by rw [B_len]; decide) hpc ho hi hsz ha hex
  refine ⟨n + 1, u, ⟨s.pc, i, i.accesses s⟩ :: tr, ?_, ?_, hq⟩
  · rw [runH_one_step n hs, hr]
  · intro e he a ha k hk
    rcases List.mem_cons.mp he with rfl | he
    · exact hacc a ha k hk
    · exact ht e he a ha k hk

/-- A conditional branch at `off` with target offset `tgt` for `ReachEvents`. -/
theorem ReachEvents.bcond {base : Word} {allowed : Word → Kind → Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → ReachEvents base allowed (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → ReachEvents base allowed (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachEvents base allowed s Q := by
  cases hc : condPassed cond s
  · apply ReachEvents.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, Bool.false_eq_true, ite_false]; rfl)
      (by intro a ha; simp [Instr.accesses] at ha)
    have := hF hc
    rwa [show s.pc + BitVec.ofNat 32 (Instr.bcond cond imm).size = base + BitVec.ofNat 32 (off + 2) by
      rw [hpc, ofNat_add_assoc]; rfl]
  · apply ReachEvents.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, ite_true]; rfl)
      (by intro a ha; simp [Instr.accesses] at ha)
    have := hT hc
    rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- An unconditional branch at `off` with target offset `tgt` for `ReachEvents`. -/
theorem ReachEvents.b {base : Word} {allowed : Word → Kind → Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachEvents base allowed (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachEvents base allowed s Q := by
  apply ReachEvents.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro a ha; simp [Instr.accesses] at ha)
  rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
    rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- A branch-with-link at `off` with target offset `tgt` for `ReachEvents`. -/
theorem ReachEvents.bl {base : Word} {allowed : Word → Kind → Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachEvents base allowed ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachEvents base allowed s Q := by
  apply ReachEvents.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro a ha; simp [Instr.accesses] at ha)
  rw [show s.pc + 4#32 = base + BitVec.ofNat 32 (off + 4) by rw [hpc, ofNat_add_assoc],
    show base + BitVec.ofNat 32 (off + 4) + imm.signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [← ht, ← ofNat_add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]]
  exact hq

end M0Crypto.Release.CT
