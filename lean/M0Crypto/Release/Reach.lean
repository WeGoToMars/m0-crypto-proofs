import M0Crypto.Thumb.SpBlock
import M0Crypto.Artifacts.Release
import M0Crypto.Proofs.Common
import M0Crypto.Release.Contract

set_option linter.unusedSimpArgs false

/-!
`Reach`: a Harvard run of the release bytes from `s` reaches a state satisfying `Q`,
with every write of the run inside `Wr`.

Whole-function proofs chain blocks and single steps in continuation style
(`Reach.block`, `Reach.step`, `Reach.bind`). `Reach.runUntil` turns a `Reach` that
ends at the return address into the model's `runUntil` (single memory, code
fetched from memory), given that `Wr` misses the code and the return address lies
outside it.
-/

namespace M0Crypto.Release

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb

/-- The word result of addition implemented with carry. -/
theorem add_flags (x y : Word) : (M0Crypto.Armv6M.addWithCarry x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_add]

/-- The word result of subtraction implemented with carry. -/
theorem sub_flags (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_sub,
    Bool.toNat_true]
  omega

theorem sub_carry (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).2.1 = decide (y.toNat ≤ x.toNat) := by
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := x.isLt; have := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not, Decidable.not_not]; omega

theorem B_len : B.length = Artifacts.Release.size := Artifacts.Release.bytes_length

theorem WritesTo.nil (Wr : Word → Prop) : WritesTo Wr [] := by intro e he; cases he

theorem WritesTo.append {Wr : Word → Prop} {t1 t2 : List Event} (h1 : WritesTo Wr t1)
    (h2 : WritesTo Wr t2) : WritesTo Wr (t1 ++ t2) := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem WritesTo.cons {Wr : Word → Prop} {e : Event} {t : List Event}
    (he : ∀ y, Writes e.accesses y → Wr y) (h : WritesTo Wr t) : WritesTo Wr (e :: t) := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | h'
  · exact he
  · exact h e' h'

theorem WritesTo.mono {Wr Wr' : Word → Prop} {t : List Event} (h : WritesTo Wr t)
    (hm : ∀ y, Wr y → Wr' y) : WritesTo Wr' t := fun e he y hy => hm y (h e he y hy)

theorem WritesTo.of_writesIn {Wr : Word → Prop} {t : List Event} {lo : Word} {n : Nat}
    (h : WritesIn t lo n) (hm : ∀ o < n, Wr (lo + BitVec.ofNat 32 o)) : WritesTo Wr t := by
  intro e he y hy
  obtain ⟨o, ho, rfl⟩ := h e he y hy
  exact hm o ho

/-- A straight-line block containing no stores has no write accesses. -/
theorem noWrite_traceAll : ∀ (is : List Instr) (s : State), is.all (!·.writesMem) = true →
    ∀ e ∈ traceAll is s, ∀ y, ¬ Writes e.accesses y
  | [], _, _ => by intro e he; cases he
  | i :: is, s, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    intro e he y ⟨a, ha, hw, _⟩
    rcases List.mem_cons.mp he with rfl | h'
    · rw [accesses_read h.1 s a ha] at hw; cases hw
    · exact noWrite_traceAll is _ (by simpa using h.2) e h' y ⟨a, ha, hw, by assumption⟩

/-- A block with no stores satisfies any write confinement predicate. -/
theorem WritesTo.of_noWritesMem (is : List Instr) (s : State)
    (h : is.all (!·.writesMem) = true) (Wr : Word → Prop) :
    WritesTo Wr (traceAll is s) :=
  fun e he y hy => absurd hy (noWrite_traceAll is s h e he y)

/-! ## Read access and generalized trace access predicates -/

/-- Every read of the trace lies in `Rd`. -/
def ReadsFrom (Rd : Word → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → Rd y

theorem ReadsFrom.nil (Rd : Word → Prop) : ReadsFrom Rd [] := by intro e he; cases he

theorem ReadsFrom.append {Rd : Word → Prop} {t1 t2 : List Event} (h1 : ReadsFrom Rd t1)
    (h2 : ReadsFrom Rd t2) : ReadsFrom Rd (t1 ++ t2) := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem ReadsFrom.cons {Rd : Word → Prop} {e : Event} {t : List Event}
    (he : ∀ y, Reads e.accesses y → Rd y) (h : ReadsFrom Rd t) : ReadsFrom Rd (e :: t) := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | h'
  · exact he
  · exact h e' h'

theorem ReadsFrom.mono {Rd Rd' : Word → Prop} {t : List Event} (h : ReadsFrom Rd t)
    (hm : ∀ y, Rd y → Rd' y) : ReadsFrom Rd' t := fun e he y hy => hm y (h e he y hy)

/-- Reads of a trace lie in `[lo, lo + n)`. -/
def ReadsIn (tr : List Event) (lo : Word) (n : Nat) : Prop :=
  ∀ e ∈ tr, ∀ y, Reads e.accesses y → ∃ o < n, y = lo + BitVec.ofNat 32 o

theorem ReadsFrom.of_readsIn {Rd : Word → Prop} {t : List Event} {lo : Word} {n : Nat}
    (h : ReadsIn t lo n) (hm : ∀ o < n, Rd (lo + BitVec.ofNat 32 o)) : ReadsFrom Rd t := by
  intro e he y hy
  obtain ⟨o, ho, rfl⟩ := h e he y hy
  exact hm o ho

theorem reads_nil (y : Word) : ¬ Reads [] y := by
  intro ⟨a, ha, _⟩; cases ha

theorem writes_nil (y : Word) : ¬ Writes [] y := by
  intro ⟨a, ha, _⟩; cases ha

theorem readsFrom_of_empty (Rd : Word → Prop) {tr : List Event}
    (h : ∀ e ∈ tr, e.accesses = []) : ReadsFrom Rd tr := by
  intro e he y hy
  rw [h e he] at hy
  exact absurd hy (reads_nil y)

theorem writesTo_of_empty (Wr : Word → Prop) {tr : List Event}
    (h : ∀ e ∈ tr, e.accesses = []) : WritesTo Wr tr := by
  intro e he y hy
  rw [h e he] at hy
  exact absurd hy (writes_nil y)

/-- Generalized access predicate on traces: every data access of every event in `tr` satisfies `ap`. -/
def AccessesTo (ap : Access → Prop) (tr : List Event) : Prop :=
  ∀ e ∈ tr, ∀ a ∈ e.accesses, ap a

theorem AccessesTo.nil (ap : Access → Prop) : AccessesTo ap [] := by intro e he; cases he

theorem AccessesTo.append {ap : Access → Prop} {t1 t2 : List Event} (h1 : AccessesTo ap t1)
    (h2 : AccessesTo ap t2) : AccessesTo ap (t1 ++ t2) := by
  intro e he; rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem AccessesTo.cons {ap : Access → Prop} {e : Event} {t : List Event}
    (he : ∀ a ∈ e.accesses, ap a) (h : AccessesTo ap t) : AccessesTo ap (e :: t) := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | h'
  · exact he
  · exact h e' h'

theorem AccessesTo.mono {ap ap' : Access → Prop} {t : List Event} (h : AccessesTo ap t)
    (hm : ∀ a, ap a → ap' a) : AccessesTo ap' t := fun e he a ha => hm a (h e he a ha)

theorem AccessesTo.and {ap1 ap2 : Access → Prop} {t : List Event} (h1 : AccessesTo ap1 t)
    (h2 : AccessesTo ap2 t) : AccessesTo (fun a => ap1 a ∧ ap2 a) t :=
  fun e he a ha => ⟨h1 e he a ha, h2 e he a ha⟩

theorem accessesTo_of_empty (ap : Access → Prop) {tr : List Event}
    (h : ∀ e ∈ tr, e.accesses = []) : AccessesTo ap tr := by
  intro e he a ha
  rw [h e he] at ha
  cases ha

/-- An access satisfies write bounds `Wr`: if it is a write, every accessed byte is in `Wr`. -/
def WriteAccess (Wr : Word → Prop) (a : Access) : Prop :=
  a.kind = .write → ∀ k < a.width, Wr (a.addr + BitVec.ofNat 32 k)

/-- An access satisfies read bounds `Rd`: if it is a read, every accessed byte is in `Rd`. -/
def ReadAccess (Rd : Word → Prop) (a : Access) : Prop :=
  a.kind = .read → ∀ k < a.width, Rd (a.addr + BitVec.ofNat 32 k)

/-- An access satisfies both read bounds `Rd` and write bounds `Wr`. -/
def RWAccess (Rd Wr : Word → Prop) (a : Access) : Prop :=
  ReadAccess Rd a ∧ WriteAccess Wr a

/-- An access satisfies byte-level access predicate `P` on `(kind, addr)`. -/
def ByteAccess (P : Kind → Word → Prop) (a : Access) : Prop :=
  ∀ k < a.width, P a.kind (a.addr + BitVec.ofNat 32 k)

theorem writesTo_iff_accessesTo (Wr : Word → Prop) (tr : List Event) :
    WritesTo Wr tr ↔ AccessesTo (WriteAccess Wr) tr := by
  constructor
  · intro h e he a ha hw k hk
    exact h e he (a.addr + BitVec.ofNat 32 k) ⟨a, ha, hw, k, hk, rfl⟩
  · intro h e he y hy
    obtain ⟨a, ha, hw, k, hk, rfl⟩ := hy
    exact h e he a ha hw k hk

theorem writesTo_to_accessesTo {Wr : Word → Prop} {tr : List Event} (h : WritesTo Wr tr) :
    AccessesTo (WriteAccess Wr) tr :=
  (writesTo_iff_accessesTo Wr tr).mp h

theorem writesTo_of_accessesTo {Wr : Word → Prop} {tr : List Event} (h : AccessesTo (WriteAccess Wr) tr) :
    WritesTo Wr tr :=
  (writesTo_iff_accessesTo Wr tr).mpr h

theorem readsFrom_iff_accessesTo (Rd : Word → Prop) (tr : List Event) :
    ReadsFrom Rd tr ↔ AccessesTo (ReadAccess Rd) tr := by
  constructor
  · intro h e he a ha hr k hk
    exact h e he (a.addr + BitVec.ofNat 32 k) ⟨a, ha, hr, k, hk, rfl⟩
  · intro h e he y hy
    obtain ⟨a, ha, hr, k, hk, rfl⟩ := hy
    exact h e he a ha hr k hk

theorem readsFrom_to_accessesTo {Rd : Word → Prop} {tr : List Event} (h : ReadsFrom Rd tr) :
    AccessesTo (ReadAccess Rd) tr :=
  (readsFrom_iff_accessesTo Rd tr).mp h

theorem readsFrom_of_accessesTo {Rd : Word → Prop} {tr : List Event} (h : AccessesTo (ReadAccess Rd) tr) :
    ReadsFrom Rd tr :=
  (readsFrom_iff_accessesTo Rd tr).mpr h

theorem rwAccessesTo_iff (Rd Wr : Word → Prop) (tr : List Event) :
    AccessesTo (RWAccess Rd Wr) tr ↔ ReadsFrom Rd tr ∧ WritesTo Wr tr := by
  rw [readsFrom_iff_accessesTo, writesTo_iff_accessesTo]
  constructor
  · intro h
    exact ⟨fun e he a ha => (h e he a ha).1, fun e he a ha => (h e he a ha).2⟩
  · intro ⟨hr, hw⟩ e he a ha
    exact ⟨hr e he a ha, hw e he a ha⟩

def Reach (base : Word) (Wr : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ∃ n s' tr, runH B base n s = .ok (s', tr) ∧ WritesTo Wr tr ∧ Q s'

variable {base : Word} {Wr : Word → Prop}

theorem Reach.done {s : State} {Q : State → Prop} (h : Q s) : Reach base Wr s Q :=
  ⟨0, s, [], rfl, WritesTo.nil _, h⟩

theorem Reach.mono {s : State} {Q Q' : State → Prop} (h : Reach base Wr s Q)
    (hq : ∀ t, Q t → Q' t) : Reach base Wr s Q' := by
  obtain ⟨n, s', tr, hr, hw, hQ⟩ := h
  exact ⟨n, s', tr, hr, hw, hq _ hQ⟩

theorem Reach.monoW {s : State} {Q : State → Prop} {Wr' : Word → Prop} (h : Reach base Wr s Q)
    (hw : ∀ y, Wr y → Wr' y) : Reach base Wr' s Q := by
  obtain ⟨n, s', tr, hr, hW, hQ⟩ := h
  exact ⟨n, s', tr, hr, hW.mono hw, hQ⟩

theorem Reach.bind {s : State} {Q : State → Prop}
    (h : Reach base Wr s fun s1 => Reach base Wr s1 Q) : Reach base Wr s Q := by
  obtain ⟨n, s1, t1, h1, w1, n2, s2, t2, h2, w2, hq⟩ := h
  refine ⟨n + n2, s2, t1 ++ t2, ?_, w1.append w2, hq⟩
  rw [runH_add, h1]; simp only [h2]

theorem Reach.runH {s s1 : State} {Q : State → Prop} {n : Nat} {tr : List Event}
    (h : runH B base n s = .ok (s1, tr)) (hw : WritesTo Wr tr) (hq : Reach base Wr s1 Q) :
    Reach base Wr s Q :=
  Reach.bind ⟨n, s1, tr, h, hw, hq⟩

theorem Reach.block {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hq : Reach base Wr (execAll is s) Q) : Reach base Wr s Q := by
  apply Reach.runH (n := is.length) (tr := traceAll is s) _ hw hq
  rw [runH_seq hb (by rw [B_len]; decide) is off s hpc ho hseq hf, runSeq_eq is s hf ha]

theorem Reach.step {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y) (hq : Reach base Wr s1 Q) : Reach base Wr s Q := by
  have h := stepH_of_instr hb (by rw [B_len]; decide) hpc ho hi hsz ha hex
  apply Reach.runH (n := 1) (tr := [⟨s.pc, i, i.accesses s⟩]) _
    (WritesTo.cons hw (WritesTo.nil _)) hq
  rw [runH_one_step 0 h]; rfl

/-- A conditional branch at `off` with target offset `tgt`. -/
theorem Reach.bcond {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → Reach base Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → Reach base Wr (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    Reach base Wr s Q := by
  cases hc : condPassed cond s
  · apply Reach.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, Bool.false_eq_true, ite_false]; rfl)
      (by intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha)
    have := hF hc
    rwa [show s.pc + BitVec.ofNat 32 (Instr.bcond cond imm).size = base + BitVec.ofNat 32 (off + 2) by
      rw [hpc, ofNat_add_assoc]; rfl]
  · apply Reach.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, ite_true]; rfl)
      (by intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha)
    have := hT hc
    rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- An unconditional branch at `off` with target offset `tgt`. -/
theorem Reach.b {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : Reach base Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : Reach base Wr s Q := by
  apply Reach.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro y ⟨a, ha, _⟩; simp [Instr.accesses] at ha)
  rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
    rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-! ## Generalized Reach carrying access predicates (`ReachA`) and read/write bounds (`ReachRW`) -/

/-- `ReachA`: a Harvard run of the release bytes from `s` reaches a state satisfying `Q`,
with every data access of the run satisfying the access predicate `ap`. -/
def ReachA (base : Word) (ap : Access → Prop) (s : State) (Q : State → Prop) : Prop :=
  ∃ n s' tr, runH B base n s = .ok (s', tr) ∧ AccessesTo ap tr ∧ Q s'

variable {ap : Access → Prop}

theorem ReachA.done {s : State} {Q : State → Prop} (h : Q s) : ReachA base ap s Q :=
  ⟨0, s, [], rfl, AccessesTo.nil _, h⟩

theorem ReachA.mono {s : State} {Q Q' : State → Prop} (h : ReachA base ap s Q)
    (hq : ∀ t, Q t → Q' t) : ReachA base ap s Q' := by
  obtain ⟨n, s', tr, hr, ha, hQ⟩ := h
  exact ⟨n, s', tr, hr, ha, hq _ hQ⟩

theorem ReachA.monoA {s : State} {Q : State → Prop} {ap' : Access → Prop}
    (h : ReachA base ap s Q) (ha : ∀ a, ap a → ap' a) : ReachA base ap' s Q := by
  obtain ⟨n, s', tr, hr, hA, hQ⟩ := h
  exact ⟨n, s', tr, hr, hA.mono ha, hQ⟩

theorem ReachA.bind {s : State} {Q : State → Prop}
    (h : ReachA base ap s fun s1 => ReachA base ap s1 Q) : ReachA base ap s Q := by
  obtain ⟨n, s1, t1, h1, a1, n2, s2, t2, h2, a2, hq⟩ := h
  refine ⟨n + n2, s2, t1 ++ t2, ?_, a1.append a2, hq⟩
  rw [runH_add, h1]; simp only [h2]

theorem ReachA.runH {s s1 : State} {Q : State → Prop} {n : Nat} {tr : List Event}
    (h : runH B base n s = .ok (s1, tr)) (ha : AccessesTo ap tr) (hq : ReachA base ap s1 Q) :
    ReachA base ap s Q :=
  ReachA.bind ⟨n, s1, tr, h, ha, hq⟩

theorem ReachA.block {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hacc : AccessesTo ap (traceAll is s))
    (hq : ReachA base ap (execAll is s) Q) : ReachA base ap s Q := by
  apply ReachA.runH (n := is.length) (tr := traceAll is s) _ hacc hq
  rw [runH_seq hb (by rw [B_len]; decide) is off s hpc ho hseq hf, runSeq_eq is s hf ha]

theorem ReachA.step {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hacc : ∀ a ∈ i.accesses s, ap a) (hq : ReachA base ap s1 Q) : ReachA base ap s Q := by
  have h := stepH_of_instr hb (by rw [B_len]; decide) hpc ho hi hsz ha hex
  apply ReachA.runH (n := 1) (tr := [⟨s.pc, i, i.accesses s⟩]) _
    (AccessesTo.cons hacc (AccessesTo.nil _)) hq
  rw [runH_one_step 0 h]; rfl

/-- A conditional branch at `off` with target offset `tgt` for `ReachA`. -/
theorem ReachA.bcond {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → ReachA base ap (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → ReachA base ap (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachA base ap s Q := by
  cases hc : condPassed cond s
  · apply ReachA.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, Bool.false_eq_true, ite_false]; rfl)
      (by intro a ha; simp [Instr.accesses] at ha)
    have := hF hc
    rwa [show s.pc + BitVec.ofNat 32 (Instr.bcond cond imm).size = base + BitVec.ofNat 32 (off + 2) by
      rw [hpc, ofNat_add_assoc]; rfl]
  · apply ReachA.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
      (by simp only [Instr.exec, hc, ite_true]; rfl)
      (by intro a ha; simp [Instr.accesses] at ha)
    have := hT hc
    rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- An unconditional branch at `off` with target offset `tgt` for `ReachA`. -/
theorem ReachA.b {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachA base ap (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachA base ap s Q := by
  apply ReachA.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro a ha; simp [Instr.accesses] at ha)
  rwa [show s.pc + 4#32 + (imm ++ 0#1).signExtend 32 = base + BitVec.ofNat 32 tgt by
    rw [hpc, BitVec.add_assoc, BitVec.add_assoc, ← ht, BitVec.add_assoc]]

/-- A branch-with-link at `off` with target offset `tgt` for `ReachA`. -/
theorem ReachA.bl {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachA base ap ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachA base ap s Q := by
  apply ReachA.step hb off _ hpc ho hi (by rw [B_len]; exact hsz) (by simp [Instr.accesses])
    (by simp only [Instr.exec]; rfl) (by intro a ha; simp [Instr.accesses] at ha)
  rw [show s.pc + 4#32 = base + BitVec.ofNat 32 (off + 4) by rw [hpc, ofNat_add_assoc],
    show base + BitVec.ofNat 32 (off + 4) + imm.signExtend 32 = base + BitVec.ofNat 32 tgt by
      rw [← ht, ← ofNat_add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]]
  exact hq

/-- Conversion: `Reach base Wr s Q` implies `ReachA base (WriteAccess Wr) s Q`. -/
theorem Reach.to_reachA {s : State} {Q : State → Prop} (h : Reach base Wr s Q) :
    ReachA base (WriteAccess Wr) s Q := by
  obtain ⟨n, s', tr, hr, hw, hq⟩ := h
  exact ⟨n, s', tr, hr, (writesTo_iff_accessesTo Wr tr).mp hw, hq⟩

/-- Conversion: `ReachA base (WriteAccess Wr) s Q` implies `Reach base Wr s Q`. -/
theorem Reach.of_reachA {s : State} {Q : State → Prop} (h : ReachA base (WriteAccess Wr) s Q) :
    Reach base Wr s Q := by
  obtain ⟨n, s', tr, hr, ha, hq⟩ := h
  exact ⟨n, s', tr, hr, (writesTo_iff_accessesTo Wr tr).mpr ha, hq⟩

/-- Equivalence between `Reach` and `ReachA` with `WriteAccess`. -/
theorem reach_iff_reachA (base : Word) (Wr : Word → Prop) (s : State) (Q : State → Prop) :
    Reach base Wr s Q ↔ ReachA base (WriteAccess Wr) s Q :=
  ⟨Reach.to_reachA, Reach.of_reachA⟩

/-- `ReachRW`: Harvard run reaching `Q` with reads inside `Rd` and writes inside `Wr`. -/
def ReachRW (base : Word) (Rd Wr : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachA base (RWAccess Rd Wr) s Q

theorem ReachRW.done {Rd : Word → Prop} {s : State} {Q : State → Prop} (h : Q s) :
    ReachRW base Rd Wr s Q :=
  ReachA.done h

theorem ReachRW.mono {Rd : Word → Prop} {s : State} {Q Q' : State → Prop}
    (h : ReachRW base Rd Wr s Q) (hq : ∀ t, Q t → Q' t) : ReachRW base Rd Wr s Q' :=
  ReachA.mono h hq

theorem ReachRW.monoRW {Rd Wr : Word → Prop} {s : State} {Q : State → Prop}
    {Rd' Wr' : Word → Prop} (h : ReachRW base Rd Wr s Q)
    (hr : ∀ y, Rd y → Rd' y) (hw : ∀ y, Wr y → Wr' y) : ReachRW base Rd' Wr' s Q := by
  apply ReachA.monoA h
  rintro a ⟨hR, hW⟩
  constructor
  · intro hkind k hk; exact hr _ (hR hkind k hk)
  · intro hkind k hk; exact hw _ (hW hkind k hk)

theorem ReachRW.monoR {Rd Wr : Word → Prop} {s : State} {Q : State → Prop}
    {Rd' : Word → Prop} (h : ReachRW base Rd Wr s Q)
    (hr : ∀ y, Rd y → Rd' y) : ReachRW base Rd' Wr s Q :=
  ReachRW.monoRW h hr (fun _ hw => hw)

theorem ReachRW.monoW {Rd Wr : Word → Prop} {s : State} {Q : State → Prop}
    {Wr' : Word → Prop} (h : ReachRW base Rd Wr s Q)
    (hw : ∀ y, Wr y → Wr' y) : ReachRW base Rd Wr' s Q :=
  ReachRW.monoRW h (fun _ hr => hr) hw

theorem ReachRW.bind {Rd : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachRW base Rd Wr s fun s1 => ReachRW base Rd Wr s1 Q) : ReachRW base Rd Wr s Q :=
  ReachA.bind h

theorem ReachRW.runH {Rd : Word → Prop} {s s1 : State} {Q : State → Prop} {n : Nat}
    {tr : List Event} (h : runH B base n s = .ok (s1, tr))
    (ha : AccessesTo (RWAccess Rd Wr) tr) (hq : ReachRW base Rd Wr s1 Q) :
    ReachRW base Rd Wr s Q :=
  ReachA.runH h ha hq

theorem ReachRW.block {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hacc : AccessesTo (RWAccess Rd Wr) (traceAll is s))
    (hq : ReachRW base Rd Wr (execAll is s) Q) : ReachRW base Rd Wr s Q :=
  ReachA.block hb is off hpc ho hseq hf ha hacc hq

theorem ReachRW.block_rw {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0)
    (is : List Instr) (off : Nat) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hr : ReadsFrom Rd (traceAll is s)) (hw : WritesTo Wr (traceAll is s))
    (hq : ReachRW base Rd Wr (execAll is s) Q) : ReachRW base Rd Wr s Q :=
  ReachRW.block hb is off hpc ho hseq hf ha ((rwAccessesTo_iff Rd Wr _).mpr ⟨hr, hw⟩) hq

theorem ReachRW.step {Rd : Word → Prop} {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hacc : ∀ a ∈ i.accesses s, RWAccess Rd Wr a) (hq : ReachRW base Rd Wr s1 Q) :
    ReachRW base Rd Wr s Q :=
  ReachA.step hb off i hpc ho hi hsz ha hex hacc hq

theorem ReachRW.step_rw {Rd : Word → Prop} {s s1 : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off : Nat)
    (i : Instr) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hr : ∀ y, Reads (i.accesses s) y → Rd y)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y)
    (hq : ReachRW base Rd Wr s1 Q) : ReachRW base Rd Wr s Q := by
  apply ReachRW.step hb off i hpc ho hi hsz ha hex _ hq
  intro a ha_mem
  constructor
  · intro hkind k hk
    exact hr _ ⟨a, ha_mem, hkind, k, hk, rfl⟩
  · intro hkind k hk
    exact hw _ ⟨a, ha_mem, hkind, k, hk, rfl⟩

theorem ReachRW.bcond {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hT : condPassed cond s = true → ReachRW base Rd Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → ReachRW base Rd Wr (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachRW base Rd Wr s Q :=
  ReachA.bcond hb off tgt cond imm hpc ho hi hsz ht hT hF

theorem ReachRW.b {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachRW base Rd Wr (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) : ReachRW base Rd Wr s Q :=
  ReachA.b hb off tgt imm hpc ho hi hsz ht hq

/-- A branch-with-link at `off` with target offset `tgt` for `ReachRW`. -/
theorem ReachRW.bl {Rd : Word → Prop} {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 25) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bl imm)) (hsz : off + 4 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + imm.signExtend 32 = BitVec.ofNat 32 tgt)
    (hq : ReachRW base Rd Wr ((s.setReg 14 ((base + BitVec.ofNat 32 (off + 4)) ||| 1#32)).setReg 15
      (base + BitVec.ofNat 32 tgt)) Q) : ReachRW base Rd Wr s Q :=
  ReachA.bl hb off tgt imm hpc ho hi hsz ht hq

theorem ReachRW.to_reach {Rd : Word → Prop} {s : State} {Q : State → Prop}
    (h : ReachRW base Rd Wr s Q) : Reach base Wr s Q := by
  apply Reach.of_reachA
  apply ReachA.monoA h
  intro a ⟨_, hw⟩
  exact hw

theorem reachRW_iff (base : Word) (Rd Wr : Word → Prop) (s : State) (Q : State → Prop) :
    ReachRW base Rd Wr s Q ↔
      ∃ n s' tr, runH B base n s = .ok (s', tr) ∧ ReadsFrom Rd tr ∧ WritesTo Wr tr ∧ Q s' := by
  simp only [ReachRW, ReachA, rwAccessesTo_iff, and_assoc]

/-- Conversion: `Reach base Wr s Q` implies `ReachRW base (fun _ => True) Wr s Q`. -/
theorem Reach.to_reachRW (base : Word) (Wr : Word → Prop) {s : State} {Q : State → Prop}
    (h : Reach base Wr s Q) : ReachRW base (fun _ => True) Wr s Q := by
  obtain ⟨n, s', tr, hr, hw, hq⟩ := h
  rw [reachRW_iff]
  refine ⟨n, s', tr, hr, fun _ _ _ _ => trivial, hw, hq⟩

/-- Equivalence between `Reach` and `ReachRW` with unconstrained reads. -/
theorem reach_iff_reachRW_true (base : Word) (Wr : Word → Prop) (s : State) (Q : State → Prop) :
    Reach base Wr s Q ↔ ReachRW base (fun _ => True) Wr s Q :=
  ⟨Reach.to_reachRW base Wr, ReachRW.to_reach⟩

/-! ## From `Reach` to `runUntil` -/

/-- Every event of a successful Harvard run is at an address inside the code. -/
theorem runH_pcs : ∀ (n : Nat) (s s' : State) (tr : List Event),
    runH B base n s = .ok (s', tr) → ∀ e ∈ tr, ∃ off < B.length, e.pc = base + BitVec.ofNat 32 off
  | 0, s, s', tr, h => by
    simp only [Thumb.runH, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; intro e he; cases he
  | n + 1, s, s', tr, h => by
    simp only [Thumb.runH] at h
    split at h
    · cases h
    · rename_i s1 e h1
      split at h
      · cases h
      · rename_i s2 es h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro e' he'
        rcases List.mem_cons.mp he' with rfl | h'
        · unfold stepH at h1; simp only at h1
          split at h1; · cases h1
          split at h1; · cases h1
          rename_i i _
          split at h1
          · rename_i hlen
            split at h1
            · split at h1
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h1
                rw [← h1.2]
                refine ⟨(s.pc - base).toNat, ?_, (base_add_sub s.pc).symm⟩
                have := instr_size_even i
                cases i <;> simp [Instr.size] at hlen ⊢ <;> omega
              · cases h1
            · cases h1
          · cases h1
        · exact runH_pcs n s1 s2 es h2 e' h'

/-- A run reaching `stop`, writing only inside `Wr`, is the model's `runUntil stop`. -/
theorem Reach.runUntil {s : State} {stop : Word} {P : State → Prop}
    (hc : CodeAt s.mem base B)
    (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i)
    (h : Reach base Wr s fun s' => s'.pc = stop ∧ P s') :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil stop fuel s = .ok (s', tr) ∧ P s' ∧
      WritesTo Wr tr := by
  obtain ⟨n, s', tr, hr, hw, hpc, hP⟩ := h
  refine ⟨n, fun fuel hf => ⟨s', tr, ?_, hP, hw⟩⟩
  apply runUntil_of_runH n fuel s s' tr hc hr _ _ hpc hf
  · intro e he i hi hwr
    exact hwc _ (hw e he _ hwr) i hi rfl
  · intro e he heq
    obtain ⟨off, ho, hpe⟩ := runH_pcs n s s' tr hr e he
    exact hstop off ho (heq ▸ hpe)

/-- A run reaching `stop`, with all accesses satisfying `ap`, is the model's `runUntil stop`
provided that writes under `ap` miss the code. -/
theorem ReachA.runUntil {s : State} {stop : Word} {P : State → Prop}
    (hc : CodeAt s.mem base B)
    (hwc : ∀ a, ap a → a.kind = .write → ∀ k < a.width, ∀ i < B.length, a.addr + BitVec.ofNat 32 k ≠ base + BitVec.ofNat 32 i)
    (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i)
    (h : ReachA base ap s fun s' => s'.pc = stop ∧ P s') :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil stop fuel s = .ok (s', tr) ∧ P s' ∧
      AccessesTo ap tr := by
  obtain ⟨n, s', tr, hr, ha, hpc, hP⟩ := h
  refine ⟨n, fun fuel hf => ⟨s', tr, ?_, hP, ha⟩⟩
  apply runUntil_of_runH n fuel s s' tr hc hr _ _ hpc hf
  · intro e he i hi hwr
    obtain ⟨a, ha_mem, hw, k, hk, heq⟩ := hwr
    exact hwc a (ha e he a ha_mem) hw k hk i hi heq.symm
  · intro e he heq
    obtain ⟨off, ho, hpe⟩ := runH_pcs n s s' tr hr e he
    exact hstop off ho (heq ▸ hpe)

/-- A run reaching `stop`, reading inside `Rd` and writing inside `Wr`, is the model's `runUntil stop`. -/
theorem ReachRW.runUntil {Rd : Word → Prop} {s : State} {stop : Word} {P : State → Prop}
    (hc : CodeAt s.mem base B)
    (hwc : ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i)
    (hstop : ∀ i < B.length, stop ≠ base + BitVec.ofNat 32 i)
    (h : ReachRW base Rd Wr s fun s' => s'.pc = stop ∧ P s') :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil stop fuel s = .ok (s', tr) ∧ P s' ∧
      ReadsFrom Rd tr ∧ WritesTo Wr tr := by
  have hwc' : ∀ a, RWAccess Rd Wr a → a.kind = .write → ∀ k < a.width, ∀ i < B.length,
      a.addr + BitVec.ofNat 32 k ≠ base + BitVec.ofNat 32 i := by
    intro a ⟨_, hW⟩ hkind k hk i hi
    exact hwc _ (hW hkind k hk) i hi
  obtain ⟨n, hn⟩ := ReachA.runUntil (ap := RWAccess Rd Wr) hc hwc' hstop h
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨s', tr, hrun, hp, ha⟩ := hn fuel hf
  rw [rwAccessesTo_iff] at ha
  exact ⟨s', tr, hrun, hp, ha.1, ha.2⟩

end M0Crypto.Release
