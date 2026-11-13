import M0Crypto.Release.X25519Block
import M0Crypto.Release.SymReadChk

/-!
Blocks with bounded reads (plan `x25519-proofs.md`, phase 10, sites).

`ReachR base Pc Wr R`: a `ReachW` whose every event also reads only bytes in `R`. The prologue of
`m0c_x25519` is proved in this form with `R` the two inputs: its only reads are the byte loads
of `scalar` and `point`, so the read bound of the load sites holds for every prologue event.

`BlockReads R is s` is the read half of a block. It holds for any block without a read access
(`blockReads_noRd`, a static check on the instructions) and composes over `++`.
-/

namespace M0Crypto.Release.X25519Block
open M0Crypto.Armv6M (Word Reg LowReg State)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW ReachS InRegion WritesTo RegionWrites BlockOk Region)

/-- Every executed instruction is at a PC in `Pc`, writes only in `Wr` and reads only in `R`. -/
def RegionRW (Pc Wr R : Word → Prop) (_ : State) (e : Event) : Prop :=
  Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧ ∀ y, Reads e.accesses y → R y

abbrev ReachR (base : Word) (Pc Wr R : Word → Prop) (s : State) (Q : State → Prop) : Prop :=
  ReachS base (RegionRW Pc Wr R) s Q

theorem RegionRW.w {Pc Wr R : Word → Prop} {z : State} {e : Event} (h : RegionRW Pc Wr R z e) :
    RegionWrites Pc Wr z e := ⟨h.1, h.2.1⟩

/-- Every read of the block's trace is in `R`. -/
def BlockReads (R : Word → Prop) (is : List Instr) (s : State) : Prop :=
  ∀ e ∈ traceAll is s, ∀ y, Reads e.accesses y → R y

theorem blockReads_append {R : Word → Prop} {is js : List Instr} {s : State}
    (h1 : BlockReads R is s) (h2 : BlockReads R js (execAll is s)) : BlockReads R (is ++ js) s := by
  intro e he
  rw [traceAll_append] at he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

/-- No read access: stores, pushes, `stm` and register-only instructions. -/
def noRd : Instr → Bool
  | .push .. | .strSp .. | .stm .. => true
  | i => X25519Mul.regOnly i

theorem noRd_of_regOnly {i : Instr} (h : X25519Mul.regOnly i = true) : noRd i = true := by
  cases i <;> simp_all [noRd, X25519Mul.regOnly]

theorem all_noRd {is : List Instr} (h : is.all X25519Mul.regOnly = true) : is.all noRd = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun i hi => noRd_of_regOnly (h i hi)

theorem noRd_reads {i : Instr} (h : noRd i = true) (s : State) (y : Word) :
    ¬ Reads (i.accesses s) y := by
  rintro ⟨a, ha, hk, -⟩
  cases i with
  | push l lr =>
    simp only [Instr.accesses, wordAccesses, List.mem_map] at ha
    obtain ⟨_, _, rfl⟩ := ha; cases hk
  | stm n l =>
    simp only [Instr.accesses, wordAccesses, List.mem_map] at ha
    obtain ⟨_, _, rfl⟩ := ha; cases hk
  | strSp t k =>
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha; cases hk
  | _ => simp_all [noRd, X25519Mul.regOnly, Instr.accesses]

theorem blockReads_noRd (R : Word → Prop) :
    ∀ (is : List Instr) (s : State), is.all noRd = true → BlockReads R is s
  | [], _, _ => fun e he => by cases he
  | i :: is, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro e he y hy
    simp only [traceAll, List.mem_cons] at he
    rcases he with rfl | he
    · exact absurd hy (noRd_reads h.1 s y)
    · exact blockReads_noRd R is _ h.2 e he y hy

/-- The reads of a block whose symbolic read check covers them. -/
theorem blockReads_chk {R : Word → Prop} {is : List Instr} {s : State} (rg : List (Reg × Word × Nat))
    (hf : is.all Instr.falls = true) (hc : M0Crypto.Sym.readChk (fun _ => true) rg is = true)
    (hr : ∀ p ∈ rg, ∀ o < p.2.2, R (s.regs p.1 + p.2.1 + BitVec.ofNat 32 o)) : BlockReads R is s := by
  intro e he y hy
  obtain ⟨p, hp, o, ho, rfl⟩ :=
    M0Crypto.Sym.readChk_sound (fun _ => true) rg is (M0Crypto.Sym.sound_all hf) s hc e he rfl y hy
  exact hr p hp o ho

theorem region_add {p : Word} {a o n : Nat} (h : a + o < n) (hn : n < 2 ^ 32) :
    Region p n (p + BitVec.ofNat 32 a + BitVec.ofNat 32 o) := by
  show ((p + BitVec.ofNat 32 a + BitVec.ofNat 32 o) - p).toNat < n
  rw [ofNat_add_assoc, Frame.sub_ofNat_toNat _ _ (by omega)]
  exact h

/-- `ReachW.blockAcc` with the read bound. -/
theorem ReachR.blockAcc {base : Word} {Pc Wr R : Word → Prop} {s : State} {Q : State → Prop}
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hacc : AccAll (AccOk Wr) is s) (hrd : BlockReads R is s) (hr : InRegion Pc base off (seqSize is))
    (hq : ReachR base Pc Wr R (execAll is s) Q) : ReachR base Pc Wr R s Q := by
  refine Release.ReachS.block hb is off s hpc ho hseq hf
    (alignedAll_of_acc (fun _ h => h.1) is s hacc) ?_ hq
  rw [show RegionRW Pc Wr R = fun _ e =>
      Pc e.pc ∧ (∀ y, Writes e.accesses y → Wr y) ∧ ∀ y, Reads e.accesses y → R y from rfl,
    Release.blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  refine ⟨?_, fun y hy => writesTo_of_acc hacc e he y hy, hrd e he⟩
  rw [hep, hpc, ofNat_add_assoc]
  exact hr j hj

/-- `ReachW.blockRuns` with the read bound (`Rd`). -/
theorem ReachR.blockRuns {base : Word} {Pc Wr Rd : Word → Prop} {s : State} {Q R : State → Prop}
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (hrun : Runs (AccOk Wr) is s R) (hrd : BlockReads Rd is s) (hr : InRegion Pc base off (seqSize is))
    (k : ∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize is) → R t → ReachR base Pc Wr Rd t Q) :
    ReachR base Pc Wr Rd s Q :=
  ReachR.blockAcc hb is off hpc ho hseq hf hrun.1 hrd hr
    (k _ (by rw [execAll_pc _ _ hf, hpc, ofNat_add_assoc]) hrun.2)

/-- A segment proved under `P'` and continued under `P`, when `P'` implies `P`. -/
theorem seg {base : Word} {P P' : State → Event → Prop} {s : State} {Q : State → Prop}
    (hp : ∀ z e, P' z e → P z e) (h : ReachS base P' s fun t => ReachS base P t Q) :
    ReachS base P s Q :=
  Release.ReachS.bind (h.mono hp fun _ h => h)

end M0Crypto.Release.X25519Block
