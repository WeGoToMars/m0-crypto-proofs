import M0Crypto.Release.AccessReach
import M0Crypto.Release.ReachSteps
import M0Crypto.Release.ChaCha20Layout

/-!
# Program-counter regions for the ChaCha20 reachability proofs

The proofs of the prologue, key and nonce loads, epilogue and error entries follow the
function's control flow with `ReachEvents`, a reachability statement that records which
program counters access which bytes. Each such proof is generic in the access policy
`allowed`. It only needs the policy to allow every access made from a program counter in a
region (`Admits`), provided the writes lie in a write set `Wr`.

Two regions matter. The front region lies below the first output store (`achOff`), and the
back region lies from the end of the block loop (`n1Off`) to the end of the artifact. Neither
region contains an output-store program counter.
-/

namespace M0Crypto.Release.ChaCha20Policy

open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.ConstantTime
open M0Crypto.Release.ChaCha20Layout (achOff n1Off berrOff2 keyOff stCtrOff nonOff bpreOff)

/-- A policy admits every access made from a program counter in `Pc` whose writes lie in `Wr`. -/
def Admits (Pc : Word → Prop) (Wr : Word → Prop)
    (allowed : Word → Kind → Word → Prop) : Prop :=
  ∀ pc kind y, Pc pc → (kind = .write → Wr y) → allowed pc kind y

/-- Offset ranges of the front region: before the key loads, between the key and nonce loads,
and from the end of the nonce loads to the first output store. The key and nonce load
instructions themselves are excluded, because they read the caller's key and nonce. -/
abbrev FrontRange (off n : Nat) : Prop :=
  off + n ≤ keyOff ∨ (stCtrOff ≤ off ∧ off + n ≤ nonOff) ∨ (bpreOff ≤ off ∧ off + n ≤ achOff)

/-- Program counters of the front region. -/
def FrontPc (base : Word) (pc : Word) : Prop :=
  PCBefore base keyOff pc ∨ PCBetween base stCtrOff nonOff pc ∨ PCBetween base bpreOff achOff pc

theorem frontRange_le {off n : Nat} (h : FrontRange off n) : off + n ≤ achOff := by
  have h1 : keyOff ≤ achOff := by decide +kernel
  have h2 : nonOff ≤ achOff := by decide +kernel
  rcases h with h | h | h <;> omega

theorem frontPc_before {base pc : Word} (h : FrontPc base pc) : PCBefore base achOff pc := by
  have h1 : keyOff ≤ achOff := by decide +kernel
  have h2 : nonOff ≤ achOff := by decide +kernel
  rcases h with ⟨o, ho, e⟩ | ⟨o, h1', h2', e⟩ | ⟨o, h1', h2', e⟩
  · exact ⟨o, by omega, e⟩
  · exact ⟨o, by omega, e⟩
  · exact ⟨o, by omega, e⟩

theorem traceAll_pcFront (base : Word) (off : Nat) (is : List Instr) (s : State)
    (hf : is.all Instr.falls = true) (hp : s.pc = base + BitVec.ofNat 32 off)
    (hr : FrontRange off (seqSize is)) :
    EventAccessesTo (fun pc _ _ => FrontPc base pc) (traceAll is s) := by
  intro e he a ha k hk
  obtain ⟨j, hj, hpc⟩ := traceAll_pc_offset is s hf e he
  have e' : e.pc = base + BitVec.ofNat 32 (off + j) := by rw [hpc, hp, ofNat_add_assoc]
  rcases hr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨off + j, by omega, e'⟩
  · exact Or.inr (Or.inl ⟨off + j, by omega, by omega, e'⟩)
  · exact Or.inr (Or.inr ⟨off + j, by omega, by omega, e'⟩)

/-- Program counters from the end of the block loop to the end of the artifact. -/
abbrev BackPc (base : Word) : Word → Prop := PCBetween base n1Off Artifacts.Release.size

/-- The ordinary write-only policy admits every access whose writes lie in `Wr`. -/
theorem admits_writeOnly (Pc : Word → Prop) (Wr : Word → Prop) :
    Admits Pc Wr (writeOnlyPolicy Wr) := by
  intro pc kind y _ hw
  cases kind with
  | read => exact Or.inl rfl
  | write => exact Or.inr (hw rfl)

theorem Admits.trace {Pc Wr : Word → Prop} {allowed : Word → Kind → Word → Prop}
    (h : Admits Pc Wr allowed) {tr : List Event}
    (hpc : EventAccessesTo (fun pc _ _ => Pc pc) tr) (hw : WritesTo Wr tr) :
    EventAccessesTo allowed tr := by
  intro e he a ha k hk
  apply h _ _ _ (hpc e he a ha k hk)
  intro hkind
  exact hw e he _ ⟨a, ha, hkind, k, hk, rfl⟩

/-- A fall-through block in the back region. -/
theorem backBlock {base : Word} {Wr : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (h : Admits (BackPc base) Wr allowed)
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hlo : n1Off ≤ off) (hhi : off + seqSize is ≤ Artifacts.Release.size)
    (hq : ReachEvents base allowed (execAll is s) Q) : ReachEvents base allowed s Q :=
  ReachEvents.block hb is off hpc ho hseq hf ha
    (h.trace (traceAll_pcBetween base n1Off Artifacts.Release.size off is s hf hpc hlo hhi) hw) hq


/-! ## Program-counter tracking

`EvP Pc allowed` is the step condition of `ReachEvents base allowed` that also records the
program counter of every executed instruction, including those without memory accesses.
With `Pc := fun _ => True` it is the event-only judgment; with `allowed := writeOnlyPolicy Wr`
it is `ReachW`. The functional proofs need the program counters to know that a call's run
reaches its return address for the first time at its last state. -/

/-- End of the ChaCha20 code: one past the last instruction of `.Lerr_counter`. -/
def chaEnd : Nat := berrOff2 + 2

/-- Program counters of the ChaCha20 function. -/
abbrev ChaPc (base : Word) : Word → Prop := PCBetween base 0 chaEnd

theorem chaRegion {Pc : Word → Prop} {base : Word} (hPc : ∀ pc, ChaPc base pc → Pc pc)
    {off n : Nat} (h : off + n ≤ chaEnd) : InRegion Pc base off n :=
  fun j hj => hPc _ ⟨off + j, by omega, by omega, rfl⟩

theorem chaAt {Pc : Word → Prop} {base : Word} (hPc : ∀ pc, ChaPc base pc → Pc pc)
    {off : Nat} (h : off < chaEnd) : Pc (base + BitVec.ofNat 32 off) :=
  hPc _ ⟨off, by omega, h, rfl⟩

/-- Step condition: the pc is in `Pc` and the accesses obey `allowed`. -/
def EvP (Pc : Word → Prop) (allowed : Word → Kind → Word → Prop) : State → Event → Prop :=
  fun _ e => Pc e.pc ∧ ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k)

theorem reachEvents_toEvP {base : Word} {allowed : Word → Kind → Word → Prop} {s : State}
    {Q : State → Prop} (h : ReachEvents base allowed s Q) :
    ReachS base (EvP (fun _ => True) allowed) s Q :=
  ((reachEvents_iff_reachS allowed s Q).mp h).mono (fun _ _ h => ⟨trivial, h⟩) (fun _ h => h)

theorem ofEvP {base : Word} {Pc : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (h : ReachS base (EvP Pc allowed) s Q) :
    ReachEvents base allowed s Q :=
  (reachEvents_iff_reachS allowed s Q).mpr (h.mono (fun _ _ h => h.2) (fun _ h => h))

theorem ofEvPW {base : Word} {Pc Wr : Word → Prop}
    {s : State} {Q : State → Prop} (h : ReachS base (EvP Pc (writeOnlyPolicy Wr)) s Q) :
    ReachW base Pc Wr s Q :=
  h.mono (fun x e h => ⟨h.1, fun y ⟨a, ha, hk, k, hk', hy⟩ => by
    have := h.2 a ha k hk'
    rw [hk] at this
    rcases this with h | h
    · cases h
    · rw [hy]; exact h⟩) (fun _ h => h)

theorem reachW_toEvP {base : Word} {Pc Wr : Word → Prop}
    {s : State} {Q : State → Prop} (h : ReachW base Pc Wr s Q) :
    ReachS base (EvP Pc (writeOnlyPolicy Wr)) s Q :=
  h.mono (fun x e h => ⟨h.1, fun a ha k hk => by
    cases hkind : a.kind with
    | read => exact Or.inl rfl
    | write => exact Or.inr (h.2 _ ⟨a, ha, hkind, k, hk, rfl⟩)⟩) (fun _ h => h)

/-- A fall-through block in the front region. -/
theorem frontBlockP {base : Word} {Pc Wr : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (h : Admits (FrontPc base) Wr allowed)
    (hPc : ∀ pc, ChaPc base pc → Pc pc)
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hlt : FrontRange off (seqSize is))
    (hq : ReachS base (EvP Pc allowed) (execAll is s) Q) : ReachS base (EvP Pc allowed) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf ha ?_ hq
  rw [show EvP Pc allowed = fun _ e => Pc e.pc ∧ ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k) from rfl, blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  have hd : achOff ≤ chaEnd := by decide +kernel
  have hle := frontRange_le hlt
  refine ⟨hPc _ ⟨off + j, by omega, by omega, by rw [hep, hpc, ofNat_add_assoc]⟩, ?_⟩
  exact fun a ha k hk => h.trace (traceAll_pcFront base off is s hf hpc hlt) hw e he a ha k hk

/-- A fall-through block in the back region. -/
theorem backBlockP {base : Word} {Pc Wr : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (h : Admits (BackPc base) Wr allowed)
    (hPc : ∀ pc, ChaPc base pc → Pc pc)
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hw : WritesTo Wr (traceAll is s))
    (hlo : n1Off ≤ off) (hhi : off + seqSize is ≤ chaEnd)
    (hq : ReachS base (EvP Pc allowed) (execAll is s) Q) : ReachS base (EvP Pc allowed) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf ha ?_ hq
  rw [show EvP Pc allowed = fun _ e => Pc e.pc ∧ ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k) from rfl, blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  refine ⟨hPc _ ⟨off + j, by omega, by omega, by rw [hep, hpc, ofNat_add_assoc]⟩, ?_⟩
  have hs : off + seqSize is ≤ Artifacts.Release.size := by
    have : chaEnd ≤ Artifacts.Release.size := by decide +kernel
    omega
  exact fun a ha k hk => h.trace
    (traceAll_pcBetween base n1Off Artifacts.Release.size off is s hf hpc hlo hs) hw e he a ha k hk

/-- One instruction in the back region. -/
theorem backStepP {base : Word} {Pc Wr : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s s1 : State} {Q : State → Prop} (h : Admits (BackPc base) Wr allowed)
    (hPc : ∀ pc, ChaPc base pc → Pc pc)
    (hb : base.toNat % 2 = 0) (off : Nat) (i : Instr)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some i) (hsz : off + i.size ≤ B.length)
    (ha : (i.accesses s).all Access.aligned = true) (hex : i.exec s = .ok s1)
    (hw : ∀ y, Writes (i.accesses s) y → Wr y)
    (hlo : n1Off ≤ off) (hhi : off + i.size ≤ chaEnd)
    (hq : ReachS base (EvP Pc allowed) s1 Q) : ReachS base (EvP Pc allowed) s Q := by
  refine ReachS.step hb off i hpc ho hi hsz ha hex ⟨?_, ?_⟩ hq
  · have := instr_size_pos i
    exact hPc _ ⟨off, by omega, by omega, hpc⟩
  · have hs : off + i.size ≤ Artifacts.Release.size := by
      have : chaEnd ≤ Artifacts.Release.size := by decide +kernel
      omega
    have := instr_size_pos i
    exact fun a ha' k hk => h _ _ _ ⟨off, hlo, by omega, hpc⟩
      (fun hkind => hw _ ⟨a, ha', hkind, k, hk, rfl⟩)

/-- A fall-through block anywhere in the ChaCha code, with its events admitted by `allowed`. -/
theorem blockP {base : Word} {Pc : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (hPc : ∀ pc, ChaPc base pc → Pc pc)
    (hb : base.toNat % 2 = 0) (is : List Instr) (off : Nat)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hf : is.all Instr.falls = true)
    (ha : alignedAll is s = true) (hacc : EventAccessesTo allowed (traceAll is s))
    (hlt : off + seqSize is ≤ chaEnd)
    (hq : ReachS base (EvP Pc allowed) (execAll is s) Q) : ReachS base (EvP Pc allowed) s Q := by
  refine ReachS.block hb is off s hpc ho hseq hf ha ?_ hq
  rw [show EvP Pc allowed = fun _ e => Pc e.pc ∧ ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k) from rfl, blockOk_events_iff]
  intro e he
  obtain ⟨j, hj, hep⟩ := traceAll_pc_offset is s hf e he
  exact ⟨hPc _ ⟨off + j, by omega, by omega, by rw [hep, hpc, ofNat_add_assoc]⟩, hacc e he⟩

/-- Events of a loop run before the output region satisfy `EvP`. -/
theorem stepsOk_evP {base : Word} {Pc : Word → Prop} {allowed : Word → Kind → Word → Prop}
    (hPc : ∀ pc, ChaPc base pc → Pc pc) {n : Nat} {s t : State} {tr : List Event}
    (hr : runH B base n s = .ok (t, tr))
    (hpcs : ∀ e ∈ tr, ∃ off < achOff, e.pc = base + BitVec.ofNat 32 off)
    (hacc : EventAccessesTo allowed tr) : StepsOk base (EvP Pc allowed) n s := by
  have hd : achOff ≤ chaEnd := by decide +kernel
  exact (stepsOk_events_iff (p := fun e => Pc e.pc ∧ ∀ a ∈ e.accesses, ∀ k < a.width,
    allowed e.pc a.kind (a.addr + BitVec.ofNat 32 k)) hr).mpr
    (fun e he => ⟨by obtain ⟨off, ho, h⟩ := hpcs e he; rw [h]; exact chaAt hPc (by omega), hacc e he⟩)

/-- A conditional branch under `EvP`: no accesses, only the program counter. -/
theorem evBcond {base : Word} {Pc : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (cond : BitVec 4) (imm : BitVec 8) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.bcond cond imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (hT : condPassed cond s = true → ReachS base (EvP Pc allowed) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q)
    (hF : condPassed cond s = false → ReachS base (EvP Pc allowed) (s.setReg 15 (base + BitVec.ofNat 32 (off + 2))) Q) :
    ReachS base (EvP Pc allowed) s Q :=
  ReachS.bcond hb off tgt cond imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, by intro a ha; simp [Instr.accesses] at ha⟩ hT hF

theorem evB {base : Word} {Pc : Word → Prop} {allowed : Word → Kind → Word → Prop}
    {s : State} {Q : State → Prop} (hb : base.toNat % 2 = 0) (off tgt : Nat)
    (imm : BitVec 11) (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hi : instrAt B off = some (.b imm)) (hsz : off + 2 ≤ Artifacts.Release.size)
    (ht : BitVec.ofNat 32 off + 4#32 + (imm ++ 0#1).signExtend 32 = BitVec.ofNat 32 tgt)
    (hr : Pc (base + BitVec.ofNat 32 off))
    (hq : ReachS base (EvP Pc allowed) (s.setReg 15 (base + BitVec.ofNat 32 tgt)) Q) :
    ReachS base (EvP Pc allowed) s Q :=
  ReachS.b hb off tgt imm hpc ho hi hsz ht
    ⟨by rw [hpc]; exact hr, by intro a ha; simp [Instr.accesses] at ha⟩ hq

theorem pcBefore_of_between {base : Word} {lo hi : Nat} {pc : Word} (h : PCBetween base lo hi pc) :
    PCBefore base hi pc := by
  obtain ⟨o, h1, h2, e⟩ := h
  exact ⟨o, h2, e⟩

/-! ## Read sites

The instructions that load from caller memory through a non-stack address are the key and nonce
byte loads and the input loads of the output region. Everything else reads the stack window or
the code, which the certificate bounds. -/

/-- Offsets of the caller-memory load instructions. -/
abbrev SiteOff (off : Nat) : Prop :=
  (keyOff ≤ off ∧ off < stCtrOff) ∨ (nonOff ≤ off ∧ off < bpreOff) ∨ (achOff ≤ off ∧ off < n1Off)

/-- Program counters of the caller-memory load instructions. -/
def SitePC (base : Word) (pc : Word) : Prop := ∃ off, SiteOff off ∧ pc = base + BitVec.ofNat 32 off

theorem site_order : keyOff ≤ stCtrOff ∧ stCtrOff ≤ nonOff ∧ nonOff ≤ bpreOff ∧ bpreOff ≤ achOff ∧
    achOff ≤ n1Off ∧ n1Off ≤ Artifacts.Release.size ∧ Artifacts.Release.size < 2 ^ 32 := by
  decide +kernel

theorem pc_off_inj {base : Word} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : base + BitVec.ofNat 32 a = base + BitVec.ofNat 32 b) : a = b := by
  have h' := (BitVec.add_right_inj base).mp h
  have := congrArg BitVec.toNat h'
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem not_sitePC {base pc : Word} {lo hi : Nat} (hhi : hi < 2 ^ 32)
    (h : PCBetween base lo hi pc) (hd : ∀ off, lo ≤ off → off < hi → ¬ SiteOff off) :
    ¬ SitePC base pc := by
  obtain ⟨o, h1, h2, rfl⟩ := h
  rintro ⟨o', hs, he⟩
  have hs' := hs
  have := site_order
  have : o' < 2 ^ 32 := by unfold SiteOff at hs; omega
  have := pc_off_inj (base := base) (by omega) this he
  exact hd o h1 h2 (this ▸ hs')

theorem not_sitePC_front {base pc : Word} (h : FrontPc base pc) : ¬ SitePC base pc := by
  have := site_order
  have k1 : keyOff < 2 ^ 32 := by omega
  have k2 : nonOff < 2 ^ 32 := by omega
  have k3 : achOff < 2 ^ 32 := by omega
  rcases h with ⟨o, ho, e⟩ | h | h
  · exact not_sitePC (lo := 0) k1 ⟨o, Nat.zero_le _, ho, e⟩ (fun off _ h1 hs => by unfold SiteOff at hs; omega)
  · exact not_sitePC k2 h (fun off _ h1 hs => by unfold SiteOff at hs; omega)
  · exact not_sitePC k3 h (fun off _ h1 hs => by unfold SiteOff at hs; omega)

/-- The block setup and rounds, between `.Lblock` and the output loads. -/
theorem not_sitePC_pre {base pc : Word} (h : PCBetween base bpreOff achOff pc) : ¬ SitePC base pc := by
  have := site_order
  have k3 : achOff < 2 ^ 32 := by omega
  exact not_sitePC k3 h (fun off h1 h2 hs => by unfold SiteOff at hs; omega)

theorem not_sitePC_back {base pc : Word} (h : PCBetween base n1Off Artifacts.Release.size pc) :
    ¬ SitePC base pc := by
  have := site_order
  have k : Artifacts.Release.size < 2 ^ 32 := by omega
  exact not_sitePC k h (fun off h1 h2 hs => by unfold SiteOff at hs; omega)


/-- Offsets of the key and nonce load instructions. -/
abbrev KNOff (off : Nat) : Prop := (keyOff ≤ off ∧ off < stCtrOff) ∨ (nonOff ≤ off ∧ off < bpreOff)

/-- Program counters of the key and nonce load instructions. -/
def KNPC (base : Word) (pc : Word) : Prop := ∃ off, KNOff off ∧ pc = base + BitVec.ofNat 32 off

theorem knPC_before {base pc : Word} (h : KNPC base pc) : PCBefore base achOff pc := by
  have := site_order
  obtain ⟨o, ho, e⟩ := h
  exact ⟨o, by unfold KNOff at ho; omega, e⟩

/-- A policy that admits the caller-memory loads of the key and nonce, bounded by `Rd`. -/
def AdmitsSite (base : Word) (Wr Rd : Word → Prop) (allowed : Word → Kind → Word → Prop) : Prop :=
  ∀ pc kind y, KNPC base pc → (kind = .write → Wr y) → (kind = .read → Rd y) → allowed pc kind y

theorem admitsSite_writeOnly (base : Word) (Wr Rd : Word → Prop) :
    AdmitsSite base Wr Rd (writeOnlyPolicy Wr) := by
  intro pc kind y _ hw _
  cases kind with
  | read => exact Or.inl rfl
  | write => exact Or.inr (hw rfl)


end M0Crypto.Release.ChaCha20Policy
