import M0Crypto.Release.ConstantTime.Reach

/-! Relational semantics of interval-aware bitwise operations. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (State LowReg Word)
open M0Crypto.Thumb

/-- Abstract result of a register AND. -/
def andResult (a b : AbsVal) : AbsVal :=
  match ival a, ival b with
  | some (_, ha), some (_, hb) =>
    if min ha hb < AbsVal.word - 1 then .num 0 (min ha hb) else .lo
  | _, _ => AbsVal.ofPub (a.pub && b.pub)

theorem andResult_public (a b : AbsVal) : (andResult a b).pub = (a.pub && b.pub) := by
  have hof (p : Bool) : (AbsVal.ofPub p).pub = p := by cases p <;> rfl
  cases ha : ival a with
  | none =>
    cases hb : ival b <;> simpa only [andResult, ha, hb] using hof (a.pub && b.pub)
  | some ia =>
    cases ia with
    | mk la ua =>
      cases hb : ival b with
      | none =>
        simpa only [andResult, ha, hb] using hof (a.pub && b.pub)
      | some ib =>
        cases ib with
        | mk lb ub =>
          have hpa := ival_public ha
          have hpb := ival_public hb
          simp only [andResult, ha, hb, hpa, hpb, Bool.true_and]
          split <;> rfl

/-- AND is bounded by either operand and preserves public equality. -/
theorem andResult_sound {p : Params} {a b : AbsVal} {x₁ x₂ y₁ y₂ : Word}
    (ha : AbsVal.Sem p a x₁ x₂) (hb : AbsVal.Sem p b y₁ y₂) :
    AbsVal.Sem p (andResult a b) (x₁ &&& y₁) (x₂ &&& y₂) := by
  cases hia : ival a with
  | none => simpa [andResult, hia] using AbsVal.ofPub_binary (fun x y => x &&& y) ha hb
  | some ia =>
    cases ia with
    | mk la ua =>
      cases hib : ival b with
      | none => simpa [andResult, hia, hib] using AbsVal.ofPub_binary (fun x y => x &&& y) ha hb
      | some ib =>
        cases ib with
        | mk lb ub =>
          have heqx := AbsVal.sem_public ha (ival_public hia)
          have heqy := AbsVal.sem_public hb (ival_public hib)
          have hxa := (interval_bounds ha hia).2.1
          have hyb := (interval_bounds hb hib).2.1
          have hleft : (x₁ &&& y₁).toNat ≤ ua := by
            rw [BitVec.toNat_and]
            exact Nat.le_trans Nat.and_le_left hxa
          have hright : (x₁ &&& y₁).toNat ≤ ub := by
            rw [BitVec.toNat_and]
            exact Nat.le_trans Nat.and_le_right hyb
          have hbound : (x₁ &&& y₁).toNat ≤ min ua ub := Nat.le_min.mpr ⟨hleft, hright⟩
          by_cases hsmall : min ua ub < AbsVal.word - 1
          · simp only [andResult, hia, hib, hsmall, ↓reduceIte, AbsVal.Sem]
            exact ⟨by rw [heqx, heqy], Nat.zero_le _, hbound⟩
          · simp [andResult, hia, hib, hsmall, AbsVal.Sem, heqx, heqy]

def andFlags (f : AFl) (pub : Bool) (r : Nat) : AFl :=
  if pub then {setNZ f pub with cmp := some ⟨r, .imm 0, true⟩} else setNZ f pub

theorem ands_sound {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {st : AbsState} {s₁ s₂ : State} (d m : LowReg)
    (hidx : st.indicesOk) (h : LowEq p bytes off st s₁ s₂) :
    ∃ t₁ t₂, (Instr.dp .ands d m).exec s₁ = .ok t₁ ∧
      (Instr.dp .ands d m).exec s₂ = .ok t₂ ∧
      LowEq p bytes (off + (Instr.dp .ands d m).size)
        { st.set d.val (andResult (st.get d.val) (st.get m.val)) with
          fl := andFlags st.fl ((st.get d.val).pub && (st.get m.val).pub) d.val } t₁ t₂ := by
  have hd : regIndexOk d.val := by
    constructor <;> have := d.isLt <;> simp [numRegs] <;> omega
  have hm : regIndexOk m.val := by
    constructor <;> have := m.isLt <;> simp [numRegs] <;> omega
  have hd16 : d.val < 16 := by have := d.isLt; omega
  have hm16 : m.val < 16 := by have := m.isLt; omega
  have ha := h.regs d.val hd.1 hd.2
  have hb := h.regs m.val hm.1 hm.2
  rw [regAt_eq_regs s₁ d.val hd16, regAt_eq_regs s₂ d.val hd16] at ha
  rw [regAt_eq_regs s₁ m.val hm16, regAt_eq_regs s₂ m.val hm16] at hb
  have hv : AbsVal.Sem p (andResult (st.get d.val) (st.get m.val))
      (s₁.reg d &&& s₁.reg m) (s₂.reg d &&& s₂.reg m) := by
    apply andResult_sound
    · simpa [State.reg, LowReg.toReg] using ha
    · simpa [State.reg, LowReg.toReg] using hb
  have hw := paired_setReg_sound hd hidx (h.withPC hidx (next := off + (Instr.dp .ands d m).size)) hv
  have hreg : (⟨d.val, by have := hd.1; simp [numRegs] at this; omega⟩ : M0Crypto.Armv6M.Reg) = d.toReg := by
    apply Fin.ext; rfl
  rw [hreg] at hw
  have hn := hw.withNZ hv
  rw [andResult_public] at hn
  simp only [AbsState.set, setNZ_touch] at hn
  have htest (s : State) (x : Word) :
      CmpSem ⟨d.val, .imm 0, true⟩ ((s.setReg d.toReg x).setNZ x) := by
    simp only [CmpSem, operand, ↓reduceIte, State.setNZ]
    change (x == 0) = (regAt (s.setReg d.toReg x) d.val == 0)
    rw [← hreg, regAt_setReg_self]
  have hout : LowEq p bytes (off + (Instr.dp .ands d m).size)
      { st.set d.val (andResult (st.get d.val) (st.get m.val)) with
        fl := andFlags st.fl ((st.get d.val).pub && (st.get m.val).pub) d.val }
      (((s₁.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .ands d m).size))).setReg d.toReg (s₁.reg d &&& s₁.reg m)).setNZ (s₁.reg d &&& s₁.reg m))
      (((s₂.setReg 15 (p.base + BitVec.ofNat 32 (off + (Instr.dp .ands d m).size))).setReg d.toReg (s₂.reg d &&& s₂.reg m)).setNZ (s₂.reg d &&& s₂.reg m)) := by
    cases hp : ((st.get d.val).pub && (st.get m.val).pub) with
    | false => simpa [andFlags, hp, AbsState.set] using hn
    | true =>
      rcases hn with ⟨a,b,c,e,f,g,_,i,j,k,l,n,o⟩
      refine ⟨a,b,c,e,f,?_,?_,i,j,k,l,n,o⟩
      · simpa [andFlags, hp, FlagSem] using g
      · intro cmp hc
        simp [andFlags] at hc
        subst cmp
        exact ⟨htest _ _, htest _ _⟩
  refine ⟨_, _, ?_, ?_, hout⟩
  · simp [Instr.exec, h.pc, ofNat_add_assoc]
  · simp [Instr.exec, h.pc_eq.trans h.pc, ofNat_add_assoc]

/-- Checked AND transfers advance paired certificate executions. -/
theorem certPoint_ands_paired {env : Env} {bytes : List (BitVec 8)} {entry : Nat}
    {init : AbsState} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState} {is : List Instr}
    {p : Params} {s₁ s₂ : State} (d m : LowReg)
    (hc : certOk env bytes entry init cert = true) (hi : certIndicesFailure cert env = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (.dp .ands d m :: is))
    (h : LowEq p bytes off st s₁ s₂)
    (heven : (p.base + BitVec.ofNat 32 off).getLsbD 0 = false) :
    PairedStep (CertAt env cert p bytes) s₁ s₂ := by
  obtain ⟨out, hx⟩ := certPoint_xfer hc hm hp
  have hidx := certPoint_state_indices hi hm hp
  have ⟨hdecode, hlen⟩ := certPoint_instrAt hc hm hp
  have hb := xfer_sp_bounds hx
  have hw : env.win.covers st.spOff st.spOff = true := by
    simp [StackWindow.covers, hb.1, hb.2.2]
  have hout : out = ⟨[(.pt (off + (Instr.dp .ands d m).size) b.ctx,
      { st.set d.val (andResult (st.get d.val) (st.get m.val)) with
        fl := andFlags st.fl ((st.get d.val).pub && (st.get m.val).pub) d.val })], []⟩ := by
    cases ha : ival (st.get d.val) <;> cases hbval : ival (st.get m.val) <;>
      simp_all [xfer, xferCore, fall, andResult, andFlags]
  have hsucc := congrArg Out.succs hout
  have hpoint := BlockPoint.next hp hx hsucc
  obtain ⟨t₁, t₂, he₁, he₂, hnext⟩ := ands_sound d m hidx h
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hc₁, hc₂⟩ := h
  have hs₁ := step_of_instrAt hc₁ off (.dp .ands d m) h.pc heven hdecode hlen
    (by simp [Instr.accesses]) he₁
  have hs₂ := step_of_instrAt hc₂ off (.dp .ands d m) (h.pc_eq.trans h.pc) heven hdecode hlen
    (by simp [Instr.accesses]) he₂
  apply certAt_paired_step hc hi hm hpoint hnext hs₁
  simpa [Instr.accesses, h.pc_eq] using hs₂

end M0Crypto.Release.ConstantTime
