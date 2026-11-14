import M0Crypto.Release.ConstantTime.HolesBits
import M0Crypto.Release.ConstantTime.ReadBounds
import M0Crypto.Release.ConstantTime.InstructionCases

set_option linter.unusedSimpArgs false

/-!
# Stack accesses of one instruction

`stackAccs` (`Holes.lean`) lists the SP-tracked accesses of an instruction. Every byte an
instruction accesses is in one of them, a literal in the artifact, or an access through an
untracked address (a load site or a store site); every byte of an exact write is written.
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-- Stores through an address the abstract state does not track on the stack. -/
def storeSite (st : AbsState) : Instr → Bool
  | .memImm op _ n imm => !op.isLoad && !((st.get n.val).addK (imm.toNat * op.width)).isSp
  | .memReg op _ n m => !op.isLoad && !((st.get n.val).add (st.get m.val)).isSp
  | .stm n _ => !(st.get n.val).isSp
  | _ => false

theorem sp_sub_ofInt (sp0 : Word) (o : Int) (n : Nat) :
    sp0 + BitVec.ofInt 32 o - BitVec.ofNat 32 n = sp0 + BitVec.ofInt 32 (o - n) := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.ofInt_natCast,
    BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The window offset of a byte of an SP-tracked access. -/
def AtOff (p : Params) (sa : SAcc) (y : Word) : Prop :=
  ∃ q : Int, sa.lo ≤ q ∧ q < sa.hi ∧ y = p.sp0 + BitVec.ofInt 32 q

/-- Every byte an instruction with a successful transfer accesses is a literal in the artifact,
read by a load site, written by a store site, or in one of its SP-tracked accesses of the same
kind. -/
theorem xfer_stack_access {env : Env} {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {ctx : Option Nat} {st : AbsState} {s : State} {out : Out} (i : Instr)
    (h : LowEq p bytes off st s s) (hx : xfer env off ctx i st = .ok out)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) :
    ∀ a ∈ i.accesses s, ∀ k < a.width,
      CodeRdAt p env.size (a.addr + BitVec.ofNat 32 k) ∨
      (loadSite st i = true ∧ a.kind = .read) ∨ (storeSite st i = true ∧ a.kind = .write) ∨
      ∃ sa ∈ stackAccs st i, (sa.read = true ↔ a.kind = .read) ∧
        AtOff p sa (a.addr + BitVec.ofNat 32 k) := by
  have hcore := xfer_core hx
  have hsp : s.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  cases i with
  | ldrLit t imm =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    simp only [xferCore] at hcore
    split at hcore
    · rename_i hb
      left
      have hlin : p.base.toNat + off + 4 + imm.toNat * 4 < 2 ^ 32 := by omega
      have hla := M0Crypto.Release.Frame.lit_addr p.base hbase off imm.toNat hlin
      dsimp only at hk ⊢
      rw [h.pc, hla, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ⟨(off + 4) / 4 * 4 + imm.toNat * 4 + k, by omega, rfl⟩
    · contradiction
  | memImm op t n imm =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    have hsem := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
    cases hv : (st.get n.val).addK (imm.toNat * op.width) with
    | sp x y =>
      rw [hv] at hsem
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      right; right; right
      refine ⟨⟨op.isLoad, x, y + (op.width : Int), x == y⟩, by simp [stackAccs, hv], ?_,
        o + k, by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
      · cases op.isLoad <;> simp
      · dsimp only
        rw [show s.reg n + BitVec.ofNat 32 (imm.toNat * op.width) = p.sp0 + BitVec.ofInt 32 o from hao,
          sp_add_ofInt]
    | _ =>
      right
      cases hl : op.isLoad
      · right; left; simp [storeSite, hl, hv, AbsVal.isSp]
      · left; simp [loadSite, hl, hv, AbsVal.isSp]
  | memReg op t n m =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    have hsem := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
    cases hv : (st.get n.val).add (st.get m.val) with
    | sp x y =>
      rw [hv] at hsem
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      right; right; right
      refine ⟨⟨op.isLoad, x, y + (op.width : Int), x == y⟩, by simp [stackAccs, hv], ?_,
        o + k, by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
      · cases op.isLoad <;> simp
      · dsimp only
        rw [show s.reg n + s.reg m = p.sp0 + BitVec.ofInt 32 o from hao, sp_add_ofInt]
    | _ =>
      right
      cases hl : op.isLoad
      · right; left; simp [storeSite, hl, hv, AbsVal.isSp]
      · left; simp [loadSite, hl, hv, AbsVal.isSp]
  | strSp t imm =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    right; right; right
    refine ⟨⟨false, st.spOff + (imm.toNat * 4 : Nat), st.spOff + (imm.toNat * 4 : Nat) + 4, true⟩,
      by simp [stackAccs], by simp, st.spOff + (imm.toNat * 4 : Nat) + k,
      by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
    dsimp only
    rw [hsp, sp_add_ofInt, sp_add_ofInt]
  | ldrSp t imm =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    right; right; right
    refine ⟨⟨true, st.spOff + (imm.toNat * 4 : Nat), st.spOff + (imm.toNat * 4 : Nat) + 4, true⟩,
      by simp [stackAccs], by simp, st.spOff + (imm.toNat * 4 : Nat) + k,
      by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
    dsimp only
    rw [hsp, sp_add_ofInt, sp_add_ofInt]
  | push l lr =>
    intro a ha k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    right; right; right
    refine ⟨⟨false, st.spOff - (4 * (bitCount l + lr.toNat) : Nat), st.spOff, true⟩,
      by simp [stackAccs], by simp,
      st.spOff - (4 * (bitCount l + lr.toNat) : Nat) + (4 * j : Nat) + k, by (try dsimp only); omega,
      by (try dsimp only at hk ⊢); omega, ?_⟩
    dsimp only
    rw [hsp, sp_sub_ofInt, sp_add_ofInt, sp_add_ofInt]
  | pop l pc =>
    intro a ha k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    right; right; right
    refine ⟨⟨true, st.spOff, st.spOff + (4 * (bitCount l + pc.toNat) : Nat), true⟩,
      by simp [stackAccs], by simp, st.spOff + (4 * j : Nat) + k, by (try dsimp only); omega,
      by (try dsimp only at hk ⊢); omega, ?_⟩
    dsimp only
    rw [hsp, sp_add_ofInt, sp_add_ofInt]
  | stm n l =>
    intro a ha k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hsem := lowReg_sem n h
    cases hv : st.get n.val with
    | sp x y =>
      rw [hv] at hsem
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      right; right; right
      refine ⟨⟨false, x, y + (4 * bitCount l : Nat), x == y⟩, by simp [stackAccs, hv], by simp,
        o + (4 * j : Nat) + k, by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
      dsimp only
      rw [hao, sp_add_ofInt, sp_add_ofInt]
    | _ => right; right; left; simp [storeSite, hv, AbsVal.isSp]
  | ldm n l =>
    intro a ha k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hsem := lowReg_sem n h
    cases hv : st.get n.val with
    | sp x y =>
      rw [hv] at hsem
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      right; right; right
      refine ⟨⟨true, x, y + (4 * bitCount l : Nat), x == y⟩, by simp [stackAccs, hv], by simp,
        o + (4 * j : Nat) + k, by (try dsimp only); omega, by (try dsimp only at hk ⊢); omega, ?_⟩
      dsimp only
      rw [hao, sp_add_ofInt, sp_add_ofInt]
    | _ => right; left; simp [loadSite, hv, AbsVal.isSp]
  | _ =>
    intro a ha
    simp [Instr.accesses] at ha

/-- Every byte of an exact SP-tracked write is written. -/
theorem stackAccs_exact {p : Params} {bytes : List (BitVec 8)} {off : Nat} {st : AbsState}
    {s : State} (i : Instr) (h : LowEq p bytes off st s s) :
    ∀ sa ∈ stackAccs st i, sa.read = false → sa.exact = true → ∀ q : Int, sa.lo ≤ q → q < sa.hi →
      Writes (i.accesses s) (p.sp0 + BitVec.ofInt 32 q) := by
  have hsp : s.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
  cases i with
  | memImm op t n imm =>
    intro sa hsa hr he q hlo hhi
    have hsem := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
    cases hv : (st.get n.val).addK (imm.toNat * op.width) with
    | sp x y =>
      rw [hv] at hsem
      simp only [stackAccs, hv, List.mem_singleton] at hsa
      subst hsa
      simp only [beq_iff_eq] at hr he hlo hhi
      subst he
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      refine ⟨_, List.mem_singleton_self _, by simp [hr], (q - x).toNat,
        show (q - x).toNat < op.width by omega, ?_⟩
      show p.sp0 + BitVec.ofInt 32 q = _ + _
      rw [hao, sp_add_ofInt]
      congr 2
      omega
    | _ => simp [stackAccs, hv] at hsa
  | memReg op t n m =>
    intro sa hsa hr he q hlo hhi
    have hsem := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
    cases hv : (st.get n.val).add (st.get m.val) with
    | sp x y =>
      rw [hv] at hsem
      simp only [stackAccs, hv, List.mem_singleton] at hsa
      subst hsa
      simp only [beq_iff_eq] at hr he hlo hhi
      subst he
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      refine ⟨_, List.mem_singleton_self _, by simp [hr], (q - x).toNat,
        show (q - x).toNat < op.width by omega, ?_⟩
      show p.sp0 + BitVec.ofInt 32 q = _ + _
      rw [hao, sp_add_ofInt]
      congr 2
      omega
    | _ => simp [stackAccs, hv] at hsa
  | strSp t imm =>
    intro sa hsa hr he q hlo hhi
    simp only [stackAccs, List.mem_singleton] at hsa
    subst hsa
    dsimp only at hlo hhi
    refine ⟨_, List.mem_singleton_self _, rfl, (q - (st.spOff + (imm.toNat * 4 : Nat))).toNat,
      show _ < 4 by omega, ?_⟩
    show p.sp0 + BitVec.ofInt 32 q = s.sp + _ + _
    rw [hsp, sp_add_ofInt, sp_add_ofInt]
    congr 2
    omega
  | push l lr =>
    intro sa hsa hr he q hlo hhi
    simp only [stackAccs, List.mem_singleton] at hsa
    subst hsa
    dsimp only at hlo hhi
    let d := (q - (st.spOff - (4 * (bitCount l + lr.toNat) : Nat))).toNat
    refine ⟨_, List.mem_map.2 ⟨d / 4, List.mem_range.2 (by omega), rfl⟩, rfl, d % 4,
      show d % 4 < 4 by omega, ?_⟩
    show p.sp0 + BitVec.ofInt 32 q = s.sp - _ + _ + _
    rw [hsp, sp_sub_ofInt, sp_add_ofInt, sp_add_ofInt]
    congr 2
    omega
  | stm n l =>
    intro sa hsa hr he q hlo hhi
    have hsem := lowReg_sem n h
    cases hv : st.get n.val with
    | sp x y =>
      rw [hv] at hsem
      simp only [stackAccs, hv, List.mem_singleton] at hsa
      subst hsa
      simp only [beq_iff_eq] at he hlo hhi
      subst he
      obtain ⟨o, hxo, hoy, hao, -⟩ := hsem
      let d := (q - x).toNat
      refine ⟨_, List.mem_map.2 ⟨d / 4, List.mem_range.2 (by omega), rfl⟩, rfl, d % 4,
        show d % 4 < 4 by omega, ?_⟩
      show p.sp0 + BitVec.ofInt 32 q = s.reg n + _ + _
      rw [hao, sp_add_ofInt, sp_add_ofInt]
      congr 2
      omega
    | _ => simp [stackAccs, hv] at hsa
  | ldrSp t imm => intro sa hsa hr; simp [stackAccs] at hsa; subst hsa; simp at hr
  | pop l pc => intro sa hsa hr; simp [stackAccs] at hsa; subst hsa; simp at hr
  | ldm n l =>
    intro sa hsa hr
    cases hv : st.get n.val <;> simp [stackAccs, hv] at hsa <;> (subst hsa; simp at hr)
  | _ => intro sa hsa; simp [stackAccs] at hsa

/-- A store site writes outside the certificate's window when the buffer obligation holds. -/
theorem storeSite_outside {env : Env} {p : Params} {bytes : List (BitVec 8)} {st : AbsState}
    {s : State} (i : Instr) (hb : BufferStoreOk env p bytes st s i) (hs : storeSite st i = true) :
    ∀ a ∈ i.accesses s, ∀ k < a.width,
      ¬ M0Crypto.Release.Region (p.sp0 - BitVec.ofNat 32 env.win.below)
        (env.win.below + env.win.above) (a.addr + BitVec.ofNat 32 k) := by
  cases i with
  | memImm op t n imm =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    simp only [storeSite, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨h1, h2, h3⟩ := (hb hs.2 hs.1).2
    exact M0Crypto.Release.Region.not fun o ho e =>
      M0Crypto.Release.Frame.ne_of_disj h1 h2 h3 ho hk e.symm
  | memReg op t n m =>
    intro a ha k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    simp only [storeSite, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨h1, h2, h3⟩ := (hb hs.2 hs.1).2
    exact M0Crypto.Release.Region.not fun o ho e =>
      M0Crypto.Release.Frame.ne_of_disj h1 h2 h3 ho hk e.symm
  | stm n l =>
    intro a ha k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hns : ∀ lo hi, st.get n.val ≠ .sp lo hi := by
      intro lo hi he; simp [storeSite, he, AbsVal.isSp] at hs
    obtain ⟨h1, h2, h3⟩ := (hb hns).2
    dsimp only at hk ⊢
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact M0Crypto.Release.Region.not fun o ho e =>
      M0Crypto.Release.Frame.ne_of_disj h1 h2 h3 ho (show 4 * j + k < 4 * bitCount l by omega) e.symm
  | _ => simp [storeSite] at hs

end M0Crypto.Release.ConstantTime
