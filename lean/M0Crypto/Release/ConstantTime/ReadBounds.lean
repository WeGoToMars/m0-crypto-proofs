import M0Crypto.Release.ConstantTime.LiteralSound
import M0Crypto.Release.ConstantTime.AccessAddress
import M0Crypto.Release.ConstantTime.StackStoreSound
import M0Crypto.Release.ConstantTime.StepBounds

set_option linter.unusedSimpArgs false

/-!
# Read bounds from a certified transfer

A successful abstract transfer bounds every byte an instruction reads, except for loads through a
non-stack address (`loadSite`). Stack reads lie in the entry window, literal loads lie in the
artifact. The certificate walk `certLoadSiteCheck` lists the positions of the remaining loads.
-/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb

/-- Bytes of the entry stack window. -/
def StackRdAt (p : Params) (w : StackWindow) (y : Word) : Prop :=
  ∃ o, o < w.below + w.above ∧ y = p.sp0 - BitVec.ofNat 32 w.below + BitVec.ofNat 32 o

/-- Bytes of the artifact. -/
def CodeRdAt (p : Params) (size : Nat) (y : Word) : Prop :=
  ∃ o, o < size ∧ y = p.base + BitVec.ofNat 32 o

def ReadOk (p : Params) (env : Env) (y : Word) : Prop :=
  StackRdAt p env.win y ∨ CodeRdAt p env.size y

/-- Loads whose address the abstract state does not track on the stack. -/
def loadSite (st : AbsState) : Instr → Bool
  | .memImm op _ n imm => op.isLoad && !((st.get n.val).addK (imm.toNat * op.width)).isSp
  | .memReg op _ n m => op.isLoad && !((st.get n.val).add (st.get m.val)).isSp
  | .ldm n _ => !(st.get n.val).isSp
  | _ => false

theorem stackRd_of_cover (p : Params) (w : StackWindow) (o : Int) (n k : Nat)
    (hc : w.covers o (o + n) = true) (hk : k < n) :
    StackRdAt p w (p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 k) := by
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [stack_offset_rebase p.sp0 w.below o hc.1, ofNat_add_assoc]
  exact ⟨(o + (w.below : Int)).toNat + k, by omega, rfl⟩

theorem sp_add_ofInt (p : Params) (o : Int) (n : Nat) :
    p.sp0 + BitVec.ofInt 32 o + BitVec.ofNat 32 n = p.sp0 + BitVec.ofInt 32 (o + n) := by
  rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]

theorem access_sp_covers {env : Env} {st : AbsState} {x y : Int} {w : Nat} {isLoad : Bool} {t : Nat}
    {out : AbsState × List SiteK} (h : access env st (.sp x y) w isLoad t = .ok out) :
    env.win.covers x (y + w) = true := by
  cases hc : env.win.covers x (y + w)
  · simp [access, hc] at h
  · rfl

theorem xfer_core {env : Env} {off : Nat} {ctx : Option Nat} {i : Instr} {st : AbsState} {out : Out}
    (h : xfer env off ctx i st = .ok out) : xferCore env off ctx i st = .ok out := by
  unfold xfer at h
  split at h
  · exact h
  · contradiction

theorem memImm_access_ok {env : Env} {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out}
    (op : MemOp) (t n : M0Crypto.Armv6M.LowReg) (imm : BitVec 5)
    (hx : xfer env off ctx (.memImm op t n imm) st = .ok out) :
    ∃ result, access env st ((st.get n.val).addK (imm.toNat * op.width))
      op.width op.isLoad t.val = .ok result := by
  simp only [xfer] at hx
  split at hx <;> simp_all [xferCore]
  split at hx <;> simp_all

theorem memReg_access_ok {env : Env} {off : Nat} {ctx : Option Nat} {st : AbsState} {out : Out}
    (op : MemOp) (t n m : M0Crypto.Armv6M.LowReg)
    (hx : xfer env off ctx (.memReg op t n m) st = .ok out) :
    ∃ result, access env st ((st.get n.val).add (st.get m.val))
      op.width op.isLoad t.val = .ok result := by
  simp only [xfer] at hx
  split at hx <;> simp_all [xferCore]
  split at hx <;> simp_all
  split at hx <;> simp_all

/-- An `sp`-abstracted address whose access was accepted reads inside the window. -/
theorem sp_access_reads {env : Env} {p : Params} {st : AbsState} {x y : Int} {w : Nat}
    {isLoad : Bool} {t : Nat} {out : AbsState × List SiteK} {a₁ a₂ : Word}
    (h : access env st (.sp x y) w isLoad t = .ok out) (hs : AbsVal.Sem p (.sp x y) a₁ a₂) :
    ∀ k < w, StackRdAt p env.win (a₁ + BitVec.ofNat 32 k) := by
  have hc := access_sp_covers h
  obtain ⟨o, hxo, hoy, ha, -⟩ := hs
  intro k hk
  simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [ha]
  exact stackRd_of_cover p env.win o w k
    (by simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq]; omega) hk

/-- Every byte read by a position with a successful transfer lies in the entry stack window or
the artifact, unless the instruction is a load through a non-stack address. -/
theorem xfer_reads {env : Env} {p : Params} {bytes : List (BitVec 8)} {off : Nat}
    {ctx : Option Nat} {st : AbsState} {s₁ s₂ : State} {out : Out} (i : Instr)
    (h : LowEq p bytes off st s₁ s₂) (hx : xfer env off ctx i st = .ok out)
    (hsize : env.size = bytes.length) (hbase : p.base.toNat % 4 = 0)
    (hnowrap : p.base.toNat + bytes.length ≤ 2 ^ 32) (hl : loadSite st i = false) :
    ∀ a ∈ i.accesses s₁, a.kind = .read → ∀ k < a.width, ReadOk p env (a.addr + BitVec.ofNat 32 k) := by
  have hcore := xfer_core hx
  cases i with
  | ldrLit t imm =>
    intro a ha _ k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    simp only [xferCore] at hcore
    split at hcore
    · rename_i hb
      right
      have hlin : p.base.toNat + off + 4 + imm.toNat * 4 < 2 ^ 32 := by omega
      have hla := M0Crypto.Release.Frame.lit_addr p.base hbase off imm.toNat hlin
      dsimp only at hk ⊢
      rw [h.pc, hla, ofNat_add_assoc]
      exact ⟨(off + 4) / 4 * 4 + imm.toNat * 4 + k, by omega, rfl⟩
    · contradiction
  | memImm op t n imm =>
    intro a ha hkind k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    have hload : op.isLoad = true := by
      cases hh : op.isLoad
      · simp [hh] at hkind
      · rfl
    obtain ⟨r, hr⟩ := memImm_access_ok op t n imm hx
    have hsem := AbsVal.addK_sound (imm.toNat * op.width) (lowReg_sem n h)
    cases hv : (st.get n.val).addK (imm.toNat * op.width) with
    | sp x y =>
      rw [hv] at hr hsem
      left
      simpa [M0Crypto.Armv6M.State.reg] using sp_access_reads hr hsem k hk
    | _ => simp [loadSite, hload, hv, AbsVal.isSp] at hl
  | memReg op t n m =>
    intro a ha hkind k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    have hload : op.isLoad = true := by
      cases hh : op.isLoad
      · simp [hh] at hkind
      · rfl
    obtain ⟨r, hr⟩ := memReg_access_ok op t n m hx
    have hsem := AbsVal.add_sound (lowReg_sem n h) (lowReg_sem m h)
    cases hv : (st.get n.val).add (st.get m.val) with
    | sp x y =>
      rw [hv] at hr hsem
      left
      simpa [M0Crypto.Armv6M.State.reg] using sp_access_reads hr hsem k hk
    | _ => simp [loadSite, hload, hv, AbsVal.isSp] at hl
  | ldrSp t imm =>
    intro a ha _ k hk
    simp only [Instr.accesses, List.mem_singleton] at ha
    subst ha
    simp only [xferCore] at hcore
    split at hcore
    · rename_i hc
      left
      have hsp : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
      dsimp only at hk ⊢
      rw [hsp, sp_add_ofInt]
      exact stackRd_of_cover p env.win _ 4 k hc hk
    · contradiction
  | pop l pcb =>
    intro a ha _ k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hc : env.win.covers st.spOff (st.spOff +
        ((4 * ((regsOf l).length + (if pcb then 1 else 0)) : Nat) : Int)) = true := by
      cases hcv : env.win.covers st.spOff (st.spOff +
        ((4 * ((regsOf l).length + (if pcb then 1 else 0)) : Nat) : Int))
      · simp only [xferCore, hcv] at hcore; simp at hcore
      · rfl
    left
    have hsp : s₁.sp = p.sp0 + BitVec.ofInt 32 st.spOff := by simpa [State.sp] using h.sp
    have hn : bitCount l + pcb.toNat = (regsOf l).length + (if pcb then 1 else 0) := by
      cases pcb <;> simp [regsOf, bitCount]
    rw [← hn] at hc
    generalize bitCount l + pcb.toNat = cnt at hc hj
    dsimp only at hk ⊢
    rw [hsp, sp_add_ofInt]
    exact stackRd_of_cover p env.win _ 4 k
      (by
        simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
        omega) hk
  | ldm n l =>
    intro a ha _ k hk
    simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hsem := lowReg_sem n h
    cases hv : st.get n.val with
    | sp x y =>
      rw [hv] at hsem
      obtain ⟨o, hxo, hoy, ha, -⟩ := hsem
      have hc : env.win.covers x (y + ((4 * (regsOf l).length : Nat) : Int)) = true := by
        cases hcv : env.win.covers x (y + ((4 * (regsOf l).length : Nat) : Int))
        · simp only [xferCore, hv, hcv] at hcore; simp at hcore
        · rfl
      left
      have hj' : j < (regsOf l).length := by simpa [regsOf, bitCount] using hj
      dsimp only at hk ⊢
      rw [ha, sp_add_ofInt]
      exact stackRd_of_cover p env.win _ 4 k
        (by
          simp only [StackWindow.covers, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
          omega) hk
    | _ => simp [loadSite, hv, AbsVal.isSp] at hl
  | push l lr =>
    intro a ha hk
    simp only [Instr.accesses, wordAccesses, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    cases hk
  | stm n l =>
    intro a ha hk
    simp only [Instr.accesses, wordAccesses, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    cases hk
  | _ =>
    intro a ha hk
    simp [Instr.accesses] at ha <;> (subst ha; simp at hk)

/-! ## Static check: non-stack loads sit at permitted offsets -/

def walkLoadFailure (ok : Nat → Bool) (env : Env) (ctx : Option Nat) :
    Nat → AbsState → List Instr → Option Nat
  | _, _, [] => none
  | off, st, i :: is =>
    if loadSite st i && !ok off then some off
    else
      match xfer env off ctx i st with
      | .error _ => some off
      | .ok out =>
        match out.succs with
        | [(_, next)] => walkLoadFailure ok env ctx (off + i.size) next is
        | _ => walkLoadFailure ok env ctx (off + i.size) st is

def certLoadFailure (ok : Nat → Bool) (env : Env) (cert : Cert) : Option (Nat × Nat) :=
  cert.findSome? fun b => (walkLoadFailure ok env b.ctx b.off b.st b.code).map fun off => (b.off, off)

theorem blockPoint_loadFailure {ok : Nat → Bool} {env : Env} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Instr} (hc : walkLoadFailure ok env b.ctx b.off b.st b.code = none)
    (hp : BlockPoint env b off st code) : walkLoadFailure ok env b.ctx off st code = none := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkLoadFailure, hx, hs] at ih
    split at ih
    · cases ih
    · exact ih

theorem certPoint_loadSite {ok : Nat → Bool} {env : Env} {cert : Cert} {b : Blk} {off : Nat}
    {st : AbsState} {i : Instr} {is : List Instr} (hc : certLoadFailure ok env cert = none)
    (hm : b ∈ cert) (hp : BlockPoint env b off st (i :: is)) (hu : loadSite st i = true) :
    ok off = true := by
  have hb : walkLoadFailure ok env b.ctx b.off b.st b.code = none := by
    unfold certLoadFailure at hc
    have := List.findSome?_eq_none_iff.mp hc b hm
    cases h : walkLoadFailure ok env b.ctx b.off b.st b.code with
    | none => rfl
    | some o => simp [h] at this
  have hw := blockPoint_loadFailure hb hp
  simp only [walkLoadFailure] at hw
  split at hw
  · cases hw
  · rename_i hn
    simp only [hu, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false', ite_eq_right_iff] at hn
    cases ho : ok off
    · simp [hu, ho] at hn
    · rfl

end M0Crypto.Release.ConstantTime
