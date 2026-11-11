import M0Crypto.Release.ConstantTime.Cert

/-! Checks on tracked stack-slot offsets in abstract certificate states. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- Every tracked slot is word-aligned and its four bytes lie in the stack window. -/
def Stk.slotsOk (w : StackWindow) (stk : Stk) : Prop :=
  ∀ slot ∈ stk, slot.1 % 4 = 0 ∧ w.covers slot.1 (slot.1 + 4) = true

def Stk.slotsCheck (w : StackWindow) (stk : Stk) : Bool :=
  stk.all fun slot => decide (slot.1 % 4 = 0) && w.covers slot.1 (slot.1 + 4)

theorem Stk.slotsCheck_iff (w : StackWindow) (stk : Stk) :
    stk.slotsCheck w = true ↔ stk.slotsOk w := by
  simp [Stk.slotsCheck, Stk.slotsOk]

/-- SP offsets are aligned along with all retained word slots. -/
def AbsState.stackCheck (w : StackWindow) (st : AbsState) : Bool :=
  decide (st.spOff % 4 = 0) && st.stk.slotsCheck w

theorem AbsState.stackCheck_iff (w : StackWindow) (st : AbsState) :
    st.stackCheck w = true ↔ st.spOff % 4 = 0 ∧ st.stk.slotsOk w := by
  simp [AbsState.stackCheck, Stk.slotsCheck_iff]

/-- Check a block head and every transfer successor. The separate certificate
validity check establishes the block's control-flow coverage. -/
def walkSlotsCheck (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Bool
  | _, st, [] => st.stackCheck env.win
  | off, st, i :: is =>
    st.stackCheck env.win &&
      match xfer env off ctx i st with
      | .error _ => false
      | .ok result =>
        result.succs.all (fun pair => pair.2.stackCheck env.win) &&
          match result.succs with
          | [(_, next)] => walkSlotsCheck env ctx (off + i.size) next is
          | _ => walkSlotsCheck env ctx (off + i.size) st is

def blockSlotsCheck (env : Env) (b : Blk) : Bool :=
  walkSlotsCheck env b.ctx b.off b.st b.code

def certSlotsCheck (env : Env) (cert : Cert) : Bool :=
  cert.all (blockSlotsCheck env)

/-- The check establishes the invariant at the current instruction. -/
theorem walkSlotsCheck_head {env : Env} {ctx : Option Nat} {off : Nat}
    {st : AbsState} {code : List Instr} (h : walkSlotsCheck env ctx off st code = true) :
    st.stackCheck env.win = true := by
  cases code with
  | nil => exact h
  | cons i is =>
    simp only [walkSlotsCheck, Bool.and_eq_true] at h
    exact h.1

/-- The check continues along the unique fall-through successor. -/
theorem walkSlotsCheck_next {env : Env} {ctx : Option Nat} {off : Nat}
    {st next : AbsState} {i : Instr} {is : List Instr} {out : Out} {target : Tgt}
    (h : walkSlotsCheck env ctx off st (i :: is) = true)
    (hx : xfer env off ctx i st = .ok out) (hs : out.succs = [(target, next)]) :
    walkSlotsCheck env ctx (off + i.size) next is = true := by
  simp only [walkSlotsCheck, Bool.and_eq_true, hx, hs] at h
  exact h.2.2

theorem certSlotsCheck_block {env : Env} {cert : Cert} {b : Blk}
    (h : certSlotsCheck env cert = true) (hm : b ∈ cert) :
    blockSlotsCheck env b = true := by
  exact List.all_eq_true.mp h b hm

/-- Abstract instruction positions reached by following a block's single
fall-through transfers. Branch successors are represented by new block heads. -/
inductive BlockPoint (env : Env) (b : Blk) : Nat → AbsState → List Instr → Prop where
  | entry : BlockPoint env b b.off b.st b.code
  | next {off st i is out next} :
      BlockPoint env b off st (i :: is) →
      xfer env off b.ctx i st = .ok out →
      out.succs = [(.pt (off + i.size) b.ctx, next)] →
      BlockPoint env b (off + i.size) next is

/-- At every fall-through position reached within a checked block, the
remaining check holds and therefore the current stack state is well formed. -/
theorem blockPoint_slotsCheck {env : Env} {b : Blk} {off : Nat} {st : AbsState} {code : List Instr}
    (hcheck : blockSlotsCheck env b = true) (hpoint : BlockPoint env b off st code) :
    walkSlotsCheck env b.ctx off st code = true ∧ st.stackCheck env.win = true := by
  have hwalk : walkSlotsCheck env b.ctx off st code = true := by
    induction hpoint with
    | entry => exact hcheck
    | next _ hx hs ih => exact walkSlotsCheck_next ih hx hs
  exact ⟨hwalk, walkSlotsCheck_head hwalk⟩

/-- Every fall-through instruction reached in a checked certificate has a
well-formed stack state. -/
theorem certPoint_stackCheck {env : Env} {cert : Cert} {b : Blk}
    {off : Nat} {st : AbsState} {code : List Instr}
    (hcheck : certSlotsCheck env cert = true) (hmem : b ∈ cert)
    (hpoint : BlockPoint env b off st code) : st.stackCheck env.win = true :=
  (blockPoint_slotsCheck (certSlotsCheck_block hcheck hmem) hpoint).2

end M0Crypto.Release.ConstantTime
