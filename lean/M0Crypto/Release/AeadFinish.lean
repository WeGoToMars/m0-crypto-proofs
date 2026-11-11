import M0Crypto.Release.AeadLengths
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Composable Poly1305 finish call for either AEAD entry point. -/
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Release.Poly1305Finish (FCtx FValid FEntry)

/-- Writes of finish: its saved registers below A and the chosen tag destination. -/
def FinishWr (A tag y : Word) : Prop := InFrame (A - 20#32) 5 y ∨ InFrame tag 4 y

theorem finishWr_swr (A y : Word) (h : FinishWr A (A + 72#32) y) : SWr A y := by
  rcases h with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · refine ⟨156 + o, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; congr 1; bv_omega
  · rw [ofNat_add_assoc]; exact swr_A A _ (by omega)

theorem finishWr_awr (c : ACall) (y : Word) (h : FinishWr c.A c.tag y) : AWr c y := by
  rcases h with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
  · left
    refine ⟨156 + o, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; congr 1; bv_omega
  · right; right
    rw [sub_off _ _ (by omega)]; exact ho

structure FinishPost (c : ACall) (tag : Word) (off : Nat) (msg : List M0Crypto.Spec.ChaCha20.Byte)
    (s t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 (off + blSize)
  sp : t.regs 13 = c.A
  hi : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → t.regs r = s.regs r
  frame : ∀ y, ¬ FinishWr c.A tag y → t.mem y = s.mem y
  tagBytes : Ctx.bytesAt t.mem tag 16 = M0Crypto.Spec.Aead.poly1305
    (M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB) msg

/-- From the `bl finish` instruction, refine the accumulated message to the RFC tag.
The tag destination is either the caller tag or the stack's expected-tag block. -/
theorem finish_call (c : ACall) (hv : AValid c) (tag : Word) (off : Nat) (i : BitVec 25)
    (hbl : instrAt B off = some (.bl i)) (ht : blTarget off i = BitVec.ofNat 32 finishOff)
    (ho : off % 2 = 0) (hox : off + blSize ≤ Artifacts.Release.size)
    (s : State) (hpc : s.pc = c.base + BitVec.ofNat 32 off) (h13 : s.regs 13 = c.A)
    (h0 : s.regs 0 = c.A + 8#32) (h1 : s.regs 1 = tag) (hc : CodeAt s.mem c.base B)
    (hcodeT : Disj c.base Artifacts.Release.size tag 16) (htagS : Disj tag 16 (c.A - 20#32) 20)
    (ic : Poly1305Init.ICtx) (ti : State) (hi : Poly1305Init.IResult ic ti) (hctx : ic.ctx = c.A + 8#32)
    (hk : Ctx.bytesAt ic.m0 ic.key 32 = M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB)
    (msg : List M0Crypto.Spec.ChaCha20.Byte) (hp : PInv c.A ti.mem msg s.mem) :
    Reach c.base (FinishWr c.A tag) s (FinishPost c tag off msg s) := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  apply Reach.bl hb2 off finishOff i hpc ho hbl (by have := blSize_eq; omega) ht
  rw [show off + 4 = off + blSize by rw [blSize_eq]]
  generalize hx : (s.setReg 14 ((c.base + BitVec.ofNat 32 (off + blSize)) ||| 1#32)).setReg 15
    (c.base + BitVec.ofNat 32 finishOff) = x
  have xr : ∀ r : Reg, r.val ≠ 14 → r.val ≠ 15 → x.regs r = s.regs r := fun r a b => by
    rw [← hx, setReg_ne _ _ _ _ (by rintro rfl; exact b rfl), setReg_ne _ _ _ _ (by rintro rfl; exact a rfl)]
  have xm : x.mem = s.mem := by rw [← hx]; rfl
  have x14 : x.regs 14 = (c.base + BitVec.ofNat 32 (off + blSize)) ||| 1#32 := by
    rw [← hx, setReg_ne _ _ _ _ (by decide), setReg_eq]
  let fc : FCtx := { base := c.base, sp0 := c.A, ctx := c.A + 8#32, tag := tag, m0 := x.mem, regs0 := x.regs }
  have fv : FValid fc := {
    base4 := hv.base4
    sp8 := by show c.A.toNat % 8 = 0; rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    spLo := by change 20 ≤ c.A.toNat; have := hv.A_lo; omega
    ctx4 := by show (c.A + 8#32).toNat % 4 = 0; rw [hv.A_off 8 (by decide), hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega
    codeS := hv.win hv.codeS 156 20 _ (by show (c.A - 20#32).toNat = _; rw [hv.sub_toNat 20 (by decide)]; have := hv.A_lo; omega) (by decide)
    codeT := hcodeT
    ctxS := by
      change Disj (c.A + 8#32) 64 (c.A - 20#32) 20
      have := hv.A_lo; have := hv.A_hi
      rw [Disj, hv.A_off 8 (by decide), hv.sub_toNat 20 (by decide)]
      exact ⟨by omega, by omega, .inr (by omega)⟩
    tagS := htagS
    code := by change CodeAt x.mem c.base B; rw [xm]; exact hc }
  have fe : FEntry fc x := ⟨rfl, rfl, by change x.regs 15 = c.base + BitVec.ofNat 32 finishOff; rw [← hx, setReg_eq],
    by change x.regs 13 = c.A; rw [xr 13 (by decide) (by decide), h13], by change x.regs 0 = c.A + 8#32; rw [xr 0 (by decide) (by decide), h0],
    by change x.regs 1 = tag; rw [xr 1 (by decide) (by decide), h1]⟩
  have hlr : (fc.regs0 14).getLsbD 0 = true := by show (x.regs 14).getLsbD 0 = true; rw [x14]; exact lr_odd _
  apply (Poly1305Finish.finish_reach fc fv x fe hlr).mono
  intro t ht'
  refine ⟨?_, ht'.sp, ?_, ?_, ?_⟩
  · rw [ht'.ret]; show x.regs 14 &&& ~~~1#32 = _
    rw [x14, lr_mask _ (even_off c.base hv.base4 _ (by have := blSize_eq; omega))]
  · intro r a b
    rw [ht'.callee r a b]; show x.regs r = _
    rw [xr r (by omega) (by omega)]
  · intro y hy
    rw [Poly1305Finish.result_frame fc x t fe ht' y hy]; exact congrFun xm y
  · have hh : fc.acc < 2 * M0Crypto.Spec.Aead.p := by
      rw [Poly1305Context.finish_acc]; change Poly1305Blocks.accAt x.mem (c.A + 8#32) < _
      rw [xm]; exact Poly1305Context.finish_bound _ hp.bound
    have tagval := Poly1305Finish.result_tag fc fv x t fe ht' hh
    rw [Poly1305Context.finish_acc, Poly1305Context.finish_pad] at tagval
    change Ctx.bytesAt t.mem tag 16 = M0Crypto.Spec.Aead.leBytes 16
      (Poly1305Blocks.accAt x.mem (c.A + 8#32) % _ + Poly1305Context.padAt x.mem (c.A + 8#32)) at tagval
    rw [xm] at tagval
    rw [tagval, ← hctx, Poly1305Context.poly1305_chain ic ti hi s.mem msg hp.len
      (by rw [hctx]; exact hp.pad) (by rw [hctx]; exact hp.acc), hk]

end M0Crypto.Release.Aead
