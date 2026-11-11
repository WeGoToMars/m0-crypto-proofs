import M0Crypto.Release.Frame
import M0Crypto.Release.Layout

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
`m0c_poly1305_init` (offsets from `entryAt` to `poolAt`, in the layout below) on the release bytes.

The body is split into groups proved once each: `gAnd` (load a key word, mask, store
`r_j`), `gS` (store `s_j = r_j + (r_j >> 2)`), `gP` (copy a pad word), `gZ` (zero `h`
and r1-r3), plus the two literal loads, the push and the pop. Context stores are
tracked as a list of `(word index, value)` pairs (`wctx`); key reads see the entry
memory because the key is disjoint from the context and the 12 pushed bytes.

Main results: `init_reach` (for composition inside the AEAD functions) and
`init_correct` (the model's `runUntil` to the return address).
-/

namespace M0Crypto.Release.PolyInit

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-! ## Word stores into a 64-byte context -/

/-- Store `(j, v)` pairs, in order, at word `j` of the context `ctx`. -/
def wctx (ctx : Word) : Mem → List (Nat × Word) → Mem
  | m, [] => m
  | m, (j, v) :: l => wctx ctx (write32 m (ctx + BitVec.ofNat 32 (4 * j)) v) l

/-- The last value stored at word `j`, else `d`. -/
def wv (j : Nat) : Word → List (Nat × Word) → Word
  | d, [] => d
  | d, (i, v) :: l => wv j (if i = j then v else d) l

theorem wctx_append (ctx : Word) : ∀ (m : Mem) (l1 l2 : List (Nat × Word)),
    wctx ctx m (l1 ++ l2) = wctx ctx (wctx ctx m l1) l2
  | _, [], _ => rfl
  | _, (_, _) :: l, l2 => wctx_append ctx _ l l2

/-- Bytes outside `[ctx, ctx + 64)` are unchanged. -/
theorem wctx_other (ctx : Word) (hc : ctx.toNat + 64 ≤ 2 ^ 32) (y : Word)
    (hy : y.toNat < ctx.toNat ∨ ctx.toNat + 64 ≤ y.toNat) :
    ∀ (m : Mem) (l : List (Nat × Word)), (∀ p ∈ l, p.1 < 16) → wctx ctx m l y = m y
  | _, [], _ => rfl
  | m, (j, v) :: l, hl => by
    simp only [wctx]
    rw [wctx_other ctx hc y hy _ l (fun p hp => hl p (List.mem_cons_of_mem _ hp))]
    have hj := hl (j, v) (by simp)
    apply M0Crypto.Armv6M.write32_other
    intro k hk e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this hj
    omega

theorem read32_wctx_other (ctx : Word) (hc : ctx.toNat + 64 ≤ 2 ^ 32) (b : Word) (hb : b.toNat + 4 ≤ 2 ^ 32)
    (hd : b.toNat + 4 ≤ ctx.toNat ∨ ctx.toNat + 64 ≤ b.toNat) (m : Mem) (l : List (Nat × Word))
    (hl : ∀ p ∈ l, p.1 < 16) : read32 (wctx ctx m l) b = read32 m b := by
  apply read32_congr
  intro k hk
  apply wctx_other ctx hc _ _ m l hl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem read32_wctx_slot (ctx : Word) (j : Nat) (hj : j < 16) :
    ∀ (m : Mem) (l : List (Nat × Word)), (∀ p ∈ l, p.1 < 16) →
      read32 (wctx ctx m l) (ctx + BitVec.ofNat 32 (4 * j)) = wv j (read32 m (ctx + BitVec.ofNat 32 (4 * j))) l
  | _, [], _ => rfl
  | m, (i, v) :: l, hl => by
    simp only [wctx, wv]
    rw [read32_wctx_slot ctx j hj _ l (fun p hp => hl p (List.mem_cons_of_mem _ hp))]
    have hi := hl (i, v) (by simp)
    have := read32_write32_slot' m ctx v i j (by simp at hi; omega) (by omega)
    simp only [slot] at this
    rw [this]



/-! ## The call -/

structure ICtx where
  base : Word
  sp0 : Word
  ctx : Word
  key : Word
  m0 : Mem
  regs0 : Reg → Word

namespace ICtx
variable (c : ICtx)

/-- Memory after `push {r4, r5, lr}`. -/
def mP : Mem := storeWords c.m0 (c.sp0 - BitVec.ofNat 32 12) [c.regs0 4, c.regs0 5, c.regs0 14]

/-- Key word `i` (little-endian, as `ldr` reads it). -/
def kw (i : Nat) : Word := read32 c.m0 (c.key + BitVec.ofNat 32 (4 * i))
end ICtx

structure IValid (c : ICtx) : Prop where
  base4 : c.base.toNat % 4 = 0
  sp4 : c.sp0.toNat % 4 = 0
  spLo : 12 ≤ c.sp0.toNat
  ctx4 : c.ctx.toNat % 4 = 0
  key4 : c.key.toNat % 4 = 0
  codeS : Disj c.base Artifacts.Release.size (c.sp0 - BitVec.ofNat 32 12) 12
  codeC : Disj c.base Artifacts.Release.size c.ctx 64
  ctxS : Disj c.ctx 64 (c.sp0 - BitVec.ofNat 32 12) 12
  keyS : Disj c.key 32 (c.sp0 - BitVec.ofNat 32 12) 12
  keyC : Disj c.key 32 c.ctx 64
  code : CodeAt c.m0 c.base B

/-- State inside `init` after the push, with `L` stored into the context. -/
structure IS (c : ICtx) (off : Nat) (L : List (Nat × Word)) (t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 off
  r0 : t.regs 0 = c.ctx
  r1 : t.regs 1 = c.key
  sp : t.regs 13 = c.sp0 - BitVec.ofNat 32 12
  oth : ∀ r : Reg, 6 ≤ r.val → r.val ≠ 13 → r.val ≠ 15 → t.regs r = c.regs0 r
  mem : t.mem = wctx c.ctx c.mP L
  keys : ∀ p ∈ L, p.1 < 16

theorem ofNat5 {i : Nat} (h : i < 32) : (BitVec.ofNat 5 i).toNat = i := by simp; omega

theorem toNat_sp12 {c : ICtx} (hv : IValid c) : (c.sp0 - BitVec.ofNat 32 12).toNat = c.sp0.toNat - 12 := by
  have := hv.spLo; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem kw_read {c : ICtx} (hv : IValid c) (L : List (Nat × Word)) (hl : ∀ p ∈ L, p.1 < 16) (i : Nat) (hi : i < 8) :
    read32 (wctx c.ctx c.mP L) (c.key + BitVec.ofNat 32 (i * 4)) = c.kw i := by
  obtain ⟨k1, k2, k3⟩ := hv.keyC
  obtain ⟨s1, s2, s3⟩ := hv.keyS
  have hs := toNat_sp12 hv
  rw [read32_wctx_other _ k2 _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ _ hl]
  simp only [ICtx.kw, ICtx.mP]
  rw [show 4 * i = i * 4 by omega]
  apply read32_congr
  intro k hk
  apply storeWords_other
  intro j q hj hq e
  have := congrArg BitVec.toNat e
  simp at hj
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

/-! ## `ldr r2, [r1, #4i]; ands r2, r4; str r2, [r0, #4a]` -/

def gAnd (i a : Nat) : List Instr :=
  [.memImm .ldr 2 1 (BitVec.ofNat 5 i), .dp .ands 2 4, .memImm .str 2 0 (BitVec.ofNat 5 a)]

theorem gAnd_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop} (hW : ∀ o < 64, Wr (c.ctx + BitVec.ofNat 32 o))
    {off : Nat} {i a : Nat} {L : List (Nat × Word)} {t : State} (hI : IS c off L t) (ho : off % 2 = 0)
    (hseq : seqAt B off (gAnd i a) = true) (hi : i < 8) (ha : a < 16) {Q : State → Prop}
    (k : ∀ t', IS c (off + seqSize (gAnd i a)) (L ++ [(a, c.kw i &&& t.regs 4)]) t' → t'.regs 2 = c.kw i &&& t.regs 4 →
      t'.regs 4 = t.regs 4 → t'.regs 5 = t.regs 5 → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨_, hc, _⟩ := hv.codeC
  have hk4 := hv.key4; have hc4 := hv.ctx4
  obtain ⟨hk, _, _⟩ := hv.keyC
  have ha' : a % 32 = a := Nat.mod_eq_of_lt (by omega)
  have hi' : i % 32 = i := Nat.mod_eq_of_lt (by omega)
  apply Reach.block hb2 (gAnd i a) off hI.pc ho hseq (by simp [gAnd, Instr.falls])
  · simp [alignedAll, gAnd, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses, Access.aligned, MemOp.width,
      MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1,
      M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_4, hI.r0, hI.r1, hi', ha', BitVec.toNat_add]
    omega
  · intro e he y ⟨acc, hacc, hw, q, hq, hy⟩
    simp only [traceAll, gAnd, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp [Instr.accesses, MemOp.isLoad, MemOp.width] at hacc <;> subst hacc <;> simp at hw hq
    simp (config := { decide := true }) [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, hI.r0,
      ha'] at hy
    rw [hy, ofNat_add_assoc]
    exact hW (a * 4 + q) (by omega)
  · have e2 : ∀ r : Reg, r.val ≠ 15 → (execAll (gAnd i a) t).regs r =
        if r = 2 then c.kw i &&& t.regs 4 else t.regs r := by
      intro r hr
      have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
      simp (config := { decide := true }) [execAll, gAnd, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
        M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_4, MemOp.width, Instr.size,
        hI.r1, hI.mem, hi', kw_read hv L hI.keys i hi, h15]
      split <;> rfl
    have em : (execAll (gAnd i a) t).mem = wctx c.ctx c.mP (L ++ [(a, c.kw i &&& t.regs 4)]) := by
      simp (config := { decide := true }) [execAll, gAnd, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
        M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_4, MemOp.width, Instr.size,
        hI.r1, hI.r0, hI.mem, hi', ha', kw_read hv L hI.keys i hi, wctx_append, wctx]
      rw [Nat.mul_comm]
    have e' : ∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → (execAll (gAnd i a) t).regs r = t.regs r := by
      intro r h2 h15; rw [e2 r h15]; simp only [show r ≠ 2 from fun e => h2 (by rw [e]; rfl), ite_false]
    apply k
    · exact { pc := by rw [execAll_pc _ _ (by simp [gAnd, Instr.falls]), hI.pc, ofNat_add_assoc]
              r0 := by rw [e' 0 (by decide) (by decide), hI.r0]
              r1 := by rw [e' 1 (by decide) (by decide), hI.r1]
              sp := by rw [e' 13 (by decide) (by decide), hI.sp]
              oth := fun r h6 h13 h15 => by rw [e' r (by omega) h15, hI.oth r h6 h13 h15]
              mem := em
              keys := by
                intro p hp
                rcases List.mem_append.mp hp with h | h
                · exact hI.keys p h
                · simp at h; subst h; exact ha }
    · rw [e2 2 (by decide)]; rfl
    · exact e' 4 (by decide) (by decide)
    · exact e' 5 (by decide) (by decide)

theorem keys_app {L : List (Nat × Word)} (hl : ∀ p ∈ L, p.1 < 16) (l : List (Nat × Word)) (h : ∀ p ∈ l, p.1 < 16) :
    ∀ p ∈ L ++ l, p.1 < 16 := by
  intro p hp; rcases List.mem_append.mp hp with h' | h'
  · exact hl p h'
  · exact h p h'

/-! ## `lsrs r5, r2, #2; adds r5, r5, r2; str r5, [r0, #4b]` -/

def gS (b : Nat) : List Instr := [.lsrImm 5 2 2, .addReg 5 5 2, .memImm .str 5 0 (BitVec.ofNat 5 b)]

theorem gS_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop} (hW : ∀ o < 64, Wr (c.ctx + BitVec.ofNat 32 o))
    {off : Nat} {b : Nat} {L : List (Nat × Word)} {t : State} (hI : IS c off L t) (ho : off % 2 = 0)
    (hseq : seqAt B off (gS b) = true) (hb : b < 16) {Q : State → Prop}
    (k : ∀ t', IS c (off + seqSize (gS b)) (L ++ [(b, (t.regs 2 >>> 2) + t.regs 2)]) t' →
      t'.regs 2 = t.regs 2 → t'.regs 4 = t.regs 4 → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨_, hc, _⟩ := hv.codeC
  have hc4 := hv.ctx4
  have hb' : b % 32 = b := Nat.mod_eq_of_lt (by omega)
  apply Reach.block hb2 (gS b) off hI.pc ho hseq (by simp [gS, Instr.falls])
  · simp (config := { decide := true }) [alignedAll, gS, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      Access.aligned, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZC,
      M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_5,
      addFlags, hI.r0, hb', BitVec.toNat_add]
    omega
  · intro e he y ⟨acc, hacc, hw, q, hq, hy⟩
    simp only [traceAll, gS, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp [Instr.accesses, MemOp.isLoad, MemOp.width] at hacc <;> subst hacc <;> simp at hw hq
    simp (config := { decide := true }) [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.setNZC, addFlags, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
      M0Crypto.Proofs.toReg_5, hI.r0, hb'] at hy
    rw [hy, ofNat_add_assoc]
    exact hW (b * 4 + q) (by omega)
  · have e2 : ∀ r : Reg, r.val ≠ 15 → (execAll (gS b) t).regs r =
        if r = 5 then (t.regs 2 >>> 2) + t.regs 2 else t.regs r := by
      intro r hr
      have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
      simp (config := { decide := true }) [execAll, gS, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV, addFlags, M0Crypto.Armv6M.State.reg,
        Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_5, lsrC,
        M0Crypto.Proofs.addWithCarry_fst, h15]
      split <;> rfl
    have em : (execAll (gS b) t).mem = wctx c.ctx c.mP (L ++ [(b, (t.regs 2 >>> 2) + t.regs 2)]) := by
      simp (config := { decide := true }) [execAll, gS, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZC, M0Crypto.Armv6M.State.setNZCV, addFlags, M0Crypto.Armv6M.State.reg,
        Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_5, lsrC,
        M0Crypto.Proofs.addWithCarry_fst, MemOp.width, hI.r0, hI.mem, hb', wctx_append, wctx]
      rw [Nat.mul_comm]
    have e' : ∀ r : Reg, r.val ≠ 5 → r.val ≠ 15 → (execAll (gS b) t).regs r = t.regs r := by
      intro r h5 h15; rw [e2 r h15]; simp only [show r ≠ 5 from fun e => h5 (by rw [e]; rfl), ite_false]
    apply k
    · exact { pc := by rw [execAll_pc _ _ (by simp [gS, Instr.falls]), hI.pc, ofNat_add_assoc]
              r0 := by rw [e' 0 (by decide) (by decide), hI.r0]
              r1 := by rw [e' 1 (by decide) (by decide), hI.r1]
              sp := by rw [e' 13 (by decide) (by decide), hI.sp]
              oth := fun r h6 h13 h15 => by rw [e' r (by omega) h15, hI.oth r h6 h13 h15]
              mem := em
              keys := keys_app hI.keys _ (by simp; omega) }
    · exact e' 2 (by decide) (by decide)
    · exact e' 4 (by decide) (by decide)

/-! ## `ldr r2, [r1, #4i]; str r2, [r0, #4a]` -/

def gP (i a : Nat) : List Instr := [.memImm .ldr 2 1 (BitVec.ofNat 5 i), .memImm .str 2 0 (BitVec.ofNat 5 a)]

theorem gP_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop} (hW : ∀ o < 64, Wr (c.ctx + BitVec.ofNat 32 o))
    {off : Nat} {i a : Nat} {L : List (Nat × Word)} {t : State} (hI : IS c off L t) (ho : off % 2 = 0)
    (hseq : seqAt B off (gP i a) = true) (hi : i < 8) (ha : a < 16) {Q : State → Prop}
    (k : ∀ t', IS c (off + seqSize (gP i a)) (L ++ [(a, c.kw i)]) t' → t'.regs 2 = c.kw i →
      t'.regs 4 = t.regs 4 → t'.regs 5 = t.regs 5 → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨_, hc, _⟩ := hv.codeC
  have hk4 := hv.key4; have hc4 := hv.ctx4
  obtain ⟨hk, _, _⟩ := hv.keyC
  have ha' : a % 32 = a := Nat.mod_eq_of_lt (by omega)
  have hi' : i % 32 = i := Nat.mod_eq_of_lt (by omega)
  apply Reach.block hb2 (gP i a) off hI.pc ho hseq (by simp [gP, Instr.falls])
  · simp (config := { decide := true }) [alignedAll, gP, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      Access.aligned, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.reg,
      M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, hI.r0, hI.r1, ha', hi',
      BitVec.toNat_add]
    omega
  · intro e he y ⟨acc, hacc, hw, q, hq, hy⟩
    simp only [traceAll, gP, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      simp [Instr.accesses, MemOp.isLoad, MemOp.width] at hacc <;> subst hacc <;> simp at hw hq
    simp (config := { decide := true }) [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_2, hI.r0,
      ha'] at hy
    rw [hy, ofNat_add_assoc]
    exact hW (a * 4 + q) (by omega)
  · have e2 : ∀ r : Reg, r.val ≠ 15 → (execAll (gP i a) t).regs r = if r = 2 then c.kw i else t.regs r := by
      intro r hr
      have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
      simp (config := { decide := true }) [execAll, gP, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1,
        M0Crypto.Proofs.toReg_2, MemOp.width, hI.r1, hI.mem, hi', kw_read hv L hI.keys i hi, h15]
    have em : (execAll (gP i a) t).mem = wctx c.ctx c.mP (L ++ [(a, c.kw i)]) := by
      simp (config := { decide := true }) [execAll, gP, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1,
        M0Crypto.Proofs.toReg_2, MemOp.width, hI.r1, hI.r0, hI.mem, hi', ha', kw_read hv L hI.keys i hi,
        wctx_append, wctx]
      rw [Nat.mul_comm]
    have e' : ∀ r : Reg, r.val ≠ 2 → r.val ≠ 15 → (execAll (gP i a) t).regs r = t.regs r := by
      intro r h2 h15; rw [e2 r h15]; simp only [show r ≠ 2 from fun e => h2 (by rw [e]; rfl), ite_false]
    apply k
    · exact { pc := by rw [execAll_pc _ _ (by simp [gP, Instr.falls]), hI.pc, ofNat_add_assoc]
              r0 := by rw [e' 0 (by decide) (by decide), hI.r0]
              r1 := by rw [e' 1 (by decide) (by decide), hI.r1]
              sp := by rw [e' 13 (by decide) (by decide), hI.sp]
              oth := fun r h6 h13 h15 => by rw [e' r (by omega) h15, hI.oth r h6 h13 h15]
              mem := em
              keys := keys_app hI.keys _ (by simp; omega) }
    · rw [e2 2 (by decide)]; rfl
    · exact e' 4 (by decide) (by decide)
    · exact e' 5 (by decide) (by decide)


/-! ## `movs r2, #0; str r2, [r0, #0..16]; movs r1, #0; movs r3, #0` -/

def gZ : List Instr :=
  [.movImm 2 0, .memImm .str 2 0 0, .memImm .str 2 0 1, .memImm .str 2 0 2, .memImm .str 2 0 3,
   .memImm .str 2 0 4, .movImm 1 0, .movImm 3 0]

def zL : List (Nat × Word) := [(0, 0#32), (1, 0#32), (2, 0#32), (3, 0#32), (4, 0#32)]

theorem gZ_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop} (hW : ∀ o < 64, Wr (c.ctx + BitVec.ofNat 32 o))
    {off : Nat} {L : List (Nat × Word)} {t : State} (hI : IS c off L t) (ho : off % 2 = 0)
    (hseq : seqAt B off gZ = true) {Q : State → Prop}
    (k : ∀ t', t'.pc = c.base + BitVec.ofNat 32 (off + seqSize gZ) →
      t'.mem = wctx c.ctx c.mP (L ++ zL) →
      (∀ r : Reg, r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 15 → t'.regs r = t.regs r) →
      t'.regs 1 = 0#32 → t'.regs 2 = 0#32 → t'.regs 3 = 0#32 → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨_, hc, _⟩ := hv.codeC
  have hc4 := hv.ctx4
  apply Reach.block hb2 gZ off hI.pc ho hseq (by simp [gZ, Instr.falls])
  · simp (config := { decide := true }) [alignedAll, gZ, Instr.next, Instr.exec, Instr.exec.memOp, Instr.accesses,
      Access.aligned, MemOp.width, MemOp.isLoad, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.setNZ,
      M0Crypto.Armv6M.State.reg, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2,
      M0Crypto.Proofs.toReg_3, hI.r0, BitVec.toNat_add]
    omega
  · intro e he y ⟨acc, hacc, hw, q, hq, hy⟩
    simp only [traceAll, gZ, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Instr.accesses, MemOp.isLoad, MemOp.width] at hacc <;> subst hacc <;> simp at hw hq <;>
      simp (config := { decide := true }) [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
        M0Crypto.Proofs.toReg_2, hI.r0] at hy <;>
      rw [hy]
    · simpa using hW q (by omega)
    all_goals rw [ofNat_add_assoc]; exact hW _ (by omega)
  · have e2 : ∀ r : Reg, r.val ≠ 15 → (execAll gZ t).regs r =
        if r = 3 then 0#32 else if r = 1 then 0#32 else if r = 2 then 0#32 else t.regs r := by
      intro r hr
      have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
      simp (config := { decide := true }) [execAll, gZ, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
        M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, h15]
    have em : (execAll gZ t).mem = wctx c.ctx c.mP (L ++ zL) := by
      simp (config := { decide := true }) [execAll, gZ, zL, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
        M0Crypto.Armv6M.State.setNZ, M0Crypto.Armv6M.State.reg, Instr.exec.memOp, M0Crypto.Proofs.toReg_0,
        M0Crypto.Proofs.toReg_2, MemOp.width, hI.r0, hI.mem, wctx_append, wctx]
    apply k
    · rw [execAll_pc _ _ (by simp [gZ, Instr.falls]), hI.pc, ofNat_add_assoc]
    · exact em
    · intro r h1 h2 h3 h15
      rw [e2 r h15]
      simp only [show r ≠ 1 from fun e => h1 (by rw [e]; rfl), show r ≠ 2 from fun e => h2 (by rw [e]; rfl),
        show r ≠ 3 from fun e => h3 (by rw [e]; rfl), ite_false]
    · rw [e2 1 (by decide)]; rfl
    · rw [e2 2 (by decide)]; rfl
    · rw [e2 3 (by decide)]; rfl

/-! ## Literal loads -/

theorem mP_other (c : ICtx) (hv : IValid c) (y : Word)
    (hy : y.toNat + 12 < c.sp0.toNat ∨ c.sp0.toNat ≤ y.toNat) :
    c.mP y = c.m0 y := by
  have hs := toNat_sp12 hv; have := hv.spLo
  simp only [ICtx.mP]
  apply storeWords_other
  intro j q hj hq e
  have := congrArg BitVec.toNat e
  simp at hj
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  omega

theorem read32_code_wctx {c : ICtx} (hv : IValid c) (L : List (Nat × Word)) (hl : ∀ p ∈ L, p.1 < 16)
    (off : Nat) (h : off + 4 ≤ Artifacts.Release.size) :
    read32 (wctx c.ctx c.mP L) (c.base + BitVec.ofNat 32 off) = codeWord off := by
  obtain ⟨b1, c1, d1⟩ := hv.codeC
  obtain ⟨b2, s2, d2⟩ := hv.codeS
  have hs := toNat_sp12 hv
  rw [read32_wctx_other _ c1 _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ _ hl]
  rw [← read32_code hv.code off h]
  apply read32_congr
  intro k hk
  apply mP_other c hv _
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem gLit_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop}
    {off imm : Nat} {L : List (Nat × Word)} {t : State} (hI : IS c off L t) (ho : off % 4 = 2)
    (hi : instrAt B off = some (.ldrLit 4 (BitVec.ofNat 8 imm))) (himm : imm < 256)
    (hl : (off + 4) / 4 * 4 + imm * 4 + 4 ≤ Artifacts.Release.size) {Q : State → Prop}
    (k : ∀ t', IS c (off + litSize) L t' → t'.regs 4 = codeWord ((off + 4) / 4 * 4 + imm * 4) →
      t'.regs 5 = t.regs 5 → t'.regs 2 = t.regs 2 → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  obtain ⟨b1, _, _⟩ := hv.codeC
  have hla : ((t.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 ((BitVec.ofNat 8 imm).toNat * 4) =
      c.base + BitVec.ofNat 32 ((off + 4) / 4 * 4 + imm * 4) := by
    rw [hI.pc, show (BitVec.ofNat 8 imm).toNat = imm by simp; omega]
    exact lit_addr c.base hv.base4 off imm (by omega)
  have hacc : (Instr.ldrLit 4 (BitVec.ofNat 8 imm)).accesses t =
      [⟨.read, c.base + BitVec.ofNat 32 ((off + 4) / 4 * 4 + imm * 4), 4⟩] := by
    simp only [Instr.accesses, M0Crypto.Armv6M.State.pc] at hla ⊢; rw [hla]
  apply Reach.step hb2 off _ hI.pc (by omega) hi (by rw [B_len]; simp [Instr.size]; omega)
    (by rw [hacc]; simp [Access.aligned, BitVec.toNat_add]; have := hv.base4; omega) rfl
    (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses] at ha; subst ha; cases hw)
  have e2 : ∀ r : Reg, r.val ≠ 15 → ((Instr.ldrLit 4 (BitVec.ofNat 8 imm)).next t).regs r =
      if r = 4 then codeWord ((off + 4) / 4 * 4 + imm * 4) else t.regs r := by
    intro r hr
    have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
    simp only [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Proofs.toReg_4, h15, ite_false]
    rw [hla, hI.mem, read32_code_wctx hv L hI.keys _ hl]
  have e' : ∀ r : Reg, r.val ≠ 4 → r.val ≠ 15 → ((Instr.ldrLit 4 (BitVec.ofNat 8 imm)).next t).regs r = t.regs r := by
    intro r h4 h15; rw [e2 r h15]; simp only [show r ≠ 4 from fun e => h4 (by rw [e]; rfl), ite_false]
  show Reach c.base Wr ((Instr.ldrLit 4 (BitVec.ofNat 8 imm)).next t) Q
  apply k
  · exact { pc := by
              have := execAll_pc [Instr.ldrLit 4 (BitVec.ofNat 8 imm)] t (by simp [Instr.falls])
              simp only [execAll] at this
              rw [this, hI.pc, ofNat_add_assoc]
              rfl
            r0 := by rw [e' 0 (by decide) (by decide), hI.r0]
            r1 := by rw [e' 1 (by decide) (by decide), hI.r1]
            sp := by rw [e' 13 (by decide) (by decide), hI.sp]
            oth := fun r h6 h13 h15 => by rw [e' r (by omega) h15, hI.oth r h6 h13 h15]
            mem := by simp [Instr.next, Instr.exec, hI.mem]
            keys := hI.keys }
  · rw [e2 4 (by decide)]; rfl
  · exact e' 5 (by decide) (by decide)
  · exact e' 2 (by decide) (by decide)


/-! ## `push {r4, r5, lr}` and `pop {r4, r5, pc}` -/

theorem listRegs_30 : listRegs 0x30 = [4, 5] := by decide
theorem listRegs_48 : listRegs 48#8 = [4, 5] := by decide
theorem bitCount_30 : bitCount 0x30 = 2 := by decide
theorem bitCount_48 : bitCount 48#8 = 2 := by decide

/-! ## Layout of `m0c_poly1305_init`

Derived, as in `PolyBlocksCode`: the function starts at `Artifacts.Release.poly1305_init`, and
each piece starts where the one before it ends. A literal load occupies `litSize` bytes whatever
its immediate; the immediate is `litImm` of the load's own offset and the pool word it reads.
The pool starts at the first word-aligned address after `pop`. -/

/-- Function entry: `push {r4, r5, lr}`. -/
def entryAt : Nat := Artifacts.Release.poly1305_init
/-- Literal load of the first mask word (`poolAt`). -/
def ld0At : Nat := entryAt + seqSize [.push 0x30 true]
/-- `ldr r2, [r1, #4i]; ands r2, r4; str r2, [r0, #4a]` for `(i, a) = (0, 5)`. -/
def and0At : Nat := ld0At + litSize
/-- Literal load of the second mask word (`poolAt + 4`). -/
def ld1At : Nat := and0At + seqSize (gAnd 0 5)
def and1At : Nat := ld1At + litSize
def s1At : Nat := and1At + seqSize (gAnd 1 6)
def and2At : Nat := s1At + seqSize (gS 9)
def s2At : Nat := and2At + seqSize (gAnd 2 7)
def and3At : Nat := s2At + seqSize (gS 10)
def s3At : Nat := and3At + seqSize (gAnd 3 8)
def p4At : Nat := s3At + seqSize (gS 11)
def p5At : Nat := p4At + seqSize (gP 4 12)
def p6At : Nat := p5At + seqSize (gP 5 13)
def p7At : Nat := p6At + seqSize (gP 6 14)
/-- `gZ`: zero `h` and r1-r3. -/
def zAt : Nat := p7At + seqSize (gP 7 15)
/-- `pop {r4, r5, pc}`: the return. -/
def popAt : Nat := zAt + seqSize gZ
/-- The first pool word; the second is at `poolAt + 4`. -/
def poolAt : Nat := (popAt + seqSize [.pop 0x30 true] + 3) / 4 * 4

/-- Entry state of `m0c_poly1305_init(ctx, key)`. -/
structure IEntry (c : ICtx) (s : State) : Prop where
  regs : s.regs = c.regs0
  mem : s.mem = c.m0
  pc : c.regs0 15 = c.base + BitVec.ofNat 32 entryAt
  sp : c.regs0 13 = c.sp0
  r0 : c.regs0 0 = c.ctx
  r1 : c.regs0 1 = c.key

theorem push_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop}
    (hWs : ∀ o < 12, Wr (c.sp0 - BitVec.ofNat 32 12 + BitVec.ofNat 32 o)) {s : State} (he : IEntry c s)
    {Q : State → Prop}
    (k : ∀ t, IS c ld0At [] t → t.regs 4 = c.regs0 4 → t.regs 5 = c.regs0 5 → t.regs 2 = c.regs0 2 →
      Reach c.base Wr t Q) :
    Reach c.base Wr s Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hpc : s.pc = c.base + BitVec.ofNat 32 entryAt := by
    show s.regs 15 = _; rw [he.regs, he.pc]
  have h13 : s.regs 13 = c.sp0 := by rw [he.regs, he.sp]
  have hs := toNat_sp12 hv; have := hv.sp4; have := hv.spLo
  have hsp : s.regs 13 - BitVec.ofNat 32 (4 * (bitCount 48#8 + true.toNat)) = c.sp0 - BitVec.ofNat 32 12 := by
    rw [h13, bitCount_48]; rfl
  apply Reach.step hb2 entryAt (.push 0x30 true) hpc (by decide) (by decide) (by rw [B_len]; decide)
    (by simp only [Instr.accesses, M0Crypto.Armv6M.State.sp, wordAccesses]
        rw [show (0x30 : BitVec 8) = 48#8 from rfl, hsp]
        simp [Access.aligned, List.range_succ, BitVec.toNat_add, bitCount_48]; omega) rfl
  · intro y ⟨a, ha, _, q, hq, hy⟩
    simp only [Instr.accesses, M0Crypto.Armv6M.State.sp, wordAccesses] at ha
    rw [show (0x30 : BitVec 8) = 48#8 from rfl, hsp] at ha
    simp [List.range_succ, bitCount_48] at ha
    rcases ha with rfl | rfl | rfl <;> simp at hq hy <;> rw [hy] <;>
      (try rw [ofNat_add_assoc]) <;> (try rw [ofNat_add_assoc]) <;> exact hWs _ (by omega)
  have e2 : ∀ r : Reg, r.val ≠ 15 → ((Instr.push 0x30 true).next s).regs r =
      if r = 13 then c.sp0 - BitVec.ofNat 32 12 else c.regs0 r := by
    intro r hr
    have h15 : (r = 15) = False := eq_false (fun e => hr (by rw [e]; rfl))
    simp only [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
      show (0x30 : BitVec 8) = 48#8 from rfl, hsp, h15, ite_false, he.regs, he.sp, bitCount_48, Bool.toNat_true]
  have e' : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → ((Instr.push 0x30 true).next s).regs r = c.regs0 r := by
    intro r h13 h15; rw [e2 r h15]; simp only [show r ≠ 13 from fun e => h13 (by rw [e]; rfl), ite_false]
  show Reach c.base Wr ((Instr.push 0x30 true).next s) Q
  apply k
  · exact { pc := by
              have := execAll_pc [Instr.push 0x30 true] s (by simp [Instr.falls])
              simp only [execAll] at this
              rw [this, hpc, ofNat_add_assoc]
              rfl
            r0 := by rw [e' 0 (by decide) (by decide), he.r0]
            r1 := by rw [e' 1 (by decide) (by decide), he.r1]
            sp := by rw [e2 13 (by decide)]; rfl
            oth := fun r h6 h13 h15 => e' r h13 h15
            mem := by
              simp only [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp,
                show (0x30 : BitVec 8) = 48#8 from rfl, hsp, wctx, ICtx.mP, listRegs_48, he.mem, List.map,
                M0Crypto.Armv6M.State.reg, he.regs, he.sp, bitCount_48, Bool.toNat_true, ite_true,
                M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, List.cons_append, List.nil_append]
            keys := by simp }
  · exact e' 4 (by decide) (by decide)
  · exact e' 5 (by decide) (by decide)
  · exact e' 2 (by decide) (by decide)

theorem saved_read {c : ICtx} (hv : IValid c) (L : List (Nat × Word)) (hl : ∀ p ∈ L, p.1 < 16) (i : Nat) (hi : i < 3) :
    read32 (wctx c.ctx c.mP L) (c.sp0 - BitVec.ofNat 32 12 + BitVec.ofNat 32 (4 * i)) =
      [c.regs0 4, c.regs0 5, c.regs0 14][i] := by
  obtain ⟨c1, s1, d1⟩ := hv.ctxS
  have hs := toNat_sp12 hv; have := hv.spLo
  rw [read32_wctx_other _ c1 _ (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) _ _ hl]
  exact Frame.read32_storeWords_same _ _ _ i (by simp; omega) (by simp)

theorem pop_run {c : ICtx} (hv : IValid c) {Wr : Word → Prop} {L : List (Nat × Word)} {t : State}
    (hpc : t.pc = c.base + BitVec.ofNat 32 popAt) (hsp : t.regs 13 = c.sp0 - BitVec.ofNat 32 12)
    (hm : t.mem = wctx c.ctx c.mP L) (hl : ∀ p ∈ L, p.1 < 16) (hlr : (c.regs0 14).getLsbD 0 = true)
    {Q : State → Prop}
    (k : ∀ t', t'.pc = c.regs0 14 &&& ~~~1#32 → t'.regs 13 = c.sp0 → t'.regs 4 = c.regs0 4 →
      t'.regs 5 = c.regs0 5 → (∀ r : Reg, r.val ≠ 4 → r.val ≠ 5 → r.val ≠ 13 → r.val ≠ 15 → t'.regs r = t.regs r) →
      t'.mem = t.mem → Reach c.base Wr t' Q) :
    Reach c.base Wr t Q := by
  have hb2 : c.base.toNat % 2 = 0 := by have := hv.base4; omega
  have hs := toNat_sp12 hv; have := hv.sp4; have := hv.spLo
  have sv0 := saved_read hv L hl 0 (by decide)
  have sv1 := saved_read hv L hl 1 (by decide)
  have sv2 := saved_read hv L hl 2 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.mul_one, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.reduceMul] at sv0 sv1 sv2
  rw [← hm] at sv0 sv1 sv2
  have e8 : t.regs 13 + BitVec.ofNat 32 (4 * 2) = c.sp0 - BitVec.ofNat 32 12 + BitVec.ofNat 32 8 := by
    rw [hsp]
  have hex : (Instr.pop 0x30 true).exec t = .ok ((((loadRegs (t.setReg 15 (t.pc + BitVec.ofNat 32 2))
      (t.regs 13) [4, 5]).setReg 13 (c.sp0)).setReg 15 (c.regs0 14 &&& ~~~1#32))) := by
    simp only [Instr.exec, M0Crypto.Armv6M.State.sp, show (0x30 : BitVec 8) = 48#8 from rfl, e8, sv2, hlr,
      ite_true, listRegs_48, List.map, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, bitCount_48, Instr.size]
    congr 4
    rw [hsp]; simp only [Bool.toNat_true]; bv_omega
  apply Reach.step hb2 popAt (.pop 0x30 true) hpc (by decide) (by decide) (by rw [B_len]; decide)
    (by simp only [Instr.accesses, M0Crypto.Armv6M.State.sp, wordAccesses, hsp,
          show (0x30 : BitVec 8) = 48#8 from rfl, bitCount_48]
        simp [Access.aligned, List.range_succ, BitVec.toNat_add]; omega) hex
    (by intro y ⟨a, ha, hw, _⟩; simp [Instr.accesses, wordAccesses] at ha
        obtain ⟨_, _, rfl⟩ := ha; cases hw)
  apply k
  · rfl
  · rfl
  · simp [M0Crypto.Armv6M.State.setReg, loadRegs, hsp, sv0]
  · simp [M0Crypto.Armv6M.State.setReg, loadRegs, hsp, sv1]
  · intro r h4 h5 h13 h15
    simp only [M0Crypto.Armv6M.State.setReg, loadRegs, show r ≠ 15 from fun e => h15 (by rw [e]; rfl),
      show r ≠ 13 from fun e => h13 (by rw [e]; rfl), show r ≠ 4 from fun e => h4 (by rw [e]; rfl),
      show r ≠ 5 from fun e => h5 (by rw [e]; rfl), ite_false]
  · simp [M0Crypto.Armv6M.State.setReg, loadRegs]


/-! ## The whole function -/

theorem cw_r0 : codeWord poolAt = 0x0fffffff#32 := by decide
theorem cw_r : codeWord (poolAt + 4) = 0x0ffffffc#32 := by decide

/-- `r_j + (r_j >> 2)` -/
def sfold (v : Word) : Word := (v >>> 2) + v

/-- Words stored by `init`, in program order. -/
def initL (c : ICtx) : List (Nat × Word) :=
  let r1 := c.kw 1 &&& 0x0ffffffc#32
  let r2 := c.kw 2 &&& 0x0ffffffc#32
  let r3 := c.kw 3 &&& 0x0ffffffc#32
  [(5, c.kw 0 &&& 0x0fffffff#32), (6, r1), (9, sfold r1), (7, r2), (10, sfold r2), (8, r3), (11, sfold r3),
   (12, c.kw 4), (13, c.kw 5), (14, c.kw 6), (15, c.kw 7)] ++ zL

theorem init_seq :
    seqAt B and0At (gAnd 0 5) = true ∧ seqAt B and1At (gAnd 1 6) = true ∧ seqAt B s1At (gS 9) = true ∧
    seqAt B and2At (gAnd 2 7) = true ∧ seqAt B s2At (gS 10) = true ∧ seqAt B and3At (gAnd 3 8) = true ∧
    seqAt B s3At (gS 11) = true ∧ seqAt B p4At (gP 4 12) = true ∧ seqAt B p5At (gP 5 13) = true ∧
    seqAt B p6At (gP 6 14) = true ∧ seqAt B p7At (gP 7 15) = true ∧ seqAt B zAt gZ = true ∧
    instrAt B ld0At = some (.ldrLit 4 (BitVec.ofNat 8 (litImm ld0At poolAt))) ∧
    instrAt B ld1At = some (.ldrLit 4 (BitVec.ofNat 8 (litImm ld1At (poolAt + 4)))) := by
  decide

/-- `m0c_poly1305_init` from entry to its return: SP and r4-r12, LR restored, r1-r3 zero,
memory equal to the entry memory with the 12 saved bytes below SP and the 64 context
bytes replaced as `initL` lists. Every write is in those 76 bytes (`Wr` contains them). -/
theorem init_run (c : ICtx) (hv : IValid c) {Wr : Word → Prop}
    (hWs : ∀ o < 12, Wr (c.sp0 - BitVec.ofNat 32 12 + BitVec.ofNat 32 o))
    (hWc : ∀ o < 64, Wr (c.ctx + BitVec.ofNat 32 o)) (s : State) (he : IEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base Wr s fun t => t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 13 → r.val ≠ 15 → t.regs r = c.regs0 r) ∧
      t.regs 1 = 0#32 ∧ t.regs 2 = 0#32 ∧ t.regs 3 = 0#32 ∧ t.mem = wctx c.ctx c.mP (initL c) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, l1, l2⟩ := init_seq
  apply push_run hv hWs he; intro t0 I0 a4 a5 _
  apply gLit_run hv I0 (by decide) l1 (by decide) (by decide); intro t1 I1 b4 b5 _
  rw [litImm_target ld0At poolAt (by decide) (by decide), cw_r0] at b4
  apply gAnd_run hv hWc I1 (by decide) q1 (by decide) (by decide); intro t2 I2 _ c4 c5
  apply gLit_run hv I2 (by decide) l2 (by decide) (by decide); intro t3 I3 d4 d5 _
  rw [show ld0At + litSize + seqSize (gAnd 0 5) = ld1At from rfl,
    litImm_target ld1At (poolAt + 4) (by decide) (by decide), cw_r] at d4
  apply gAnd_run hv hWc I3 (by decide) q2 (by decide) (by decide); intro t4 I4 e2 e4 e5
  apply gS_run hv hWc I4 (by decide) q3 (by decide); intro t5 I5 f2 f4
  apply gAnd_run hv hWc I5 (by decide) q4 (by decide) (by decide); intro t6 I6 g2 g4 g5
  apply gS_run hv hWc I6 (by decide) q5 (by decide); intro t7 I7 h2 h4
  apply gAnd_run hv hWc I7 (by decide) q6 (by decide) (by decide); intro t8 I8 i2 i4 i5
  apply gS_run hv hWc I8 (by decide) q7 (by decide); intro t9 I9 _ _
  apply gP_run hv hWc I9 (by decide) q8 (by decide) (by decide); intro t10 I10 _ _ _
  apply gP_run hv hWc I10 (by decide) q9 (by decide) (by decide); intro t11 I11 _ _ _
  apply gP_run hv hWc I11 (by decide) q10 (by decide) (by decide); intro t12 I12 _ _ _
  apply gP_run hv hWc I12 (by decide) q11 (by decide) (by decide); intro t13 I13 _ _ _
  apply gZ_run hv hWc I13 (by decide) q12; intro t14 p14 m14 o14 z1 z2 z3
  apply pop_run hv p14 (by rw [o14 13 (by decide) (by decide) (by decide) (by decide), I13.sp]) m14
    (keys_app I13.keys _ (by simp [zL])) hlr
  intro t15 p15 s15 r4 r5 o15 m15
  apply Reach.done
  refine ⟨p15, s15, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h1 h2 h3 h13 h15
    by_cases h4 : r.val = 4
    · obtain rfl : r = 4 := Fin.ext h4; exact r4
    by_cases h5 : r.val = 5
    · obtain rfl : r = 5 := Fin.ext h5; exact r5
    rw [o15 r h4 h5 h13 h15, o14 r h1 h2 h3 h15]
    by_cases h0 : r.val = 0
    · obtain rfl : r = 0 := Fin.ext h0; rw [I13.r0, he.r0]
    · exact I13.oth r (by omega) h13 h15
  · rw [o15 1 (by decide) (by decide) (by decide) (by decide), z1]
  · rw [o15 2 (by decide) (by decide) (by decide) (by decide), z2]
  · rw [o15 3 (by decide) (by decide) (by decide) (by decide), z3]
  · rw [m15, m14]
    congr 1
    simp only [initL, sfold, i2, h4, g4, f4, e4, d4, g2, e2, b4, List.nil_append, List.cons_append, List.append_assoc]


/-- Context word `j` after `init`: `h = 0`, clamped `r`, `s_j = r_j + (r_j >> 2)`, `pad`. -/
def initW (c : ICtx) (j : Nat) : Word :=
  match j with
  | 5 => c.kw 0 &&& 0x0fffffff#32
  | 6 => c.kw 1 &&& 0x0ffffffc#32
  | 7 => c.kw 2 &&& 0x0ffffffc#32
  | 8 => c.kw 3 &&& 0x0ffffffc#32
  | 9 => sfold (c.kw 1 &&& 0x0ffffffc#32)
  | 10 => sfold (c.kw 2 &&& 0x0ffffffc#32)
  | 11 => sfold (c.kw 3 &&& 0x0ffffffc#32)
  | 12 => c.kw 4
  | 13 => c.kw 5
  | 14 => c.kw 6
  | 15 => c.kw 7
  | _ => 0#32

theorem initL_keys (c : ICtx) : ∀ p ∈ initL c, p.1 < 16 := by
  have e : (initL c).map (·.1) = [5, 6, 9, 7, 10, 8, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4] := rfl
  intro p hp
  have := List.mem_map_of_mem (f := (·.1)) hp
  rw [e] at this; simp at this; omega

theorem initL_words (c : ICtx) (m : Mem) (j : Nat) (hj : j < 16) :
    read32 (wctx c.ctx m (initL c)) (c.ctx + BitVec.ofNat 32 (4 * j)) = initW c j := by
  rw [read32_wctx_slot c.ctx j hj m _ (initL_keys c)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wv, initL, zL, initW]

/-- The bytes `init` may write: the 12 saved-register bytes below SP and the context. -/
def IWr (c : ICtx) (y : Word) : Prop :=
  (∃ o < 12, y = c.sp0 - BitVec.ofNat 32 12 + BitVec.ofNat 32 o) ∨ ∃ o < 64, y = c.ctx + BitVec.ofNat 32 o

/-- State after `init` returns. -/
structure IResult (c : ICtx) (t : State) : Prop where
  pc : t.pc = c.regs0 14 &&& ~~~1#32
  sp : t.regs 13 = c.sp0
  regs : ∀ r : Reg, r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 13 → r.val ≠ 15 → t.regs r = c.regs0 r
  r1 : t.regs 1 = 0#32
  r2 : t.regs 2 = 0#32
  r3 : t.regs 3 = 0#32
  ctx : ∀ j < 16, read32 t.mem (c.ctx + BitVec.ofNat 32 (4 * j)) = initW c j
  frame : ∀ y, ¬ IWr c y → t.mem y = c.m0 y

theorem result_of_reach (c : ICtx) (hv : IValid c) {t : State}
    (h : t.pc = c.regs0 14 &&& ~~~1#32 ∧ t.regs 13 = c.sp0 ∧
      (∀ r : Reg, r.val ≠ 1 → r.val ≠ 2 → r.val ≠ 3 → r.val ≠ 13 → r.val ≠ 15 → t.regs r = c.regs0 r) ∧
      t.regs 1 = 0#32 ∧ t.regs 2 = 0#32 ∧ t.regs 3 = 0#32 ∧ t.mem = wctx c.ctx c.mP (initL c)) : IResult c t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun j hj => by rw [h7]; exact initL_words c _ j hj, fun y hy => ?_⟩
  obtain ⟨c1, _, _⟩ := hv.ctxS
  have hs := toNat_sp12 hv; have := hv.spLo
  have hy1 : ¬ (c.sp0.toNat - 12 ≤ y.toNat ∧ y.toNat < c.sp0.toNat) := by
    rintro ⟨a, b⟩; apply hy; left
    refine ⟨y.toNat - (c.sp0.toNat - 12), by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hy2 : ¬ (c.ctx.toNat ≤ y.toNat ∧ y.toNat < c.ctx.toNat + 64) := by
    rintro ⟨a, b⟩; apply hy; right
    refine ⟨y.toNat - c.ctx.toNat, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [h7, wctx_other _ c1 _ (by omega) _ _ (initL_keys c), mP_other c hv _ (by omega)]

/-- `m0c_poly1305_init` composed inside a larger run (`Wr` contains the 76 bytes). -/
theorem init_reach (c : ICtx) (hv : IValid c) {Wr : Word → Prop} (hW : ∀ y, IWr c y → Wr y)
    (s : State) (he : IEntry c s) (hlr : (c.regs0 14).getLsbD 0 = true) :
    Reach c.base Wr s (IResult c) :=
  (init_run c hv (fun o ho => hW _ (.inl ⟨o, ho, rfl⟩)) (fun o ho => hW _ (.inr ⟨o, ho, rfl⟩)) s he hlr).mono
    (fun _ h => result_of_reach c hv h)

/-- `m0c_poly1305_init`: from an entry state with an odd LR whose target is outside the
Artifacts.Release.size code bytes, the model's `runUntil` returns in an `IResult` state, and every write of the
run lies in `IWr` (12 bytes below SP and the 64-byte context). -/
theorem init_correct (c : ICtx) (hv : IValid c) (s : State) (he : IEntry c s)
    (hlr : (c.regs0 14).getLsbD 0 = true)
    (hret : ∀ i < Artifacts.Release.size, c.regs0 14 &&& ~~~1#32 ≠ c.base + BitVec.ofNat 32 i) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ s' tr, Thumb.runUntil (c.regs0 14 &&& ~~~1#32) fuel s = .ok (s', tr) ∧
      IResult c s' ∧ WritesTo (IWr c) tr := by
  have hc : CodeAt s.mem c.base B := by rw [he.mem]; exact hv.code
  have hs := toNat_sp12 hv
  obtain ⟨n, hn⟩ := Reach.runUntil (P := IResult c) hc
    (fun y hy i hi => by
      rw [B_len] at hi
      rcases hy with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := hv.codeS
        exact ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) (by omega)
      · obtain ⟨h1, h2, h3⟩ := hv.codeC
        exact ne_of_disj (i := o) (j := i) h2 h1 (by omega) (by omega) (by omega))
    (fun i hi => hret i (by rw [B_len] at hi; exact hi))
    ((init_reach c hv (fun _ h => h) s he hlr).mono fun t h => ⟨h.pc, h⟩)
  exact ⟨n, fun fuel hf => by
    obtain ⟨s', tr, hr, hP, hw⟩ := hn fuel hf
    exact ⟨s', tr, hr, hP, hw⟩⟩

end M0Crypto.Release.PolyInit
