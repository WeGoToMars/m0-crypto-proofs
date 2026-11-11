import M0Crypto.Release.AeadBody
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame
open M0Crypto.Spec.Aead (pad16)

structure PhasePost (c : ACall) (Wr : Word → Prop) (e : Nat) (ti : Mem)
    (msg : List M0Crypto.Spec.ChaCha20.Byte) (s t : State) : Prop where
  pc : t.pc = c.base + BitVec.ofNat 32 e
  body : Body c Wr t
  inv : PInv c.A ti msg t.mem
  frame : ∀ y, ¬ MacWr c.A y → t.mem y = s.mem y

/-- Loads and one complete padded-message MAC. -/
theorem mac_phase (c : ACall) (hv : AValid c) (Wr : Word → Prop) (off : Nat) (is : List Instr)
    (u v : BitVec 8) (his : is = [.ldrSp 4 u, .ldrSp 5 v])
    (hseq : seqAt B off is = true) (i1 i2 : BitVec 25) (hat : MacAt (off + seqSize is) i1 i2)
    (ho : off % 2 = 0) (hx : off + seqSize is + macSize ≤ Artifacts.Release.size) (s : State) (hp : s.pc = c.base + BitVec.ofNat 32 off)
    (d n : Word) (hd : Disj d n.toNat (c.sp0-320#32) 320)
    (hloadD : read32 s.mem (c.A + BitVec.ofNat 32 (4*u.toNat)) = d)
    (hloadN : read32 s.mem (c.A + BitVec.ofNat 32 (4*v.toNat)) = n)
    (hbody : Body c Wr s) (ti : Mem) (msg : List M0Crypto.Spec.ChaCha20.Byte) (hpi : PInv c.A ti msg s.mem)
    (hw : ∀ y, MacWr c.A y → Wr y) :
    Reach c.base Wr s (PhasePost c Wr (off + seqSize is + macSize) ti
      (msg ++ (Ctx.bytesAt s.mem d n.toNat ++ pad16 (Ctx.bytesAt s.mem d n.toNat))) s) := by
  have hsz : seqSize is = 4 := by subst his; exact loadPair_size u v
  apply Reach.bind
  apply (load_reach c.base c.A d n off is s hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega)
    ho hseq hp hbody.sp u v his hloadD hloadN Wr).mono
  rintro t ⟨tp, t4, t5, tm, tr⟩
  have tb : Body c Wr t := ⟨by rw [tr 13 (by decide) (by decide) (by decide), hbody.sp],
    by rw [tm]; exact hbody.high, by rw [tm]; exact hbody.nonce,
    fun r a b => by rw [tr r (by omega) (by omega) (by omega), hbody.hi r a b],
    fun y hy => by rw [tm]; exact hbody.frame y hy, by rw [tm]; exact hbody.code⟩
  have he := hv.macEnv hd tb.code
  have pi : PInv c.A ti msg t.mem := by rw [tm]; exact hpi
  apply ((mac_padded c.base c.A d n t.mem (off + seqSize is) i1 i2 hat (by omega) hx he t tp tb.sp
    t4 t5 rfl pi.keyOk pi.bound).monoW hw).mono
  intro z hz
  refine ⟨hz.pc, tb.mac he hz hw, ?_, fun y hy => (hz.frame y hy).trans (congrFun tm y)⟩
  have pz := pi.mac he hz
  rw [tm] at pz
  exact pz

def finArgs (dec : Bool) : List Instr := if dec then finD else finE

theorem finArgs_effect (dec : Bool) (s : State) :
    (execAll (finArgs dec) s).regs 0 = s.regs 13 + 8#32 ∧
    (execAll (finArgs dec) s).regs 1 = (if dec then s.regs 13 + 72#32 else read32 s.mem (s.regs 13 + 108#32)) ∧
    (execAll (finArgs dec) s).mem = s.mem ∧
    (∀ r : Reg, 2 ≤ r.val → r.val ≠ 15 → (execAll (finArgs dec) s).regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals cases dec <;> simp [finArgs, finD, finE, execAll, Instr.next, Instr.exec,
    M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1]
  all_goals intro r a b
  all_goals have h0 : r ≠ 0 := by intro e; have := congrArg Fin.val e; omega
  all_goals have h1 : r ≠ 1 := by intro e; have := congrArg Fin.val e; omega
  all_goals have h15 : r ≠ 15 := by intro e; have := congrArg Fin.val e; omega
  all_goals simp [h0, h1, h15]

/-- Finish arguments plus the internal call, for either tag destination. -/
theorem finish_phase (c : ACall) (hv : AValid c) (hb : ABuf c) (dec : Bool) (off : Nat)
    (hseq : seqAt B off (finArgs dec) = true) (i : BitVec 25)
    (hbl : instrAt B (off + seqSize (finArgs dec)) = some (.bl i))
    (ht : blTarget (off + seqSize (finArgs dec)) i = BitVec.ofNat 32 finishOff)
    (ho : off % 2 = 0) (hx : off + seqSize (finArgs dec) + blSize ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base + BitVec.ofNat 32 off) (hs : s.regs 13 = c.A) (hh : Hi c s.mem)
    (hc : CodeAt s.mem c.base B)
    (ic : Poly1305Init.ICtx) (ti : State) (hi : Poly1305Init.IResult ic ti) (hctx : ic.ctx = c.A+8#32)
    (hk : Ctx.bytesAt ic.m0 ic.key 32 = M0Crypto.Spec.Aead.polyKey c.keyB c.nonceB)
    (msg : List M0Crypto.Spec.ChaCha20.Byte) (hpi : PInv c.A ti.mem msg s.mem) :
    Reach c.base (FinishWr c.A (if dec then c.A+72#32 else c.tag)) s
      (FinishPost c (if dec then c.A+72#32 else c.tag) (off + seqSize (finArgs dec)) msg s) := by
  obtain ⟨e0, e1, em, er⟩ := finArgs_effect dec s
  have hfa : seqSize (finArgs dec) = 4 := by cases dec <;> decide
  rw [hs] at e0 e1
  rw [hh.tag] at e1
  apply Reach.block (by have := hv.base4; omega) (finArgs dec) off hp ho hseq
    (by cases dec <;> rfl)
    (alignedAll_sp _ _ (sp_al (by cases dec <;> rfl))
      (by rw [hs, hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega))
    (ChaCha20Block.noWrites _ _ (by cases dec <;> rfl) _)
  generalize hu : execAll (finArgs dec) s = u at e0 e1 em er
  have up : u.pc = c.base + BitVec.ofNat 32 (off + seqSize (finArgs dec)) := by
    rw [← hu, execAll_pc _ _ (by cases dec <;> rfl), hp, ofNat_add_assoc]
  have tagS : Disj (if dec then c.A+72#32 else c.tag) 16 (c.A-20#32) 20 := by
    cases dec
    · exact hv.win hb.tagS 156 20 _ (by rw [hv.sub_toNat 20 (by decide)]; have := hv.A_lo; omega) (by decide)
    · change Disj (c.A+72#32) 16 (c.A-20#32) 20
      have := hv.A_lo; have := hv.A_hi
      rw [Disj, hv.A_off 72 (by decide), hv.sub_toNat 20 (by decide)]
      exact ⟨by omega, by omega, .inr (by omega)⟩
  have codeT : Disj c.base Artifacts.Release.size (if dec then c.A+72#32 else c.tag) 16 := by
    cases dec
    · exact hb.codeT
    · change Disj c.base Artifacts.Release.size (c.A+72#32) 16
      exact hv.win hv.codeS 248 16 _ (by rw [hv.A_off 72 (by decide)]; have := hv.A_lo; omega) (by decide)
  apply (finish_call c hv _ (off + seqSize (finArgs dec)) i hbl ht (by have := hfa; omega) (by omega) u up
    (by rw [er 13 (by decide) (by decide), hs]) e0 e1 (by rw [em]; exact hc)
    codeT tagS ic ti hi hctx hk msg (by rw [em]; exact hpi)).mono
  intro t ht'
  exact ⟨ht'.pc, ht'.sp, fun r a b => (ht'.hi r a b).trans (er r (by omega) (by omega)),
    fun y hy => (ht'.frame y hy).trans (congrFun em y), ht'.tagBytes⟩

/-- High frame words miss the finish writes for either tag destination. -/
theorem finish_not_A (c : ACall) (hv : AValid c) (hb : ABuf c) (dec : Bool) (o : Nat)
    (ho : o < 160) (hr : o < 8 ∨ 104 ≤ o) :
    ¬ FinishWr c.A (if dec then c.A+72#32 else c.tag) (c.A + BitVec.ofNat 32 o) := by
  rintro (⟨q, hq, eq⟩ | ⟨q, hq, eq⟩)
  · have e : c.A - 20#32 + BitVec.ofNat 32 (20+o) = c.A + BitVec.ofNat 32 o := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [← e] at eq
    exact off_ne (c.A-20#32) (by omega) (by omega) (by omega) eq
  · cases dec
    · exact hb.tagA hv o ho (by rw [eq, if_neg (by decide), sub_off _ _ (by omega)]; exact hq)
    · exact off_ne c.A (a := o) (b := 72+q) (by omega) (by omega) (by omega)
        (by simpa only [Bool.true_eq, ite_true, ofNat_add_assoc] using eq)

/-- Shared final erasure and return; the result word was selected before this phase. -/
theorem clear_return (c : ACall) (hv : AValid c) (dec : Bool) (off : Nat)
    (hA : seqAt B off clrA = true) (hL : seqAt B (off + seqSize clrA) clrL = true)
    (hbr : instrAt B (off + seqSize clrA + seqSize clrL) = some (.bcond 1 (brImm8 (off + seqSize clrA + seqSize clrL) (off + seqSize clrA))))
    (hep : seqAt B (off + seqSize clrA + seqSize clrL + brSize) (epilogue dec) = true)
    (hpop : instrAt B (off + seqSize clrA + seqSize clrL + brSize + seqSize (epilogue dec))
      = some (.pop 0xf0 true))
    (ho : off % 2 = 0)
    (hx : off + seqSize clrA + seqSize clrL + brSize + seqSize (epilogue dec) + seqSize [.pop 0xf0 true]
      ≤ Artifacts.Release.size) (s : State)
    (hp : s.pc = c.base+BitVec.ofNat 32 off) (hs : s.regs 13=c.A) (hh : Hi c s.mem)
    (hr : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → s.regs r=c.regs0 r)
    (hlr : (c.regs0 14).getLsbD 0=true) :
    Reach c.base (SWr c.A) s (fun t => RetPost c (if dec then s.regs 4 else 0#32) t ∧
      (∀ o<96, t.mem (c.A+BitVec.ofNat 32 (8+o))=0#8) ∧
      (∀ y, ¬ClearWr c.A y → t.mem y=s.mem y)) := by
  have hA6 := clrA_size
  have hL6 := clrL_size
  have hB := brSize_eq
  have he := epilogue_size dec
  have hP := popSize_eq
  apply Reach.bind
  apply ((clear_reach c.base c.A off hA hL hbr hv.base4
    (by rw [hv.A_toNat]; have := hv.sp8; have := hv.spLo; omega) ho (by omega) s hp hs).monoW (clearWr_swr c.A)).mono
  intro u hu
  have uh : Hi c u.mem := hh.congr (fun o a b => hu.frame _ (by
    rintro ⟨j, hj, eq⟩
    exact off_ne c.A (a := o) (b := 8+j) (by omega) (by omega) (by omega) eq))
  apply (epilogue_reach c hv (SWr c.A) dec (off + seqSize clrA + seqSize clrL + brSize) hep hpop
    (by omega) hx u hu.pc
    (by rw [hu.hi 13 (by decide) (by decide), hs]) uh
    (fun r a b => by rw [hu.hi r (by omega) (by omega), hr r a b]) hlr).mono
  rintro t ⟨ht, tm⟩
  have h4 : u.regs 4=s.regs 4 := hu.hi 4 (by decide) (by decide)
  rw [h4] at ht
  exact ⟨ht, fun o ho => by rw [tm]; exact hu.zero o ho,
    fun y hy => by rw [tm]; exact hu.frame y hy⟩

end M0Crypto.Release.Aead
