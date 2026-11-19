import M0Crypto.Release.Ed25519MulBaseTab
import M0Crypto.Release.Ed25519SignBlocks
import M0Crypto.Release.Ed25519GeCompressProg
import M0Crypto.Release.Ed25519TablesCompact
import M0Crypto.Release.Ed25519TablesFast

/-!
# `m0c_ge_mul_base`'s adapters

The blocks' adapters (`mbD`): `ident` and `nset` store the word `1` into elements of zero bytes,
`mask` and `sub8` leave a register word. The callees' adapters (`mbAd`): `cmov3` is `m0c_cmov`
pinned at 24 words, `copyPt` is `m0c_copy` pinned at 32 words with one point view out. The callee
`mulBaseAd` follows from the program's value `mb_val`.
-/

namespace M0Crypto.Release.Ed25519MulBaseAd

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length bytesAt_congr)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519MulBaseProg
open M0Crypto.Release.Ed25519MulBaseVal
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Ed25519GeCompressProg (dec_fe)
open M0Crypto.Spec.Ed25519 (decodeInt)

/-! ## Word stores -/

/-- A word stored at `r + o'` leaves the `n` bytes at `r + o` that it misses. -/
theorem w32_apart (m : Mem) (r v : Word) {o o' n : Nat} (h : o + n ≤ o' ∨ o' + 4 ≤ o)
    (hb : o + n + o' + 4 < 2 ^ 32) :
    bytesAt (write32 m (r + BitVec.ofNat 32 o') v) (r + BitVec.ofNat 32 o) n = bytesAt m (r + BitVec.ofNat 32 o) n :=
  bytesAt_congr fun i _ => Armv6M.write32_other _ _ _ _ fun k _ => by
    rw [off_add, off_add, Ne, off_eq (by omega) (by omega)]; omega

/-- The word `1` stored at `a`: the 32 bytes there with the low word `1`. -/
theorem w32_one (m : Mem) (a : Word) : bytesAt (write32 m a 1#32) a 32 = setLo (bytesAt m a 32) := by
  have e1 : bytesAt (write32 m a 1#32) a 32 = _ := bytesAt_split _ a 4 28
  have e2 : bytesAt m a 32 = _ := bytesAt_split m a 4 28
  rw [e1, e2, setLo, List.drop_left' (bytesAt_length _ _ 4)]
  congr 1
  · refine Footprint.bytesAt_eq_list rfl fun k hk => ?_
    rw [Frame.byte_of_read32 (write32 m a 1#32) a k hk, Armv6M.read32_write32_same]
    obtain _ | _ | _ | _ | k := k <;> first | decide | omega
  · refine bytesAt_congr fun i hi => Armv6M.write32_other _ _ _ _ fun k hk e => ?_
    have e' : a + BitVec.ofNat 32 (4 + i) = a + BitVec.ofNat 32 k := by rw [← off_add]; exact e
    rw [off_eq (by omega) (by omega)] at e'; omega

theorem ident_mem (t : State) : (execAll identG t).mem =
    write32 (write32 t.mem (t.regs 0 + BitVec.ofNat 32 32) 1#32) (t.regs 0 + BitVec.ofNat 32 64) 1#32 := rfl

theorem nset_mem (t : State) : (execAll nsetG t).mem =
    write32 (write32 t.mem (t.regs 0 + BitVec.ofNat 32 0) 1#32) (t.regs 0 + BitVec.ofNat 32 32) 1#32 := rfl

theorem mask_reg (t : State) : (execAll maskG t).regs 3 = ((t.mem (t.regs 1)).setWidth 32 &&& 1#32) - 1#32 := by
  simp only [maskG, execAll]
  rw [Ed25519Sha512Exec.regs_subImm8 _ _ _ 3 (by decide)]
  simp [Instr.next, Instr.exec, Instr.exec.memOp, MemOp.width, State.setReg, State.reg, State.setNZ,
    M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, read8]

theorem sub8_reg (t : State) : (execAll sub8G t).regs 2 = t.regs 2 - 8#32 := by
  simp [sub8G, execAll, Ed25519Sha512Exec.regs_subImm8 _ _ _ 2 (by decide), M0Crypto.Proofs.toReg_2]

theorem bytesAt_head (m : Mem) (a : Word) (n : Nat) : (bytesAt m a (n + 1)).headD 0 = m a := by
  simp [bytesAt, List.range_succ_eq_map]

/-! ## The blocks' adapters -/

theorem ident_ins : ioIdent.ins = [(0, 0, .view (.bytes 32)), (0, 32, .view (.bytes 32)), (0, 64, .view (.bytes 32)),
    (0, 96, .view (.bytes 32))] := rfl
theorem ident_outs : ioIdent.outs = [(0, 0, .fe), (0, 32, .fe), (0, 64, .fe), (0, 96, .fe)] := rfl
theorem nset_ins : ioNset.ins = [(0, 0, .view (.bytes 32)), (0, 32, .view (.bytes 32)), (0, 64, .view (.bytes 32))] :=
  rfl
theorem nset_outs : ioNset.outs = [(0, 0, .bytes 32), (0, 32, .bytes 32), (0, 64, .bytes 32)] := rfl

/-- **The blocks' adapters.** -/
def mbD (Rs : Rels) : ∀ b, Bd Rs (mbS b)
  | .ident => ⟨identV, fun c sp t vs _ _ _ hi => by
      show OutsRel Rs c sp ioIdent t (execAll identG t).mem ((identV vs).take 4)
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | _⟩⟩⟩⟩ <;>
        simp only [InsRel, All2, mbS, ident_ins, and_true, and_false] at hi
      obtain ⟨hx, hy, hz, hw⟩ := hi
      cases x <;> simp only [Rel, In.kd] at hx <;> cases y <;> simp only [Rel, In.kd] at hy <;>
        cases z <;> simp only [Rel, In.kd] at hz <;> cases w <;> simp only [Rel, In.kd] at hw
      simp only [OutsRel, All2, ident_outs, identV, Rel, List.take_succ_cons, List.take_zero, and_true]
      rw [← dec_fe, ← dec_fe, ← dec_fe, ← dec_fe, ident_mem,
        w32_apart (o := 0) (o' := 64) _ _ _ (by decide) (by decide),
        w32_apart (o := 0) (o' := 32) _ _ _ (by decide) (by decide),
        w32_apart (o := 32) (o' := 64) _ _ _ (by decide) (by decide), w32_one,
        w32_one, w32_apart (o := 64) (o' := 32) _ _ _ (by decide) (by decide),
        w32_apart (o := 96) (o' := 64) _ _ _ (by decide) (by decide),
        w32_apart (o := 96) (o' := 32) _ _ _ (by decide) (by decide), hx, hy, hz, hw]
      exact ⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp [mbS, ioIdent])⟩
  | .nset => ⟨nsetV, fun c sp t vs _ _ _ hi => by
      show OutsRel Rs c sp ioNset t (execAll nsetG t).mem ((nsetV vs).take 3)
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;>
        simp only [InsRel, All2, mbS, nset_ins, and_true, and_false] at hi
      obtain ⟨hx, hy, hz⟩ := hi
      cases x <;> simp only [Rel, In.kd] at hx <;> cases y <;> simp only [Rel, In.kd] at hy <;>
        cases z <;> simp only [Rel, In.kd] at hz
      simp only [OutsRel, All2, nset_outs, nsetV, Rel, List.take_succ_cons, List.take_zero, and_true]
      rw [nset_mem, w32_apart (o := 0) (o' := 32) _ _ _ (by decide) (by decide), w32_one, w32_one,
        w32_apart (o := 32) (o' := 0) _ _ _ (by decide) (by decide), w32_apart (o := 64) (o' := 32) _ _ _ (by decide) (by decide),
        w32_apart (o := 64) (o' := 0) _ _ _ (by decide) (by decide), hx, hy, hz]
      exact ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp [mbS, ioNset])⟩
  | .mask => ⟨maskV, fun _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, mbS, ioMask],
      fun _ _ t vs _ _ _ hi i h => by
        obtain rfl : i = 0 := by simp [mbS, ioMask] at h; omega
        rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, mbS, ioMask, and_true, and_false] at hi
        cases x <;> simp only [Rel, In.kd] at hi
        obtain ⟨rfl, -⟩ := hi
        show some (V.w _) = some (V.w ((execAll maskG t).regs 3))
        rw [mask_reg, BitVec.add_zero, bytesAt_head]⟩
  | .sub8 => ⟨sub8V, fun _ _ _ _ _ _ _ _ => by simp [OutsRel, All2, mbS, ioSub8],
      fun _ _ t vs _ _ _ hi i h => by
        obtain rfl : i = 0 := by simp [mbS, ioSub8] at h; omega
        rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, mbS, ioSub8, and_true, and_false] at hi
        cases x <;> simp only [Rel, In.kd] at hi
        subst hi
        show some (V.w _) = some (V.w ((execAll sub8G t).regs 2))
        rw [sub8_reg, BitVec.add_zero]⟩

theorem mbD_sem (Rs : Rels) : ∀ b, (mbD Rs b).sem = mbBV b
  | .ident | .nset | .mask | .sub8 => rfl

/-! ## `m0c_cmov` of three elements and `m0c_copy` of a point -/

section
open M0Crypto.Release.Ed25519ScReduceProg (dW word_dW)
open M0Crypto.Release.Ed25519WordLoop (sel)
open M0Crypto.Release.Ed25519Words (wsum wsum_congr)
open M0Crypto.Release.Ed25519FePow (inR_of)
open M0Crypto.Release.StackEffect (EffT)
open M0Crypto.Artifacts.Ed25519Compact (cmov copy)
open M0Crypto.Sym (SExpr)

/-- An address lies in its 32-byte element from `a`. -/
theorem elem_in (a y : Word) :
    (y - (a + BitVec.ofNat 32 (32 * ((y - a).toNat / 32)))).toNat < 32 := by
  bv_omega

/-- The bytes `cmov3` reads first: the three elements and the source. -/
def cmovIni : List (SExpr × Nat) := (List.range 3).map (fun j => rgnE 0 (32 * j) 32) ++ [rgnE 1 0 96]

/-- `m0c_cmov` of 24 words, its count pinned. -/
noncomputable def cmov24 (b : Build) := letI := b.codeBytes
  ((Ed25519WordLoop.cmov_te b).pin 2 2 (BitVec.ofNat 32 24) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 96⟩])
    (fun s => [⟨s.regs 0, 96⟩, ⟨s.regs 1, 96⟩]) (fun _ h => by simp [Ed25519WordLoop.wordR, h])
    fun _ h => by simp [Ed25519WordLoop.wordR, h]).code (footprint cmov) (by decide +kernel)

theorem cmov3_eff {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {p : Nat → Word}
    {tr : List Event} (h : Ed25519WordLoop.wloopE true true base (setPub p 2 (BitVec.ofNat 32 24)) tr) :
    (maS .cmov3).Eff p base tr := by
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, true_and] at h
  have r0 : (SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 0 := rfl
  have r1 : (SExpr.reg0 1).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 1 := rfl
  have hf : ∀ y, Region (p 0) 96 y ∨ Region (p 1) 96 y →
      StackEffect.InR (Ed25519Leaf.blkSt [0, 1, 2] 0 p) [(.reg0 0, 96), (.reg0 1, 96)] y := fun y hy => by
    rcases hy with hy | hy
    · exact inR_of List.mem_cons_self (r0 ▸ hy)
    · exact inR_of (List.mem_cons_of_mem _ List.mem_cons_self) (r1 ▸ hy)
  refine Ed25519Leaf.blk_eff (L := [0, 1, 2]) (pc := 0) (fp := [(.reg0 0, 96), (.reg0 1, 96)]) (ini := cmovIni)
    (wo := [(.reg0 0, 96)])
    (EffT.mono h (Nat.le_refl _) (fun y hy => .inr (hf y hy)) (fun y hy => .inr ?_) fun y hy => ?_)
    (by decide +kernel) (by decide) (by decide)
  · rcases hy with hy | hy
    · have hj : (y - p 0).toNat / 32 < 3 := by simp only [Region] at hy; omega
      refine inR_of (List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩)) ?_
      show (y - (p 0 + BitVec.ofNat 32 (32 * ((y - p 0).toNat / 32)))).toNat < 32
      exact elem_in _ _
    · refine inR_of (List.mem_append_right _ List.mem_cons_self) ?_
      show Region (p 1 + BitVec.ofNat 32 0) 96 y
      rw [BitVec.add_zero]; exact hy
  · obtain ⟨r, hr, o, ho, rfl⟩ := hy
    simp only [List.mem_singleton] at hr; subst hr
    exact region_lt ho

/-- Element `e` after `cmov3`: the words of the element and of the source's element `e` under the
mask. -/
theorem cmov_el {m m0 : Mem} {r0 r1 κ : Word}
    (hw : ∀ i < 24, read32 m (r0 + BitVec.ofNat 32 (4 * i)) =
      sel κ (read32 m0 (r0 + BitVec.ofNat 32 (4 * i))) (read32 m0 (r1 + BitVec.ofNat 32 (4 * i))))
    {e : Nat} (he : e < 3) :
    ModP (feVal m (r0 + BitVec.ofNat 32 (32 * e)))
      (selF κ (bytesAt m0 (r0 + BitVec.ofNat 32 (32 * e)) 32) (bytesAt m0 (r1 + BitVec.ofNat 32 (32 * e)) 32)) := by
  have hd : ∀ a, feVal m a = wsum (fun j => (read32 m (a + BitVec.ofNat 32 (4 * j))).toNat) 8 := fun a => by
    rw [← dec_fe]; exact decodeInt_words m a 8
  have hs : wsum (fun j => (read32 m (r0 + BitVec.ofNat 32 (32 * e) + BitVec.ofNat 32 (4 * j))).toNat) 8 =
      wsum (fun j => (sel κ (dW (bytesAt m0 (r0 + BitVec.ofNat 32 (32 * e)) 32) j)
        (dW (bytesAt m0 (r1 + BitVec.ofNat 32 (32 * e)) 32) j)).toNat) 8 := wsum_congr fun j hj => by
    rw [ofNat_add_assoc, show 32 * e + 4 * j = 4 * (8 * e + j) by omega, hw _ (by omega),
      show 4 * (8 * e + j) = 32 * e + 4 * j by omega, ← ofNat_add_assoc, ← ofNat_add_assoc, word_dW m0 _ hj,
      word_dW m0 _ hj]
  unfold ModP selF
  rw [hd, hs]

theorem take_bytes (m : Mem) (a : Word) (n k : Nat) : (bytesAt m a (n + k)).take n = bytesAt m a n := by
  rw [bytesAt_split, List.take_left' (bytesAt_length _ _ _)]

theorem drop_bytes (m : Mem) (a : Word) (o k : Nat) :
    (bytesAt m a (o + k)).drop o = bytesAt m (a + BitVec.ofNat 32 o) k := by
  rw [bytesAt_split, List.drop_left' (bytesAt_length _ _ _)]

theorem cmov3_ins : ioCmov3.ins = [(0, 0, .view (.bytes 32)), (0, 32, .view (.bytes 32)), (0, 64, .view (.bytes 32)),
    (1, 0, .raw (.k 96)), (3, 0, .view .rw)] := rfl
theorem cmov3_outs : ioCmov3.outs = [(0, 0, .fe), (0, 32, .fe), (0, 64, .fe)] := rfl

/-- **`m0c_cmov`'s adapter** over three elements: the word loop pinned at 24 words. -/
noncomputable def cmov3Ad (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (maS .cmov3) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf cmov; decide) (cmov24 b) (fun _ _ _ h => cmov3_eff h) cmov3V
    (fun _ _ _ st _ hg _ _ => by
      have h2 : st.regs 2 = BitVec.ofNat 32 24 := hg.2.2 (2, 24) (by simp [maS, calleeAt, ioCmov3])
      refine ⟨⟨by rw [h2]; unfold Ed25519WordLoop.WordsOk; decide, hg.1 0 (by simp [maS, calleeAt, ioCmov3]),
        fun _ => ⟨hg.1 1 (by simp [maS, calleeAt, ioCmov3]), ?_⟩, trivial⟩, h2⟩
      rw [h2]; exact hg.2.1 (0, 1, 96) (by simp [maS, calleeAt, ioCmov3]))
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, maS, calleeAt, ioCmov3])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, maS, calleeAt, ioCmov3])
    fun _ _ st m _ vs _ hi hp => by
      have hw : ∀ i < 24, read32 m (st.regs 0 + BitVec.ofNat 32 (4 * i)) = sel (st.regs 3)
          (read32 st.mem (st.regs 0 + BitVec.ofNat 32 (4 * i))) (read32 st.mem (st.regs 1 + BitVec.ofNat 32 (4 * i))) :=
        fun i hi => hp.1 i (by rw [hp.2]; exact hi)
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨l, _ | ⟨κ, _ | _⟩⟩⟩⟩⟩ <;>
        simp only [InsRel, All2, maS, calleeAt, cmov3_ins, and_true, and_false] at hi
      obtain ⟨hx, hy, hz, hl, hk⟩ := hi
      cases x <;> simp only [Rel, In.kd] at hx <;> cases y <;> simp only [Rel, In.kd] at hy <;>
        cases z <;> simp only [Rel, In.kd] at hz <;> cases l <;> simp only [Rel, In.kd, ALen.val] at hl <;>
        cases κ <;> simp only [Rel, In.kd] at hk
      simp only [BitVec.add_zero] at hx hl hk
      subst hx hy hz hl hk
      have c0 := cmov_el hw (e := 0) (by decide)
      have c1 := cmov_el hw (e := 1) (by decide)
      have c2 := cmov_el hw (e := 2) (by decide)
      simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero] at c0 c1 c2
      simp only [OutsRel, All2, maS, calleeAt, cmov3_outs, cmov3V, Rel, BitVec.add_zero, and_true]
      rw [(take_bytes st.mem (st.regs 1) 32 64 : (bytesAt st.mem (st.regs 1) 96).take 32 = _),
        (drop_bytes st.mem (st.regs 1) 32 64 : (bytesAt st.mem (st.regs 1) 96).drop 32 = _),
        (take_bytes _ _ 32 32 : (bytesAt st.mem (st.regs 1 + BitVec.ofNat 32 32) 64).take 32 = _),
        (drop_bytes st.mem (st.regs 1) 64 32 : (bytesAt st.mem (st.regs 1) 96).drop 64 = _)]
      exact ⟨c0, c1, c2⟩

/-- A field value's residue is the value modulo `p`. -/
theorem nm_modP (x : Int) : ModP (nm x) x := by
  have hp : Field25519Congr.p ≠ 0 := by decide
  unfold ModP nm
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp), Int.emod_emod]

theorem modP_nm {a x : Int} (h : ModP a x) : ModP a (nm x) := by
  have hp : Field25519Congr.p ≠ 0 := by decide
  unfold ModP nm at *
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp), Int.emod_emod]; exact h

theorem copyPt_eff {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {p : Nat → Word}
    {tr : List Event} (h : Ed25519WordLoop.wloopE false true base (setPub p 2 (BitVec.ofNat 32 32)) tr) :
    (maS .copyPt).Eff p base tr := by
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, true_and, Bool.false_eq_true, false_and, false_or] at h
  have r0 : (SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 0 := rfl
  have r1 : (SExpr.reg0 1).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 1 := rfl
  refine Ed25519Leaf.blk_eff (L := [0, 1, 2]) (pc := 0) (fp := [(.reg0 0, 128), (.reg0 1, 128)])
    (ini := Ed25519WordAd.copyIni 4) (wo := [(.reg0 0, 128)])
    (EffT.mono h (Nat.le_refl _) (fun y hy => .inr ?_) (fun y hy => .inr ?_) fun y hy => ?_) (by decide +kernel)
    (by decide) (by decide)
  · rcases hy with hy | hy
    · exact inR_of List.mem_cons_self (r0 ▸ hy)
    · exact inR_of (List.mem_cons_of_mem _ List.mem_cons_self) (r1 ▸ hy)
  · have hj : (y - p 1).toNat / 32 < 4 := by simp only [Region] at hy; omega
    refine inR_of (List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩) ?_
    show (y - (p 1 + BitVec.ofNat 32 (32 * ((y - p 1).toNat / 32)))).toNat < 32
    exact elem_in _ _
  · obtain ⟨r, hr, o, ho, rfl⟩ := hy
    simp only [List.mem_singleton] at hr; subst hr
    exact region_lt ho

theorem copyPt_ins : ioCopyPt.ins = [(1, 0, .view .fe), (1, 32, .view .fe), (1, 64, .view .fe), (1, 96, .view .fe)] :=
  rfl

/-- **`m0c_copy`'s adapter** for a point: four field elements in, one point view out. -/
noncomputable def copyPtAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (maS .copyPt) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf copy; decide) (Ed25519WordAd.copyN b 4 (by decide))
    (fun _ _ _ h => copyPt_eff h) copyPtV
    (fun _ _ _ st _ hg _ _ => by
      have h2 : st.regs 2 = BitVec.ofNat 32 32 := hg.2.2 (2, 32) (by simp [maS, calleeAt, ioCopyPt])
      refine ⟨⟨by rw [h2]; unfold Ed25519WordLoop.WordsOk; decide, hg.1 0 (by simp [maS, calleeAt, ioCopyPt]),
        fun _ => ⟨hg.1 1 (by simp [maS, calleeAt, ioCopyPt]), ?_⟩, trivial⟩, h2⟩
      rw [h2]; exact hg.2.1 (0, 1, 128) (by simp [maS, calleeAt, ioCopyPt]))
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, maS, calleeAt, ioCopyPt])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, maS, calleeAt, ioCopyPt])
    fun _ _ st m _ vs _ hi hp => by
      have hf : ∀ j < 4, feVal m (st.regs 0 + BitVec.ofNat 32 (32 * j)) =
          feVal st.mem (st.regs 1 + BitVec.ofNat 32 (32 * j)) := fun j hj => by
        unfold feVal; congr 1; apply List.map_congr_left; intro i hi
        have := List.mem_range.mp hi
        rw [Ed25519WordAd.elem_word, Ed25519WordAd.elem_word, hp.1 _ (by rw [hp.2]; show _ < 32; omega)]
      have f0 := hf 0 (by decide)
      have f1 := hf 1 (by decide)
      have f2 := hf 2 (by decide)
      have f3 := hf 3 (by decide)
      simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero] at f0 f1 f2 f3
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨t, _ | _⟩⟩⟩⟩ <;>
        simp only [InsRel, All2, maS, calleeAt, copyPt_ins, and_true, and_false] at hi
      obtain ⟨hx, hy, hz, ht⟩ := hi
      cases x <;> simp only [Rel, In.kd] at hx <;> cases y <;> simp only [Rel, In.kd] at hy <;>
        cases z <;> simp only [Rel, In.kd] at hz <;> cases t <;> simp only [Rel, In.kd] at ht
      simp only [BitVec.add_zero] at hx
      simp only [OutsRel, All2, maS, calleeAt, ioCopyPt, copyPtV, Rel, BitVec.add_zero, and_true]
      rw [f0, f1, f2, f3]
      exact ⟨modP_nm hx, modP_nm hy, modP_nm hz, modP_nm ht⟩

end

/-! ## The callees' adapters -/

/-- **The callees' adapters** in build `b`. -/
noncomputable def mbAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (maS a)
  | .recode => Ed25519RecodeAd.recAd b Rs
  | .zero4 => Ed25519WordAd.zeroAd b Rs 4 Ed25519WordAd.zeroOk_34.2
  | .zero3 => Ed25519WordAd.zeroAd b Rs 3 Ed25519WordAd.zeroOk_34.1
  | .look => Ed25519LookupTE.lookAd b Rs
  | .f .add => Ed25519GeField.addAd b Rs
  | .f .sub => Ed25519GeField.subAd b Rs
  | .f .mul => Ed25519FePow.mulAd b Rs
  | .f .sqr => Ed25519FePow.sqrAd b Rs
  | .cmov3 => cmov3Ad b Rs
  | .copyPt => copyPtAd b Rs

theorem mbAd_sem (b : Build) (Rs : Rels) :
    ∀ a vs, @Ad.sem Rs b.bytes b.size b.codeBytes _ (mbAd b Rs a).ad vs = mbV b.combs a vs
  | .recode, _ | .zero4, _ | .zero3, _ | .look, _ | .f .add, _ | .f .sub, _ | .cmov3, _ | .copyPt, _ => rfl
  | .f .mul, vs => congrArg (· :: []) (Ed25519GeProg.paV_mul vs)
  | .f .sqr, vs => congrArg (· :: []) (Ed25519GeProg.paV_sqr vs)

/-! ## The callee -/

section
open M0Crypto.Artifacts.Ed25519Compact (ed_comb ed_odd_b)
open M0Crypto.Release.Ed25519GeProg (RepV ptR_of)
open M0Crypto.Release.Ed25519Bridge (specRep_scalarMul specRep_B)
open M0Crypto.Release.Ed25519Tables (TablesOk)

theorem tables_ok : ∀ b : Build, TablesOk b
  | .compact => Ed25519TablesCompact.tables_ok
  | .fast => Ed25519TablesFast.tables_ok

/-- **`m0c_ge_mul_base`'s result**: `[k]B` at `out`, with points related by `PtR`. -/
theorem mb_post (b : Build) {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (hB : B = b.bytes) {Rs : Rels} (hpt : Rs.pt = Ed25519GeCompressProg.PtR)
    {semA : MA → List V → List V} (hA : ∀ a vs, semA a vs = mbV b.combs a vs) (c : Ctx) (sp : Word) (st : State)
    (m : Mem) (r0 : Word) (vs : List V) (hi : InsRel Rs c sp (mbQ b.combs).s.io st vs)
    (hp : (mbQ b.combs).post maS mbS Rs semA (fun x => (mbD Rs x).sem) st m r0) :
    OutsRel Rs c sp (mbQ b.combs).s.io st m (semE .mulBase vs) := by
  obtain ⟨-, base, m0, hcode, hm, ho⟩ := hp
  subst hB
  obtain rfl : semA = mbV b.combs := funext fun a => funext (hA a)
  rw [show (fun x => (mbD Rs x).sem) = mbBV from funext (mbD_sem Rs)] at ho
  generalize hcc : (mbQ b.combs).ctx base ((mbQ b.combs).s.pub base st) = cc at ho hm
  dsimp only at ho
  have p1 : cc.ptr 1 = st.regs 1 := by
    rw [← hcc, CalleeP.ctx_ptr (by simp [mbQ])]; exact CalleeP.reg_pub (r := 1) (by simp [mbQ, eaS, calleeAt])
  have p2 : cc.ptr 2 = base + BitVec.ofNat 32 ed_comb := by rw [← hcc]; rfl
  have p3 : cc.ptr 3 = base + BitVec.ofNat 32 ed_odd_b := by rw [← hcc]; rfl
  have hk : kB cc m0 = bytesAt st.mem (st.regs 1) 32 := by
    unfold kB; rw [BitVec.add_zero, ← p1]
    exact bytesAt_congr fun i hi => hm 1 ⟨.k 32, false, true, true⟩ rfl rfl _
      ⟨⟨cc.ptr 1, 32⟩, by simp [XInfo.rgns, XLen.v], ⟨i, hi, rfl⟩⟩
  rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩ <;>
    simp only [InsRel, All2, mbQ, eaS, calleeAt, io1, Rel, In.kd, and_true, and_false] at hi
  rename_i k
  simp only [BitVec.add_zero] at hi
  obtain ⟨rfl, hlt⟩ := hi
  rw [← hk] at hlt
  obtain ⟨x, y, z, t, hev, hrep⟩ := Ed25519MulBaseTab.mb_val b hcode (tables_ok b) p2 p3 hlt
  have hev' : (mbQ b.combs).outVals (Prog.ev maS mbS (mbQ b.combs).geo (mbV b.combs) mbBV cc m0 (mbQ b.combs).P
      (mbQ b.combs).st0 fun _ => .none) = _ := hev
  rw [hev'] at ho
  simp only [OutsRel, All2, mbQ, eaS, calleeAt, io1, Iface.base, Kd.base, Rel, List.map, and_true,
    BitVec.add_zero] at ho
  obtain ⟨hx, hy, hz, ht⟩ := ho
  simp only [semE, OutsRel, All2, mbQ, eaS, calleeAt, io1, Rel, and_true, BitVec.add_zero, hpt]
  rw [hk] at hrep
  refine ptR_of (x := x) (y := y) (z := z) (t := t) ?_ ?_ ?_ ?_ (specRep_scalarMul _ specRep_B) hrep
  · rw [BitVec.add_zero]; exact ModP.trans hx (nm_modP x)
  · exact ModP.trans hy (nm_modP y)
  · exact ModP.trans hz (nm_modP z)
  · exact ModP.trans ht (nm_modP t)

/-- **`m0c_ge_mul_base`'s adapter** in build `b`, at relations whose point relation is `PtR`. -/
noncomputable def mulBaseAd (b : Build) (Rs : Rels) (hpt : Rs.pt = Ed25519GeCompressProg.PtR) :
    AdE Rs (cb := b.codeBytes) (eaS .mulBase) :=
  CalleeP.adE (cb := b.codeBytes) (q := mbQ b.combs) (cE := maS) (bE := mbS) (mbAd b Rs) (mbD Rs)
    (CalleeP.ok_parts (mb_ok b)).choose_spec (mb_code b) (semE .mulBase)
    fun c sp st m r0 vs _ hi hp => letI := b.codeBytes; mb_post b rfl hpt (mbAd_sem b Rs) c sp st m r0 vs hi hp

end

end M0Crypto.Release.Ed25519MulBaseAd
