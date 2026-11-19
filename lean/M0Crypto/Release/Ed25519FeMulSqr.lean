import M0Crypto.Release.Ed25519GeAdd
import M0Crypto.Release.Ed25519FeAddSub
import M0Crypto.Release.Field25519FeMul
import M0Crypto.Release.Field25519FeSqr
import M0Crypto.Release.RoutineBlock
import M0Crypto.Release.SegEffect

/-!
# `m0c_fe_mul` and `m0c_fe_sqr` as routines

Both are `push {lr}`, `sub sp`, a straight-line middle block, `add sp` and `pop {pc}`
(`Field25519FeMul.body`, `Field25519FeSqr.body`). `frame_tspec` proves the call lemma of such a
routine from its body's value lemma (`body_runs`) and the decided checks of the middle block
(`midOk`): its accesses lie in the frame and the pointed fields, and its addresses are the
pointers and `sp` plus constants. `fe_mul_tspec` and `fe_sqr_tspec` apply it in each build, and
`callees_tspec` gives `ge_add_run` in `m0c_ge_mul_base` its callees.
-/

namespace M0Crypto.Release.Ed25519FeMulSqr

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Sym (SExpr alignChkE rgnChk)
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519Routines
open M0Crypto.Release.Field25519Routines (Call Pre feVal mulFrame)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519Macros (SFRAME feMulList feSqrList)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts
open M0Crypto.Release.StackEffect (atomOf addrE_atom EffT effT_of_gp GP frameK_gp sir_segR blkE_seg InR InRD
  above_sub reg_sub_above frameTr)
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)

/-- `sub sp` and `add sp` of the frame. -/
abbrev subF : Instr := .subSp (BitVec.ofNat 7 SFRAME)
abbrev addF : Instr := .addSp (BitVec.ofNat 7 SFRAME)

/-- The pointers read: `r1`, and `r2` when `useB`. -/
def ins (useB : Bool) : List Reg := if useB then [1, 2] else [1]

/-- The atoms of the middle block's addresses: the pointers and `sp`. -/
def atoms (useB : Bool) : List SExpr := (0 :: ins useB ++ [13]).map .reg0

/-- The decided checks of a middle block: it falls through, keeps `sp`, aligns `sp` and the
pointers, writes the frame and `dst`, reads the frame and the inputs, and its addresses are its
atoms plus constants. -/
def midOk (useB : Bool) (mid : List Instr) : Bool :=
  mid.all Instr.falls && keepsSp mid && seqSize mid % 2 == 0 &&
    alignChkE (((13 : Reg) :: 0 :: ins useB).map fun r => (.reg0 r, 4)) mid &&
    rgnChk .write [(.reg0 13, mulFrame - 4), (.reg0 0, 32)] mid &&
    rgnChk .read ((.reg0 13, mulFrame - 4) :: (ins useB).map fun r => (.reg0 r, 32)) mid &&
    traceOkE mid (atoms useB)

/-- `sp` among the public values of a call. -/
def spOf (useB : Bool) (P : Nat → Word) : Word := if useB then P 3 else P 2

/-- The atoms' values in the middle block, from the public values. -/
def vals (useB : Bool) (P : Nat → Word) : List Word :=
  (if useB then [P 0, P 1, P 2] else [P 0, P 1]) ++ [spOf useB P - BitVec.ofNat 32 mulFrame]

/-- The call a field routine entered in `s` makes. -/
def callOf (base : Word) (s : State) : Call := ⟨base, s.regs 13, s.regs 0, s.regs 1, s.regs 2, s.mem, s.regs⟩

theorem pcIn_of_region {base y : Word} {o n : Nat} (h : Region (base + BitVec.ofNat 32 o) n y) :
    PcIn base [(o, o + n)] y := by
  refine ⟨(o, o + n), List.mem_singleton_self _, o + (y - (base + BitVec.ofNat 32 o)).toNat,
    by omega, by simp only [Region] at h; omega, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

theorem sp_sub (x : Word) (a b : Nat) :
    x - BitVec.ofNat 32 a - BitVec.ofNat 32 b = x - BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add]; bv_omega

theorem sp_add (x : Word) (a b : Nat) :
    x - BitVec.ofNat 32 (a + b) + BitVec.ofNat 32 b = x - BitVec.ofNat 32 a := by
  rw [BitVec.ofNat_add]; bv_omega

theorem frame_eq : mulFrame = 4 * nSaved 0 + (BitVec.ofNat 7 SFRAME).toNat * 4 := by decide

theorem nSaved0 : nSaved 0 = 1 := by decide

section

variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- A field routine's entry facts as `Field25519Routines.Pre`. -/
theorem pre_of {o size : Nat} {useB : Bool} {fn : Int → Int → Int} {base : Word} {s : State}
    (e : (fieldR o size mulFrame useB fn).Entry base s) :
    Pre o size mulFrame useB (callOf base s) s := by
  obtain ⟨a0, a1, a2, dA, dB⟩ := e.pre
  exact
    { regs := rfl, mem := rfl, pc := e.pc, sp := rfl, r0 := rfl, r1 := rfl, r2 := (fun _ => rfl),
      thumb := e.lr, retOut := fun h => e.ret (pcIn_of_region h), base4 := e.base4, sp4 := e.sp4,
      spLo := e.room, al := ⟨a0, a1, a2⟩, code := e.code,
      codeS := e.sepCode _ (List.mem_singleton_self _) _ List.mem_cons_self,
      codeD := e.sepCode _ (List.mem_singleton_self _) _ (List.mem_cons_of_mem _ List.mem_cons_self),
      dstS := e.sepWr _ List.mem_cons_self _ (List.mem_singleton_self _),
      aS := e.sepRd ⟨s.regs 1, 32⟩ (by cases useB <;> simp [fieldR]) _ (List.mem_singleton_self _),
      bS := fun h => e.sepRd ⟨s.regs 2, 32⟩ (by subst h; simp [fieldR]) _ (List.mem_singleton_self _),
      dstA := dA, dstB := dB }

/-- The bytes a field routine accesses outside its frame: `dst` and the inputs. -/
def fpX (useB : Bool) : List (SExpr × Nat) := (0 :: ins useB).map fun r => (.reg0 r, 32)

/-- The inputs, read first. -/
def iniX (useB : Bool) : List (SExpr × Nat) := (ins useB).map fun r => (.reg0 r, 32)

/-- The written field. -/
def woX : List (SExpr × Nat) := [(.reg0 0, 32)]

/-- The pointers of a call at the public values `P`. -/
def ptrSt (useB : Bool) (P : Nat → Word) : State :=
  regState 0 (0 :: ins useB) (if useB then [P 0, P 1, P 2] else [P 0, P 1])

theorem wo_fp {useB : Bool} {t : State} {y : Word} (h : InR t woX y) : InR t (fpX useB) y := by
  obtain ⟨x, hx, k, hk, e⟩ := h
  simp only [woX, List.mem_singleton] at hx; subst hx
  exact ⟨_, by cases useB <;> simp [fpX, ins], k, hk, e⟩

/-- **The effect of a field routine**: in its frame, it reads its inputs and writes `dst`. -/
def fieldE (useB : Bool) (base : Word) (P : Nat → Word) : TrP :=
  StackEffect.EffT mulFrame (fun y => Has [codeR base] y ∨ StackEffect.InR (ptrSt useB P) (fpX useB) y)
    (fun y => Has [codeR base] y ∨ StackEffect.InR (ptrSt useB P) (iniX useB) y)
    (StackEffect.InR (ptrSt useB P) woX) (spOf useB P)

/-- An atom's address at the atoms' values. -/
theorem addr_at {pc : Word} {As : List SExpr} {vs : List Word} {e : SExpr} {i : Nat} {v : Word}
    (hl : vs.length = As.length) (ha : atomOf As e = some (i, 0)) (hv : vs[i]? = some v) : addrE pc As vs e = v := by
  obtain ⟨v', h', e'⟩ := addrE_atom (pc := pc) hl ha
  rw [hv] at h'; cases h'; simpa using e'

theorem addr_sp (useB : Bool) (P : Nat → Word) (pc : Word) :
    addrE pc (atoms useB) (vals useB P) (.reg0 13) = spOf useB P - BitVec.ofNat 32 mulFrame := by
  cases useB
  · exact addr_at (i := 2) rfl (by decide) rfl
  · exact addr_at (i := 3) rfl (by decide) rfl

theorem addr_ptr (useB : Bool) (P : Nat → Word) (pc : Word) {r : Reg} (hr : r ∈ 0 :: ins useB) :
    addrE pc (atoms useB) (vals useB P) (.reg0 r) = (SExpr.reg0 r).denote (ptrSt useB P) := by
  cases useB <;> simp only [ins, List.mem_cons, List.not_mem_nil, or_false, ↓reduceIte, Bool.false_eq_true] at hr <;>
    rcases hr with rfl | rfl | rfl <;>
    first
    | exact addr_at (i := 0) rfl (by decide) rfl
    | exact addr_at (i := 1) rfl (by decide) rfl
    | exact addr_at (i := 2) rfl (by decide) rfl

/-- **A field routine `push {lr}; sub sp; mid; add sp; pop {pc}`** whose body computes `fn` into
`dst` and leaves the return address where `push` put it, with its byte effect from the decided
effect of `mid` over its frame and the pointed fields. -/
noncomputable def frame_te {o : Nat} {useB : Bool} {fn : Int → Int → Int} {mid body : List Instr}
    (hbody : body = .push 0 true :: subF :: (mid ++ [addF]))
    (hex : ∀ c s, Pre o (seqSize body + 2) mulFrame useB c s →
      read32 (execAll body s).mem (c.sp0 - 4#32) = c.regs0 14 ∧
        ModP (feVal (execAll body s).mem c.dst) (fn (feVal c.m0 c.a) (feVal c.m0 c.b)))
    (hok : midOk useB mid = true) (hseq : seqAt B o (body ++ [.pop 0 true]) = true)
    (ho : o % 2 = 0)
    (hblk : StackEffect.blkChk (iniX useB) woX ((.reg0 13, mulFrame - 4) :: fpX useB) mid = true) :
    (fieldR o (seqSize body + 2) mulFrame useB fn).TE (fieldPub useB) (fieldE useB) := by
  simp only [midOk, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hf, hk⟩, hev⟩, ha⟩, hw⟩, hr⟩, htr⟩ := hok
  simp only [beq_iff_eq] at hev
  have hsz : seqSize body + 2 = seqSize mid + 8 := by
    rw [hbody]; simp [seqSize, Instr.size]; omega
  rw [hsz] at hex ⊢
  have hs := hseq
  rw [hbody, show (Instr.push 0 true :: subF :: (mid ++ [addF])) ++ [.pop 0 true] =
      [.push 0 true, subF] ++ (mid ++ [addF, .pop 0 true]) by simp, seqAt_append, seqAt_append] at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨hpre, hmid, hpost⟩ := hs
  rw [show seqSize [Instr.push 0 true, subF] = 4 from rfl] at hmid hpost
  simp only [seqAt, Bool.and_eq_true, beq_iff_eq, Instr.size] at hpre hpost
  obtain ⟨⟨h0, -⟩, ⟨h1, -⟩, -⟩ := hpre
  obtain ⟨⟨h3, -⟩, ⟨h4, h4l⟩, -⟩ := hpost
  have hlen : o + (seqSize mid + 8) ≤ BS := by rw [← B_len]; have := of_decide_eq_true h4l; omega
  have hmf := frame_eq
  have hn0 := nSaved0
  have hmf' : mulFrame = 148 := by decide
  have hb0 : bitCount (0 : BitVec 8) = 0 := by decide
  have hsf : (BitVec.ofNat 7 SFRAME).toNat = 36 := by decide
  trefine Routine.te_by (fun base s e => ?_) (fun _ _ => ?_) (fun _ _ => ?_) (fun b P tr h => ?_)
  generalize hP : fieldPub useB base s = P
  have q0 : s.regs 0 = P 0 := by subst hP; cases useB <;> rfl
  have q1 : s.regs 1 = P 1 := by subst hP; cases useB <;> rfl
  have q2 : useB = true → s.regs 2 = P 2 := by subst hP; intro h; subst h; rfl
  have q13 : s.regs 13 = spOf useB P := by subst hP; cases useB <;> rfl
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hent : (fieldR o (seqSize mid + 8) mulFrame useB fn).entry = o := rfl
  have hstk : (fieldR o (seqSize mid + 8) mulFrame useB fn).stack = mulFrame := rfl
  have hroom := e.room
  have hsp4 := e.sp4
  obtain ⟨a0, a1, a2, -, -⟩ := e.pre
  have hsplt := (s.regs 13).isLt
  have hcd := e.sepCode (codeR base) (List.mem_singleton_self _) _ List.mem_cons_self
  obtain ⟨xlr, xv⟩ := hex _ s (pre_of e)
  have hx : execAll body s = addF.next (execAll mid (subF.next ((Instr.push 0 true).next s))) := by
    rw [hbody, execAll, execAll, execAll_append]; rfl
  rw [hx] at xlr xv
  have hwr : ∀ {d j}, d ≤ mulFrame → j < d →
      (fieldR o (seqSize mid + 8) mulFrame useB fn).WrP s (s.regs 13 - BitVec.ofNat 32 d + BitVec.ofNat 32 j) :=
    fun hd hj => ⟨_, List.mem_cons_self, win_has hd hj⟩
  have hrd : ∀ {d j}, d ≤ mulFrame → j < d →
      (fieldR o (seqSize mid + 8) mulFrame useB fn).RdP base s (s.regs 13 - BitVec.ofNat 32 d + BitVec.ofNat 32 j) :=
    fun hd hj => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, win_has hd hj⟩
  have hpc : ∀ {j}, o ≤ j → j < o + (seqSize mid + 8) → PcIn base [(o, o + (seqSize mid + 8))] (base + BitVec.ofNat 32 j) :=
    fun h1 h2 => PcIn.at List.mem_cons_self h1 h2
  -- `push {lr}`
  trefine ReachFT.step (s1 := (Instr.push 0 true).next s) hb2 (.push 0 true) e.pc ho h0
    (by rw [B_len]; simp only [Instr.size]; omega)
    (by simp only [Instr.accesses]
        exact words_aligned _ _ _ (by simp only [State.sp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
    (push_exec s 0) (hpc (Nat.le_refl _) (by omega)) ?_ ?_ ⟨0, Nat.zero_le _, by simp⟩
    (ev := ⟨base + BitVec.ofNat 32 o, .push 0 true,
      wordAccesses .write (spOf useB P - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩)
    (by rw [e.pc, ← q13]; rfl) ?_
  · intro y hy
    simp only [Instr.accesses, State.sp, Bool.toNat_true] at hy
    obtain ⟨j, hj, rfl⟩ := words_writes hy
    exact hwr (by omega) hj
  · intro y hy; simp only [Instr.accesses] at hy; exact absurd hy words_no_reads
  have s1_13 := push_sp (s := s) (l := 0)
  have s1_pc : ((Instr.push 0 true).next s).pc = base + BitVec.ofNat 32 (o + 2) := by
    rw [push_pc]; exact pc_add e.pc
  -- `sub sp`
  generalize ht1 : (Instr.push 0 true).next s = t1 at s1_13 s1_pc xlr xv ⊢
  trefine ReachFT.step (s1 := subF.next t1) hb2 subF s1_pc (by omega) h1
    (by rw [B_len]; simp only [Instr.size]; omega) rfl (subSp_exec t1 _) (hpc (by omega) (by omega))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    ⟨4 * nSaved 0, by omega, s1_13⟩ (ev := ⟨base + BitVec.ofNat 32 (o + 2), subF, []⟩)
    (by rw [s1_pc]; rfl) ?_
  have t2_13 : (subF.next t1).regs 13 = s.regs 13 - BitVec.ofNat 32 mulFrame := by
    rw [subSp_sp, s1_13, sp_sub, hmf]
  have t2_pc : (subF.next t1).pc = base + BitVec.ofNat 32 (o + 4) := by
    rw [subSp_pc]; exact pc_add s1_pc
  have t2_r : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → (subF.next t1).regs r = s.regs r := fun r h13 h15 => by
    rw [subSp_regs _ _ _ (ne13 h13) (ne15 h15), ← ht1, push_regs _ _ _ (ne13 h13) (ne15 h15)]
  have t2_code : CodeAt (subF.next t1).mem base B := by
    rw [subSp_mem, ← ht1, push_mem]
    intro i hi
    rw [storeWords_other _ _ _ _ fun j k hj hk he => ?_]
    · exact e.code i hi
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hj
    have := congrArg BitVec.toNat he
    rw [B_len] at hi
    obtain ⟨d1, d2, d3⟩ := hcd
    simp only [codeR, Routine.win, fieldR, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at this d1 d2 d3
    simp only [show listRegs (0 : BitVec 8) = [] by decide, List.length_nil] at hj
    omega
  generalize ht2 : subF.next t1 = t2 at t2_13 t2_pc t2_r t2_code xlr xv ⊢
  -- the middle block
  have F : Caller base (s.regs 13) mulFrame (Routine.win (fieldR o (seqSize mid + 8) mulFrame useB fn) s ::
      (fieldR o (seqSize mid + 8) mulFrame useB fn).wr s) :=
    ⟨e.base4, e.sp4, e.room, e.sepCode, by have := hcd.1; simp only [codeR] at this; exact this⟩
  trefine ReachFT.sglue F mid (((13 : Reg) :: 0 :: ins useB).map fun r => (.reg0 r, 4))
    [(.reg0 13, mulFrame - 4), (.reg0 0, 32)]
    ((.reg0 13, mulFrame - 4) :: (ins useB).map fun r => (.reg0 r, 32)) hmid t2_pc t2_13 t2_code ?_
    (traceAll_blockTrE (vs := vals useB P) hf htr t2_pc ?_) ?_
    (by simp only [sglueOk, hf, hk, ha, hw, hr, rangesSub, fieldR, List.all_cons, List.all_nil, List.any_cons,
          List.any_nil, Bool.and_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        exact ⟨⟨by omega, by omega, by omega⟩, decide_eq_true (Nat.le_refl _)⟩)
  · have hsW := e.sepWr; have hsR := e.sepRd
    cases useB <;> (try have a2' := a2 rfl) <;>
      simp only [fieldR, Routine.win, hmf', ↓reduceIte, Bool.false_eq_true] at hsW hsR <;>
      fp_simp at hsW hsR <;> glue_tac [ins, fieldR, Routine.win, ↓reduceIte, Bool.false_eq_true, hmf', t2_13,
      t2_r 0 (by decide) (by decide), t2_r 1 (by decide) (by decide), t2_r 2 (by decide) (by decide)]
  · cases useB <;> simp [atoms, ins, vals, spOf, SExpr.denote, t2_13, t2_r 0 (by decide) (by decide),
      t2_r 1 (by decide) (by decide), t2_r 2 (by decide) (by decide), q0, q1, q2, q13]
  intro t3_pc t3_13 _ _
  -- `add sp`
  generalize ht3 : execAll mid t2 = t3 at t3_pc t3_13 xlr xv ⊢
  trefine ReachFT.step (s1 := addF.next t3) hb2 addF t3_pc (by omega) h3
    (by rw [B_len]; simp only [Instr.size]; omega) rfl (addSp_exec t3 _) (hpc (by omega) (by omega))
    (fun y hy => absurd hy (writes_nil y)) (fun y hy => absurd hy (reads_nil y))
    ⟨mulFrame, Nat.le_refl _, t3_13⟩ (ev := ⟨base + BitVec.ofNat 32 (o + 4 + seqSize mid), addF, []⟩)
    (by rw [t3_pc]; rfl) ?_
  have t4_13 : (addF.next t3).regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved 0) := by
    rw [addSp_sp, t3_13, hmf, sp_add]
  have t4_pc : (addF.next t3).pc = base + BitVec.ofNat 32 (o + 4 + seqSize mid + 2) := by
    rw [addSp_pc]; exact pc_add t3_pc
  generalize ht4 : addF.next t3 = t4 at t4_13 t4_pc xlr xv ⊢
  -- `pop {pc}`
  have hlr : read32 t4.mem (t4.regs 13 + BitVec.ofNat 32 (4 * bitCount 0)) = s.regs 14 := by
    rw [t4_13, hn0, show bitCount 0 = 0 by decide]; simpa [callOf] using xlr
  have hva : (t4.regs 13).toNat % 4 = 0 := by
    rw [t4_13]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hn0]; omega
  trefine ReachT.mono (ReachFT.step (s1 := popState t4 0) hb2 (.pop 0 true) t4_pc (by omega) h4
    (by rw [B_len]; simp only [Instr.size]; omega)
    (by simp only [Instr.accesses]; exact words_aligned _ _ _ hva)
    (pop_exec _ _ (by rw [hlr]; exact e.lr)) (hpc (by omega) (by omega))
    (fun y hy => by simp only [Instr.accesses] at hy; exact absurd hy words_no_writes) ?_
    ⟨4 * nSaved 0, by omega, t4_13⟩
    (ev := ⟨base + BitVec.ofNat 32 (o + 4 + seqSize mid + 2), .pop 0 true,
      wordAccesses .read (spOf useB P - BitVec.ofNat 32 (4 * nSaved 0)) (nSaved 0)⟩)
    (by rw [t4_pc]; simp [Instr.accesses, State.sp, t4_13, q13] <;> rfl)
    (ReachT.done ⟨?_, ?_, fun r h4 h11 hK => absurd (mem_hiRegs h4 h11) hK, ?_⟩))
    (fun _ _ h => h) (fun _ h => h) Tr.cat_nil
  · intro y hy
    simp only [Instr.accesses, State.sp, Bool.toNat_true] at hy
    obtain ⟨j, hj, rfl⟩ := words_reads hy
    rw [t4_13]; exact hrd (by omega) hj
  · rw [popState_pc, hlr]
  · rw [popState_sp, t4_13, BitVec.sub_add_cancel]
  · rw [popState_mem]; exact xv
  · uniq_tac
  · simp only [Tr.cat_is_is]; exact ⟨_, rfl⟩
  · -- the effect: the frame around the middle block's decided effect
    have hfr : 4 * nSaved 0 + 4 * SFRAME = mulFrame := by decide
    have hin : ∀ {rs : List (SExpr × Nat)}, (∀ x ∈ rs, ∃ r ∈ 0 :: ins useB, x.1 = .reg0 r) → ∀ y,
        InRD (addrE (b + BitVec.ofNat 32 (o + 4)) (atoms useB) (vals useB P)) rs y → InR (ptrSt useB P) rs y := by
      rintro rs hrs y ⟨x, hx, k, hk, rfl⟩
      obtain ⟨r, hr, hx1⟩ := hrs x hx
      exact ⟨x, hx, k, hk, by rw [hx1, addr_ptr useB P _ hr]⟩
    have hin' : ∀ {rs : List (SExpr × Nat)}, (∀ x ∈ rs, ∃ r ∈ 0 :: ins useB, x.1 = .reg0 r) → ∀ y,
        InR (ptrSt useB P) rs y → InRD (addrE (b + BitVec.ofNat 32 (o + 4)) (atoms useB) (vals useB P)) rs y := by
      rintro rs hrs y ⟨x, hx, k, hk, rfl⟩
      obtain ⟨r, hr, hx1⟩ := hrs x hx
      exact ⟨x, hx, k, hk, by rw [hx1, addr_ptr useB P _ hr]⟩
    have hfpS : ∀ x ∈ fpX useB, ∃ r ∈ 0 :: ins useB, x.1 = .reg0 r := fun x hx => by
      simp only [fpX, List.mem_map] at hx; obtain ⟨r, hr, rfl⟩ := hx; exact ⟨r, hr, rfl⟩
    have hiniS : ∀ x ∈ iniX useB, ∃ r ∈ 0 :: ins useB, x.1 = .reg0 r := fun x hx => by
      simp only [iniX, List.mem_map] at hx; obtain ⟨r, hr, rfl⟩ := hx; exact ⟨r, List.mem_cons_of_mem _ hr, rfl⟩
    have hwoS : ∀ x ∈ woX, ∃ r ∈ 0 :: ins useB, x.1 = .reg0 r := fun x hx => by
      simp only [woX, List.mem_singleton] at hx; subst hx; exact ⟨0, List.mem_cons_self, rfl⟩
    refine effT_of_gp fun sp0 n U hroom hn hF hR => GP.is_of (Φ := frameTr b o (o + 4 + seqSize mid) 0 SFRAME
      (spOf useB P) (Tr.is (blockTrE mid (b + BitVec.ofNat 32 (o + 4)) (atoms useB) (vals useB P))))
      (frameK_gp (U := U) (R2 := fun y => (U y ∨ Region (spOf useB P - BitVec.ofNat 32 (4 * nSaved 0))
        (4 * nSaved 0) y) ∨ InR (ptrSt useB P) woX y ∧ BelowEntry sp0 n y)
        (R' := fun y => U y ∨ InR (ptrSt useB P) woX y ∧ BelowEntry sp0 n y) (by decide) (by rw [hfr]; omega) ?_
        (fun y h => .inl (.inr h))
        (fun y h => h.elim .inl fun h => .inr ⟨hF y (.inr (wo_fp h.1)) h.2, .inr h⟩) (fun y h => .inl (.inl h)))
      (by unfold frameTr; simp only [Tr.cat_is_is, List.append_assoc] at h ⊢; exact h)
    refine sir_segR (fun hA => blkE_seg hblk (fun _ h => h) fun y hy hb => ?_) (fun y hy hb => ?_) fun y h => ?_
    · rw [sub_sub_ofNat, hfr]
      obtain ⟨r, hr, k, hk, rfl⟩ := hy
      rcases List.mem_cons.1 hr with rfl | hr
      · rw [addr_sp]
        refine reg_sub_above (e := mulFrame - 4) ?_ (by omega) (by omega)
        simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp only [BitVec.toNat_ofNat]
        exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk
      · exact above_sub (hF _ (.inr (hin hfpS _ ⟨r, hr, k, hk, rfl⟩)) hb) (by omega)
    · exact .inl (hR y (.inr (hin hiniS y hy)) hb)
    · exact h.imp id fun h => ⟨hin' hwoS y h.1, h.2⟩

end

/-- `m0c_fe_mul` in each build, with its byte effect. -/
noncomputable def fe_mul_te (b : Build) : letI := b.codeBytes
    (fieldR Ed25519Compact.fe_mul (seqSize feMulList) mulFrame true (· * ·)).TE (fieldPub true) (fieldE true) := by
  letI := b.codeBytes
  rw [← Field25519FeMul.body_size]
  exact frame_te (mid := (Field25519FeMul.body.drop 2).dropLast) (by decide +kernel)
    (fun c s hp => ⟨(Field25519FeMul.body_runs c s hp).2.2.1, (Field25519FeMul.body_runs c s hp).2.2.2.1⟩)
    (by decide +kernel)
    (by rw [← Field25519FeMul.split]; cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide) (by decide +kernel)

/-- `m0c_fe_mul` in each build. -/
theorem fe_mul_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => fieldR Ed25519Compact.fe_mul (seqSize feMulList) mulFrame true (· * ·))
      (fieldPub true) :=
  letI := b.codeBytes; ⟨(fe_mul_te b).T, fun _ => (fe_mul_te b).spec⟩

/-- `m0c_fe_sqr` in each build, with its byte effect. -/
noncomputable def fe_sqr_te (b : Build) : letI := b.codeBytes
    (fieldR Ed25519Compact.fe_sqr (seqSize feSqrList) mulFrame false (fun a _ => a * a)).TE (fieldPub false) (fieldE false) := by
  letI := b.codeBytes
  rw [← Field25519FeSqr.body_size]
  exact frame_te (mid := (Field25519FeSqr.body.drop 2).dropLast) (by decide +kernel)
    (fun c s hp => ⟨(Field25519FeSqr.body_runs c s hp).2.2.1, (Field25519FeSqr.body_runs c s hp).2.2.2.1⟩)
    (by decide +kernel)
    (by rw [← Field25519FeSqr.split]; cases b <;> (rw [seqAt_eq_scan]; decide +kernel)) (by decide) (by decide +kernel)

/-- `m0c_fe_sqr` in each build. -/
theorem fe_sqr_tspec (b : Build) : letI := b.codeBytes
    Routine.TSpec (fun _ : Unit => fieldR Ed25519Compact.fe_sqr (seqSize feSqrList) mulFrame false (fun a _ => a * a))
      (fieldPub false) :=
  letI := b.codeBytes; ⟨(fe_sqr_te b).T, fun _ => (fe_sqr_te b).spec⟩

/-- **`ge_add_run`'s callees in `m0c_ge_mul_base`**, in each build. -/
theorem callees_tspec (b : Build) : letI := b.codeBytes
    ∀ op, Routine.TSpec (fun _ : Unit => Ed25519GeAdd.MulBase.callees.R op) (fieldPub true) := by
  intro op
  cases op
  · exact Ed25519FeAddSub.fe_add_tspec b
  · exact Ed25519FeAddSub.fe_sub_tspec b
  · exact fe_mul_tspec b

end M0Crypto.Release.Ed25519FeMulSqr
