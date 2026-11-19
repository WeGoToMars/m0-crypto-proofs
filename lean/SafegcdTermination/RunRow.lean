import SafegcdTermination.BatchLinks
import SafegcdTermination.PublicTrace

namespace SafegcdTermination.RunRow

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.BatchMachine (Slot)
open SafegcdTermination.FoldRefine (value vec)
open SafegcdTermination.CoreRows (exact_output)
open SafegcdTermination.RowCalls
open SafegcdTermination.ModularCalls
open SafegcdTermination.FoldCall
open SafegcdTermination.PublicTrace
open M0Crypto.Armv6M (State read32)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

def rowLit (q : Targets) (o : Nat) (r : RowCall) : BitVec 8 :=
  literalImm (o + seqSize (prepareRow r) + seqSize correctionPrefix) q.literal

def rowPre (q : Targets) (o : Nat) (r : RowCall) : List Instr :=
  if r.modular then prepareRow r ++ prepareCorrection (rowLit q o r) else prepareRow r

def rowSteps (q : Targets) (o : Nat) (r : RowCall) : Nat :=
  (rowPre q o r).length + ((body r.modular).length + 1 + 1) +
    if r.modular then (prepareFold r).length + (FoldCode.body.length + 1 + 1) else 0

private theorem predicted_eq (p : Pins) (pc : Word) (modular : Bool) :
    predictedBody p pc modular = predictedBody ⟨p.out,p.x,p.y,0,0,0,0,0⟩ pc modular := by
  have go (pc : Word) (is : List Nat) : predicted p pc modular is =
      predicted ⟨p.out,p.x,p.y,0,0,0,0,0⟩ pc modular is := by
    induction is generalizing pc with
    | nil => rfl
    | cons i is ih =>
      rw [predicted,predicted,ih]
      rfl
  simp only [predictedBody,go]

def rowTrace (q : Targets) (base sp : Word) (off : Nat) (r : RowCall) : List Event :=
  let pre := rowPre q off r
  let call := off+seqSize pre
  let dest := if r.modular then q.modular else q.exact
  let leaf := base + BitVec.ofNat 32 dest
  let pins : Pins := ⟨addr sp r.dst,addr sp r.x,addr sp r.y,0,0,0,0,0⟩
  let preFold := prepareFold r
  let foldPC := call+4+seqSize preFold
  traceAll pre (stackState (base + BitVec.ofNat 32 off) sp) ++
    (⟨base + BitVec.ofNat 32 call,callTo call dest,[]⟩ ::
      (predictedBody pins leaf r.modular ++ [⟨nextPC leaf (body r.modular),.bx 12,[]⟩])) ++
    if r.modular then
      traceAll preFold (stackState (base + BitVec.ofNat 32 (call+4)) sp) ++
        (⟨base + BitVec.ofNat 32 foldPC,callTo foldPC q.fold,[]⟩ ::
          FoldCode.predictedTrace (base + BitVec.ofNat 32 q.fold) pins.out)
    else []

private theorem correction_public (lit : BitVec 8) : traceChk [15,1,2] (prepareCorrection lit) = true := by
  rfl

private theorem prep_trace {q : Targets} {off : Nat} {r : RowCall} {s t : State}
    (ha : Setup s.sp r) (hb : Setup t.sp r) (hp : s.pc = t.pc) (hSp : s.sp = t.sp) :
    traceAll (rowPre q off r) s = traceAll (rowPre q off r) t := by
  have hPrep := traceAll_sp_congr (prepareRow r) s t ((prepareRow_sp r).mono (fun _ _ => trivial))
    (prepareRow_falls r) hp hSp
  cases h : r.modular
  · simpa only [rowPre,h,Bool.false_eq_true,ite_false] using hPrep
  · let c := prepareCorrection (rowLit q off r)
    have hCorr : traceAll c (execAll (prepareRow r) s) = traceAll c (execAll (prepareRow r) t) := by
      apply trace_chk_sound (regs := [15,1,2]) (by rfl) (correction_public _)
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with e | e | e <;> subst i
      · change (execAll (prepareRow r) s).pc = (execAll (prepareRow r) t).pc
        rw [execAll_pc _ _ (prepareRow_falls r),execAll_pc _ _ (prepareRow_falls r),hp]
      · rw [ha.prepare.2.1,hb.prepare.2.1,hSp]
      · rw [ha.prepare.2.2.1,hb.prepare.2.2.1,hSp]
    simp only [rowPre,h,ite_true,traceAll_append,hPrep,← show c = prepareCorrection (rowLit q off r) from rfl,hCorr]

private theorem fold_trace {r : RowCall} (s : State) :
    traceAll (prepareFold r) s = traceAll (prepareFold r) (stackState s.pc s.sp) := by
  unfold prepareFold
  rfl

def rightValue (r : RowCall) (m : Row) (x y : Int) : Int :=
  if r.modular then fold (rowQuotient (m.apply x y)) else rowQuotient (m.apply x y)

structure LeafLinks (code : List (BitVec 8)) (q : Targets) : Prop where
  mat : seqAt code q.matrix (MatrixCode.body ++ [.bx 14]) = true
  exact : seqAt code q.exact (body false ++ [.bx 12]) = true
  mod : seqAt code q.modular (body true ++ [.bx 12]) = true
  fold : seqAt code q.fold (FoldCode.body ++ [.bx 14]) = true
  even : q.matrix % 2 = 0 ∧ q.exact % 2 = 0 ∧ q.modular % 2 = 0 ∧ q.fold % 2 = 0

private theorem call_size (o d : Nat) : seqSize [callTo o d] = 4 := rfl

theorem core_row {code : List (BitVec 8)} {base : Word} {s : State}
    (q : Targets) (off : Nat) (r : RowCall) (m : Row)
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^23)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (links : LeafLinks code q) (hLink : seqAt code off (rowCode q off r) = true)
    (h : Setup s.sp r) (hn : m.norm ≤ batchScale)
    (hA : stackWord s (matrixAt+4*r.coeff) = BitVec.ofInt 32 m.a)
    (hB : stackWord s (matrixAt+4*(r.coeff+1)) = BitVec.ofInt 32 m.b)
    (hLit : r.modular = true → read32 s.mem (literalAddress (execAll (prepareRow r) s) (rowLit q off r)) = 2587#32)
    (x y : Int) (hx : Slot s.mem s.sp r.x x) (hy : Slot s.mem s.sp r.y y)
    (hrange : r.modular = true → ResidueBounds x ∧ ResidueBounds y)
    (nz : Int) (hexact : r.modular = false → m.apply x y = batchScale * nz)
    (hnz : r.modular = false → -2 * foldRadix ≤ nz ∧ nz < 3 * foldRadix) :
    ∃ t, runH code base (rowSteps q off r) s = .ok (t, rowTrace q base s.sp off r) ∧
      t.pc = base + BitVec.ofNat 32 (off + seqSize (rowCode q off r)) ∧ t.sp = s.sp ∧
      Slot t.mem s.sp r.dst (rightValue r m x y) ∧ WritesOnly s.mem t.mem (addr s.sp r.dst) vectorBytes := by
  have hlen' : code.length < 2^32 := by omega
  have trPre := prep_trace (q := q) (off := off) h
    (show Setup (stackState (base + BitVec.ofNat 32 off) s.sp).sp r from h) hpc rfl
  cases ht : r.modular
  · have hl : seqAt code off (prepareRow r ++ [callTo (off + seqSize (prepareRow r)) q.exact]) = true := by
      simpa only [rowCode, ht, Bool.false_eq_true, ite_false] using hLink
    have hs := (seqAt_size _ _ _ hl).resolve_right (by simp [prepareRow])
    have hs' := (seqAt_size _ _ _ links.exact).resolve_right (by simp [body, prologue])
    rw [seqSize_append, call_size] at hs
    obtain ⟨t, ht', hp, hsp, hv, hw, hmem⟩ :=
      exact_call hb hlen' hpc ho links.even.2.1 (by omega) (by omega) hl links.exact
        h m nz hn hA hB hx.formed hy.formed (by rw [hx.value, hy.value]; exact hexact ht)
    have hR : rightValue r m x y = nz := by
      simp only [rightValue, ht, Bool.false_eq_true, ite_false]
      exact exact_output _ _ _ _ (hexact ht)
    refine ⟨t, ?_, ?_, hsp, ?_, hmem⟩
    · simp only [rowPre,ht,Bool.false_eq_true,ite_false] at trPre
      rw [trPre,predicted_eq] at ht'
      simpa only [rowSteps, rowTrace, rowPre, ht, Bool.false_eq_true, ite_false, Nat.add_zero,
        qAt, List.append_nil] using ht'
    · simpa only [rowCode, ht, Bool.false_eq_true, ite_false, seqSize_append, call_size, Nat.add_assoc] using hp
    · rw [hR]
      exact Slot.of_low hv hw (hnz ht).1 (hnz ht).2
  · let pre := prepareRow r ++ prepareCorrection (rowLit q off r)
    let call := off + seqSize pre
    let moff := call + 4
    let foldPre := prepareFold r
    let foldIns := foldPre ++ [callTo (moff + seqSize foldPre) q.fold]
    have HCode : rowCode q off r = (pre ++ [callTo call q.modular]) ++ foldIns := by
      simp only [rowCode, ht, ite_true, pre, foldIns, foldPre, call, moff, rowLit,
        seqSize_append, Nat.add_assoc, List.append_assoc]
    have hl := hLink
    rw [HCode, seqAt_append, Bool.and_eq_true, seqSize_append, call_size, ← Nat.add_assoc] at hl
    have hl₁ : seqAt code off (pre ++ [callTo call q.modular]) = true := hl.1
    have hl₂ : seqAt code moff foldIns = true := hl.2
    have hs := (seqAt_size _ _ _ hl₁).resolve_right (by simp [pre, prepareRow])
    have hs' := (seqAt_size _ _ _ links.mod).resolve_right (by simp [body, prologue])
    rw [seqSize_append, call_size] at hs
    have hsSmall : off + seqSize (prepareRow r ++ prepareCorrection (rowLit q off r)) + 4 < 2^23 := by
      have hh := Nat.lt_of_le_of_lt hs hlen
      simpa only [pre, Nat.add_assoc] using hh
    obtain ⟨t₁, hh₁, hp, hsp, hv, hw, hmem⟩ :=
      modular_call (rowLit q off r) hb hlen' hpc ho links.even.2.2.1 hsSmall (by omega)
        hl₁ links.mod h m hn hA hB (hLit ht) hx.formed hy.formed
    rw [hx.value, hy.value] at hv
    have he : moff % 2 = 0 := by
      have he' := seqSize_mod_two pre
      change (off + seqSize pre + 4) % 2 = 0
      omega
    have h₂ := (seqAt_size _ _ _ hl₂).resolve_right (by simp [foldIns, foldPre, prepareFold])
    have h₂' := (seqAt_size _ _ _ links.fold).resolve_right (by simp [FoldCode.body, FoldCode.head])
    have hset : Setup t₁.sp r := by rwa [hsp]
    have hw' : Vectors.LowLimbs t₁.mem (addr t₁.sp r.dst) := by rwa [hsp]
    have ⟨ha, hz⟩ := hrange ht
    have hbnd := rowQuotient_range hn ha hz
    have hv' : value t₁.mem (addr t₁.sp r.dst) = rowQuotient (m.apply x y) := by rwa [hsp]
    change moff + seqSize foldIns ≤ code.length at h₂
    rw [show seqSize foldIns = seqSize foldPre + 4 by rw [seqSize_append, call_size]] at h₂
    have hb₂ : moff + seqSize (prepareFold r) + 4 < 2^23 := by
      change moff + seqSize foldPre + 4 < 2^23
      omega
    obtain ⟨t, hh₂, hp₂, hsp₂, hv₂, hw₂, hm₂⟩ :=
      fold_call hb hlen' hp he links.even.2.2.2 hb₂ (by omega) hl₂ links.fold
        hset hw' (by rw [hv']; exact hbnd.1) (by rw [hv']; exact hbnd.2)
    rw [hsp, hv] at hv₂
    rw [hsp] at hw₂ hm₂
    have hPreTr : traceAll pre s = traceAll pre (stackState (base + BitVec.ofNat 32 off) s.sp) := by
      simpa only [rowPre,ht,ite_true] using trPre
    rw [hPreTr,predicted_eq] at hh₁
    rw [fold_trace (r := r) t₁,hp,hsp] at hh₂
    have hr := runH_compose hh₁ hh₂
    refine ⟨t, ?_, ?_, hsp₂.trans hsp, ?_, ?_⟩
    · simpa only [rowTrace, rowSteps, rowPre, ht, ite_true, qAt, pre, call, moff, foldPre,
        Nat.add_zero] using hr
    · simpa only [HCode, foldIns, seqSize_append, call_size, foldPre, moff, call, pre, Nat.add_assoc] using hp₂
    · exact ⟨by simpa only [rightValue, ht, ite_true] using hv₂, hw₂⟩
    · intro a ha
      exact (hm₂ a ha).trans (hmem a ha)

end SafegcdTermination.RunRow
