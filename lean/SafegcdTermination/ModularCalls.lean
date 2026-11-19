import SafegcdTermination.RowCalls

namespace SafegcdTermination.ModularCalls

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.CoreRows
open SafegcdTermination.RowCalls
open SafegcdTermination.RowsRefine
open M0Crypto.Armv6M (State Mem read32 slot)
open M0Crypto.Thumb

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

def corWord (s : State) (r : RowCall) (m : Row) : Word :=
  BitVec.ofInt 32 (correction (m.apply (value s.mem (addr s.sp r.x)) (value s.mem (addr s.sp r.y))))

theorem corWord_nat (s : State) (r : RowCall) (m : Row) :
    (corWord s r m).toNat = (correction (m.apply (value s.mem (addr s.sp r.x))
      (value s.mem (addr s.sp r.y)))).toNat := by
  unfold corWord
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt]
  · exact (correction_bounds _).1
  · have hp := (correction_bounds (m.apply (value s.mem (addr s.sp r.x))
      (value s.mem (addr s.sp r.y)))).2
    change _ < (16384 : Int) at hp
    omega

theorem cor_prepared {s : State} {r : RowCall} (lit : BitVec 8) (hs : Setup s.sp r)
    (m : Row)
    (hA : stackWord s (matrixAt + 4*r.coeff) = BitVec.ofInt 32 m.a)
    (hB : stackWord s (matrixAt + 4*(r.coeff+1)) = BitVec.ofInt 32 m.b)
    (hL : read32 s.mem (literalAddress (execAll (prepareRow r) s) lit) = 2587#32) :
    let t := execAll (prepareRow r ++ prepareCorrection lit) s
    t.regs 0 = addr s.sp r.dst ∧ t.regs 1 = addr s.sp r.x ∧ t.regs 2 = addr s.sp r.y ∧
      t.regs 3 = BitVec.ofInt 32 m.a ∧ t.regs 4 = BitVec.ofInt 32 m.b ∧
      t.regs 5 = corWord s r m ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  let u := execAll (prepareRow r) s
  obtain ⟨ho, hx, hy, ha, hb, hm, hp⟩ := hs.prepare
  obtain ⟨hc, h0, h1, h2, h3, h4, hmem, hsp⟩ := correction_argument u lit
  have hb₁ : read32 s.mem (addr s.sp r.x) = vec s.mem (addr s.sp r.x) 0 := by
    simp [vec, slot]
  have hb₂ : read32 s.mem (addr s.sp r.y) = vec s.mem (addr s.sp r.y) 0 := by
    simp [vec, slot]
  rw [hm, hL, hx, hy, hb₁, hb₂] at hc
  have hC := prepare_correction_word (u.regs 3) (u.regs 4)
    (vec s.mem (addr s.sp r.x) 0) (vec s.mem (addr s.sp r.y) 0) m
    (value s.mem (addr s.sp r.x)) (value s.mem (addr s.sp r.y))
    (ha.trans hA) (hb.trans hB) (Vectors.value_low_correction _ _) (Vectors.value_low_correction _ _)
  rw [execAll_append]
  refine ⟨h0.trans ho, h1.trans hx, h2.trans hy, h3.trans (ha.trans hA), h4.trans (hb.trans hB),
    ?_, hmem.trans hm, hsp.trans hp⟩
  apply BitVec.eq_of_toNat_eq
  rw [hc, corWord_nat]
  simpa only [BitVec.mul_comm (u.regs 3), BitVec.mul_comm (u.regs 4)] using hC

theorem prepareMod_align {s : State} {r : RowCall} (lit : BitVec 8) (hs : Setup s.sp r) :
    alignedAll (prepareRow r ++ prepareCorrection lit) s = true := by
  rw [alignedAll_append, Bool.and_eq_true]
  obtain ⟨_, hx, hy, _⟩ := hs.prepare
  refine ⟨alignedAll_sp _ _ (prepareRow_sp r) hs.frame.1, correction_aligned _ _ ?_ ?_⟩
  · rw [hx]
    exact Bank.aligned hs.frame hs.x
  · rw [hy]
    exact Bank.aligned hs.frame hs.y

theorem prepareMod_falls (r : RowCall) (lit : BitVec 8) :
    (prepareRow r ++ prepareCorrection lit).all Instr.falls = true := by
  simp only [List.all_append, prepareRow_falls]
  rfl

set_option maxRecDepth 12000 in
theorem modular_call {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State} {r : RowCall}
    (lit : BitVec 8) (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (hob : off + seqSize (prepareRow r ++ prepareCorrection lit) + 4 < 2^23) (hdb : dest < 2^23)
    (link : seqAt code off ((prepareRow r ++ prepareCorrection lit) ++
      [callTo (off + seqSize (prepareRow r ++ prepareCorrection lit)) dest]) = true)
    (leaf : seqAt code dest (body true ++ [.bx 12]) = true)
    (hs : Setup s.sp r) (m : Row) (hn : m.norm ≤ batchScale)
    (hA : stackWord s (matrixAt + 4*r.coeff) = BitVec.ofInt 32 m.a)
    (hB : stackWord s (matrixAt + 4*(r.coeff+1)) = BitVec.ofInt 32 m.b)
    (hL : read32 s.mem (literalAddress (execAll (prepareRow r) s) lit) = 2587#32)
    (hx : VecWellFormed (vec s.mem (addr s.sp r.x))) (hy : VecWellFormed (vec s.mem (addr s.sp r.y))) :
    let pre := prepareRow r ++ prepareCorrection lit
    let call := off + seqSize pre
    let q := qAt s.sp r s.mem (BitVec.ofInt 32 m.a) (BitVec.ofInt 32 m.b)
      (corWord s r m) (linkedRet base call)
    ∃ t, runH code base (pre.length + ((body true).length + 1 + 1)) s =
      .ok (t, traceAll pre s ++
        (⟨base + BitVec.ofNat 32 call, callTo call dest, []⟩ ::
          (predictedBody q.pins (base + BitVec.ofNat 32 dest) true ++
           [⟨nextPC (base + BitVec.ofNat 32 dest) (body true), .bx 12, []⟩]))) ∧
      t.pc = base + BitVec.ofNat 32 (call + 4) ∧ t.sp = s.sp ∧
      value t.mem (addr s.sp r.dst) = rowQuotient
        (m.apply (value s.mem (addr s.sp r.x)) (value s.mem (addr s.sp r.y))) ∧
      Vectors.LowLimbs t.mem (addr s.sp r.dst) ∧ WritesOnly s.mem t.mem (addr s.sp r.dst) vectorBytes := by
  let pre := prepareRow r ++ prepareCorrection lit
  let call := off + seqSize pre
  let u := execAll pre s
  let entry := entered base call dest u
  let q := qAt s.sp r s.mem (BitVec.ofInt 32 m.a) (BitVec.ofInt 32 m.b)
    (corWord s r m) (linkedRet base call)
  obtain ⟨h0, h1, h2, h3, h4, h5, hMem, hSp⟩ := cor_prepared lit hs m hA hB hL
  have hq : q = ⟨Pins.load entry true, entry.mem⟩ := by
    dsimp only [q, qAt, Pins.load, entry]
    rw [entered_mem, entered_sp, entered_lr,
      entered_regs _ _ _ _ 0 (by decide) (by decide), entered_regs _ _ _ _ 1 (by decide) (by decide),
      entered_regs _ _ _ _ 2 (by decide) (by decide), entered_regs _ _ _ _ 3 (by decide) (by decide),
      entered_regs _ _ _ _ 4 (by decide) (by decide), entered_regs _ _ _ _ 5 (by decide) (by decide)]
    change _ = (⟨⟨u.regs 0, u.regs 1, u.regs 2, u.regs 3, u.regs 4, u.regs 5,
      linkedRet base call, u.sp⟩, u.mem⟩ : Input)
    rw [h0, h1, h2, h3, h4, h5, hMem, hSp]
  have hc : (q.pins.t.toNat : Int) = correction (rowInput q m) := by
    change ((corWord s r m).toNat : Int) = _
    rw [corWord_nat, Int.toNat_of_nonneg (correction_bounds _).1]
    rfl
  have hpr : entry.pc = base + BitVec.ofNat 32 dest := entered_pc _ _ _ _
  have hret : (entry.regs 14).getLsbD 0 = true := by rw [entered_lr]; exact linkedRet_odd _ _
  obtain ⟨t, ht, hp, hsp, hm, hv, hw, _⟩ :=
    row_at_quotient hb hlen hpr hd leaf hret m q hq (hs.layout ..) (hs.aligned ..)
      hn rfl rfl hx hy hc
  rw [seqAt_append, Bool.and_eq_true] at link
  obtain ⟨hpre, hpc'⟩ := execute_pre hb hlen hpc ho link.1 (prepareMod_falls r lit) (prepareMod_align lit hs)
  have hoe : call % 2 = 0 := by
    have hz := seqSize_mod_two pre
    change (off + seqSize pre) % 2 = 0
    omega
  have hcall := run_call hb hlen hpc' hoe hob hdb link.2 ht
  rw [hpc', hpr] at hcall
  refine ⟨t, runH_compose hpre hcall, hp.trans (linkedRet_clear hb hoe),
    hsp.trans ((entered_sp _ _ _ _).trans hSp), hv, hw, ?_⟩
  intro a ha
  rw [hm]
  exact row_frame q a ha

end SafegcdTermination.ModularCalls
