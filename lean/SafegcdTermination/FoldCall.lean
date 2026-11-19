import SafegcdTermination.RowCalls

namespace SafegcdTermination.FoldCall

open SafegcdRow
open SafegcdRow.BatchCode
open SafegcdTermination.Bank
open SafegcdTermination.FoldRefine (vec value)
open SafegcdTermination.RowCalls
open SafegcdTermination.RowsRefine
open M0Crypto.Armv6M (State)
open M0Crypto.Thumb

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

private theorem fold_prep (r : RowCall) (s : State) (h : InSlot r.dst) :
    let t := execAll (prepareFold r) s
    t.regs 0 = addr s.sp r.dst ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  have hB : frameBytes < 1024 := by decide
  have ho := h.1
  have he := h.2
  unfold prepareFold withSp BatchCode.imm addr
  row_simps
  have hi : r.dst / 4 % 256 * 4 = r.dst := by omega
  rw [hi]

set_option maxRecDepth 15000 in
theorem fold_call {code : List (BitVec 8)} {base : Word} {off dest : Nat} {s : State} {r : RowCall}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0) (hd : dest % 2 = 0)
    (hob : off + seqSize (prepareFold r) + 4 < 2^23) (hdb : dest < 2^23)
    (link : seqAt code off (prepareFold r ++ [callTo (off + seqSize (prepareFold r)) dest]) = true)
    (leaf : seqAt code dest (FoldCode.body ++ [.bx 14]) = true)
    (hs : Setup s.sp r) (hw : Vectors.LowLimbs s.mem (addr s.sp r.dst))
    (hlo : -2 * foldRadix ≤ value s.mem (addr s.sp r.dst)) (hhi : value s.mem (addr s.sp r.dst) < 3 * foldRadix) :
    let call := off + seqSize (prepareFold r)
    ∃ t, runH code base ((prepareFold r).length + (FoldCode.body.length + 1 + 1)) s =
      .ok (t, traceAll (prepareFold r) s ++
        (⟨base + BitVec.ofNat 32 call, callTo call dest, []⟩ ::
          FoldCode.predictedTrace (base + BitVec.ofNat 32 dest) (addr s.sp r.dst))) ∧
      t.pc = base + BitVec.ofNat 32 (call + 4) ∧ t.sp = s.sp ∧
      value t.mem (addr s.sp r.dst) = fold (value s.mem (addr s.sp r.dst)) ∧
      VecWellFormed (vec t.mem (addr s.sp r.dst)) ∧
      WritesOnly s.mem t.mem (addr s.sp r.dst) vectorBytes := by
  let pre := prepareFold r
  let call := off + seqSize pre
  let u := execAll pre s
  let entry := entered base call dest u
  obtain ⟨h0, hm, hsp⟩ := fold_prep r s hs.dst
  have hp : entry.pc = base + BitVec.ofNat 32 dest := entered_pc _ _ _ _
  have hR : (entry.regs 14).getLsbD 0 = true := by rw [entered_lr]; exact linkedRet_odd _ _
  have hA : entry.regs 0 = addr s.sp r.dst :=
    (entered_regs _ _ _ _ 0 (by decide) (by decide)).trans h0
  have hM : entry.mem = s.mem := (entered_mem _ _ _ _).trans hm
  have hsp' : entry.sp = s.sp := (entered_sp _ _ _ _).trans hsp
  have ha : (entry.regs 0).toNat % 4 = 0 := by rw [hA]; exact Bank.aligned hs.frame hs.dst
  have he : call % 2 = 0 := by
    have h := seqSize_mod_two pre
    change (off + seqSize pre) % 2 = 0
    omega
  obtain ⟨t, ht, hm', hs', hpc', hv, hw', _⟩ :=
    fold_at_value hb hlen hp hd leaf ha hR (by simpa only [hM, hA] using hw)
      (by simpa only [hM, hA] using hlo) (by simpa only [hM, hA] using hhi)
  rw [seqAt_append, Bool.and_eq_true] at link
  obtain ⟨hpre, hu⟩ := execute_pre hb hlen hpc ho link.1 (by rfl) (by rfl)
  have hcall := run_call hb hlen hu he hob hdb link.2 ht
  rw [hu, hp, hA] at hcall
  refine ⟨t, runH_compose hpre hcall, ?_, hs'.trans hsp', ?_, ?_, ?_⟩
  · rw [hpc', entered_lr, linkedRet_clear hb he]
  · simpa only [hM, hA] using hv
  · simpa only [hA] using hw'
  · intro a h
    rw [hm', hM, hA]
    exact FoldCode.fold_frame _ _ _ h

end SafegcdTermination.FoldCall
