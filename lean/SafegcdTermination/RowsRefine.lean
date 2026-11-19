import SafegcdTermination.CoreRows

namespace SafegcdTermination.RowsRefine

open M0Crypto.Armv6M (State)
open M0Crypto.Thumb
open SafegcdRow
open SafegcdTermination.FoldRefine (vec value folded_value)
open SafegcdTermination.Vectors (well_formed_of_range folded_low)
open SafegcdTermination.CoreRows

set_option maxHeartbeats 1800000

theorem row_at_quotient {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State} {modular : Bool}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt code off (body modular ++ [.bx 12]) = true)
    (hret : (s.regs 14).getLsbD 0 = true)
    (r : Row) (q : Input) (hq : q = ⟨Pins.load s modular, s.mem⟩)
    (hl : Layout q.pins) (ha : Aligned q.pins) (hn : r.norm ≤ batchScale)
    (ha' : q.pins.a = BitVec.ofInt 32 r.a) (hb' : q.pins.b = BitVec.ofInt 32 r.b)
    (hx : VecWellFormed (vec q.mem q.pins.x)) (hy : VecWellFormed (vec q.mem q.pins.y))
    (hc : (q.pins.t.toNat : Int) = correction (rowInput q r)) :
    ∃ t, runH code base ((body modular).length + 1) s =
      .ok (t, predictedBody q.pins s.pc modular ++ [⟨nextPC s.pc (body modular), .bx 12, []⟩]) ∧
      t.pc = q.pins.ret &&& ~~~1#32 ∧ t.sp = s.sp ∧ t.mem = outPrefix q 17 ∧
      value t.mem q.pins.out = rowQuotient (rowInput q r) ∧
      Vectors.LowLimbs t.mem q.pins.out ∧ TraceIn q.pins (predictedBody q.pins s.pc modular) := by
  have hargs := row_args q r hn ha' hb' hx hy hc
  subst q
  have heven : s.pc.toNat % 2 = 0 := by
    rw [hpc, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have ent : Entry s.pc s modular := ⟨rfl, heven, hret, hl, ha, hargs⟩
  obtain ⟨t, hr, hT, hSp, hm, hv, hTr⟩ := row_at hb hlen hpc ho hat ent
  refine ⟨t, hr, hT, hSp, hm, quotient_output _ r _ hn ha' hb' hc hv, ?_, hTr⟩
  rw [hm]
  exact result_low_limbs _

theorem fold_at_value {code : List (BitVec 8)} {base : Word} {off : Nat} {s : State}
    (hb : base.toNat % 2 = 0) (hlen : code.length < 2^32)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (ho : off % 2 = 0)
    (hat : seqAt code off (FoldCode.body ++ [.bx 14]) = true)
    (ha : (s.regs 0).toNat % 4 = 0) (hr : (s.regs 14).getLsbD 0 = true)
    (hl : Vectors.LowLimbs s.mem (s.regs 0))
    (hlo : -2 * foldRadix ≤ value s.mem (s.regs 0)) (hhi : value s.mem (s.regs 0) < 3 * foldRadix) :
    let addr := s.regs 0
    ∃ t, runH code base (FoldCode.body.length + 1) s = .ok (t, FoldCode.predictedTrace s.pc addr) ∧
      t.mem = FoldCode.foldedMemory s.mem addr ∧ t.sp = s.sp ∧ t.pc = (s.regs 14 &&& ~~~1#32) ∧
      value t.mem addr = fold (value s.mem addr) ∧ VecWellFormed (vec t.mem addr) ∧
      ResidueBounds (value t.mem addr) := by
  obtain ⟨t, ht, hm, hsp, hret⟩ := FoldCode.run_fold hb hlen hpc ho hat ha hr
  have hw := well_formed_of_range s.mem (s.regs 0) hl hlo hhi
  have hv : value t.mem (s.regs 0) = fold (value s.mem (s.regs 0)) := by
    rw [hm]
    exact folded_value _ _ hw
  have hd := fold_range hlo hhi
  have hf : ResidueBounds (value t.mem (s.regs 0)) := by rwa [hv]
  have hb₁ : -2 * foldRadix ≤ value t.mem (s.regs 0) :=
    Int.le_trans (by decide : -2 * foldRadix ≤ -38) hf.1
  have hb₂ : value t.mem (s.regs 0) < 3 * foldRadix :=
    Int.lt_of_lt_of_le hf.2 (by decide : foldRadix + 38 ≤ 3 * foldRadix)
  refine ⟨t, ht, hm, hsp, hret, hv, well_formed_of_range _ _ ?_ hb₁ hb₂, hf⟩
  rw [hm]
  exact folded_low _ _

end SafegcdTermination.RowsRefine
