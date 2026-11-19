import M0Crypto.Release.StackEffectGP

/-!
# Call programs: frames of two steps

A frame larger than 508 bytes takes two `sub sp` steps: `push {mask, lr}; sub sp, #4k₁;
sub sp, #4k₂`, the body, then `add sp, #4k₁; add sp, #4k₂; pop {mask, pc}` (the generator's
`prologue` and `epilogue`). `ReachFT.frameK2` is `ReachFT.frameK` with the two steps, and
`frameK2_gp` is `frameK_gp` with them.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.StackEffect
open M0Crypto.Release.TraceSpec (AtOrAboveSp BelowEntry)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

/-- **A routine from its frame of two steps.** -/
theorem ReachFT.frameK2 {f : Routine} {mask : BitVec 8} {k1 k2 epi : Nat} {s : State} {sp : Word}
    {Ψ : TrP}
    (hmask : ∀ x ∈ listRegs mask, 4 ≤ x.val)
    (hpush : instrAt B f.entry = some (.push mask true))
    (hsub : instrAt B (f.entry + 2) = some (.subSp (BitVec.ofNat 7 k1)))
    (hsub2 : instrAt B (f.entry + 4) = some (.subSp (BitVec.ofNat 7 k2)))
    (hadd : instrAt B epi = some (.addSp (BitVec.ofNat 7 k1)))
    (hadd2 : instrAt B (epi + 2) = some (.addSp (BitVec.ofNat 7 k2)))
    (hpop : instrAt B (epi + 4) = some (.pop mask true))
    (he2 : f.entry % 2 = 0) (hep2 : epi % 2 = 0) (hepi : epi + 6 ≤ BS)
    (hent : f.entry + 6 ≤ BS)
    (hcode : rangesSub [(f.entry, f.entry + 6), (epi, epi + 6)] f.code = true)
    (hk1 : k1 < 128) (hk2 : k2 < 128) (hst : 4 * nSaved mask + 4 * k1 + 4 * k2 ≤ f.stack)
    (e : f.Entry base s) (hsp : s.regs 13 = sp)
    (body : ∀ t : State,
      t.pc = base + BitVec.ofNat 32 (f.entry + 6) →
      t.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k1 + 4 * k2) →
      (∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t.regs r = s.regs r) →
      MemEq [saved mask s] s.mem t.mem → CodeAt t.mem base B →
      ReachFT base (f.PcP base) (f.RdP base s) (Has (lowWin f mask s :: f.wr s)) (f.SpP s) t
        (fun u => u.pc = base + BitVec.ofNat 32 epi ∧ u.regs 13 = t.regs 13 ∧
          (∀ r : Reg, 4 ≤ r.val → r.val ≤ 11 → ¬ Saves mask r → r ∉ f.clob → u.regs r = s.regs r) ∧
          f.Post s u.mem (u.regs 0)) Ψ) :
    ReachFT base (f.PcP base) (f.RdP base s) (f.WrP s) (f.SpP s) s (f.Ret s)
      (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 f.entry, .push mask true,
          wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (f.entry + 2), .subSp (BitVec.ofNat 7 k1), []⟩])
            (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (f.entry + 4), .subSp (BitVec.ofNat 7 k2), []⟩])
              (Tr.cat Ψ (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 epi, .addSp (BitVec.ofNat 7 k1), []⟩])
                (Tr.is [⟨base + BitVec.ofNat 32 (epi + 2), .addSp (BitVec.ofNat 7 k2), []⟩])))))
          (Tr.is [⟨base + BitVec.ofNat 32 (epi + 4), .pop mask true,
            wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩]))) := by
  refine ReachFT.push_popK (epi := epi + 4) hmask hpush hpop he2 (by omega) (by omega)
    (by omega) (rangesSub_trans (ds := [(f.entry, f.entry + 6), (epi, epi + 6)])
      (by simp [rangesSub]) hcode) (by omega) e hsp ?_
  intro t tpc t13 tr hm hc
  have hb2 : base.toNat % 2 = 0 := by have := e.base4; omega
  have hk7 : (BitVec.ofNat 7 k1).toNat = k1 := by simp; omega
  have hk7' : (BitVec.ofNat 7 k2).toNat = k2 := by simp; omega
  have hroom := e.room
  have hpc : ∀ off, (f.entry ≤ off ∧ off < f.entry + 6) ∨ (epi ≤ off ∧ off < epi + 6) →
      f.PcP base (base + BitVec.ofNat 32 off) := by
    rintro off (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact PcIn.mono hcode (PcIn.at List.mem_cons_self h1 h2)
    · exact PcIn.mono hcode (PcIn.at (List.mem_cons_of_mem _ List.mem_cons_self) h1 h2)
  -- `sub sp, #4k₁`
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = (Instr.subSp (BitVec.ofNat 7 k1)).next t := ⟨_, rfl⟩
  refine ReachFT.step (s1 := t0) hb2 (.subSp (BitVec.ofNat 7 k1)) tpc (by omega) hsub
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [ht0]; exact subSp_exec _ _)
    (hpc _ (Or.inl ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, t13⟩ (by rw [tpc]; rfl) ?_
  have t0_13 : t0.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k1) := by
    rw [ht0, subSp_sp, t13, hk7, sub_sub_ofNat, Nat.mul_comm k1 4]
  have t0_pc : t0.pc = base + BitVec.ofNat 32 (f.entry + 4) := by
    rw [ht0, subSp_pc]; exact pc_add tpc
  -- `sub sp, #4k₂`
  obtain ⟨t1, ht1⟩ : ∃ t1, t1 = (Instr.subSp (BitVec.ofNat 7 k2)).next t0 := ⟨_, rfl⟩
  refine ReachFT.step (s1 := t1) hb2 (.subSp (BitVec.ofNat 7 k2)) t0_pc (by omega) hsub2
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [ht1]; exact subSp_exec _ _)
    (hpc _ (Or.inl ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, t0_13⟩ (by rw [t0_pc]; rfl) ?_
  have t1_13 : t1.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k1 + 4 * k2) := by
    rw [ht1, subSp_sp, t0_13, hk7', sub_sub_ofNat, Nat.mul_comm k2 4]
  have t1_pc : t1.pc = base + BitVec.ofNat 32 (f.entry + 6) := by
    rw [ht1, subSp_pc]; exact pc_add t0_pc
  have t1_r : ∀ r : Reg, r.val ≠ 13 → r.val ≠ 15 → t1.regs r = s.regs r := fun r h13 h15 => by
    rw [ht1, subSp_regs _ _ _ (ne13 h13) (ne15 h15), ht0, subSp_regs _ _ _ (ne13 h13) (ne15 h15), tr r h13 h15]
  have t1_m : t1.mem = t.mem := by rw [ht1, subSp_mem, ht0, subSp_mem]
  refine ReachT.seq (body t1 t1_pc t1_13 t1_r (t1_m ▸ hm) (t1_m ▸ hc)) fun v hv => ?_
  obtain ⟨vpc, v13, vkeep, vpost⟩ := hv
  -- `add sp, #4k₁`
  have hspv : v.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k1 + 4 * k2) := by rw [v13, t1_13]
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = (Instr.addSp (BitVec.ofNat 7 k1)).next v := ⟨_, rfl⟩
  refine ReachFT.step (s1 := v1) hb2 (.addSp (BitVec.ofNat 7 k1)) vpc hep2 hadd
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [hv1]; exact addSp_exec _ _)
    (hpc _ (Or.inr ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, hspv⟩ (by rw [vpc]; rfl) ?_
  have v1_13 : v1.regs 13 = s.regs 13 - BitVec.ofNat 32 (4 * nSaved mask + 4 * k2) := by
    rw [hv1, addSp_sp, hspv, hk7, sub_add_ofNat _ _ _ (by omega)]; congr 2; omega
  have v1_pc : v1.pc = base + BitVec.ofNat 32 (epi + 2) := by rw [hv1, addSp_pc]; exact pc_add vpc
  -- `add sp, #4k₂`
  obtain ⟨v2, hv2⟩ : ∃ v2, v2 = (Instr.addSp (BitVec.ofNat 7 k2)).next v1 := ⟨_, rfl⟩
  refine ReachT.mono (ReachFT.step (s1 := v2) hb2 (.addSp (BitVec.ofNat 7 k2)) v1_pc (by omega) hadd2
    (by rw [B_len]; simp [Instr.size]; omega) rfl (by rw [hv2]; exact addSp_exec _ _)
    (hpc _ (Or.inr ⟨by omega, by omega⟩)) (fun y hy => absurd hy (writes_nil y))
    (fun y hy => absurd hy (reads_nil y)) ⟨_, by omega, v1_13⟩ (by rw [v1_pc]; rfl)
    (ReachT.done ⟨?_, ?_, ?_, ?_⟩)) (fun _ _ h => h) (fun _ h => h) Tr.cat_nil
  · rw [hv2, addSp_pc]; exact pc_add v1_pc
  · rw [hv2, addSp_sp, v1_13, hk7', sub_add_ofNat _ _ _ (by omega), t13]; congr 2; omega
  · intro r h4 h11 hs hK
    rw [hv2, addSp_regs _ _ _ (ne13 (by omega)) (ne15 (by omega)),
      hv1, addSp_regs _ _ _ (ne13 (by omega)) (ne15 (by omega))]
    exact vkeep r h4 h11 hs hK
  · rw [hv2, addSp_regs _ _ _ (by decide) (by decide), addSp_mem, hv1, addSp_regs _ _ _ (by decide) (by decide),
      addSp_mem]
    exact vpost

end

theorem sub2_add (x a b : Word) : x - a - b + a = x - b := by bv_omega

section gp
variable {sp0 : Word} {n : Nat}

/-- **A framed non-entry routine with a frame of two steps** (`frameK_gp`). -/
theorem frameK2_gp {mask : BitVec 8} {k1 k2 : Nat} {sp pc1 pc2 pc2' pc3 pc3' pc4 : Word} {U R2 R' : Word → Prop}
    {Ψ : TrP} (hk1 : k1 < 128) (hk2 : k2 < 128)
    (hroom : (sp0 - sp).toNat + (4 * nSaved mask + 4 * k1 + 4 * k2) < 2 ^ 32)
    (hB : GP sp0 n (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1) - BitVec.ofNat 32 (4 * k2))
      (fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)) Ψ
      (SIR sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1) - BitVec.ofNat 32 (4 * k2)) R2))
    (hS : ∀ y, Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y → R2 y)
    (hR' : ∀ y, R' y → U y ∨ AtOrAboveSp sp0 sp y ∧ R2 y) (hUR : ∀ y, U y → R2 y) :
    GP sp0 n (SIR sp0 sp U)
      (Tr.cat (Tr.is [⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])
        (Tr.cat (Tr.cat (Tr.is [⟨pc2, .subSp (BitVec.ofNat 7 k1), []⟩])
            (Tr.cat (Tr.is [⟨pc2', .subSp (BitVec.ofNat 7 k2), []⟩])
              (Tr.cat Ψ (Tr.cat (Tr.is [⟨pc3, .addSp (BitVec.ofNat 7 k1), []⟩])
                (Tr.is [⟨pc3', .addSp (BitVec.ofNat 7 k2), []⟩])))))
          (Tr.is [⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩])))
      (SIR sp0 sp R') := fun q hq => by
  have hU : ∀ y, U y → AtOrAboveSp sp0 sp y := fun y hy => hq.ab y (hq.r y hy)
  have h4 : 4 * nSaved mask < 2 ^ 32 := by omega
  have r1 : (sp0 - sp).toNat + 4 * nSaved mask < 2 ^ 32 := by omega
  have r2 : (sp0 - (sp - BitVec.ofNat 32 (4 * nSaved mask))).toNat + 4 * k1 < 2 ^ 32 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hroom ⊢; have := sp.isLt; have := sp0.isLt; omega
  have r3 : (sp0 - (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1))).toNat + 4 * k2 < 2 ^ 32 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hroom ⊢; have := sp.isLt; have := sp0.isLt; omega
  have r4 : (sp0 - (sp - BitVec.ofNat 32 (4 * nSaved mask))).toNat + 4 * k2 < 2 ^ 32 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hroom ⊢; have := sp.isLt; have := sp0.isLt; omega
  have a1 : ∀ y, (U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) →
      AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y :=
    fun y hy => hy.elim (fun h => above_sub (hU y h) r1) fun h => reg_sub_above h (Nat.le_refl _) r1
  have hks : (BitVec.ofNat 7 k1).toNat * 4 = 4 * k1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1, Nat.mul_comm]
  have hks' : (BitVec.ofNat 7 k2).toNat * 4 = 4 * k2 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2, Nat.mul_comm]
  have s1 : spAfter (.push mask true) sp = sp - BitVec.ofNat 32 (4 * nSaved mask) := by
    simp only [spAfter, nSaved, Bool.toNat_true]
  have s2 : spAfter (.subSp (BitVec.ofNat 7 k1)) (sp - BitVec.ofNat 32 (4 * nSaved mask)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1) := by simp only [spAfter, hks]
  have s2' : spAfter (.subSp (BitVec.ofNat 7 k2)) (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1) - BitVec.ofNat 32 (4 * k2) := by
    simp only [spAfter, hks']
  have s3 : spAfter (.addSp (BitVec.ofNat 7 k1))
      (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k1) - BitVec.ofNat 32 (4 * k2)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k2) := by
    simp only [spAfter, hks]; exact sub2_add _ _ _
  have s3' : spAfter (.addSp (BitVec.ofNat 7 k2)) (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k2)) =
      sp - BitVec.ofNat 32 (4 * nSaved mask) := by simp only [spAfter, hks', BitVec.sub_add_cancel]
  have s4 : spAfter (.pop mask true) (sp - BitVec.ofNat 32 (4 * nSaved mask)) = sp := by
    show _ + BitVec.ofNat 32 (4 * nSaved mask) = sp; exact BitVec.sub_add_cancel _ _
  have e1 := sir_ev (sp0 := sp0) (n := n) (R := U)
    (e := ⟨pc1, .push mask true, wordAccesses .write (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩) (R' := fun y => U y ∨
      Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y) rfl s1
    (fun y hy => .inr (hy.elim (fun h => absurd h no_reads)
      fun h => reg_sub_above (writes_words h4 h) (Nat.le_refl _) r1)) (fun y h => absurd h no_reads)
    (fun y hy => ⟨a1 y hy, hy.imp_right words_of⟩)
  have e2 := sir_quiet (sp0 := sp0) (n := n) (e := ⟨pc2, .subSp (BitVec.ofNat 7 k1), []⟩) rfl s2 rfl
    (R' := fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)
    fun y hy => ⟨above_sub (a1 y hy) r2, hy⟩
  have e2' := sir_quiet (sp0 := sp0) (n := n) (e := ⟨pc2', .subSp (BitVec.ofNat 7 k2), []⟩) rfl s2' rfl
    (R' := fun y => U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved mask)) (4 * nSaved mask) y)
    fun y hy => ⟨above_sub (above_sub (a1 y hy) r2) r3, hy⟩
  have e3 := sir_quiet (sp0 := sp0) (n := n) (R := R2) (e := ⟨pc3, .addSp (BitVec.ofNat 7 k1), []⟩) rfl s3 rfl
    (R' := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k2)) y ∧ R2 y)
    fun y hy => ⟨hy.1, hy.2⟩
  have e3' := sir_quiet (sp0 := sp0) (n := n) (e := ⟨pc3', .addSp (BitVec.ofNat 7 k2), []⟩) rfl s3' rfl
    (R := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask) - BitVec.ofNat 32 (4 * k2)) y ∧ R2 y)
    (R' := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y ∧ R2 y)
    fun y hy => ⟨hy.1, above_sub hy.1 r4, hy.2⟩
  have e4 := sir_ev (sp0 := sp0) (n := n) (R' := R')
    (R := fun y => AtOrAboveSp sp0 (sp - BitVec.ofNat 32 (4 * nSaved mask)) y ∧ R2 y)
    (e := ⟨pc4, .pop mask true, wordAccesses .read (sp - BitVec.ofNat 32 (4 * nSaved mask)) (nSaved mask)⟩) rfl s4
    (fun y hy => .inl (hy.elim (fun h => reg_sub_above (reads_words h4 h) (Nat.le_refl _) r1)
      fun h => absurd h no_writes))
    (fun y h => ⟨reg_sub_above (reads_words h4 h) (Nat.le_refl _) r1, hS y (reads_words h4 h)⟩)
    fun y hy => (hR' y hy).elim (fun h => ⟨hU y h, .inl ⟨above_sub (hU y h) r1, hUR y h⟩⟩)
      fun h => ⟨h.1, .inl ⟨above_sub h.1 r1, h.2⟩⟩
  exact GP.cat e1 (GP.cat (GP.cat e2 (GP.cat e2' (GP.cat hB (GP.cat e3 e3')))) e4) q hq

end gp

end M0Crypto.Release.Ed25519CallProg
