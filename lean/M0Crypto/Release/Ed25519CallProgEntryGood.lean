import M0Crypto.Release.Ed25519CallProgGood

set_option linter.unusedSimpArgs false

/-!
# Call programs: the byte effect of an entry

Outside the body, an entry's trace keeps an invariant `SIR sp R`: SP at `sp`, the bytes `R`
written, and the written bytes at or above SP. One rule per event (`sir_ev`) covers the pushes of
the saved words, the `sp` steps, the wipe's stores and the pops. From the empty written set at
the entry SP, `entry_good` composes the saves, the frame's `sp` steps, the body (`prog_good`) and
the leave into a `Good` trace.
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
variable {sp0 : Word} {n : Nat}

theorem sv_split {y : Word} (h : Sv sp0 y) :
    Region (sp0 - BitVec.ofNat 32 36) 16 y ∨ Region (sp0 - BitVec.ofNat 32 20) 20 y := by
  simp only [Sv, Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at h ⊢
  have := sp0.isLt; have := y.isLt; omega

theorem top_sv {y : Word} (h : Region (sp0 - BitVec.ofNat 32 20) 20 y) : Sv sp0 y := by
  simp only [Sv, Region, BitVec.toNat_sub, BitVec.toNat_ofNat] at h ⊢
  have := sp0.isLt; have := y.isLt; omega

/-! ## The pieces outside the body -/

theorem spAfter_spI (up : Bool) {k : Nat} (hk : k ≤ 508) (h4 : k % 4 = 0) (sp : Word) :
    spExact (spI up k) = true ∧
      spAfter (spI up k) sp = if up then sp + BitVec.ofNat 32 k else sp - BitVec.ofNat 32 k := by
  have e : (BitVec.ofNat 7 (k / 4)).toNat * 4 = k := by simp; omega
  cases up <;> simp only [spI, spAfter, spExact, e, Bool.false_eq_true, ↓reduceIte, and_self]

/-- `sp` steps down from `d` bytes below `sp0`. -/
theorem sp_down (base : Word) : ∀ (ks : List Nat) (o d : Nat), (∀ k ∈ ks, k ≤ 508 ∧ k % 4 = 0) → 36 ≤ d →
    d + ks.sum < 2 ^ 32 → GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 d) (Sv sp0)) (Tr.is (spTr base false o ks))
      (SIR sp0 (sp0 - BitVec.ofNat 32 (d + ks.sum)) (Sv sp0))
  | [], _, d, _, _, _ => GP.nil fun q h => by simpa using h
  | k :: ks, o, d, hk, h36, hn => by
    obtain ⟨x, e⟩ := spAfter_spI false (hk k List.mem_cons_self).1 (hk k List.mem_cons_self).2 (sp0 - BitVec.ofNat 32 d)
    simp only [Bool.false_eq_true, ↓reduceIte, sub_sub_ofNat] at e
    simp only [List.sum_cons] at hn ⊢
    have h2 := sp_down base ks (o + 2) (d + k) (fun j hj => hk j (List.mem_cons_of_mem _ hj)) (by omega) (by omega)
    rw [Nat.add_assoc] at h2
    exact GP.cons (sir_quiet x e rfl fun y hy => ⟨reg_above hy (Nat.le_refl _) (by omega) (by omega), hy⟩) h2

/-- `sp` steps up to `d - Σ ks` bytes below `sp0`. -/
theorem sp_up (base : Word) : ∀ (ks : List Nat) (o d : Nat), (∀ k ∈ ks, k ≤ 508 ∧ k % 4 = 0) → 36 + ks.sum ≤ d →
    d < 2 ^ 32 → GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 d) (Sv sp0)) (Tr.is (spTr base true o ks))
      (SIR sp0 (sp0 - BitVec.ofNat 32 (d - ks.sum)) (Sv sp0))
  | [], _, d, _, _, _ => GP.nil fun q h => by simpa using h
  | k :: ks, o, d, hk, h36, hn => by
    obtain ⟨x, e⟩ := spAfter_spI true (hk k List.mem_cons_self).1 (hk k List.mem_cons_self).2 (sp0 - BitVec.ofNat 32 d)
    simp only [List.sum_cons] at h36 ⊢
    simp only [↓reduceIte, sp_add (by omega : k ≤ d)] at e
    have h2 := sp_up base ks (o + 2) (d - k) (fun j hj => hk j (List.mem_cons_of_mem _ hj)) (by omega) (by omega)
    rw [show d - k - ks.sum = d - (k + ks.sum) by omega] at h2
    exact GP.cons (sir_quiet x e rfl fun y hy => ⟨reg_above hy (Nat.le_refl _) (by omega) (by omega), hy⟩) h2

theorem quiet_sir_tr (base sp : Word) {R : Word → Prop} (hR : ∀ y, R y → AtOrAboveSp sp0 sp y) :
    ∀ (is : List Instr) (o : Nat), (∀ i ∈ is, spExact i = true ∧ spAfter i sp = sp) →
    GP sp0 n (SIR sp0 sp R) (Tr.is (quietTr base o is)) (SIR sp0 sp R)
  | [], _, _ => GP.nil fun _ h => h
  | i :: is, _, h => GP.cons (sir_quiet (h i List.mem_cons_self).1 (h i List.mem_cons_self).2 rfl
      fun y hy => ⟨hR y hy, hy⟩) (quiet_sir_tr base sp hR is _ fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The saves of `abi_enter`, as instructions and accesses. -/
def saveEv (sp0 : Word) : List Event :=
  [ev (.push 0xf0 true) (wordAccesses .write (sp0 - BitVec.ofNat 32 20) 5), ev (.movHi 4 8) [], ev (.movHi 5 9) [],
   ev (.movHi 6 10) [], ev (.movHi 7 11) [], ev (.push 0xf0 false) (wordAccesses .write (sp0 - BitVec.ofNat 32 36) 4)]

theorem save_ia (pc sp0 : Word) : (blockTr saveHi pc [13] [sp0]).map ia = (saveEv sp0).map ia := by
  simp [blockTr, traceAll, saveHi, ia, saveEv, ev, Instr.accesses, Instr.next, Instr.exec, regState, List.lookup,
    lr_f0, State.sp, State.setReg]
  congr 1; bv_omega

/-- The restores of `abi_leave` before its last `pop`. -/
def restEv (sp0 : Word) : List Event :=
  [ev (.movImm 1 0) [], ev (.movHi 12 1) [], ev (.pop 0xf0 false) (wordAccesses .read (sp0 - BitVec.ofNat 32 36) 4),
   ev (.movHi 8 4) [], ev (.movHi 9 5) [], ev (.movHi 10 6) [], ev (.movHi 11 7) []]

theorem rest_ia (pc sp0 : Word) : (blockTr restoreHi pc [13] [sp0 - 36#32]).map ia = (restEv sp0).map ia := by
  simp [blockTr, traceAll, restoreHi, ia, restEv, ev, Instr.accesses, Instr.next, Instr.exec, regState, List.lookup,
    lr_f0, lr1, State.sp, State.setReg]

theorem wipe_ia (pc a : Word) :
    (blockTr wipeBody pc [0] [a]).map ia = [ev (.stm 0 6) (wordAccesses .write a 2), ev (.subImm8 3 1) []].map ia := by
  simp [blockTr, traceAll, wipeBody, ia, ev, Instr.accesses, Instr.next, Instr.exec, regState, List.lookup, lr_06, lr0,
    State.setReg, State.reg, show bitCount 6#8 = 2 by decide]

theorem save_gp (pc : Word) :
    GP sp0 n (SIR sp0 sp0 fun _ => False) (Tr.is (blockTr saveHi pc [13] [sp0])) (SIR sp0 (sp0 - BitVec.ofNat 32 36) (Sv sp0)) := by
  have q : ∀ i, spExact i = true → spAfter i (sp0 - BitVec.ofNat 32 20) = sp0 - BitVec.ofNat 32 20 →
      GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 20) (Region (sp0 - BitVec.ofNat 32 20) 20)) (Tr.is [ev i []])
        (SIR sp0 (sp0 - BitVec.ofNat 32 20) (Region (sp0 - BitVec.ofNat 32 20) 20)) := fun i hx hs =>
    sir_quiet hx hs rfl fun y hy => ⟨reg_above hy (by omega) (by omega) (by omega), hy⟩
  refine GP.ia (save_ia pc sp0) (GP.cons (sir_ev rfl (by show sp0 - BitVec.ofNat 32 (4 * (bitCount 0xf0#8 + true.toNat)) = _; rfl) (fun y h => .inr ?_)
    (fun y h => absurd h no_reads) fun y hy => ⟨reg_above hy (by omega) (by omega) (by omega), .inr (words_of hy)⟩)
    (GP.cons (q _ rfl rfl) (GP.cons (q _ rfl rfl) (GP.cons (q _ rfl rfl) (GP.cons (q _ rfl rfl) (GP.cons (sir_ev rfl (by
      show sp0 - BitVec.ofNat 32 20 - BitVec.ofNat 32 (4 * (bitCount 0xf0#8 + false.toNat)) = _
      rw [sub_sub_ofNat]; rfl) (fun y h => .inr ?_)
      (fun y h => absurd h no_reads) fun y hy => ⟨reg_above hy (by omega) (by omega) (by omega), ?_⟩)
      (GP.nil fun _ h => h)))))))
  · exact reg_above (h.elim (absurd · no_reads) (writes_words (by omega))) (by omega) (by omega) (by omega)
  · exact reg_above (h.elim (absurd · no_reads) (writes_words (by omega))) (by omega) (by omega) (by omega)
  · exact (sv_split hy).elim (.inr ∘ words_of (k := 4)) .inl

theorem rest_gp (pc : Word) :
    GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 36) (Sv sp0)) (Tr.is (blockTr restoreHi pc [13] [sp0 - 36#32]))
      (SIR sp0 (sp0 - BitVec.ofNat 32 20) (Region (sp0 - BitVec.ofNat 32 20) 20)) := by
  have q : ∀ (d : Nat) (R : Word → Prop), (∀ y, R y → AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 d) y) → ∀ i,
      spExact i = true → spAfter i (sp0 - BitVec.ofNat 32 d) = sp0 - BitVec.ofNat 32 d →
      GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 d) R) (Tr.is [ev i []]) (SIR sp0 (sp0 - BitVec.ofNat 32 d) R) :=
    fun d R hR i hx hs => sir_quiet hx hs rfl fun y hy => ⟨hR y hy, hy⟩
  have a36 : ∀ y, Sv sp0 y → AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 36) y :=
    fun y hy => reg_above hy (by omega) (by omega) (by omega)
  have a20 : ∀ y, Region (sp0 - BitVec.ofNat 32 20) 20 y → AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 20) y :=
    fun y hy => reg_above hy (by omega) (by omega) (by omega)
  refine GP.ia (rest_ia pc sp0) (GP.cons (q _ _ a36 _ rfl rfl) (GP.cons (q _ _ a36 _ rfl rfl) (GP.cons (sir_ev rfl
    (by show sp0 - BitVec.ofNat 32 36 + BitVec.ofNat 32 16 = _; exact sp_add (by omega)) (fun y h => .inl (reg_above (h.elim (reads_words (by omega))
      (absurd · no_writes)) (by omega) (by omega) (by omega)))
    (fun y h => Nat.lt_of_lt_of_le (reads_words (k := 4) (by omega) h) (by omega))
    fun y hy => ⟨a20 y hy, .inl (top_sv hy)⟩) ?_)))
  exact GP.cons (q _ _ a20 _ rfl rfl) (GP.cons (q _ _ a20 _ rfl rfl) (GP.cons (q _ _ a20 _ rfl rfl)
    (GP.cons (q _ _ a20 _ rfl rfl) (GP.nil fun _ h => h))))

/-- One pass of the wipe, `d` bytes above the bottom of the `D`-byte window. -/
theorem wipe_gp {D d : Nat} (pb : Word) (imm : BitVec 8) (hd : d + 8 ≤ D) (h36 : 36 ≤ D) (hD : D < 2 ^ 32) :
    GP sp0 n (SIR sp0 (sp0 - BitVec.ofNat 32 D) (Sv sp0))
      (wipeTr pb (sp0 - BitVec.ofNat 32 D + BitVec.ofNat 32 d) imm) (SIR sp0 (sp0 - BitVec.ofNat 32 D) (Sv sp0)) := by
  have hq : ∀ y, Sv sp0 y → AtOrAboveSp sp0 (sp0 - BitVec.ofNat 32 D) y ∧ Sv sp0 y :=
    fun y hy => ⟨reg_above hy (by omega) h36 hD, hy⟩
  exact GP.cat (GP.ia (wipe_ia _ _) (GP.cons (sir_ev rfl rfl
    (fun y h => .inl (reg_above2 (h.elim (absurd · no_reads) (writes_words (by omega))) hd hD))
    (fun y h => absurd h no_reads) fun y hy => ⟨(hq y hy).1, .inl hy⟩)
    (GP.cons (sir_quiet rfl rfl rfl hq) (GP.nil fun _ h => h)))) (GP.cons (sir_quiet rfl rfl rfl hq) (GP.nil fun _ h => h))

end

/-! ## The entry -/

section
variable {A Bk : Type} {cE : A → CalleeS} {bE : Bk → BlockS} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]
  {T : A → Word → (Nat → Word) → List Event} {c : Ctx} {G : Geo} {Wc Rc : List Rgn} {sp0 : Word}

theorem chunks_ok {m : Nat} (h : m % 4 = 0) : ∀ k ∈ chunks m m, k ≤ 508 ∧ k % 4 = 0 :=
  fun k hk => ⟨(chunks_le _ _ k hk).1, chunks_four _ _ h k hk⟩

/-- **An entry with a given body has a good trace**: the enter, the body's trace `Ψ`, which keeps
the frame's invariant from the program state `st0` to the leave, and the leave. -/
theorem entry_goodB (hsp : c.sp0 = sp0 - 36#32) {bsz : Nat} {Ψ : TrP} {st0 : St}
    {oE : Nat} (hok : entryOkB G bsz oE = true) (hΓ : st0.Γ = [])
    (hb : GP sp0 (36 + G.N) (BI c G sp0 (36 + G.N) (Sv sp0) st0) Ψ (SIR sp0 (G.fsp c) (Sv sp0))) :
    ∀ tr, entryTrB G c sp0 oE bsz Ψ tr → Good sp0 (36 + G.N) ⟨sp0, fun _ => False⟩ tr := by
  simp only [entryOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, ht4⟩, hN8⟩, htN⟩, hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hw4 : (G.N - G.top) % 4 = 0 := by omega
  have sT := chunks_sum G.top G.top (by omega); have sW := chunks_sum (G.N - G.top) (G.N - G.top) (by omega)
  have hf : G.fsp c = sp0 - BitVec.ofNat 32 (36 + G.top) := by rw [Geo.fsp, hsp, ad_sub36]
  have d1 := sp_down (n := 36 + G.N) (sp0 := sp0) c.base _ (oE + 12) 36 (chunks_ok ht4) (by omega) (by omega)
  have d2 := sp_down (n := 36 + G.N) (sp0 := sp0) c.base (chunks (G.N - G.top) (G.N - G.top))
    (bodyAt G oE + bsz) (36 + G.top) (chunks_ok hw4) (by omega) (by omega)
  have u1 := sp_up (n := 36 + G.N) (sp0 := sp0) c.base (chunks (G.N - G.top) (G.N - G.top) ++ chunks G.top G.top)
    (bodyAt G oE + bsz + 2 * (chunks (G.N - G.top) (G.N - G.top)).length + 10 + 8)
    (36 + G.top + (G.N - G.top)) (fun k hk => (List.mem_append.mp hk).elim (chunks_ok hw4 k) (chunks_ok ht4 k))
    (by simp only [List.sum_append]; omega) (by omega)
  rw [sT] at d1; rw [sW] at d2
  rw [show 36 + G.top + (G.N - G.top) - (chunks (G.N - G.top) (G.N - G.top) ++ chunks G.top G.top).sum = 36 by
    simp only [List.sum_append]; omega] at u1
  have pop : GP sp0 (36 + G.N) (SIR sp0 (sp0 - BitVec.ofNat 32 20) (Region (sp0 - BitVec.ofNat 32 20) 20))
      (Tr.is [⟨c.base + BitVec.ofNat 32 (bodyAt G oE + bsz + 2 * (chunks (G.N - G.top) (G.N - G.top)).length
        + 10 + 8 + 2 * ((chunks (G.N - G.top) (G.N - G.top)).length + (chunks G.top G.top).length) + 14),
        .pop 0xf0 true, wordAccesses .read (sp0 - 20#32) 5⟩]) (fun _ => True) :=
    fun q hq tr htr => ⟨(sir_ev (R' := fun _ => False) rfl rfl (fun y h => .inl (reg_above (h.elim
      (reads_words (by omega)) (absurd · no_writes)) (by omega) (by omega) (by omega))) (fun y h => reads_words (k := 5)
      (by omega) h) nofun q hq tr htr).1, trivial⟩
  have hL : GP sp0 (36 + G.N) (SIR sp0 (G.fsp c) (Sv sp0))
      (leaveTr c.base sp0 G.top (G.N - G.top) (bodyAt G oE + bsz) (Tr.is [])) (fun _ => True) := by
    refine GP.pre (fun q h => ⟨h.hs.trans hf, h.r, fun y hy => hf ▸ h.ab y hy⟩) (GP.cat d2 (GP.cat
      (quiet_sir_tr _ _ (fun y hy => reg_above hy (by omega) (by omega) (by omega)) _ _
      (by simp [wipeSet, spExact, Instr.dsts, spAfter]; decide)) (GP.rep ?_ _ 0 fun j hj => wipe_gp _ _ (by omega) (by omega)
      (by omega))))
    exact GP.cat (quiet_sir_tr _ _ (fun y hy => reg_above hy (by omega) (by omega) (by omega)) _ _
      (by simp [spExact, Instr.dsts, spAfter])) (GP.cat u1 (GP.cat (rest_gp _) (GP.cat pop (GP.nil fun _ _ => trivial))))
  intro tr htr
  exact (GP.cat (save_gp _) (GP.cat d1 (GP.cat (GP.pre (fun q h => ⟨h.hs.trans hf.symm, fun y hy => hf ▸ h.ab y hy,
    h.r, fun y hy => by rw [hΓ] at hy; obtain ⟨_, hp, _⟩ := hy; cases hp⟩) hb) hL)) ⟨sp0, fun _ => False⟩ ⟨rfl, fun _ h => h, fun _ h => h.elim⟩ tr htr).1

/-- **An entry has a good trace**: the enter, the body's trace from the checks of `P` and the
callees' effects, and the leave. -/
theorem entry_good (g : GeoOk c G Wc Rc) (hsp : c.sp0 = sp0 - 36#32) (h36 : 36 + G.N ≤ sp0.toNat)
    (hT : ∀ a base p, @CalleeS.Eff (cE a) p B BS _ base (T a base p))
    (hcode : ∀ y, Has [@codeR B BS _ c.base] y → ¬ BelowEntry sp0 (36 + G.N) y)
    (P : Prog A Bk) {st0 st' : St} {oE : Nat} (hok : entryOk cE bE G P oE = true)
    (hty : P.ty cE bE G st0 = some st') (hex0 : st0.ex = none) (hexf : st'.ex = none)
    (he : P.eok cE bE G st0 = true) (hbk : P.bok cE bE G [] (bodyAt G oE) = true)
    (hΓ : st0.Γ = []) :
    ∀ tr, entryTr cE bE G T c sp0 oE P st0 tr → Good sp0 (36 + G.N) ⟨sp0, fun _ => False⟩ tr :=
  entry_goodB hsp hok hΓ (prog_good (frm_entry g hsp h36) hT (fun y hy hb => absurd hb (hcode y hy)) P (bodyAt G oE)
    st0 st' (Tr.is []) (SIR sp0 (G.fsp c) (Sv sp0)) [] [] hty hex0 he hbk
    (fun _ => GP.nil fun _ h => ⟨h.sp, h.sv, h.ab⟩) (fun l hl => by rw [hexf] at hl; cases hl))

end

end M0Crypto.Release.Ed25519CallProg
