import M0Crypto.Release.AeadReturn
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Frame invariants shared by the two AEAD compositions. -/
namespace M0Crypto.Release.Aead
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release.Frame

/-- Bytes of a buffer disjoint from the output cannot be output bytes. -/
theorem not_out {c : ACall} {a : Word} {n j : Nat} (hd : Disj a n c.out c.len.toNat) (hj : j < n) :
    ¬ OutR c (a + BitVec.ofNat 32 j) := by
  intro h
  exact ne_of_disj hd.1 hd.2.1 hd.2.2 hj h (add_toNat_sub c.out _).symm

theorem not_tag {c : ACall} {a : Word} {n j : Nat} (hd : Disj a n c.tag 16) (hj : j < n) :
    ¬ (a + BitVec.ofNat 32 j - c.tag).toNat < 16 := by
  intro h
  exact ne_of_disj hd.1 hd.2.1 hd.2.2 hj h (add_toNat_sub c.tag _).symm

theorem ABuf.outA {c : ACall} (hb : ABuf c) (hv : AValid c) (o : Nat) (ho : o < 160) :
    ¬ OutR c (c.A + BitVec.ofNat 32 o) := by
  have hd := hv.win hb.outS 176 160 c.A (by have := hv.A_lo; omega) (by decide)
  exact not_out ⟨hd.2.1, hd.1, Or.symm hd.2.2⟩ ho

theorem ABuf.tagA {c : ACall} (hb : ABuf c) (hv : AValid c) (o : Nat) (ho : o < 160) :
    ¬ (c.A + BitVec.ofNat 32 o - c.tag).toNat < 16 := by
  have hd := hv.win hb.tagS 176 160 c.A (by have := hv.A_lo; omega) (by decide)
  exact not_tag ⟨hd.2.1, hd.1, Or.symm hd.2.2⟩ ho

theorem ABuf.codeAt {c : ACall} (hb : ABuf c) (hv : AValid c) {m : Mem}
    (hf : ∀ y, ¬ AWr c y → m y = c.m0 y) : CodeAt m c.base B := by
  intro i hi
  have hi' : i < Artifacts.Release.size := by rwa [B_len] at hi
  rw [hf _ (fun h => by rcases h with h | h | h
                        · exact hv.code_not_swr hi' h
                        · exact not_out hb.codeO hi' h
                        · exact not_tag hb.codeT hi' h)]
  exact hv.code i hi

theorem ABuf.outStack {c : ACall} (hb : ABuf c) : Disj c.out c.len.toNat (c.sp0-320#32) 320 :=
  disj_sub hb.outS (Nat.le_refl _) (by omega)

theorem ABuf.tagStack {c : ACall} (hb : ABuf c) : Disj c.tag 16 (c.sp0-320#32) 320 :=
  disj_sub hb.tagS (Nat.le_refl _) (by omega)

/-- The frame and preserved registers needed between AEAD phases. -/
structure Body (c : ACall) (Wr : Word → Prop) (s : State) : Prop where
  sp : s.regs 13 = c.A
  high : Hi c s.mem
  nonce : read32 s.mem c.A = c.nonce
  hi : ∀ r : Reg, 8 ≤ r.val → r.val < 12 → s.regs r = c.regs0 r
  frame : ∀ y, ¬ Wr y → s.mem y = c.m0 y
  code : CodeAt s.mem c.base B

theorem SetupPost.body {c : ACall} (hv : AValid c) {e : Nat} {ic : Poly1305Init.ICtx} {s : State}
    (h : SetupPost c e ic s) : Body c (SWr c.A) s :=
  ⟨h.sp, h.high, h.nonce, fun r a b => h.hi r (by omega) b, h.out, hv.codeAt_of h.out⟩

theorem mac_not_A (A : Word) (o : Nat) (ho : o < 160) (hn : o < 8 ∨ 88 ≤ o) :
    ¬ MacWr A (A + BitVec.ofNat 32 o) := by
  intro hw
  obtain ⟨q, hq, eq⟩ := macWr_W hw
  have hq' : q < 208 := by rcases hq with hq | hq | hq <;> omega
  have eo : A + BitVec.ofNat 32 o = W A (64+o) := by simpa using W_add A o 0
  rw [eo] at eq
  exact off_ne (A-64#32) (by omega) (by omega) (by unfold MacOff at hq; omega) eq

theorem Body.mac {c : ACall} {Wr : Word → Prop} {s t : State} {d n : Word} {off : Nat}
    (h : Body c Wr s) (he : MacEnv c.base c.A d n s.mem) (ht : MacPost c.base c.A d n s.mem off s t)
    (hw : ∀ y, MacWr c.A y → Wr y) : Body c Wr t := by
  refine ⟨ht.sp, h.high.mac he ht.frame, ?_, ?_, ?_, he.codeAt_of ht.frame⟩
  · rw [← h.nonce]
    exact read32_congr (fun k hk => ht.frame _ (mac_not_A c.A k (by omega) (.inl (by omega))))
  · intro r a b; rw [ht.hi r (by omega) b, h.hi r a b]
  · intro y hy; rw [ht.frame y (fun h' => hy (hw y h')), h.frame y hy]

theorem Body.lengths {c : ACall} {Wr : Word → Prop} {s t : State} {off : Nat} {ti : Mem} {msg}
    (hv : AValid c) (h : Body c Wr s) (ht : LengthPost c off ti msg s t)
    (hw : ∀ y, MacWr c.A y → Wr y) : Body c Wr t := by
  have he : MacEnv c.base c.A c.base 0#32 s.mem := hv.macEnv
    (disj_mono (hv.win hv.codeS 0 320 _ (by rw [hv.lo]; omega) (by decide)) (by decide)) h.code
  refine ⟨ht.sp, h.high.mac he ht.frame, ?_, ?_, ?_, he.codeAt_of ht.frame⟩
  · rw [← h.nonce]
    exact read32_congr (fun k hk => ht.frame _ (mac_not_A c.A k (by omega) (.inl (by omega))))
  · intro r a b; rw [ht.hi r (by omega) b, h.hi r a b]
  · intro y hy; rw [ht.frame y (fun h' => hy (hw y h')), h.frame y hy]

theorem CryptPost.atA {c : ACall} (hv : AValid c) (hb : ABuf c) {off : Nat} {s t : State}
    (h : CryptPost c off s t) (o : Nat) (ho : o < 160) (h4 : o < 4 ∨ 8 ≤ o) :
    t.mem (c.A + BitVec.ofNat 32 o) = s.mem (c.A + BitVec.ofNat 32 o) := by
  apply h.keep
  · intro q hq e
    have ea : c.A - BitVec.ofNat 32 176 + BitVec.ofNat 32 (176+o) = c.A + BitVec.ofNat 32 o := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [← ea] at e
    exact off_ne (c.A-176#32) (by omega) (by omega) (by omega) e
  · intro q hq e; exact off_ne c.A (by omega) (by omega) (by omega) e
  · exact hb.outA hv o ho

theorem Body.crypt {c : ACall} (hv : AValid c) (hb : ABuf c) {off : Nat} {s t : State}
    (h : Body c (SWr c.A) s) (ht : CryptPost c off s t) : Body c (AWr c) t := by
  have hf : ∀ y, ¬ AWr c y → t.mem y = c.m0 y := by
    intro y hy
    rw [ht.keep y (fun o ho e => hy (.inl (e ▸ swr_lo c.A o ho)))
      (fun o ho e => hy (.inl (e ▸ swr_A c.A (4+o) (by omega)))) (fun h' => hy (.inr (.inl h')))]
    exact h.frame y (fun h' => hy (.inl h'))
  refine ⟨ht.sp, h.high.congr (fun o a b => ht.atA hv hb o b (.inr (by omega))), ?_, ?_, hf, hb.codeAt hv hf⟩
  · rw [← h.nonce]
    exact read32_congr (fun k hk => by simpa using ht.atA hv hb k (by omega) (.inl hk))
  · intro r a b; rw [ht.hi r (by omega) b, h.hi r a b]

/-- Read-only two-load setup for the next MAC. -/
theorem load_reach (base A d n : Word) (off : Nat) (is : List Instr) (s : State)
    (hb : base.toNat % 4 = 0) (ha : A.toNat % 4 = 0) (ho : off % 2 = 0)
    (hseq : seqAt B off is = true) (hp : s.pc = base + BitVec.ofNat 32 off)
    (hs : s.regs 13 = A) (u v : BitVec 8)
    (his : is = [.ldrSp 4 u, .ldrSp 5 v])
    (hd : read32 s.mem (A + BitVec.ofNat 32 (4*u.toNat)) = d)
    (hn : read32 s.mem (A + BitVec.ofNat 32 (4*v.toNat)) = n) (Wr : Word → Prop) :
    Reach base Wr s (fun t => t.pc = base + BitVec.ofNat 32 (off + seqSize is) ∧ t.regs 4 = d ∧ t.regs 5 = n ∧
      t.mem = s.mem ∧ ∀ r : Reg, r.val ≠ 4 → r.val ≠ 5 → r.val ≠ 15 → t.regs r = s.regs r) := by
  subst his
  apply Reach.block (by omega) _ off hp ho hseq (by rfl)
    (by simp [alignedAll, Instr.accesses, Access.aligned, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg,
      M0Crypto.Armv6M.State.sp, hs, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, BitVec.toNat_add, BitVec.toNat_ofNat]; exact ha)
    (ChaCha20Block.noWrites _ _ (by rfl) _)
  apply Reach.done
  refine ⟨by rw [execAll_pc _ _ (by rfl), hp, ofNat_add_assoc], ?_, ?_, rfl, ?_⟩
  · simpa [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, hs, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, Nat.mul_comm] using hd
  · simpa [execAll, Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg, M0Crypto.Armv6M.State.sp, hs, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5, Nat.mul_comm] using hn
  · intro r h4 h5 h15
    exact execAll_regs_other _ _ _ h15 (by simp [Instr.dsts, Fin.ext_iff, h4, h5, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5]; omega)

end M0Crypto.Release.Aead
