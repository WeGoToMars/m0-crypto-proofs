import M0Crypto.Release.Ed25519DecompressProg

/-!
# The blocks of `m0c_ge_decompress`

* `load_run`: the load block leaves at `Y` the input's number below `2^255` (the field value)
  and at `SIGN` its bit 255, when the input lies apart from `Y`. The group of word `i`
  (`grp_run`) stores the input's word `i`, read through `r2 = r1`; `loads_run` chains the
  eight; the mask (`mask_mem`) moves bit 255 to `SIGN`; `sign_word` reads it back as a word.
* `yp_run`: the test at `0x2100`, the carry chain of `y + 19` over `Y`'s words, clears `Z`
  exactly when `p ≤ y` (`decodeCode`'s rejection), for `y` below `2^255`.
* `z_run`, `z_spec`: the test at `0x21f2` sets `Z` exactly when `x = 0`, and leaves the `SIGN`
  word in `r2`; `s_spec`: `cmp r2, #0` sets `Z` exactly when the sign is `0`.
* `p_run`, `p_spec`: the test at `0x2214` sets `Z` exactly when `x mod 2` is the sign.
* `st_spec`: `cmp r0, #0` after `fe_eq` sets `Z` exactly when the field values agree.

`yp_at`, `z_at`, `p_at`, `s_at` and `st_at` decide each test's instructions at its offset in
both builds. The tests are generic in the state; each statement is the form a branch rule takes
as a hypothesis.
-/

namespace M0Crypto.Release.Ed25519DecompressProg

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Ed25519Words (wsum)
open M0Crypto.Spec.Ed25519 (decodeInt)
open M0Crypto.Release.X25519Bytes (loadLe32 loadLe32_exec loadLe32_noW loadLe32_regs_other)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519PrimeCert (p)

/-! ## Words -/

theorem read32_le (m : Mem) (a : Word) :
    (read32 m a).toNat = (m a).toNat + 2 ^ 8 * (m (a + BitVec.ofNat 32 1)).toNat +
      2 ^ 16 * (m (a + BitVec.ofNat 32 2)).toNat + 2 ^ 24 * (m (a + BitVec.ofNat 32 3)).toNat := by
  have h8 : ∀ (x : Nat) (y : BitVec 8), x <<< 8 ||| y.toNat = 256 * x + y.toNat := fun x y => by
    rw [← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]; omega
  simp only [read32, BitVec.toNat_append, h8]
  omega

/-! ## One word -/

/-- `load_le32(r4, r3, r2, 4i)` and its store at frame offset `o + 4i`. -/
def grp (o i : Nat) : List Instr := loadLe32 4 3 2 (4 * i) ++ [.strSp 4 (BitVec.ofNat 8 ((o + 4 * i) / 4))]

theorem grp_run {o : Nat} (ho : o % 4 = 0) (ho' : o + 32 ≤ 1024) (u : State) {i : Nat} (hi : i < 8) :
    (execAll (grp o i) u).mem =
      write32 u.mem (slot (u.regs 13) (o / 4 + i)) (read32 u.mem (u.regs 2 + BitVec.ofNat 32 (4 * i))) ∧
    (execAll (grp o i) u).regs 2 = u.regs 2 ∧ (execAll (grp o i) u).regs 13 = u.regs 13 := by
  rw [grp, execAll_append, execAll, execAll, show (o + 4 * i) / 4 = o / 4 + i by omega,
    Frame.strSp_next _ _ _ (by omega)]
  have hm := execAll_mem _ u (loadLe32_noW 4 3 2 (4 * i))
  have h2 := loadLe32_regs_other u (rd := 4) (rt := 3) (rb := 2) (4 * i) (r := 2) (by decide) (by decide) (by decide)
  have h13 := loadLe32_regs_other u (rd := 4) (rt := 3) (rb := 2) (4 * i) (r := 13) (by decide) (by decide) (by decide)
  have h4 := loadLe32_exec u (rd := 4) (rt := 3) (rb := 2) (k := 4 * i) (by decide) (by decide) (by decide) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [hm, h13]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [h4, read32_le, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc]; rfl
  · rw [RoutineBranch.setReg15_regs _ _ 2 (by decide)]; exact h2
  · rw [RoutineBranch.setReg15_regs _ _ 13 (by decide)]; exact h13

/-! ## The eight words -/

/-- After the groups `0 … k − 1` at frame offset `o₀`: the stored words and the memory
elsewhere. -/
theorem loads_run {o₀ : Nat} (h0 : o₀ % 4 = 0) (h0' : o₀ + 32 ≤ 1024) (u : State) (hsep : ∀ o < 32, ∀ q < 32,
      u.regs 13 + BitVec.ofNat 32 (o₀ + o) ≠ u.regs 2 + BitVec.ofNat 32 q) :
    ∀ k ≤ 8, let w := execAll ((List.range k).flatMap (grp o₀)) u
      w.regs 2 = u.regs 2 ∧ w.regs 13 = u.regs 13 ∧
      (∀ j < k, read32 w.mem (slot (u.regs 13) (o₀ / 4 + j)) = read32 u.mem (u.regs 2 + BitVec.ofNat 32 (4 * j))) ∧
      ∀ y, (∀ o < 4 * k, y ≠ u.regs 13 + BitVec.ofNat 32 (o₀ + o)) → w.mem y = u.mem y
  | 0, _ => ⟨rfl, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨r2, r13, hw, ho⟩ := loads_run h0 h0' u hsep k (by omega)
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      execAll_append]
    generalize execAll ((List.range k).flatMap (grp o₀)) u = w at r2 r13 hw ho
    obtain ⟨gm, g2, g13⟩ := grp_run h0 h0' w (i := k) (by omega)
    have hin : read32 w.mem (w.regs 2 + BitVec.ofNat 32 (4 * k)) = read32 u.mem (u.regs 2 + BitVec.ofNat 32 (4 * k)) := by
      rw [r2]
      apply Frame.read32_congr
      intro q hq
      apply ho
      intro o ho' e
      rw [ofNat_add_assoc] at e
      exact hsep o (by omega) (4 * k + q) (by omega) e.symm
    refine ⟨g2.trans r2, g13.trans r13, fun j hj => ?_, fun y hy => ?_⟩
    · rw [gm, r13]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Frame.read32_write32_slot' _ _ _ _ _ (by omega) (by omega),
          ite_eq_right_iff.mpr fun e => absurd e (by omega)]
        exact hw j hj
      · rw [M0Crypto.Armv6M.read32_write32_same, hin]
    · rw [gm, M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq e => hy (4 * k + q) (by omega) (by
          rw [e, r13, slot, ofNat_add_assoc]; congr 2; omega)]
      exact ho y fun o ho' => hy o (by omega)

/-! ## The mask and the whole block -/

theorem mask_mem (w : State) :
    (execAll maskG w).mem =
      write32 (write32 w.mem (slot (w.regs 13) 1) (read32 w.mem (slot (w.regs 13) 9) >>> 31)) (slot (w.regs 13) 9)
        ((read32 w.mem (slot (w.regs 13) 9) <<< 1) >>> 1) := rfl

theorem mov_run (t : State) : ((Instr.movHi 2 1).next t).regs 2 = t.regs 1 ∧
    ((Instr.movHi 2 1).next t).regs 13 = t.regs 13 ∧ ((Instr.movHi 2 1).next t).mem = t.mem := by
  refine ⟨?_, ?_, rfl⟩ <;> simp [Instr.next, Instr.exec, M0Crypto.Armv6M.State.setReg]

theorem write32_byte (m : Mem) (a v : Word) {k : Nat} (hk : k < 4) :
    write32 m a v (a + BitVec.ofNat 32 k) = v.extractLsb' (8 * k) 8 := by
  have n1 : a + BitVec.ofNat 32 1 ≠ a := by bv_omega
  have n2 : a + BitVec.ofNat 32 2 ≠ a := by bv_omega
  have n3 : a + BitVec.ofNat 32 3 ≠ a := by bv_omega
  have n21 : a + BitVec.ofNat 32 2 ≠ a + 1#32 := by bv_omega
  have n31 : a + BitVec.ofNat 32 3 ≠ a + 1#32 := by bv_omega
  have n32 : a + BitVec.ofNat 32 3 ≠ a + 2#32 := by bv_omega
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simp [write32]
  · simp only [write32, n1, ite_false]; rfl
  · simp only [write32, n2, n21, ite_false]; rfl
  · simp only [write32, n3, n31, n32, ite_false]; rfl

/-- `SIGN`'s bytes: bit 255 of the input's number, as a little-endian word. -/
def signB (l : List (BitVec 8)) : List (BitVec 8) := [BitVec.ofNat 8 (decodeInt l / 2 ^ 255), 0, 0, 0]

theorem shl_shr (x : Word) : ((x <<< 1) >>> 1).toNat = x.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem loadG_eq : loadG = .movHi 2 1 :: ((List.range 8).flatMap (grp Y) ++ maskG) := rfl

theorem slotY (sp : Word) (i : Nat) : slot (sp + BitVec.ofNat 32 Y) i = slot sp (2 + i) := by
  rw [slot, slot, ofNat_add_assoc]; congr 2; unfold Y; omega

/-- The mask's memory at `Y`'s words. -/
theorem fin_word (M : Mem) (sp W : Word) {i : Nat} (hi : i < 8) :
    read32 (write32 (write32 M (slot sp 1) (W >>> 31)) (slot sp 9) ((W <<< 1) >>> 1)) (slot sp (2 + i)) =
      if i = 7 then (W <<< 1) >>> 1 else read32 M (slot sp (2 + i)) := by
  rw [M0Crypto.Armv6M.read32_write32_slot _ _ _ _ _ (by omega) (by omega)]
  by_cases h : i = 7
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h, M0Crypto.Armv6M.read32_write32_slot _ _ _ _ _ (by omega) (by omega),
      ite_eq_right (by omega)]

/-- The mask's memory at `SIGN`. -/
theorem fin_sign (M : Mem) (sp W : Word) {k : Nat} (hk : k < 4) :
    write32 (write32 M (slot sp 1) (W >>> 31)) (slot sp 9) ((W <<< 1) >>> 1) (sp + BitVec.ofNat 32 SIGN + BitVec.ofNat 32 k) =
      (W >>> 31).extractLsb' (8 * k) 8 := by
  rw [M0Crypto.Armv6M.write32_other _ _ _ _ fun q hq => by simp only [slot, SIGN]; bv_omega,
    show sp + BitVec.ofNat 32 SIGN = slot sp 1 from rfl, write32_byte _ _ _ hk]

/-- `psum` of the masked words is the number below `2^255`. -/
theorem masked_sum {f : Nat → Nat} (hfl : ∀ j, f j < 2 ^ 32) :
    Field25519Facts.psum (fun i => if i = 7 then f 7 % 2 ^ 31 else f i) 8 = wsum f 8 % 2 ^ 255 := by
  have hw8 := Ed25519Words.wsum_lt (f := f) (n := 7) fun j _ => hfl j
  have h7 := hfl 7
  simp only [Field25519Facts.psum, wsum] at hw8 ⊢
  simp only [show (0 : Nat) ≠ 7 by decide, show (1 : Nat) ≠ 7 by decide, show (2 : Nat) ≠ 7 by decide,
    show (3 : Nat) ≠ 7 by decide, show (4 : Nat) ≠ 7 by decide, show (5 : Nat) ≠ 7 by decide,
    show (6 : Nat) ≠ 7 by decide, ↓reduceIte]
  omega

/-- **The load block**: from an input apart from `Y`, its number below `2^255` at `Y` and its bit
255 at `SIGN`. -/
theorem load_run (t : State) (hsep : ∀ o < 32, ∀ q < 32,
      t.regs 13 + BitVec.ofNat 32 (Y + o) ≠ t.regs 1 + BitVec.ofNat 32 q) :
    feVal (execAll loadG t).mem (t.regs 13 + BitVec.ofNat 32 Y) = decodeInt (bytesAt t.mem (t.regs 1) 32) % 2 ^ 255 ∧
    bytesAt (execAll loadG t).mem (t.regs 13 + BitVec.ofNat 32 SIGN) 4 = signB (bytesAt t.mem (t.regs 1) 32) := by
  obtain ⟨u2, u13, um⟩ := mov_run t
  rw [loadG_eq, execAll, execAll_append, mask_mem]
  generalize (Instr.movHi 2 1).next t = u at u2 u13 um
  obtain ⟨-, w13, hw, -⟩ := loads_run (o₀ := Y) (by decide) (by decide) u (by rw [u2, u13]; exact hsep) 8 (Nat.le_refl _)
  simp only [show Y / 4 = 2 from rfl] at hw
  generalize execAll ((List.range 8).flatMap (grp Y)) u = w at w13 hw
  rw [w13, u13]; rw [u13, u2, um] at hw
  generalize t.regs 13 = sp at hw ⊢
  generalize hW : read32 w.mem (slot sp 9) = W
  generalize w.mem = M at hw hW
  generalize hf : (fun j => (read32 t.mem (t.regs 1 + BitVec.ofNat 32 (4 * j))).toNat) = f
  have hfl : ∀ j, f j < 2 ^ 32 := fun j => by rw [← hf]; exact (read32 _ _).isLt
  have hd : decodeInt (bytesAt t.mem (t.regs 1) 32) = wsum f 8 := by
    rw [← hf]; exact Ed25519CallProg.decodeInt_words t.mem (t.regs 1) 8
  have f7 : W.toNat = f 7 := by rw [← hW, hw 7 (by decide), ← hf]
  simp only [signB]
  rw [hd]
  constructor
  · rw [Field25519Facts.feVal_psum, ← masked_sum hfl]
    apply Field25519Facts.psum_congr
    intro i hi
    rw [slotY, fin_word M sp W hi]
    by_cases h : i = 7
    · rw [ite_eq_left h, ite_eq_left h, shl_shr, f7]
    · rw [ite_eq_right h, ite_eq_right h, hw i hi, ← hf]
  · simp only [bytesAt, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil]
    rw [show BitVec.ofNat 32 0 = BitVec.ofNat 32 (0 : Nat) from rfl, fin_sign M sp W (k := 0) (by decide), fin_sign M sp W (k := 1) (by decide),
      fin_sign M sp W (k := 2) (by decide), fin_sign M sp W (k := 3) (by decide)]
    have hv : (W >>> 31).toNat = f 7 / 2 ^ 31 := by rw [BitVec.toNat_ushiftRight, f7, Nat.shiftRight_eq_div_pow]
    have hw8 := Ed25519Words.wsum_lt (f := f) (n := 7) fun j _ => hfl j
    have hs8 : wsum f 8 = wsum f 7 + 2 ^ (32 * 7) * f 7 := Ed25519Words.wsum_succ f 7
    have := hfl 7
    have h0 : (0 : BitVec 8).toNat = 0 := rfl
    simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.extractLsb'_toNat, hv, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] <;> omega

/-- The `SIGN` word is bit 255 of a 32-byte input. -/
theorem sign_word {m : Mem} {a : Word} {l : List (BitVec 8)} (hl : l.length = 32) (h : bytesAt m a 4 = signB l) :
    (read32 m a).toNat = decodeInt l / 2 ^ 255 ∧ decodeInt l / 2 ^ 255 < 2 := by
  have hd := Ed25519Bytes.decodeInt_lt l
  rw [hl] at hd
  simp only [bytesAt, signB, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [read32_le, h1, h2, h3, show a = a + BitVec.ofNat 32 0 from (BitVec.add_zero a).symm, h0]
  have z : (0 : BitVec 8).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat]
  omega

/-! ## The `y ≥ p` test -/

/-- `ldr r1, [r0, #4k]; adcs r1, r3`. -/
def pairG (k : Nat) : List Instr := [.memImm .ldr 1 0 (BitVec.ofNat 5 k), .dp .adcs 1 3]

/-- The test at `0x2100`: the carry chain of `y + 19` over `Y`'s words, bit 255 of the sum in
`r1`; `beq` continues on `Z`. -/
def ypG : List Instr :=
  [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] ++
    (List.range 7).flatMap (fun i => pairG (i + 1)) ++ [.lsrImm 1 1 31]

theorem yp_at (b : Build) : seqAt b.bytes 0x2100 ypG = true := by cases b <;> decide +kernel

/-- Word `j` from `a`, as a number. -/
def wf (m : Mem) (a : Word) (j : Nat) : Nat := (read32 m (a + BitVec.ofNat 32 (4 * j))).toNat

theorem awc (x y : Word) (c : Bool) :
    (M0Crypto.Armv6M.addWithCarry x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 2 ^ 32 ∧
    (M0Crypto.Armv6M.addWithCarry x y c).2.1.toNat = (x.toNat + y.toNat + c.toNat) / 2 ^ 32 := by
  have := x.isLt; have := y.isLt
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat]
  refine ⟨trivial, ?_⟩
  by_cases h : x.toNat + y.toNat + c.toNat < 2 ^ 32
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
  · have h2 : (x.toNat + y.toNat + c.toNat) / 2 ^ 32 = 1 := by cases c <;> simp at h ⊢ <;> omega
    rw [h2]; simp only [ne_eq]
    cases c <;> simp at h ⊢ <;> omega

theorem pair_run (u : State) {k : Nat} (hk : k < 32) (h3 : u.regs 3 = 0#32) :
    (execAll (pairG k) u).regs 0 = u.regs 0 ∧ (execAll (pairG k) u).regs 3 = 0#32 ∧
    (execAll (pairG k) u).mem = u.mem ∧
    ((execAll (pairG k) u).regs 1).toNat = (wf u.mem (u.regs 0) k + u.c.toNat) % 2 ^ 32 ∧
    (execAll (pairG k) u).c.toNat = (wf u.mem (u.regs 0) k + u.c.toNat) / 2 ^ 32 := by
  have hk' : k % 32 * 4 = 4 * k := by omega
  have e0 : LowReg.toReg 0 = 0 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  have a := awc (read32 u.mem (u.regs 0 + BitVec.ofNat 32 (4 * k))) 0#32 u.c
  simp (config := {decide := true}) [pairG, execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg,
    State.reg, MemOp.width, M0Crypto.Thumb.addFlags, State.setNZCV, State.setNZ, hk', e0, e3, h3, wf] at a ⊢
  exact a

/-- `(X / B + f) / D`, the carry of the next word. -/
theorem div_step (X f B D : Nat) (hB : 0 < B) : (X / B + f) / D = (X + B * f) / (B * D) := by
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB]

theorem carry_step (F : Nat → Nat) (n : Nat) :
    ((wsum F (n + 1) + 19) / 2 ^ (32 * (n + 1)) + F (n + 1)) / 2 ^ 32 = (wsum F (n + 2) + 19) / 2 ^ (32 * (n + 2)) := by
  rw [div_step _ _ _ _ (Nat.two_pow_pos _), ← Nat.pow_add, show 32 * (n + 1) + 32 = 32 * (n + 2) by omega,
    Ed25519Words.wsum_succ F (n + 1)]
  congr 1; omega

/-- The pairs `1..n`: the carry of `y + 19` past word `n`. -/
theorem chain_run (u : State) (h3 : u.regs 3 = 0#32) (hc : u.c.toNat = (wsum (wf u.mem (u.regs 0)) 1 + 19) / 2 ^ 32) :
    ∀ n, n ≤ 7 → (execAll ((List.range n).flatMap fun i => pairG (i + 1)) u).regs 0 = u.regs 0 ∧
      (execAll ((List.range n).flatMap fun i => pairG (i + 1)) u).regs 3 = 0#32 ∧
      (execAll ((List.range n).flatMap fun i => pairG (i + 1)) u).mem = u.mem ∧
      (execAll ((List.range n).flatMap fun i => pairG (i + 1)) u).c.toNat =
        (wsum (wf u.mem (u.regs 0)) (n + 1) + 19) / 2 ^ (32 * (n + 1))
  | 0, _ => ⟨rfl, h3, rfl, hc⟩
  | n + 1, hn => by
    obtain ⟨r0, r3, hm, hc'⟩ := chain_run u h3 hc n (by omega)
    rw [List.range_succ, List.flatMap_append, execAll_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨q0, q3, qm, -, qc⟩ := pair_run (execAll ((List.range n).flatMap fun i => pairG (i + 1)) u)
      (k := n + 1) (by omega) r3
    rw [q0, q3, qm, qc, r0, hm, hc', Nat.add_comm (wf _ _ (n + 1)), carry_step]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem psum_wsum (f : Nat → Nat) (n : Nat) : Field25519Facts.psum f n = wsum f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Field25519Facts.psum, ih]; rfl

/-- **The `y ≥ p` test**: on `Y` below `2^255`, `Z` is clear exactly when `p ≤ y`; memory is
unchanged. -/
theorem pre_run (t : State) :
    (execAll [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] t).regs 0 = t.regs 13 + BitVec.ofNat 32 Y ∧
    (execAll [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] t).regs 3 = 0#32 ∧
    (execAll [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] t).mem = t.mem ∧
    (execAll [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] t).c.toNat =
      (wsum (wf t.mem (t.regs 13 + BitVec.ofNat 32 Y)) 1 + 19) / 2 ^ 32 := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  have e1 : LowReg.toReg 1 = 1 := rfl
  have e3 : LowReg.toReg 3 = 3 := rfl
  simp (config := {decide := true}) [execAll, Instr.next, Instr.exec, Instr.exec.memOp, State.setReg,
    State.reg, State.sp, MemOp.width, M0Crypto.Thumb.addFlags, State.setNZCV, State.setNZ, e0, e1, e3, wf,
    wsum, Y]
  refine (awc _ _ false).2.trans ?_
  simp

theorem lsr_z (u : State) : ((Instr.lsrImm 1 1 31).next u).z = (u.regs 1 >>> 31 == 0#32) := by
  have e1 : LowReg.toReg 1 = 1 := rfl
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.lsrC, State.setReg, State.setNZC, State.setNZ, State.reg, e1]

theorem lsr_mem (u : State) : ((Instr.lsrImm 1 1 31).next u).mem = u.mem := by
  simp [Instr.next, Instr.exec, State.setReg, State.setNZC]

/-- **The `y ≥ p` test**: on `Y` below `2^255`, `Z` is clear exactly when `p ≤ y`; memory is
unchanged. -/
theorem yp_run (t : State) (hy : feVal t.mem (t.regs 13 + BitVec.ofNat 32 Y) < 2 ^ 255) :
    ((execAll ypG t).z = false ↔ p ≤ feVal t.mem (t.regs 13 + BitVec.ofNat 32 Y)) ∧
    (execAll ypG t).mem = t.mem := by
  obtain ⟨u0, u3, um, uc⟩ := pre_run t
  rw [ypG, execAll_append, execAll_append, List.range_succ, List.flatMap_append, execAll_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  generalize execAll [.addRdSp 0 2, .memImm .ldr 1 0 0, .addImm8 1 19, .movImm 3 0] t = u at u0 u3 um uc
  rw [← u0, ← um] at uc
  obtain ⟨v0, v3, vm, vc⟩ := chain_run u u3 uc 6 (by decide)
  generalize execAll ((List.range 6).flatMap fun i => pairG (i + 1)) u = v at v0 v3 vm vc
  obtain ⟨-, -, wm, w1, -⟩ := pair_run v (k := 7) (by decide) v3
  generalize execAll (pairG 7) v = w at wm w1
  simp only [execAll]
  rw [lsr_z, lsr_mem, wm, vm, um, v0, vm, u0, um] at *
  rw [vc] at w1
  have hv : feVal t.mem (t.regs 13 + BitVec.ofNat 32 Y) = wsum (wf t.mem (t.regs 13 + BitVec.ofNat 32 Y)) 8 := by
    rw [Field25519Facts.feVal_psum, psum_wsum]; rfl
  rw [hv] at hy ⊢
  have hF : ∀ j, wf t.mem (t.regs 13 + BitVec.ofNat 32 Y) j < 2 ^ 32 := fun j => (read32 _ _).isLt
  generalize wf t.mem (t.regs 13 + BitVec.ofNat 32 Y) = F at w1 hy hF ⊢
  have hw7 := Ed25519Words.wsum_lt (f := F) (n := 7) fun j _ => hF j
  have hs8 : wsum F 8 = wsum F 7 + 2 ^ (32 * 7) * F 7 := Ed25519Words.wsum_succ F 7
  have hd := div_step (wsum F 7 + 19) (F 7) (2 ^ 224) (2 ^ 31) (Nat.two_pow_pos _)
  refine ⟨?_, rfl⟩
  rw [Ed25519Decode.ge_p_iff hy]
  have hz : (w.regs 1 >>> 31 == 0#32) = false ↔ (w.regs 1).toNat / 2 ^ 31 ≠ 0 := by
    rw [beq_eq_false_iff_ne, ne_eq, ne_eq, BitVec.toNat_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  rw [hz, w1]
  simp only [show 32 * (6 + 1) = 224 by rfl, show 6 + 1 = 7 by rfl] at hd w1 ⊢
  omega

/-! ## Comparisons -/

theorem awc_not (x y : Word) : (M0Crypto.Armv6M.addWithCarry x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [M0Crypto.Armv6M.addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_sub,
    Bool.toNat_true]
  have := x.isLt; have := y.isLt
  omega

/-- `cmp r, #0`: `Z` exactly when `r = 0`. -/
theorem cmp0_z (s : State) (n : LowReg) : ((Instr.cmpImm n 0).next s).z = (s.regs n.toReg == 0#32) := by
  have h := awc_not (s.regs n.toReg) 0#32
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, State.reg] at h ⊢
  rw [h]; rfl

/-- `cmp a, b`: `Z` exactly when `a = b`. -/
theorem cmp_z (s : State) (a b : LowReg) : ((Instr.dp .cmp a b).next s).z = (s.regs a.toReg == s.regs b.toReg) := by
  have h := awc_not (s.regs a.toReg) (s.regs b.toReg)
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, State.reg] at h ⊢
  rw [h]; show (_ == _) = _
  by_cases e : s.regs a.toReg = s.regs b.toReg
  · simp [e]
  · have : s.regs a.toReg - s.regs b.toReg ≠ 0 := by bv_omega
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr e]

/-! ## The zero test on `x` -/

open M0Crypto.Sym (SExpr SBool SMem)
open M0Crypto.Release.BlockEffect (Eff effOk eff_run)

/-- Word `i` of `X` at the entry. -/
def xW (i : Nat) : SExpr := .ld32 .mem0 (.add (.reg0 13) (.const (BitVec.ofNat 32 (X + 4 * i))))
def orX : Nat → SExpr
  | 0 => xW 0
  | n + 1 => .or (orX n) (xW (n + 1))
/-- The `SIGN` word at the entry. -/
def signW : SExpr := .ld32 .mem0 (.add (.reg0 13) (.const (BitVec.ofNat 32 SIGN)))

/-- `add r0, sp, #X; ldm r0!, {r1-r4}`, three `orrs`, `ldm r0!, {r2-r5}`, four `orrs`,
`ldr r2, [sp, #SIGN]`. -/
def zPre : List Instr :=
  [.addRdSp 0 42, .ldm 0 0x1e, .dp .orrs 1 2, .dp .orrs 1 3, .dp .orrs 1 4, .ldm 0 0x3c, .dp .orrs 1 2,
   .dp .orrs 1 3, .dp .orrs 1 4, .dp .orrs 1 5, .ldrSp 2 1]
/-- The test at `0x21f2`: `Z` when `x = 0`. -/
def zG : List Instr := zPre ++ [.cmpImm 1 0]

def eZ : Eff := { regs := [(1, orX 7), (2, signW)], clob := [0, 3, 4, 5] }
theorem eZ_ok : effOk zPre eZ = true := by decide +kernel

theorem z_at (b : Build) : seqAt b.bytes 0x21f2 zG = true := by cases b <;> decide +kernel

theorem xW_den (t : State) (i : Nat) :
    (xW i).denote t = read32 t.mem (slot (t.regs 13 + BitVec.ofNat 32 X) i) := by
  rw [slot, ofNat_add_assoc]; rfl

theorem orX_zero (t : State) : (orX 7).denote t = 0#32 ↔ feVal t.mem (t.regs 13 + BitVec.ofNat 32 X) = 0 := by
  rw [Ed25519DecompressVal.zero_iff]
  simp only [orX, SExpr.denote, BitVec.or_eq_zero_iff, xW_den]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  constructor
  · intro h i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h 0 (by decide), h 1 (by decide)⟩, h 2 (by decide)⟩, h 3 (by decide)⟩, h 4 (by decide)⟩,
      h 5 (by decide)⟩, h 6 (by decide)⟩, h 7 (by decide)⟩

theorem cmpImm_regs (s : State) (n : LowReg) (k : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.cmpImm n k).next s).regs r = s.regs r := by
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, hr]

theorem cmpImm_mem (s : State) (n : LowReg) (k : BitVec 8) : ((Instr.cmpImm n k).next s).mem = s.mem := by
  simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, State.setNZ]

/-- **The zero test**: `Z` exactly when the value at `X` is `0`; `r2` holds the `SIGN` word and
memory is unchanged. -/
theorem z_run (t : State) :
    ((execAll zG t).z = true ↔ feVal t.mem (t.regs 13 + BitVec.ofNat 32 X) = 0) ∧
    (execAll zG t).regs 2 = read32 t.mem (t.regs 13 + BitVec.ofNat 32 SIGN) ∧ (execAll zG t).mem = t.mem := by
  have H := eff_run eZ_ok t
  have h1 := H.reg 1 (by decide) (by decide)
  have h2 := H.reg 2 (by decide) (by decide)
  have hm := H.mem _ rfl
  rw [zG, execAll_append]
  simp only [execAll]
  rw [cmp0_z, cmpImm_regs _ _ _ _ (by decide), cmpImm_mem, show LowReg.toReg 1 = 1 from rfl, h1, h2, hm]
  refine ⟨?_, rfl, rfl⟩
  rw [beq_iff_eq]; exact orX_zero t

/-- The zero test on canonical bytes: `Z` exactly when the field element is `0`. -/
theorem z_spec (t : State) {x : Int}
    (hx : bytesAt t.mem (t.regs 13 + BitVec.ofNat 32 X) 32 = Spec.Ed25519.encodeInt (x % (Field25519Reduce.pN : Int)).toNat) :
    (execAll zG t).z = true ↔ Ed25519GeProg.fI x = 0 := by
  rw [(z_run t).1, ← Ed25519GeCompressProg.dec_fe, hx, Ed25519DecompressVal.canon_val]
  exact ⟨fun h => Ed25519Field.Fp.ext h, fun h => by rw [h]; rfl⟩

/-! ## The sign test and the parity -/

/-- `ldr r0, [sp, #X]; movs r1, #1; ands r0, r1; ldr r1, [sp, #SIGN]`. -/
def pPre : List Instr := [.ldrSp 0 42, .movImm 1 1, .dp .ands 0 1, .ldrSp 1 1]
/-- The test at `0x2214`: `Z` when the parity of `x` is the sign. -/
def pG : List Instr := pPre ++ [.dp .cmp 0 1]

def eP : Eff := { regs := [(0, .and (xW 0) (.const 1#32)), (1, signW)] }
theorem eP_ok : effOk pPre eP = true := by decide +kernel

theorem p_at (b : Build) : seqAt b.bytes 0x2214 pG = true := by cases b <;> decide +kernel
/-- The sign test at `0x220e`. -/
theorem s_at (b : Build) : seqAt b.bytes 0x220e [.cmpImm 2 0] = true := by cases b <;> decide +kernel
/-- `fe_eq`'s status tests at `0x21be` and `0x21da`. -/
theorem st_at (b : Build) : seqAt b.bytes 0x21be [.cmpImm 0 0] = true ∧ seqAt b.bytes 0x21da [.cmpImm 0 0] = true := by
  cases b <;> decide +kernel

theorem and1 (w : Word) : (w &&& 1#32).toNat = w.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- **The parity test**: `Z` exactly when the parity of the value at `X` is the `SIGN` word;
memory is unchanged. -/
theorem p_run (t : State) :
    ((execAll pG t).z = true ↔
      feVal t.mem (t.regs 13 + BitVec.ofNat 32 X) % 2 = (read32 t.mem (t.regs 13 + BitVec.ofNat 32 SIGN)).toNat) ∧
    (execAll pG t).mem = t.mem := by
  have H := eff_run eP_ok t
  have h0 := H.reg 0 (by decide) (by decide)
  have h1 := H.reg 1 (by decide) (by decide)
  have hm := H.mem _ rfl
  rw [pG, execAll_append]
  simp only [execAll]
  rw [cmp_z, show LowReg.toReg 0 = 0 from rfl, show LowReg.toReg 1 = 1 from rfl, h0, h1]
  refine ⟨?_, ?_⟩
  · rw [Ed25519DecompressVal.par_eq, beq_iff_eq, ← BitVec.toNat_inj]
    show ((xW 0).denote t &&& 1#32).toNat = _ ↔ _
    rw [and1, xW_den]; rfl
  · simp [Instr.next, Instr.exec, M0Crypto.Thumb.addFlags, State.setNZCV, State.setReg, hm]; rfl

/-- The parity test on canonical bytes: `Z` exactly when `x mod 2` is the sign. -/
theorem p_spec (t : State) {x : Int}
    (hx : bytesAt t.mem (t.regs 13 + BitVec.ofNat 32 X) 32 = Spec.Ed25519.encodeInt (x % (Field25519Reduce.pN : Int)).toNat) :
    (execAll pG t).z = true ↔ (Ed25519GeProg.fI x).val % 2 = (read32 t.mem (t.regs 13 + BitVec.ofNat 32 SIGN)).toNat := by
  rw [(p_run t).1, ← Ed25519GeCompressProg.dec_fe, hx, Ed25519DecompressVal.canon_val]

/-- **`fe_eq`'s status test** `cmp r0, #0`: `Z` exactly when the field values agree. -/
theorem st_spec (s : State) {a b : Nat} {x y : Int} (ha : Field25519Congr.ModP a x) (hb : Field25519Congr.ModP b y)
    (h0 : s.regs 0 = 0#32 ↔ a % Field25519Reduce.pN = b % Field25519Reduce.pN) :
    ((Instr.cmpImm 0 0).next s).z = true ↔ Ed25519GeProg.fI x = Ed25519GeProg.fI y := by
  rw [cmp0_z, beq_iff_eq, ← Ed25519DecompressVal.eq_iff ha hb]; exact h0

/-- **The sign test** `cmp r2, #0`: `Z` exactly when the sign is `0`. -/
theorem s_spec (s : State) : ((Instr.cmpImm 2 0).next s).z = true ↔ s.regs 2 = 0#32 := by
  rw [cmp0_z, beq_iff_eq]; rfl

/-! ## The load block's adapter -/

section
open M0Crypto.Release.Ed25519CallProg (Ctx Rels Rel InsRel OutsRel PreV All2 In ALen rgnsC SRgn Bd)

theorem rel_bytes {c : Ctx} {sp : Word} {n : Nat} {m : Mem} {a : Word} {v : Ed25519CallProg.V} (Rs : Rels)
    (h : Rel Rs c sp (.bytes n) m a v) : ∃ l, v = .b l ∧ bytesAt m a n = l := by
  cases v <;> simp only [Rel] at h
  exact ⟨_, rfl, h⟩

/-- `Y` as the input's value below `2^255`, `SIGN` as its top bit. -/
def loadV : List Ed25519CallProg.V → List Ed25519CallProg.V
  | [.b l] => [.f ((decodeInt l % 2 ^ 255 : Nat) : Int), .b (signB l)]
  | _ => []

/-- **The load block**: `Y` and `SIGN` from the input bytes, apart from `Y` by `apt`. -/
theorem load_post (Rs : Rels) (c : Ctx) (sp : Word) (t : State) (vs : List Ed25519CallProg.V)
    (hpv : PreV ioLoad c sp t.regs) (hin : InsRel Rs c sp ioLoad t vs) :
    OutsRel Rs c sp ioLoad t (execAll loadG t).mem ((loadV vs).take ioLoad.outs.length) := by
  rcases vs with _ | ⟨x, _ | _⟩ <;> simp only [InsRel, All2, ioLoad, and_true, and_false, In.kd, ALen.val] at hin
  obtain ⟨l, rfl, hl⟩ := rel_bytes Rs hin
  have hs := hpv.2.2 _ (List.mem_singleton_self _)
  simp only [rgnsC, SRgn.rgnC, ALen.val, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    show (32 = 0) = False from by decide, ite_false] at hs
  have hsep : ∀ o < 32, ∀ q < 32, t.regs 13 + BitVec.ofNat 32 (Y + o) ≠ t.regs 1 + BitVec.ofNat 32 q := by
    intro o ho q hq he
    refine hs.not_has (y := t.regs 13 + BitVec.ofNat 32 (Y + o)) ⟨_, List.mem_singleton_self _, o, ho, ?_⟩
      ⟨_, List.mem_singleton_self _, q, hq, ?_⟩
    · exact (ofNat_add_assoc _ _ _).symm
    · rw [he, BitVec.add_zero]
  obtain ⟨hY, hS⟩ := load_run t hsep
  simp only [OutsRel, All2, ioLoad, loadV, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
    Rel, and_true]
  rw [BitVec.add_zero] at hl
  rw [hY, hS, hl]
  exact ⟨rfl, rfl⟩

def dbD (Rs : Rels) : ∀ b, Bd Rs (dbS b)
  | .load => ⟨loadV, fun c sp t vs _ _ hpv hin => load_post Rs c sp t vs hpv hin,
      fun _ _ _ _ _ _ _ _ _ h => by simp [dbS, ioLoad] at h⟩

end

/-! ## The status -/

section
open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Curve M0Crypto.Release.Ed25519Decode
open M0Crypto.Release.Ed25519Bridge (toF ofSpec)

/-- The root checks and the `x = 0` check. -/
def rootTests (x vxx u : Fp) (sign : Nat) : Bool :=
  (decide (vxx = u) || decide (vxx = 0 - u)) && !(decide ((if vxx = u then x else x * sqrtM1) = 0) && decide (sign ≠ 0))

/-- `root` then `finish` succeed exactly when the checks pass. -/
theorem tests_eq (x vxx u Y : Fp) (sign : Nat) :
    ((root x vxx u).bind fun x => finish x Y sign).isSome = rootTests x vxx u sign := by
  unfold rootTests
  by_cases h1 : vxx = u
  · rw [root, ite_eq_left h1, Option.bind_some, decide_eq_true h1, Bool.true_or, Bool.true_and, ite_eq_left h1]
    unfold finish
    by_cases h3 : x = 0 ∧ sign ≠ 0
    · rw [ite_eq_left h3, decide_eq_true h3.1, decide_eq_true h3.2]; rfl
    · rw [ite_eq_right h3]
      by_cases h4 : x = 0
      · rw [decide_eq_true h4, decide_eq_false fun h => h3 ⟨h4, h⟩]; rfl
      · rw [decide_eq_false h4]; rfl
  · rw [root, ite_eq_right h1, decide_eq_false h1, Bool.false_or, ite_eq_right h1]
    by_cases h2 : vxx = 0 - u
    · rw [ite_eq_left h2, Option.bind_some, decide_eq_true h2, Bool.true_and]
      unfold finish
      by_cases h3 : x * sqrtM1 = 0 ∧ sign ≠ 0
      · rw [ite_eq_left h3, decide_eq_true h3.1, decide_eq_true h3.2]; rfl
      · rw [ite_eq_right h3]
        by_cases h4 : x * sqrtM1 = 0
        · rw [decide_eq_true h4, decide_eq_false fun h => h3 ⟨h4, h⟩]; rfl
        · rw [decide_eq_false h4]; rfl
    · rw [ite_eq_right h2, decide_eq_false h2]; rfl

/-- **The routine's tests**, in its order: `y < p` (`yp_run`), `v x² = u` or `v x² = −u`
(`st_spec`), not `x = 0` with the sign set (`z_spec`, `s_spec`). -/
def decTests (y sign : Nat) : Bool :=
  let Y := toF y
  let u := Y * Y - 1
  let v := Y * Y * d + 1
  let v3 := v * v * v
  let x := (v3 * v3 * v * u) ^ ((p - 5) / 8) * v3 * u
  decide (y < p) && rootTests x (x * x * v) u sign

/-- `decodeCode` succeeds exactly when the routine's tests pass. -/
theorem decodeCode_isSome (y sign : Nat) : (decodeCode y sign).isSome = decTests y sign := by
  unfold decodeCode decTests
  by_cases hp : p ≤ y
  · rw [ite_eq_left hp, decide_eq_false (Nat.not_lt.mpr hp)]; rfl
  · rw [ite_eq_right hp, decide_eq_true (Nat.lt_of_not_le hp), Bool.true_and]
    exact tests_eq _ _ _ _ _

/-- The status words: `movs r0, #0` on success, `movs r0, #1` on a rejection. -/
theorem movImm_r0 (s : State) (k : BitVec 8) : ((Instr.movImm 0 k).next s).regs 0 = k.setWidth 32 := by
  have e0 : LowReg.toReg 0 = 0 := rfl
  simp [Instr.next, Instr.exec, State.setReg, State.setNZ, e0]

/-- The status words at `0x2262` (success, then `b` to the epilogue) and `0x2266` (rejection). -/
theorem stat_at (b : Build) : seqAt b.bytes 0x2262 [.movImm 0 0] = true ∧ seqAt b.bytes 0x2266 [.movImm 0 1] = true := by
  cases b <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- **The status of `m0c_ge_decompress`**: with `r0` set by the exit the tests choose, `r0 = 0`
exactly when the specification decodes the 32 input bytes. -/
theorem dec_status {l : List (BitVec 8)} (hl : l.length = 32) {r : Word}
    (hr : r = if decTests (decodeInt l % 2 ^ 255) (decodeInt l / 2 ^ 255) then 0#32 else 1#32) :
    r = 0#32 ↔ (Spec.Ed25519.decodePoint l).isSome = true := by
  have hd := Ed25519Bytes.decodeInt_lt l
  rw [hl] at hd
  rw [← Option.isSome_map (f := ofSpec), decodePoint_eq, Nat.mod_eq_of_lt (a := decodeInt l / 2 ^ 255) (by omega),
    decodeCode_isSome, hr]
  cases decTests _ _
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

end

end M0Crypto.Release.Ed25519DecompressProg
