import M0Crypto.Thumb.SpBlock
import M0Crypto.Proofs.Common
import M0Crypto.Spec.Blake2s
import M0Crypto.Release.Blake2sInstr

set_option linter.unusedSimpArgs false

namespace M0Crypto.Release.Blake2s

open M0Crypto.Armv6M (Word Reg LowReg State read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Proofs (toReg_0 toReg_1 toReg_2 toReg_3 toReg_4)
open M0Crypto.Spec.Blake2s (rotr)

/-- Half of `B2_G`: `a += b + m; d = (d ^ a) >>> kd; c += d; b = (b ^ c) >>> kb`, with the message word
in r4, the rotation counts loaded into r4. -/
def half (rb rt creg : LowReg) (kd kb : Nat) : List Instr :=
  [ .addReg 0 0 rb, .addReg 0 0 4, .dp .eors rt 0, .movImm 4 (BitVec.ofNat 8 kd), .dp .rors rt 4,
    .addReg creg creg rt, .dp .eors rb creg, .movImm 4 (BitVec.ofNat 8 kb), .dp .rors rb 4 ]

/-- The register-only half-step of `G` (RFC 7693 section 3.1, one of its two halves). -/
def halfG (a b c d x : Word) (kd kb : Nat) : Word × Word × Word × Word :=
  let a := a + b + x
  let d := rotr (d ^^^ a) kd
  let c := c + d
  let b := rotr (b ^^^ c) kb
  (a, b, c, d)

/-- The two scratch registers of `B2_G` (the macro's `r1` and `r3`). `rB` holds `v[b]`, `rT` a copy
of `v[d]`. Everything below is proved for any `rb`, `rt` meeting `Scr`; only the final
specialisation (`b2g`) names these. -/
def rB : LowReg := 1
def rT : LowReg := 3

/-- Register roles of a `B2_G`: scratch registers `rb`, `rt` and the row-c register `creg` are
pairwise distinct low registers other than r0 (v[a]) and r4 (message word / rotation count). -/
structure Scr (rb rt creg : LowReg) : Prop where
  b0 : rb.val ≠ 0
  b4 : rb.val ≠ 4
  t0 : rt.val ≠ 0
  t4 : rt.val ≠ 4
  c0 : creg.val ≠ 0
  c4 : creg.val ≠ 4
  bt : rb.val ≠ rt.val
  bc : rb.val ≠ creg.val
  tc : rt.val ≠ creg.val

theorem toReg_val (x : LowReg) : x.toReg.val = x.val := rfl

theorem ne_lo (x y : LowReg) (h : x.val ≠ y.val) : (x.toReg = y.toReg) = False := by
  apply eq_false; intro e; apply h; have := congrArg Fin.val e; simpa [LowReg.toReg] using this

theorem ne_lit (x : LowReg) (k : Reg) (h : x.val ≠ k.val) : (x.toReg = k) = False := by
  apply eq_false; intro e; apply h; have := congrArg Fin.val e; simpa [LowReg.toReg] using this

theorem ne_lit' (x : LowReg) (k : Reg) (h : x.val ≠ k.val) : (k = x.toReg) = False := by
  apply eq_false; intro e; apply h; have := congrArg Fin.val e; simpa [LowReg.toReg] using this.symm

theorem rorC_rotr (x : Word) (m : Nat) (c : Bool) (h0 : m ≠ 0) (h32 : m < 32) :
    (M0Crypto.Armv6M.rorC x m c).1 = rotr x m := by
  simp only [M0Crypto.Armv6M.rorC, h0, ite_false, Nat.mod_eq_of_lt h32, rotr]

theorem half_regs (s : State) (rb rt creg : LowReg) (kd kb : Nat) (hc : Scr rb rt creg)
    (hkd0 : kd ≠ 0) (hkd : kd < 32) (hkb0 : kb ≠ 0) (hkb : kb < 32) :
    let s' := execAll (half rb rt creg kd kb) s
    let q := halfG (s.regs 0) (s.reg rb) (s.reg creg) (s.reg rt) (s.regs 4) kd kb
    s'.regs 0 = q.1 ∧ s'.reg rb = q.2.1 ∧ s'.reg creg = q.2.2.1 ∧ s'.reg rt = q.2.2.2 ∧
    s'.regs 4 = BitVec.ofNat 32 kb ∧ s'.mem = s.mem ∧
    ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rb.val → r.val ≠ rt.val → r.val ≠ 4 →
      r.val ≠ creg.val → s'.regs r = s.regs r := by
  obtain ⟨b0, b4, t0, t4, c0, c4, bt, bc, tc⟩ := hc
  have z : ∀ x : LowReg, x.val ≠ 0 → (x.toReg = 0) = False := fun x h => ne_lit x 0 h
  have z' : ∀ x : LowReg, x.val ≠ 0 → ((0 : Reg) = x.toReg) = False := fun x h => ne_lit' x 0 h
  have f : ∀ x : LowReg, x.val ≠ 4 → (x.toReg = 4) = False := fun x h => ne_lit x 4 h
  have f' : ∀ x : LowReg, x.val ≠ 4 → ((4 : Reg) = x.toReg) = False := fun x h => ne_lit' x 4 h
  have c15 := toReg_ne15 creg
  have cnt : ∀ k : Nat, k < 32 → (BitVec.setWidth 32 (BitVec.ofNat 8 k)).toNat % 256 = k := by
    intro k hk; simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have wb : BitVec.setWidth 32 (BitVec.ofNat 8 kb) = BitVec.ofNat 32 kb := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have wd : BitVec.setWidth 32 (BitVec.ofNat 8 kd) = BitVec.ofNat 32 kd := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have mb : kb % 256 = kb := Nat.mod_eq_of_lt (by omega)
  have md : kd % 256 = kd := Nat.mod_eq_of_lt (by omega)
  have hm := execAll_mem (half rb rt creg kd kb) s (by simp [half, Instr.writesMem])
  simp only [half, execAll] at hm
  intro s' q
  simp only [s', q, half, execAll, halfG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 6
  · intro r h15 h0 hrb hrt h4 hcr
    have fr : ∀ k : Reg, k.val ≠ r.val → (r = k) = False := by
      intro k hk; apply eq_false; intro h; apply hk; rw [h]
    have r0 := fr 0 (by have : (0:Reg).val = 0 := rfl; omega)
    have r4 := fr 4 (by have : (4:Reg).val = 4 := rfl; omega)
    have rb' := fr rb.toReg (by rw [toReg_val]; omega)
    have rt' := fr rt.toReg (by rw [toReg_val]; omega)
    have rc := fr creg.toReg (by rw [toReg_val]; omega)
    have h15' : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    simp (config := {decide := true}) [regs_addReg, regs_eors, regs_rors, regs_movImm, h15', r0, r4, rb', rt', rc, M0Crypto.Armv6M.State.reg, toReg_0, toReg_4]
  all_goals first
    | exact hm
    | simp (config := {decide := true}) [regs_addReg, regs_eors, regs_rors, regs_movImm,
      M0Crypto.Armv6M.State.reg, toReg_0, toReg_4,
      z rb b0, z rt t0, z creg c0, z' rb b0, z' rt t0, z' creg c0,
      f rb b4, f rt t4, f creg c4, f' rb b4, f' rt t4, f' creg c4,
      ne_lo rb rt bt, ne_lo rt rb (Ne.symm bt), ne_lo rb creg bc, ne_lo creg rb (Ne.symm bc),
      ne_lo rt creg tc, ne_lo creg rt (Ne.symm tc),
      cnt kd hkd, cnt kb hkb, wb, wd, mb, md, rorC_rotr _ kd _ hkd0 hkd, rorC_rotr _ kb _ hkb0 hkb, c15, toReg_ne15 rb, toReg_ne15 rt]


/-! ## The whole `B2_G` macro -/

/-- Frame slot of `V(i)` as a word index (`ldr/str Rt, [sp, #4i]`). -/
def vSlot (i : Nat) : Nat := i

/-- Frame slot of `M(i)`: byte offset `32 + 4i`. -/
def mSlot (i : Nat) : Nat := 8 + i

/-- `LOAD_A a`: v0 lives in r8, v1..v7 in frame slots. -/
def loadA (a : Nat) : List Instr :=
  if a = 0 then [.movHi 0 8] else [Thumb.Instr.ldrSp 0 (BitVec.ofNat 8 (vSlot a))]

/-- `STORE_A a`. -/
def storeA (a : Nat) : List Instr :=
  if a = 0 then [.movHi 8 0] else [Thumb.Instr.strSp 0 (BitVec.ofNat 8 (vSlot a))]

/-- Loads of `B2_G`: v[a] unless already in r0, v[b], v[d], first message word. -/
def gPre (rb rt : LowReg) (a b x : Nat) (dreg : Reg) (haveA : Bool) : List Instr :=
  (if haveA then [] else loadA a) ++
  [Thumb.Instr.ldrSp rb (BitVec.ofNat 8 (vSlot b)), .movHi rt.toReg dreg,
   Thumb.Instr.ldrSp 4 (BitVec.ofNat 8 (mSlot x))]

/-- Stores of `B2_G`. -/
def gPost (rb rt : LowReg) (a b : Nat) (dreg : Reg) (keepA : Bool) : List Instr :=
  (if keepA then [] else storeA a) ++
  [Thumb.Instr.strSp rb (BitVec.ofNat 8 (vSlot b)), .movHi dreg rt.toReg]

/-- `B2_G a,b,creg,dreg,x,y,have_a,keep_a` (src/blake2s_compress.S) with scratch registers `rb`,
`rt`; the macro itself is `b2g`, which fixes them to `rB`, `rT`. -/
def b2gR (rb rt : LowReg) (a b : Nat) (creg : LowReg) (dreg : Reg) (x y : Nat)
    (haveA keepA : Bool) : List Instr :=
  gPre rb rt a b x dreg haveA ++ half rb rt creg 16 12 ++
  [Thumb.Instr.ldrSp 4 (BitVec.ofNat 8 (mSlot y))] ++ half rb rt creg 8 7 ++
  gPost rb rt a b dreg keepA

/-- `B2_G a,b,creg,dreg,x,y,have_a,keep_a` (src/blake2s_compress.S). -/
def b2g (a b : Nat) (creg : LowReg) (dreg : Reg) (x y : Nat) (haveA keepA : Bool) : List Instr :=
  b2gR rB rT a b creg dreg x y haveA keepA

theorem G_eq (a b c d x y : Word) :
    M0Crypto.Spec.Blake2s.G a b c d x y =
      (let q := halfG a b c d x 16 12; halfG q.1 q.2.1 q.2.2.1 q.2.2.2 y 8 7) := rfl


theorem sp_off (sp : Word) (k : Nat) (hk : k < 64) :
    sp + BitVec.ofNat 32 ((BitVec.ofNat 8 k).toNat * 4) = slot sp k := by
  simp only [slot, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem sp_off' (sp : Word) (k : Nat) (hk : k < 64) :
    sp + BitVec.ofNat 32 (k % 256 * 4) = slot sp k := by
  simp only [slot]; rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

/-- The d-row registers of `B2_G`: r9..r12 (`r8` holds v0). -/
structure DReg (dreg : Reg) : Prop where
  lo : 9 ≤ dreg.val
  hi : dreg.val ≤ 12

theorem gPre_regs (s : State) (rb rt : LowReg) (a b x : Nat) (dreg : Reg) (haveA : Bool)
    (ha : a < 8) (hb : b < 8) (hx : x < 16) (hd : DReg dreg)
    (b0 : rb.val ≠ 0) (b4 : rb.val ≠ 4) (t0 : rt.val ≠ 0) (t4 : rt.val ≠ 4) (bt : rb.val ≠ rt.val) :
    let s' := execAll (gPre rb rt a b x dreg haveA) s
    s'.regs 0 = (if haveA then s.regs 0 else if a = 0 then s.regs 8 else
        read32 s.mem (slot (s.regs 13) a)) ∧
    s'.reg rb = read32 s.mem (slot (s.regs 13) b) ∧
    s'.reg rt = s.regs dreg ∧
    s'.regs 4 = read32 s.mem (slot (s.regs 13) (8 + x)) ∧
    s'.mem = s.mem ∧
    ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rb.val → r.val ≠ rt.val → r.val ≠ 4 →
      s'.regs r = s.regs r := by
  obtain ⟨h9, h12⟩ := hd
  have f : ∀ k : Reg, k.val ≠ dreg.val → (dreg = k) = False := by
    intro k hk; apply eq_false; intro e; apply hk; rw [e]
  have f' : ∀ k : Reg, k.val ≠ dreg.val → (k = dreg) = False := by
    intro k hk; apply eq_false; intro e; apply hk; rw [e]
  have hm := execAll_mem (gPre rb rt a b x dreg haveA) s (by cases haveA <;> by_cases a = 0 <;>
    simp [gPre, loadA, Instr.writesMem, *])
  have d15 : dreg ≠ 15 := fun h => by rw [h] at h12; exact absurd h12 (by decide)
  have z : ∀ x : LowReg, x.val ≠ 0 → (x.toReg = 0) = False := fun x h => ne_lit x 0 h
  have z' : ∀ x : LowReg, x.val ≠ 0 → ((0 : Reg) = x.toReg) = False := fun x h => ne_lit' x 0 h
  have f4 : ∀ x : LowReg, x.val ≠ 4 → (x.toReg = 4) = False := fun x h => ne_lit x 4 h
  have f4' : ∀ x : LowReg, x.val ≠ 4 → ((4 : Reg) = x.toReg) = False := fun x h => ne_lit' x 4 h
  have lo : ∀ x : LowReg, x.val < 8 := fun x => x.isLt
  have dB : ∀ x : LowReg, (dreg = x.toReg) = False := fun x => ne_lit' x dreg
      (by have := lo x; show x.val ≠ dreg.val; omega) |> fun h => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have dB' : ∀ x : LowReg, (x.toReg = dreg) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have e13 : ∀ x : LowReg, ((13 : Reg) = x.toReg) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have e13' : ∀ x : LowReg, (x.toReg = (13 : Reg)) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  intro s'
  refine ⟨?_, ?_, ?_, ?_, hm, ?_⟩
  all_goals first
    | (intro r h15 h0 hrb hrt h4
       have fr : ∀ k : Reg, k.val ≠ r.val → (r = k) = False := by
         intro k hk; apply eq_false; intro h; apply hk; rw [h]
       have r0 := fr 0 (by have : (0:Reg).val = 0 := rfl; omega)
       have r4 := fr 4 (by have : (4:Reg).val = 4 := rfl; omega)
       have rb' := fr rb.toReg (by rw [toReg_val]; omega)
       have rt' := fr rt.toReg (by rw [toReg_val]; omega)
       have h15' : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
       cases haveA <;> by_cases h0' : a = 0 <;>
       simp (config := {decide := true}) [s', gPre, loadA, execAll, regs_ldrSp, regs_movHi, h15', r0, r4, rb', rt',
         toReg_0, toReg_4, h0'])
    | (cases haveA <;> by_cases h0 : a = 0 <;>
       simp (config := {decide := true}) [s', gPre, loadA, execAll, regs_ldrSp, regs_movHi, mem_movHi, mem_ldrSp, M0Crypto.Armv6M.State.sp,
         M0Crypto.Armv6M.State.reg,
         vSlot, mSlot, sp_off _ _ (by omega : a < 64), sp_off _ _ (by omega : b < 64), sp_off' _ _ (by omega : a < 64), sp_off' _ _ (by omega : b < 64),
         sp_off _ _ (by omega : 8 + x < 64), sp_off' _ _ (by omega : 8 + x < 64), h0, toReg_0, toReg_4,
         z rb b0, z rt t0, z' rb b0, z' rt t0, f4 rb b4, f4 rt t4, f4' rb b4, f4' rt t4,
         ne_lo rb rt bt, ne_lo rt rb (Ne.symm bt), dB rb, dB rt, dB' rb, dB' rt, e13 rb, e13 rt, e13' rb, e13' rt,
         f 0 (by simp; omega), f 4 (by simp; omega), f 13 (by simp; omega), f' 0 (by simp; omega),
         f' 4 (by simp; omega), f' 13 (by simp; omega), d15, toReg_ne15 rb, toReg_ne15 rt])


theorem gPost_effect (s : State) (rb rt : LowReg) (a b : Nat) (dreg : Reg) (keepA : Bool)
    (ha : a < 8) (hb : b < 8) (hd : DReg dreg)
    (b0 : rb.val ≠ 0) (t0 : rt.val ≠ 0) (bt : rb.val ≠ rt.val) :
    let s' := execAll (gPost rb rt a b dreg keepA) s
    s'.mem = write32 (if keepA ∨ a = 0 then s.mem else
        write32 s.mem (slot (s.regs 13) a) (s.regs 0)) (slot (s.regs 13) b) (s.reg rb) ∧
    s'.regs 8 = (if ¬keepA ∧ a = 0 then s.regs 0 else s.regs 8) ∧
    s'.regs dreg = s.reg rt ∧
    ∀ r : Reg, r.val ≠ 15 → r.val ≠ 8 → r ≠ dreg → s'.regs r = s.regs r := by
  obtain ⟨h9, h12⟩ := hd
  have f : ∀ k : Reg, k.val ≠ dreg.val → (dreg = k) = False := by
    intro k hk; apply eq_false; intro e; apply hk; rw [e]
  have f' : ∀ k : Reg, k.val ≠ dreg.val → (k = dreg) = False := by
    intro k hk; apply eq_false; intro e; apply hk; rw [e]
  have d15 : dreg ≠ 15 := fun h => by rw [h] at h12; exact absurd h12 (by decide)
  have lo : ∀ x : LowReg, x.val < 8 := fun x => x.isLt
  have dB : ∀ x : LowReg, (dreg = x.toReg) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have dB' : ∀ x : LowReg, (x.toReg = dreg) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have z : ∀ x : LowReg, x.val ≠ 0 → (x.toReg = 0) = False := fun x h => ne_lit x 0 h
  have z' : ∀ x : LowReg, x.val ≠ 0 → ((0 : Reg) = x.toReg) = False := fun x h => ne_lit' x 0 h
  have e8 : ∀ x : LowReg, (x.toReg = 8) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  have e8' : ∀ x : LowReg, ((8 : Reg) = x.toReg) = False := fun x => by
        apply eq_false; intro e; have := lo x; have := congrArg Fin.val e; simp [LowReg.toReg] at this; omega
  intro s'
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases keepA <;> by_cases h0 : a = 0 <;>
    simp (config := {decide := true}) [s', gPost, storeA, execAll, mem_strSp, mem_movHi, regs_strSp, regs_movHi,
      M0Crypto.Armv6M.State.sp, M0Crypto.Armv6M.State.reg, vSlot,
      sp_off _ _ (by omega : a < 64), sp_off _ _ (by omega : b < 64),
      sp_off' _ _ (by omega : a < 64), sp_off' _ _ (by omega : b < 64), h0, toReg_0, f' 8 (by simp; omega),
      e8 rb, e8' rb, toReg_ne15 rb, ne_lit rb 0 b0, ne_lit' rb 0 b0]
  · cases keepA <;> by_cases h0 : a = 0 <;>
    simp (config := {decide := true}) [s', gPost, storeA, execAll, regs_strSp, regs_movHi, d15, h0, toReg_0,
      f 8 (by simp; omega), f' 8 (by simp; omega), f' 0 (by simp; omega), f 0 (by simp; omega),
      dB rt, dB' rt, e8 rt, e8' rt, toReg_ne15 rt]
  · cases keepA <;> by_cases h0 : a = 0 <;>
    simp (config := {decide := true}) [s', gPost, storeA, execAll, regs_strSp, regs_movHi, d15, h0, toReg_0,
      f 8 (by simp; omega), f' 8 (by simp; omega), f' 0 (by simp; omega), f 0 (by simp; omega),
      dB rt, dB' rt, e8 rt, e8' rt, toReg_ne15 rt, M0Crypto.Armv6M.State.reg]
  · intro r h15 h8 hne
    have h15' : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    have r8 : (r = 8) = False := by apply eq_false; intro h; apply h8; rw [h]; rfl
    cases keepA <;> by_cases h0 : a = 0 <;>
    simp (config := {decide := true}) [s', gPost, storeA, execAll, regs_strSp, regs_movHi, h15', r8, hne, h0]


open M0Crypto.Spec.Blake2s (G)

/-- **One `B2_G`** is the RFC 7693 `G` on the working vector: inputs `v[a]` (r0 if `haveA`, r8 if
`a = 0`, else frame slot `a`), `v[b]` (frame), `v[c]` (`creg`), `v[d]` (`dreg`) and the two message
words (frame slots `8 + x`, `8 + y`); outputs back in the same places, with `v[a]` left in r0
when `keepA`. The scratch registers `rb`, `rt` are arbitrary distinct low registers. -/
theorem b2gR_effect (s : State) (rb rt : LowReg) (a b x y : Nat) (creg : LowReg) (dreg : Reg)
    (haveA keepA : Bool)
    (ha : a < 8) (hb : b < 8) (hx : x < 16) (hy : y < 16) (hs : Scr rb rt creg) (hd : DReg dreg) :
    let s' := execAll (b2gR rb rt a b creg dreg x y haveA keepA) s
    let sp := s.regs 13
    let A := if haveA then s.regs 0 else if a = 0 then s.regs 8 else read32 s.mem (slot sp a)
    let q := G A (read32 s.mem (slot sp b)) (s.reg creg) (s.regs dreg)
      (read32 s.mem (slot sp (8 + x))) (read32 s.mem (slot sp (8 + y)))
    s'.regs 0 = q.1 ∧ s'.reg creg = q.2.2.1 ∧ s'.regs dreg = q.2.2.2 ∧
    s'.regs 8 = (if ¬keepA ∧ a = 0 then q.1 else s.regs 8) ∧
    s'.mem = write32 (if keepA ∨ a = 0 then s.mem else write32 s.mem (slot sp a) q.1)
      (slot sp b) q.2.1 ∧
    ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rb.val → r.val ≠ rt.val → r.val ≠ 4 → r.val ≠ 8 →
      r.val ≠ creg.val → r ≠ dreg → s'.regs r = s.regs r := by
  intro s' sp A q
  have hs0 := hs
  have hd' := hd
  obtain ⟨h9, h12⟩ := hd'
  obtain ⟨b0, b4, t0, t4, c0, c4, bt, bc, tc⟩ := hs
  have cv : creg.toReg.val = creg.val := rfl
  have bv : rb.toReg.val = rb.val := rfl
  have tv : rt.toReg.val = rt.val := rfl
  have cl : creg.val < 8 := creg.isLt
  have bl : rb.val < 8 := rb.isLt
  have tl : rt.val < 8 := rt.isLt
  -- stage 1: loads
  obtain ⟨p0, p1, p3, p4, pm, pf⟩ := gPre_regs s rb rt a b x dreg haveA ha hb hx hd b0 b4 t0 t4 bt
  generalize hs1 : execAll (gPre rb rt a b x dreg haveA) s = s1 at p0 p1 p3 p4 pm pf
  have sp1 : s1.regs 13 = sp := pf 13 (by decide) (by decide) (by show 13 ≠ rb.val; omega)
    (by show 13 ≠ rt.val; omega) (by decide)
  have c1 : s1.reg creg = s.reg creg := pf creg.toReg (by rw [cv]; omega) (by rw [cv]; omega)
    (by rw [cv]; omega) (by rw [cv]; omega) (by rw [cv]; omega)
  -- stage 2: first half
  obtain ⟨q0, q1, qc, q3, q4, qm, qf⟩ := half_regs s1 rb rt creg 16 12 hs0 (by decide) (by decide)
    (by decide) (by decide)
  generalize hs2 : execAll (half rb rt creg 16 12) s1 = s2 at q0 q1 qc q3 q4 qm qf
  have sp2 : s2.regs 13 = sp := by
    rw [qf 13 (by decide) (by decide) (by show 13 ≠ rb.val; omega) (by show 13 ≠ rt.val; omega)
      (by decide) (by show 13 ≠ creg.val; omega), sp1]
  have m2 : s2.mem = s.mem := by rw [qm, pm]
  -- stage 3: second message word
  obtain ⟨s3, hs3⟩ : ∃ s3, s3 = (Thumb.Instr.ldrSp 4 (BitVec.ofNat 8 (mSlot y))).next s2 := ⟨_, rfl⟩
  have l3 : ∀ r : Reg, r.val ≠ 15 → r.val ≠ 4 → s3.regs r = s2.regs r := by
    intro r h15 h4
    have h15' : r ≠ 15 := fun h => h15 (by rw [h]; rfl)
    have h4' : (r = LowReg.toReg 4) = False := by
      apply eq_false; intro h; apply h4; rw [h]; rfl
    simp only [hs3, regs_ldrSp _ _ _ _ h15', h4', ite_false]
  have s3_4 : s3.regs 4 = read32 s.mem (slot sp (8 + y)) := by
    rw [hs3, regs_ldrSp _ _ _ _ (by decide)]
    simp only [M0Crypto.Armv6M.State.sp, sp2, m2, mSlot, toReg_4, ite_true]
    rw [sp_off _ _ (by omega : 8 + y < 64)]
  have m3 : s3.mem = s.mem := by rw [hs3, mem_ldrSp, m2]
  have sp3 : s3.regs 13 = sp := by rw [l3 13 (by decide) (by decide), sp2]
  have c3 : s3.reg creg = s2.reg creg := l3 creg.toReg (by rw [cv]; omega) (by rw [cv]; omega)
  -- stage 4: second half
  obtain ⟨u0, u1, uc, u3, u4, um, uf⟩ := half_regs s3 rb rt creg 8 7 hs0 (by decide) (by decide)
    (by decide) (by decide)
  generalize hs4 : execAll (half rb rt creg 8 7) s3 = s4 at u0 u1 uc u3 u4 um uf
  have sp4 : s4.regs 13 = sp := by
    rw [uf 13 (by decide) (by decide) (by show 13 ≠ rb.val; omega) (by show 13 ≠ rt.val; omega)
      (by decide) (by show 13 ≠ creg.val; omega), sp3]
  have m4 : s4.mem = s.mem := by rw [um, m3]
  -- stage 5: stores
  obtain ⟨g_mem, g8, gd, gf⟩ := gPost_effect s4 rb rt a b dreg keepA ha hb hd b0 t0 bt
  have hs' : s' = execAll (gPost rb rt a b dreg keepA) s4 := by
    rw [← hs4, hs3, ← hs2, ← hs1]
    simp only [s', b2gR, execAll_append]; rfl
  -- the two halves compose to G
  have hq : (s4.regs 0, s4.reg rb, s4.reg creg, s4.reg rt) = (q.1, q.2.1, q.2.2.1, q.2.2.2) := by
    have e1 : (s1.regs 0, s1.reg rb, s1.reg creg, s1.reg rt, s1.regs 4) =
        (A, read32 s.mem (slot sp b), s.reg creg, s.regs dreg, read32 s.mem (slot sp (8 + x))) := by
      rw [p0, p1, p3, p4, c1]
    have e3 : (s3.regs 0, s3.reg rb, s3.reg creg, s3.reg rt) = (s2.regs 0, s2.reg rb, s2.reg creg, s2.reg rt) := by
      rw [l3 0 (by decide) (by decide), show s3.reg rb = s2.reg rb from
        l3 rb.toReg (by rw [bv]; omega) (by rw [bv]; omega),
        show s3.reg rt = s2.reg rt from l3 rt.toReg (by rw [tv]; omega) (by rw [tv]; omega), c3]
    simp only [Prod.mk.injEq] at e1 e3 ⊢
    obtain ⟨a1, b1, c1', d1, x1⟩ := e1
    obtain ⟨a3, b3, c3', d3⟩ := e3
    simp only [q, G_eq]
    rw [u0, u1, uc, u3, s3_4, a3, b3, c3', d3, q0, q1, qc, q3, a1, b1, c1', d1, x1]
    simp
  simp only [Prod.mk.injEq] at hq
  obtain ⟨hq0, hq1, hqc, hq3⟩ := hq
  rw [hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gf 0 (by decide) (by decide) (by intro h; have := congrArg Fin.val h; simp at this; omega)]; exact hq0
  · have : (execAll (gPost rb rt a b dreg keepA) s4).reg creg = s4.reg creg := gf creg.toReg
      (by rw [cv]; omega) (by rw [cv]; omega) (by intro h; have := congrArg Fin.val h; rw [cv] at this; omega)
    rw [this]; exact hqc
  · rw [gd]; exact hq3
  · rw [g8, hq0]
    by_cases hk : ¬keepA ∧ a = 0
    · simp [hk]
    · simp only [hk, ite_false]
      rw [uf 8 (by decide) (by decide) (by show 8 ≠ rb.val; omega) (by show 8 ≠ rt.val; omega)
          (by decide) (by show 8 ≠ creg.val; omega),
        l3 8 (by decide) (by decide), qf 8 (by decide) (by decide) (by show 8 ≠ rb.val; omega)
          (by show 8 ≠ rt.val; omega) (by decide) (by show 8 ≠ creg.val; omega)]
      exact pf 8 (by decide) (by decide) (by show 8 ≠ rb.val; omega) (by show 8 ≠ rt.val; omega)
        (by decide)
  · rw [g_mem, m4, sp4, hq0, hq1]
  · intro r h15 h0 hrb hrt h4 h8 hc hdr
    rw [gf r h15 h8 hdr, uf r h15 h0 hrb hrt h4 hc, l3 r h15 h4, qf r h15 h0 hrb hrt h4 hc,
      pf r h15 h0 hrb hrt h4]

/-- The macro as assembled: scratch registers `rB`, `rT` (r1, r3). -/
theorem b2g_effect (s : State) (a b x y : Nat) (creg : LowReg) (dreg : Reg) (haveA keepA : Bool)
    (ha : a < 8) (hb : b < 8) (hx : x < 16) (hy : y < 16) (hs : Scr rB rT creg) (hd : DReg dreg) :
    let s' := execAll (b2g a b creg dreg x y haveA keepA) s
    let sp := s.regs 13
    let A := if haveA then s.regs 0 else if a = 0 then s.regs 8 else read32 s.mem (slot sp a)
    let q := G A (read32 s.mem (slot sp b)) (s.reg creg) (s.regs dreg)
      (read32 s.mem (slot sp (8 + x))) (read32 s.mem (slot sp (8 + y)))
    s'.regs 0 = q.1 ∧ s'.reg creg = q.2.2.1 ∧ s'.regs dreg = q.2.2.2 ∧
    s'.regs 8 = (if ¬keepA ∧ a = 0 then q.1 else s.regs 8) ∧
    s'.mem = write32 (if keepA ∨ a = 0 then s.mem else write32 s.mem (slot sp a) q.1)
      (slot sp b) q.2.1 ∧
    ∀ r : Reg, r.val ≠ 15 → r.val ≠ 0 → r.val ≠ rB.val → r.val ≠ rT.val → r.val ≠ 4 → r.val ≠ 8 →
      r.val ≠ creg.val → r ≠ dreg → s'.regs r = s.regs r :=
  b2gR_effect s rB rT a b x y creg dreg haveA keepA ha hb hx hy hs hd

end M0Crypto.Release.Blake2s
