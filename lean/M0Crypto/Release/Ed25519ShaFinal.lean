import M0Crypto.Release.Ed25519ShaUpdate
import M0Crypto.Release.Ed25519Sha512Pairs

set_option linter.unusedSimpArgs false

/-!
# `m0c_sha512_final`

The context at `r0` holds the stream `M` (`ShaCtx`). The routine pads the buffer: `0x80` after the
pending bytes, zeros to byte 112 of the block (to its end and a block first, when they do not fit),
the 128-bit big-endian bit length (`length_bytes`), the last block, and stores the eight words of
`H` big-endian at `r1` (`bytesBE_pair`): `sha512 M`. The two zero loops are one loop at two
positions (`zl_run`).
-/

namespace M0Crypto.Release.Ed25519ShaFinal

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Footprint
open M0Crypto.Release.BlockEffect
open M0Crypto.Sym (SExpr SBool SMem)
open M0Crypto.Release.TraceSpec (InStackWindow AtOrAboveSp BelowEntry)
open M0Crypto.Artifacts
open M0Crypto.Release.Ed25519Sha512Block (blockR blockPub blockE hOf blkOf)
open M0Crypto.Release.RoutineBranch (cmpImm_flags cmpReg_flags cond_eq cond_ne cond_hi)
open M0Crypto.Release.Ed25519ShaUpdate (ShaCtx Ct full hash_block hash_append hOf_congr Same196 adr cw spA sg sq bA
  ofs_ne rd4 rd_w8 blk_of hOf_of at_regs compress_size inc dec1 beq0 and127 same_of take_full)

/-! ## Code -/

abbrev O : Nat := Ed25519Compact.sha512_final

/-- `r0 + 180`: the length field. -/
def bL : SExpr := .add (cw 180) (.reg0 0)

def s0 := sg [.strSp 0 0, .strSp 1 1] [] [(spA 0, 8)]
def s1 : Seg :=
  { g := [.memImm .ldr 3 0 0, .movImm 4 127, .dp .ands 4 3, .addImm8 4 68],
    al := [(.reg0 0, 4)], wg := [], rg := [(.reg0 0, 4)], As := [.reg0 0] }
def s2 : Seg :=
  { g := [.movImm 5 0x80, .memReg .strb 5 0 4, .addImm8 4 1, .movImm 5 0, .movImm 6 180],
    al := [(bA, 1)], wg := [(bA, 1)], rg := [], As := [bA] }
def sK := sq [.dp .cmp 4 6]
def s3 := sq [.movImm 6 196]
def sW : Seg := { g := [.memReg .strb 5 0 4, .addImm8 4 1], al := [(bA, 1)], wg := [(bA, 1)], rg := [], As := [bA] }
def sG1 := sq [.movImm 1 68, .addReg 1 1 0, .addImm8 0 4]
def sR1 := sg [.ldrSp 0 0, .movImm 4 68, .movImm 5 0, .movImm 6 180] [(spA 0, 4)] []
/-- The length field. -/
def sLn : Seg :=
  { g := [.memImm .ldr 3 0 0, .lsrImm 1 3 29, .lslImm 3 3 3, .rev 1 1, .rev 3 3, .movImm 4 180, .addReg 4 4 0,
      .movImm 2 0, .memImm .str 2 4 0, .memImm .str 2 4 1, .memImm .str 1 4 2, .memImm .str 3 4 3],
    al := [(.reg0 0, 4), (bL, 4)], wg := [(bL, 16)], rg := [(.reg0 0, 4)], As := [.reg0 0, bL] }
def sO := sg [.ldrSp 0 0, .ldrSp 1 1, .addImm8 0 4, .movImm 7 8] [(spA 0, 8)] []
def sL : Seg :=
  { g := [.ldm 0 0b1100, .rev 3 3, .rev 2 2, .stm 1 0b1000, .stm 1 0b0100, .subImm8 7 1],
    al := [(.reg0 0, 4), (.reg0 1, 4)], wg := [(.reg0 1, 8)], rg := [(.reg0 0, 8)], As := [.reg0 0, .reg0 1] }

/-! ## Layout -/

local notation "FR" => 12
def D : Nat := FR + Ed25519Sha512Pass.D

/-- The zero loop at `z`: `cmp r4, r6; beq exit; strb r5, [r0, r4]; adds r4, #1; b z`. -/
def zlSize : Nat := seqSize sK.g + brSize + seqSize sW.g + brSize

def oS0 : Nat := seqSize [.push 0 true, .subSp 2]
def oS1 : Nat := oS0 + seqSize s0.g
def oS2 : Nat := oS1 + seqSize s1.g
def oK0 : Nat := oS2 + seqSize s2.g
def oB0 : Nat := oK0 + seqSize sK.g
def oT : Nat := oB0 + brSize
def oZ1 : Nat := oT + seqSize s3.g
def oG1 : Nat := oZ1 + zlSize
def oR1 : Nat := oG1 + seqSize sG1.g + blSize
def oZ2 : Nat := oR1 + seqSize sR1.g
def oN2 : Nat := oZ2 + zlSize
def oG2 : Nat := oN2 + seqSize sLn.g
def oO : Nat := oG2 + seqSize sG1.g + blSize
def oL : Nat := oO + seqSize sO.g
def oP : Nat := oL + seqSize sL.g + brSize
def oN : Nat := oP + seqSize [.addSp 2, .pop 0 true]

def cs : List (Nat × Nat) := (O, O + oN) :: blockR.code

section ok
variable (B : List (BitVec 8)) (BS : Nat) [CodeBytes B BS]

def segAt (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && (sglueOk cs s.g (O + o) FR D s.al s.wg s.rg && traceOkE s.g s.As)
def brAt (o : Nat) (c : BitVec 4) (tgt : Nat) : Bool :=
  seqAt B (O + o) [.bcond c (brImm8 (O + o) (O + tgt))] && brOk (B := B) cs (O + o) (O + tgt) FR D (brImm8 (O + o) (O + tgt))
def siteAt (f : Routine) (o : Nat) (s : Seg) : Bool :=
  seqAt B (O + o) s.g && seqAt B (O + o + seqSize s.g) [.bl (blImm (O + o + seqSize s.g) f.entry)] &&
  siteOkE (BS := BS) cs f s (O + o) FR D (blImm (O + o + seqSize s.g) f.entry)
def jmpAt (o tgt : Nat) : Bool :=
  seqAt B (O + o) [.b (brImm11 (O + o) (O + tgt))] && jmpOk (B := B) cs (O + o) (O + tgt) FR D (brImm11 (O + o) (O + tgt))

/-- The zero loop's checks at `z`. -/
def zlAt (z : Nat) : Bool :=
  segAt B (z) sK && brAt B BS (z + seqSize sK.g) 0 (z + zlSize) && segAt B (z + seqSize sK.g + brSize) sW &&
  jmpAt B BS (z + seqSize sK.g + brSize + seqSize sW.g) z

def segL : List (Nat × Seg) := [(oS0, s0), (oS1, s1), (oS2, s2), (oK0, sK), (oT, s3), (oR1, sR1), (oN2, sLn), (oO, sO), (oL, sL)]

/-- The decided checks of a build. -/
structure Ok : Prop where
  segs : segL.all (fun p => segAt B p.1 p.2) = true
  b0 : brAt B BS oB0 9 oZ2 = true
  z1 : zlAt B BS oZ1 = true
  z2 : zlAt B BS oZ2 = true
  c1 : siteAt B BS blockR oG1 sG1 = true
  c2 : siteAt B BS blockR oG2 sG1 = true
  bL : brAt B BS (oL + seqSize sL.g) 1 oL = true
  en : seqAt B O [.push 0 true, .subSp (BitVec.ofNat 7 2)] = true
  po : seqAt B (O + oP) [.addSp (BitVec.ofNat 7 2), .pop 0 true] = true
  cd : rangesSub [(O, O + 4), (O + oP, O + oP + 4)] cs = true
  sz : O + oN ≤ BS ∧ O % 2 = 0
end ok

open M0Crypto.Release.Ed25519 (Build)

theorem ok_c : @Ok _ _ Build.compact.codeBytes := by
  refine @Ok.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, segL, List.all_cons, List.all_nil, segAt, siteAt, brAt, jmpAt, zlAt, seqAt_eq_scan]) <;>
    decide +kernel

theorem ok_f : @Ok _ _ Build.fast.codeBytes := by
  refine @Ok.mk _ _ (Build.codeBytes _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try simp only [Build.bytes, Build.size, segL, List.all_cons, List.all_nil, segAt, siteAt, brAt, jmpAt, zlAt, seqAt_eq_scan]) <;>
    decide +kernel

theorem ok_b : ∀ b : Build, @Ok _ _ b.codeBytes
  | .compact => ok_c
  | .fast => ok_f

/-! ## Block effects -/

def ld0 : SExpr := .ld32 .mem0 (.reg0 0)
def ldS (n : Nat) : SExpr := .ld32 .mem0 (spA n)
def E0 : Eff := { mem := some (.w32 (.w32 .mem0 (spA 0) (.reg0 0)) (spA 4) (.reg0 1)) }
def E1 : Eff := { regs := [(3, ld0), (4, .add (.and (cw 127) ld0) (cw 68))] }
def E2 : Eff := { regs := [(4, .add (.reg0 4) (cw 1)), (5, cw 0), (6, cw 180)], mem := some (.w8 .mem0 bA (cw 128)) }
def EK : Eff := {}
def E3 : Eff := { regs := [(6, cw 196)] }
def EW : Eff := { regs := [(4, .add (.reg0 4) (cw 1))], mem := some (.w8 .mem0 bA (.reg0 5)) }
def EG : Eff := { regs := [(0, .add (.reg0 0) (cw 4)), (1, .add (cw 68) (.reg0 0))] }
def ER1 : Eff := { regs := [(0, ldS 0), (4, cw 68), (5, cw 0), (6, cw 180)] }
def lA (n : Nat) : SExpr := .add (.add (cw 180) (.reg0 0)) (cw n)
def ELn : Eff :=
  { regs := [(1, .rev (.lsr ld0 29)), (2, cw 0), (3, .rev (.lsl ld0 3)), (4, .add (cw 180) (.reg0 0))],
    mem := some (.w32 (.w32 (.w32 (.w32 .mem0 (lA 0) (cw 0)) (lA 4) (cw 0)) (lA 8) (.rev (.lsr ld0 29)))
      (lA 12) (.rev (.lsl ld0 3))) }
def EO : Eff := { regs := [(0, .add (ldS 0) (cw 4)), (1, ldS 4), (7, cw 8)] }
def ldA (n : Nat) : SExpr := .ld32 .mem0 (.add (.reg0 0) (cw n))
def EL : Eff :=
  { regs := [(0, .add (.reg0 0) (cw 8)), (1, .add (.reg0 1) (cw 8)), (2, .rev ld0), (3, .rev (ldA 4)),
      (7, .add (.reg0 7) (.const (-1#32)))], z := some (.isZero (.add (.reg0 7) (.const (-1#32)))),
    mem := some (.w32 (.w32 .mem0 (.reg0 1) (.rev (ldA 4))) (.add (.reg0 1) (cw 4)) (.rev ld0)) }

def effL : List (List Instr × Eff) := [(s0.g, E0), (s1.g, E1), (s2.g, E2), (sK.g, EK), (s3.g, E3), (sW.g, EW),
  (sG1.g, EG), (sR1.g, ER1), (sLn.g, ELn), (sO.g, EO), (sL.g, EL)]

theorem effs : effL.all (fun p => effOk p.1 p.2) = true := by decide +kernel

/-! ## The padded tail -/

open M0Crypto.Spec.Sha512 (compress H0 pad bytesBE)
open M0Crypto.Release.Ed25519CallProg (ctxSize)
open M0Crypto.Release.Ed25519Sha512Pairs (leBytes rev32 length_bytes bytesBE_pair pad_zeros)

section
variable (P : Nat → Word) (m1 : Mem)
/-- The stream length at the entry, and its bytes in the buffer. -/
def c0 : Nat := (P 3).toNat
def pp : Nat := c0 P % 128
/-- The zero bytes of the padding. -/
def zc (p : Nat) : Nat := if p ≤ 111 then 111 - p else 239 - p
/-- **The padded tail**: the buffered bytes, `0x80`, the zeros and the length field. -/
def Zs : List (BitVec 8) :=
  (List.range (pp P)).map (fun j => m1 (P 0 + BitVec.ofNat 32 (68 + j))) ++
    (0x80#8 :: (List.replicate (zc (pp P)) 0#8 ++ bytesBE 16 (8 * c0 P)))
/-- The whole blocks before the last. -/
def fL : Nat := if pp P ≤ 111 then 0 else 128
def H₀ : Array (BitVec 64) := hOf m1 (P 0 + 4#32)
end

section
variable {P : Nat → Word} {m1 : Mem}

theorem pp_lt : pp P < 128 := Nat.mod_lt _ (by decide)
theorem zc_eq : pp P + 1 + zc (pp P) = fL P + 112 := by
  have := pp_lt (P := P); simp only [zc, fL]; split <;> omega

theorem bytesBE_len (n x : Nat) : (bytesBE n x).length = n := by simp [bytesBE]

theorem Z_len : (Zs P m1).length = fL P + 128 := by
  have := zc_eq (P := P); simp only [Zs, List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_replicate, bytesBE_len]; omega

theorem Z_pend {j : Nat} (hj : j < pp P) : (Zs P m1).getD j 0 = m1 (P 0 + BitVec.ofNat 32 (68 + j)) := by
  rw [Zs, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj), List.getElem?_eq_getElem (by simpa using hj),
    Option.getD_some, List.getElem_map, List.getElem_range]

theorem Z_tail {i : Nat} : (Zs P m1).getD (pp P + i) 0 = (0x80#8 :: (List.replicate (zc (pp P)) 0#8 ++ bytesBE 16 (8 * c0 P))).getD i 0 := by
  rw [Zs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
  simp

theorem Z_80 : (Zs P m1).getD (pp P) 0 = 0x80#8 := by
  have := Z_tail (P := P) (m1 := m1) (i := 0); simpa using this

theorem Z_zero {i : Nat} (h1 : pp P + 1 ≤ i) (h2 : i < fL P + 112) : (Zs P m1).getD i 0 = 0#8 := by
  have := zc_eq (P := P)
  obtain ⟨k, rfl⟩ : ∃ k, i = pp P + 1 + k := ⟨i - (pp P + 1), by omega⟩
  rw [Nat.add_assoc, Z_tail, Nat.add_comm 1 k]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  have hk : k < zc (pp P) := by omega
  rw [List.getElem?_append_left (by simpa using hk), List.getElem?_replicate]; simp [hk]

theorem Z_len16 {k : Nat} : (Zs P m1).getD (fL P + 112 + k) 0 = (bytesBE 16 (8 * c0 P)).getD k 0 := by
  have := zc_eq (P := P)
  rw [show fL P + 112 + k = pp P + ((zc (pp P) + k) + 1) by omega, Z_tail]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left]

/-- **The padding**: with `M` in the context and `|M| < 2^32`, `pad M` is `M`'s whole blocks, then `Zs`. -/
theorem pad_eq {m0 : Mem} {M : List (BitVec 8)} (hM : ShaCtx m0 (P 0) M) (hl : M.length < 2 ^ 32)
    (h4 : read32 m0 (P 0) = P 3) (hc : Same196 m0 m1 (P 0)) : pad M = M.take (full M.length) ++ Zs P m1 := by
  obtain ⟨h0, -, hb⟩ := hM
  have hc0 : c0 P = M.length := by simp only [c0, ← h4, h0, BitVec.toNat_ofNat]; omega
  have hp : pp P = M.length % 128 := by simp only [pp, hc0]
  have hD : M.drop (full M.length) = (List.range (pp P)).map (fun j => m1 (P 0 + BitVec.ofNat 32 (68 + j))) := by
    refine List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_drop, full, hp]; omega) fun j h1 _ => ?_
    have hj : j < M.length % 128 := by simp only [List.length_drop, full] at h1; omega
    rw [List.getElem_map, List.getElem_range, List.getElem_drop, hc _ (by simp only [ctxSize]; omega), hb j hj,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [full]; omega), Option.getD_some]
  simp only [Spec.Sha512.pad]
  rw [Zs, ← hD, pad_zeros, ← List.append_assoc (M.take _), List.take_append_drop, hc0, hp]
  simp only [zc, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
end

/-! ## Stores -/

theorem gd_l {A C : List (BitVec 8)} {i : Nat} (h : i < A.length) : (A ++ C).getD i 0 = A.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem gd_r {A C : List (BitVec 8)} {i : Nat} (h : A.length ≤ i) : (A ++ C).getD i 0 = C.getD (i - A.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]
theorem leBytes_len (x : Word) : (leBytes x).length = 4 := rfl

/-- The byte `i` of a word store. -/
theorem w32_in (m : Mem) (a v : Word) {x i : Nat} (hi : i < 4) :
    write32 m (a + BitVec.ofNat 32 x) v (a + BitVec.ofNat 32 (x + i)) = (leBytes v).getD i 0 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp only [write32] <;> (repeat' split) <;> first | rfl | (exfalso; bv_omega)

/-- A byte apart from a word store. -/
theorem w32_out (m : Mem) (a v : Word) {x y : Nat} (h : y < x ∨ x + 4 ≤ y) (hx : x + 4 ≤ 2 ^ 32) (hy : y < 2 ^ 32) :
    write32 m (a + BitVec.ofNat 32 x) v (a + BitVec.ofNat 32 y) = m (a + BitVec.ofNat 32 y) := by
  simp only [write32]; (repeat' split) <;> first | rfl | (exfalso; bv_omega)

section
variable {m : Mem} {a : Word} {H : Array (BitVec 64)} {Y : List (BitVec 8)} {f b : Nat}
/-- A word stored at buffer position `b`. -/
theorem ct_w32 (c : Ct m a H Y f b) {x : Nat} (hx : x = 68 + b) (hb : b + 4 ≤ 128) {v : Word}
    (hv : ∀ i < 4, (leBytes v).getD i 0 = Y.getD (f + b + i) 0) : Ct (write32 m (a + BitVec.ofNat 32 x) v) a H Y f (b + 4) := by
  subst hx
  refine ⟨by rw [hOf_congr fun j hj => w32_out m a v (by omega) (by omega) (by omega)]; exact c.h, fun j hj => ?_⟩
  by_cases e : j < b
  · rw [w32_out m a v (by omega) (by omega) (by omega)]; exact c.bf j e
  · obtain ⟨i, rfl⟩ : ∃ i, j = b + i := ⟨j - b, by omega⟩
    rw [show 68 + (b + i) = 68 + b + i by omega, w32_in m a v (by omega), hv i (by omega), Nat.add_assoc]
end

theorem slots2 (m : Mem) (p x y : Word) :
    read32 (write32 (write32 m (p + BitVec.ofNat 32 0) x) (p + BitVec.ofNat 32 4) y) (p + BitVec.ofNat 32 0) = x ∧
    read32 (write32 (write32 m (p + BitVec.ofNat 32 0) x) (p + BitVec.ofNat 32 4) y) (p + BitVec.ofNat 32 4) = y :=
  ⟨by rw [read32_write32_add _ _ _ 4 0 (by omega) (by omega) (by omega), M0Crypto.Armv6M.read32_write32_same],
    M0Crypto.Armv6M.read32_write32_same _ _ _⟩

theorem l180 (a : Word) (n : Nat) : BitVec.ofNat 32 180 + a + BitVec.ofNat 32 n = a + BitVec.ofNat 32 (180 + n) := by
  rw [BitVec.add_comm (BitVec.ofNat 32 180) a, adr]

/-- The digest's bytes. -/
def Ob (X : Array (BitVec 64)) : List (BitVec 8) := X.toList.flatMap fun w => bytesBE 8 w.toNat

theorem fm_get (L : List (BitVec 64)) : ∀ (i q : Nat), i < L.length → q < 8 →
    (L.flatMap fun w => bytesBE 8 w.toNat).getD (8 * i + q) 0 = (bytesBE 8 (L.getD i 0).toNat).getD q 0 := by
  induction L with
  | nil => intro i q h; simp at h
  | cons w L ih =>
    intro i q hi hq
    rw [List.flatMap_cons]
    cases i with
    | zero => rw [Nat.mul_zero, Nat.zero_add, gd_l (by rw [bytesBE_len]; exact hq)]; rfl
    | succ i =>
      rw [gd_r (by rw [bytesBE_len]; omega), bytesBE_len, show 8 * (i + 1) + q - 8 = 8 * i + q by omega,
        ih i q (by simp at hi; omega) hq]; rfl

theorem fm_len (L : List (BitVec 64)) : (L.flatMap fun w => bytesBE 8 w.toNat).length = 8 * L.length := by
  induction L with
  | nil => rfl
  | cons w L ih => rw [List.flatMap_cons, List.length_append, ih, bytesBE_len, List.length_cons]; omega

theorem hOf_getD (m : Mem) (a : Word) {i : Nat} (hi : i < 8) :
    (hOf m a).toList.getD i 0 = Ed25519Sha512Exec.pairAt m (a + BitVec.ofNat 32 (8 * i)) := by
  simp [hOf, List.getD_eq_getElem?_getD, hi]

theorem hOf_len (m : Mem) (a : Word) : (hOf m a).toList.length = 8 := by simp [hOf]

/-- `cmp r4, r6`: `beq` and `bls`. -/
theorem cmp46 (u : State) {x y : Nat} (h4 : u.regs 4 = BitVec.ofNat 32 x) (h6 : u.regs 6 = BitVec.ofNat 32 y)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    condPassed 0 (execAll sK.g u) = decide (x = y) ∧ condPassed 9 (execAll sK.g u) = decide (x ≤ y) := by
  obtain ⟨c, z⟩ := cmpReg_flags 4 6 u
  refine ⟨?_, ?_⟩
  · rw [cond_eq]; show ((Instr.dp .cmp 4 6).next u).z = _; rw [z]; erw [h4, h6]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  · show (!((Instr.dp .cmp 4 6).next u).c || ((Instr.dp .cmp 4 6).next u).z) = _
    rw [c, z]; erw [h4, h6]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    by_cases e : x ≤ y <;> by_cases e' : x = y <;> simp [e, e'] <;> omega

theorem eff (i : Nat) {g : List Instr} {E : Eff} (hm : effL[i]? = some (g, E) := by rfl) : effOk g E = true :=
  by have := List.all_eq_true.mp effs _ (List.mem_of_getElem? hm); exact this

/-! ## The routine -/

/-- **`m0c_sha512_final`**: the 64 bytes at `r1` are `sha512 M` of the stream `M` in the context at `r0`. -/
def finR : Routine where
  entry := O
  code := cs
  stack := D
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0 ∧ Sep [⟨s.regs 0, ctxSize⟩] [⟨s.regs 1, 64⟩]
  wr := fun s => [⟨s.regs 0, ctxSize⟩, ⟨s.regs 1, 64⟩]
  rd := fun s => [⟨s.regs 0, ctxSize⟩]
  Post := fun s m _ => ∀ M, ShaCtx s.mem (s.regs 0) M → M.length < 2 ^ 32 →
    bytesAt m (s.regs 1) 64 = Spec.Sha512.sha512 M
  clob := Ed25519Routines.hiRegs

/-! ## The run state -/

section
variable (P : Nat → Word)
def Wc : List Rgn := [⟨P 2 - BitVec.ofNat 32 D, D - 4⟩, ⟨P 0, ctxSize⟩, ⟨P 1, 64⟩]
def Rc {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] (base : Word) : List Rgn :=
  codeR base :: ⟨P 2 - BitVec.ofNat 32 D, D⟩ :: [⟨P 0, ctxSize⟩]

/-- The layout: the frame below `sp`; the context and the output apart from it and each other. -/
structure Lay : Prop where
  sp : D ≤ (P 2).toNat ∧ (P 2).toNat % 4 = 0
  a4 : (P 0).toNat % 4 = 0 ∧ (P 1).toNat % 4 = 0
  ab : (P 0).toNat + ctxSize ≤ 2 ^ 32 ∧ (P 1).toNat + 64 ≤ 2 ^ 32
  w0 : (P 0).toNat + ctxSize ≤ (P 2).toNat - D ∨ (P 2).toNat ≤ (P 0).toNat
  w1 : (P 1).toNat + 64 ≤ (P 2).toNat - D ∨ (P 2).toNat ≤ (P 1).toNat
  d : (P 0).toNat + ctxSize ≤ (P 1).toNat ∨ (P 1).toNat + 64 ≤ (P 0).toNat

/-- The digest of the padded tail. -/
def A (m1 : Mem) : Array (BitVec 64) := Spec.Sha512.hash (H₀ P m1) (Zs P m1)
end

set_option hygiene false in
local notation "fp" => (P 2 - BitVec.ofNat 32 FR)

section
variable (P : Nat → Word) (m1 : Mem)

/-- Kept through the body: `sp`, the caller frame, the two slots and the stream length. -/
structure Cm (u : State) : Prop where
  r13 : u.regs 13 = fp
  fr : MemEq (Wc P) m1 u.mem
  s0 : read32 u.mem (fp + BitVec.ofNat 32 0) = P 0
  s1 : read32 u.mem (fp + BitVec.ofNat 32 4) = P 1
  n : read32 u.mem (P 0) = P 3

/-- Before position `j` of a zero loop to `e`, with `f` bytes of `Zs` hashed. -/
structure ZI (f e j : Nat) (u : State) : Prop where
  c : Cm P m1 u
  r0 : u.regs 0 = P 0
  r4 : u.regs 4 = BitVec.ofNat 32 (68 + j)
  r5 : u.regs 5 = 0#32
  r6 : u.regs 6 = BitVec.ofNat 32 (68 + e)
  ct : Ct u.mem (P 0) (H₀ P m1) (Zs P m1) f j
  je : j ≤ e
  e1 : e ≤ 128
  z0 : pp P + 1 ≤ f + j
  z1 : f + e ≤ fL P + 112

/-- Before pair `i` of the output. -/
structure OI (i : Nat) (u : State) : Prop where
  r0 : u.regs 0 = P 0 + BitVec.ofNat 32 (4 + 8 * i)
  r1 : u.regs 1 = P 1 + BitVec.ofNat 32 (8 * i)
  r7 : u.regs 7 = BitVec.ofNat 32 (8 - i)
  r13 : u.regs 13 = fp
  fr : MemEq (Wc P) m1 u.mem
  h : hOf u.mem (P 0 + 4#32) = A P m1
  ob : ∀ j < 8 * i, u.mem (P 1 + BitVec.ofNat 32 j) = (Ob (A P m1)).getD j 0
  i8 : i ≤ 8

variable (base : Word)
/-- The end of the body: the digest at `r1`. -/
def Qf (u : State) : Prop := u.pc = base + BitVec.ofNat 32 (O + oP) ∧ u.regs 13 = fp ∧
  bytesAt u.mem (P 1) 64 = Ob (A P m1)
end

section
variable {P : Nat → Word} {m1 : Mem} {u u' : State}

theorem Cm.same (c : Cm P m1 u) (hs : Same u u') : Cm P m1 u' :=
  ⟨(hs.2 13 (by decide)).trans c.r13, hs.1 ▸ c.fr, hs.1 ▸ c.s0, hs.1 ▸ c.s1, hs.1 ▸ c.n⟩
theorem Cm.regs (c : Cm P m1 u) (h13 : u'.regs 13 = fp) (hm : u'.mem = u.mem) : Cm P m1 u' :=
  ⟨h13, hm ▸ c.fr, hm ▸ c.s0, hm ▸ c.s1, hm ▸ c.n⟩
theorem Cm.grow (c : Cm P m1 u) {W : List Rgn} (h13 : u'.regs 13 = fp) (hm : MemEq W u.mem u'.mem)
    (hW : Sub W (Wc P)) (h0 : Sep [⟨fp + BitVec.ofNat 32 0, 4⟩] W) (h1 : Sep [⟨fp + BitVec.ofNat 32 4, 4⟩] W)
    (hn : Sep [⟨P 0, 4⟩] W) : Cm P m1 u' :=
  ⟨h13, c.fr.grow hm hW, by rw [hm.read32 h0]; exact c.s0, by rw [hm.read32 h1]; exact c.s1, by rw [hm.read32 hn]; exact c.n⟩
theorem ZI.same {f e j : Nat} (h : ZI P m1 f e j u) (hs : Same u u') : ZI P m1 f e j u' :=
  have e := fun (r : Reg) (hr : r.val ≠ 15) => hs.2 r hr
  ⟨h.c.same hs, (e 0 (by decide)).trans h.r0, (e 4 (by decide)).trans h.r4, (e 5 (by decide)).trans h.r5,
    (e 6 (by decide)).trans h.r6, hs.1 ▸ h.ct, h.je, h.e1, h.z0, h.z1⟩
theorem OI.same {i : Nat} (h : OI P m1 i u) (hs : Same u u') : OI P m1 i u' :=
  have e := fun (r : Reg) (hr : r.val ≠ 15) => hs.2 r hr
  ⟨(e 0 (by decide)).trans h.r0, (e 1 (by decide)).trans h.r1, (e 7 (by decide)).trans h.r7,
    (e 13 (by decide)).trans h.r13, hs.1 ▸ h.fr, hs.1 ▸ h.h, hs.1 ▸ h.ob, h.i8⟩

theorem ct0 : Ct m1 (P 0) (H₀ P m1) (Zs P m1) 0 (pp P) :=
  ⟨by rw [List.take_zero, Spec.Sha512.hash]; rfl, fun j hj => by rw [Nat.zero_add, Z_pend hj]⟩
end

/-! ## The trace -/

section
variable (Tb : Word → (Nat → Word) → List Event) (base : Word) (P : Nat → Word)

def bT (o : Nat) (s : Seg) (vs : List Word) : TrP := Tr.is (blockTrE s.g (base + BitVec.ofNat 32 (O + o)) s.As vs)
def rT (o : Nat) (c : BitVec 4) (tgt : Nat) (p : Bool) (ΨT ΨF : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), .bcond c (brImm8 (O + o) (O + tgt)), []⟩]) (Tr.cond p ΨT ΨF)
def jT (o tgt : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o), .b (brImm11 (O + o) (O + tgt)), []⟩]) Ψ
/-- The block call at `o`. -/
def cT (o : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base o sG1 []) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o + seqSize sG1.g),
    .bl (blImm (O + o + seqSize sG1.g) blockR.entry), []⟩])
    (Tr.cat (Tr.is (Tb base (pubOf [P 0 + 4#32, BitVec.ofNat 32 68 + P 0, fp]))) Ψ))
/-- Position `j` of the zero loop at `z` to `e`; `Ψx` after it. -/
def zB (z e : Nat) (Ψx : TrP) (j : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base z sK []) (rT base (z + seqSize sK.g) 0 (z + zlSize) (decide (j = e)) Ψx
    (Tr.cat (bT base (z + seqSize sK.g + brSize) sW [P 0 + BitVec.ofNat 32 (68 + j)])
      (jT base (z + seqSize sK.g + brSize + seqSize sW.g) z Ψ)))
def zT (z e j : Nat) (Ψx : TrP) : TrP := wTr (zB base P z e Ψx) Nat.succ 129 j
/-- Pair `i` of the output. -/
def oB (i : Nat) (Ψ : TrP) : TrP :=
  Tr.cat (bT base oL sL [P 0 + BitVec.ofNat 32 (4 + 8 * i), P 1 + BitVec.ofNat 32 (8 * i)])
    (rT base (oL + seqSize sL.g) 1 oL (decide (i + 1 < 8)) Ψ (Tr.is []))
/-- From the second zero loop at position `j`. -/
def t2 (j : Nat) : TrP :=
  zT base P oZ2 112 j (Tr.cat (bT base oN2 sLn [P 0, BitVec.ofNat 32 180 + P 0]) (cT Tb base P oG2
    (Tr.cat (bT base oO sO [fp]) (wTr (oB base P) Nat.succ 8 0))))
/-- **The body's trace**: a function of `base`, `r0`, `r1`, `sp` and the stream length. -/
def finTr : TrP :=
  Tr.cat (bT base oS0 s0 [fp]) (Tr.cat (bT base oS1 s1 [P 0]) (Tr.cat (bT base oS2 s2 [P 0 + BitVec.ofNat 32 (68 + pp P)])
    (Tr.cat (bT base oK0 sK []) (rT base oB0 9 oZ2 (decide (pp P ≤ 111)) (t2 Tb base P (pp P + 1))
      (Tr.cat (bT base oT s3 []) (zT base P oZ1 128 (pp P + 1) (cT Tb base P oG1
        (Tr.cat (bT base oR1 sR1 [fp]) (t2 Tb base P 0)))))))))
end

/-! ## The run -/

macro "fin_lay" L:ident : tactic =>
  `(tactic| (have := ($L).sp; have := ($L).a4; have := ($L).ab; have := ($L).w0; have := ($L).w1; have := ($L).d; have : D = 220 := rfl; have : ctxSize = 196 := rfl))
macro "fin_fp" : tactic => `(tactic| ((try simp only [Wc, Rc]); fp_tac))

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem Ok.sg (h : Ok B BS) (i : Nat) {o : Nat} {s : Seg} (hm : segL[i]? = some (o, s) := by rfl) : segAt B o s = true := by
  have := List.all_eq_true.mp h.segs _ (List.mem_of_getElem? hm); exact this

/-- The hypotheses of the run: the caller frame, the decided checks, the layout, the code at `m1`,
the call lemma of `m0c_sha512_block` with trace `Tb`. -/
structure Hy (base : Word) (P : Nat → Word) (m1 : Mem) (Tb : Word → (Nat → Word) → List Event) : Prop where
  F : Caller base (P 2) D (Wc P)
  ok : Ok B BS
  L : Lay P
  cd : CodeAt m1 base B
  bl : blockR.SpecT fun b s => Tr.is (Tb b (blockPub b s))

abbrev RF (base : Word) (P : Nat → Word) (u : State) (Q : State → Prop) (Ψ : TrP) : Prop :=
  ReachFT base (PcIn base cs) (Has (Rc P base)) (Has (Wc P)) (InStackWindow (P 2) D) u Q Ψ

variable {base : Word} {P : Nat → Word} {m1 : Mem} {Tb : Word → (Nat → Word) → List Event} {t : State}
  {Q : State → Prop}

theorem Hy.code (H : Hy base P m1 Tb) {u : State} (h : MemEq (Wc P) m1 u.mem) : CodeAt u.mem base B :=
  CodeAt.of_memEq H.cd h H.F.codeW

theorem Hy.cb (H : Hy base P m1 Tb) : base.toNat + BS ≤ 2 ^ 32 := by
  have h := H.F.codeW; simp only [codeR, Wc] at h; fp_simp at h; omega

theorem Hy.seg (H : Hy base P m1 Tb) {o : Nat} {s : Seg} (hk : segAt B o s = true) {Ψ : TrP} {vs : List Word}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp) (hfr : MemEq (Wc P) m1 t.mem)
    (hs : SGlueSides t (Rc P base) (Wc P) s.al s.wg s.rg) (hv : s.As.map (·.denote t) = vs)
    (kk : (execAll s.g t).pc = base + BitVec.ofNat 32 (O + o + seqSize s.g) → (execAll s.g t).regs 13 = fp →
      MemEq (sregions t s.wg) t.mem (execAll s.g t).mem → RF base P (execAll s.g t) Q Ψ) :
    RF base P t Q (Tr.cat (bT base o s vs) Ψ) := by
  rw [segAt, Bool.and_eq_true] at hk
  exact ReachFT.seg1 H.F s hk.1 hk.2 hpc h13 (H.code hfr) hs hv fun hp h13 _ hm => kk hp h13 hm

theorem Hy.br (H : Hy base P m1 Tb) {o tgt : Nat} {c : BitVec 4} (hb : brAt B BS o c tgt = true) {ΨT ΨF : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp) (p : Bool) (hc : condPassed c t = p)
    (kT : p = true → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + tgt) → RF base P u Q ΨT)
    (kF : p = false → ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + o + 2) → RF base P u Q ΨF) :
    RF base P t Q (rT base o c tgt p ΨT ΨF) := by
  simp only [brAt, Bool.and_eq_true] at hb
  exact ReachFT.br H.F (instrAt_of_seqAt hb.1) hb.2 hpc h13 p hc kT kF

theorem Hy.jmp (H : Hy base P m1 Tb) {o tgt : Nat} (hj : jmpAt B BS o tgt = true) {Ψ : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp)
    (kk : ∀ u, Same t u → u.pc = base + BitVec.ofNat 32 (O + tgt) → RF base P u Q Ψ) : RF base P t Q (jT base o tgt Ψ) := by
  simp only [jmpAt, Bool.and_eq_true] at hj
  exact ReachFT.jmp H.F (instrAt_of_seqAt hj.1) hj.2 hpc h13 kk

/-- **The zero loop** at `z` from position `j` to `e`. -/
theorem zl_run (H : Hy base P m1 Tb) {z f e j : Nat} (hz : zlAt B BS z = true) {Ψx : TrP} (hI : ZI P m1 f e j t)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + z))
    (hx : ∀ u, ZI P m1 f e e u → u.pc = base + BitVec.ofNat 32 (O + (z + zlSize)) → RF base P u Q Ψx) :
    RF base P t Q (zT base P z e j Ψx) := by
  have L := H.L; fin_lay L
  simp only [zlAt, Bool.and_eq_true] at hz
  obtain ⟨⟨⟨hk, hb⟩, hw⟩, hj⟩ := hz
  refine ReachT.wloop (I := fun j u => ZI P m1 f e j u ∧ u.pc = base + BitVec.ofNat 32 (O + z))
    (go := fun j => decide (j < e)) (fun j => e - j) (fun j h => by simp at h; omega) (fun j u Ψ hI' hc => ?_) _ j t
    (by have := hI.je; have := hI.e1; omega) ⟨hI, hpc⟩
  obtain ⟨I, hp⟩ := hI'
  have := I.je; have := I.e1
  refine H.seg hk hp I.c.r13 I.c.fr (by glue_tac [sK, sq]) (by simp [sK, sq]) fun hp1 h13 _ => ?_
  have I1 := I.same (same_of (eff 3) rfl rfl rfl u)
  have hz : condPassed 0 (execAll sK.g u) = decide (j = e) := by
    rw [(cmp46 u I.r4 I.r6 (by omega) (by omega)).1]; simp
  refine H.br hb (by at_pc hp1) h13 _ hz (fun hT u2 hs hpu => ?_) (fun hF u2 hs hpu => ?_)
  · have e' : j = e := by simpa using hT
    exact hx u2 (e' ▸ I1.same hs) hpu
  have hje : j < e := by have : j ≠ e := by simpa using hF
                         omega
  have I2 := I1.same hs
  refine H.seg hw (by at_pc hpu) I2.c.r13 I2.c.fr (by glue_tac [sW, bA, I2.r0, I2.r4, Wc, Rc])
    (by simp [sW, bA, SExpr.denote, I2.r0, I2.r4]) fun hp2 h132 hm => ?_
  have E := eff_run (eff 5) u2
  have J : ZI P m1 f e (j + 1) (execAll sW.g u2) := by
    have r := fun (r : Reg) (h1 : r.val ≠ 15) (h2 : r ∉ EW.clob) => E.reg r h1 h2
    have hW : sregions u2 sW.wg = [⟨P 0 + BitVec.ofNat 32 (68 + j), 1⟩] := by
      simp [sregions, sW, bA, SExpr.denote, I2.r0, I2.r4]
    refine ⟨I2.c.grow h132 hm (by rw [hW]; fin_fp) (by rw [hW]; fin_fp) (by rw [hW]; fin_fp) (by rw [hW]; fin_fp),
      ?_, ?_, ?_, ?_, ?_, by omega, I2.e1, by have := I2.z0; omega, I2.z1⟩
    · rw [r 0 (by decide) (by decide)]; exact I2.r0
    · rw [r 4 (by decide) (by decide)]; show u2.regs 4 + BitVec.ofNat 32 1 = _; rw [I2.r4, inc]; rfl
    · rw [r 5 (by decide) (by decide)]; exact I2.r5
    · rw [r 6 (by decide) (by decide)]; exact I2.r6
    · rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, bA, I2.r0, I2.r4, I2.r5]
      exact I2.ct.w8 (by omega) (by rw [Z_zero (by have := I2.z0; omega) (by have := I2.z1; omega)]; rfl)
  exact H.jmp hj (by at_pc hp2) h132 fun w hw hpw => hc (by simpa using hje) w ⟨J.same hw, hpw⟩

theorem Hy.site (H : Hy base P m1 Tb) {o : Nat} (hst : siteAt B BS blockR o sG1 = true) {Ψ : TrP}
    (hpc : t.pc = base + BitVec.ofNat 32 (O + o)) (h13 : t.regs 13 = fp) (hfr : MemEq (Wc P) m1 t.mem)
    (hsd : SiteSidesE blockR base sG1 (O + o) t (Rc P base) (Wc P))
    (hpre : blockR.Pre base (atCall base blockR sG1.g (O + o) t)) {pb : Nat → Word}
    (hb : blockPub base (atCall base blockR sG1.g (O + o) t) = pb)
    (kk : ∀ u, u.pc = base + BitVec.ofNat 32 (O + o + seqSize sG1.g + 4) → u.regs 13 = fp →
      MemEq (sregions t sG1.wg ++ blockR.win (atCall base blockR sG1.g (O + o) t) ::
        blockR.wr (atCall base blockR sG1.g (O + o) t)) t.mem u.mem →
      blockR.Post (atCall base blockR sG1.g (O + o) t) u.mem (u.regs 0) → RF base P u Q Ψ) :
    RF base P t Q (Tr.cat (bT base o sG1 []) (Tr.cat (Tr.is [⟨base + BitVec.ofNat 32 (O + o + seqSize sG1.g),
      .bl (blImm (O + o + seqSize sG1.g) blockR.entry), []⟩]) (Tr.cat (Tr.is (Tb base pb)) Ψ))) := by
  simp only [siteAt, Bool.and_eq_true] at hst
  exact ReachFT.siteE H.bl H.F sG1 hst.1.1 (instrAt_of_seqAt hst.1.2) hst.2 hpc (Hi.self t) h13 (H.code hfr) hsd
    rfl hpre (by rw [hb]) fun u hu _ h13 _ hm _ hp => kk u hu h13 hm hp

/-- **A block call**: the full buffer compressed into `H`. -/
theorem call_run (H : Hy base P m1 Tb) {o f : Nat} (hst : siteAt B BS blockR o sG1 = true) {Ψ : TrP}
    (hc : Cm P m1 t) (h0 : t.regs 0 = P 0) (hct : Ct t.mem (P 0) (H₀ P m1) (Zs P m1) f 128) (hf : f % 128 = 0)
    (hfl : f ≤ fL P) (hpc : t.pc = base + BitVec.ofNat 32 (O + o))
    (kk : ∀ u, Cm P m1 u → Ct u.mem (P 0) (H₀ P m1) (Zs P m1) (f + 128) 0 →
      u.pc = base + BitVec.ofNat 32 (O + o + seqSize sG1.g + 4) → RF base P u Q Ψ) :
    RF base P t Q (cT Tb base P o Ψ) := by
  have L := H.L; fin_lay L; have := H.cb; have : Ed25519Sha512Pass.D = 208 := rfl
  have E := eff_run (eff 6) t
  have a0 : (atCall base blockR sG1.g (O + o) t).regs 0 = P 0 + 4#32 := by
    rw [at_regs 0, E.reg 0 (by decide) (by decide)]; show t.regs 0 + BitVec.ofNat 32 4 = _; rw [h0]
  have a1 : (atCall base blockR sG1.g (O + o) t).regs 1 = BitVec.ofNat 32 68 + P 0 := by
    rw [at_regs 1, E.reg 1 (by decide) (by decide)]; show BitVec.ofNat 32 68 + t.regs 0 = _; rw [h0]
  have a13 : (atCall base blockR sG1.g (O + o) t).regs 13 = fp := by
    rw [at_regs 13, E.reg 13 (by decide) (by decide)]; exact hc.r13
  have am : (atCall base blockR sG1.g (O + o) t).mem = t.mem := E.mem _ rfl
  refine H.site hst hpc hc.r13 hc.fr ?_ ?_ (by simp only [blockPub, a0, a1, a13]) fun u3 hp3 h133 hm3 hpost => ?_
  · unfold SiteSidesE; generalize atCall base blockR sG1.g (O + o) t = a at a0 a1 a13 ⊢
    glue_tac [sq, sG1, Wc, Rc, blockR, a0, a1, a13, hc.r13]
  · show (_ : Word).toNat % 4 = 0 ∧ (_ : Word).toNat % 4 = 0; rw [a0, a1]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  generalize atCall base blockR sG1.g (O + o) t = a at a0 a1 a13 am hm3 hpost
  simp only [blockR, Routine.win, a0, a1, a13, Ed25519Sha512Pass.D, Ed25519Sha512Code.BFRAME] at hm3 hpost
  rw [am] at hpost
  have hW : sregions t sG1.wg ++ [⟨fp - BitVec.ofNat 32 (4 + 204), 4 + 204⟩, ⟨P 0 + 4#32, 8 * 8⟩] =
      [⟨fp - BitVec.ofNat 32 (4 + 204), 4 + 204⟩, ⟨P 0 + 4#32, 8 * 8⟩] := rfl
  rw [hW] at hm3
  have hZ := Z_len (P := P) (m1 := m1)
  refine kk u3 (hc.grow h133 hm3 (by fin_fp) (by fin_fp) (by fin_fp) (by fin_fp)) ⟨?_, fun j hj => absurd hj (by omega)⟩ hp3
  rw [hash_block hf (by omega), hOf_of (compress_size _ _) hpost, hct.h, blk_of hct (by omega)]

/-- **Pair `i` of the output**: the two words of `H`, each reversed, at `r1`. -/
theorem out_step (H : Hy base P m1 Tb) {i : Nat} {Ψ : TrP} (hI : OI P m1 i t) (hi : i < 8)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oL))
    (hg : i + 1 < 8 → ∀ u, OI P m1 (i + 1) u → u.pc = base + BitVec.ofNat 32 (O + oL) → RF base P u (Qf P m1 base) Ψ) :
    RF base P t (Qf P m1 base) (oB base P i Ψ) := by
  have L := H.L; fin_lay L
  have hW : sregions t sL.wg = [⟨P 1 + BitVec.ofNat 32 (8 * i), 8⟩] := by simp [sregions, sL, SExpr.denote, hI.r1]
  refine H.seg (H.ok.sg 8) hpc hI.r13 hI.fr (by glue_tac [sL, hI.r0, hI.r1, Wc, Rc]) (by simp [sL, SExpr.denote, hI.r0, hI.r1])
    fun hp1 h13 hm => ?_
  rw [hW] at hm
  have E := eff_run (eff 10) t
  have hmem : (execAll sL.g t).mem = write32 (write32 t.mem (P 1 + BitVec.ofNat 32 (8 * i))
      (revBytes (read32 t.mem (P 0 + BitVec.ofNat 32 (4 + 8 * i + 4))))) (P 1 + BitVec.ofNat 32 (8 * i + 4))
      (revBytes (read32 t.mem (P 0 + BitVec.ofNat 32 (4 + 8 * i)))) := by
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, ldA, ld0, cw, hI.r0, hI.r1, adr]
  have hpr : (hOf t.mem (P 0 + 4#32)).toList.getD i 0 =
      read32 t.mem (P 0 + BitVec.ofNat 32 (4 + 8 * i + 4)) ++ read32 t.mem (P 0 + BitVec.ofNat 32 (4 + 8 * i)) := by
    rw [hOf_getD _ _ hi]; simp only [Ed25519Sha512Exec.pairAt, adr]
  have r := fun (r : Reg) (h1 : r.val ≠ 15) (h2 : r ∉ EL.clob) => E.reg r h1 h2
  have J : OI P m1 (i + 1) (execAll sL.g t) := by
    refine ⟨?_, ?_, ?_, h13, hI.fr.grow hm (by fin_fp), ?_, fun j hj => ?_, by omega⟩
    · rw [r 0 (by decide) (by decide)]; show t.regs 0 + BitVec.ofNat 32 8 = _
      rw [hI.r0, adr, show 4 + 8 * i + 8 = 4 + 8 * (i + 1) by omega]
    · rw [r 1 (by decide) (by decide)]; show t.regs 1 + BitVec.ofNat 32 8 = _
      rw [hI.r1, adr, show 8 * i + 8 = 8 * (i + 1) by omega]
    · rw [r 7 (by decide) (by decide)]; show t.regs 7 + -1#32 = _; rw [hI.r7, dec1 (by omega)]; rfl
    · rw [hOf_congr (m := t.mem) fun j hj => hm.byte (by fin_fp)]; exact hI.h
    · by_cases e : j < 8 * i
      · rw [hm.byte (by fin_fp)]; exact hI.ob j e
      obtain ⟨q, rfl⟩ : ∃ q, j = 8 * i + q := ⟨j - 8 * i, by omega⟩
      rw [hmem, ← hI.h, Ob, fm_get _ i q (by rw [hOf_len]; exact hi) (by omega), hpr, bytesBE_pair]
      by_cases h4 : q < 4
      · rw [w32_out _ _ _ (by omega) (by omega) (by omega), w32_in _ _ _ h4, gd_l (by rw [leBytes_len]; exact h4)]
        rfl
      · rw [show 8 * i + q = 8 * i + 4 + (q - 4) by omega, w32_in _ _ _ (by omega),
          gd_r (by rw [leBytes_len]; omega), leBytes_len]; rfl
  have hz : condPassed 1 (execAll sL.g t) = decide (i + 1 < 8) := by
    rw [cond_ne, E.z _ rfl]; simp only [SBool.denote, SExpr.denote, hI.r7]
    rw [dec1 (by omega), beq0 (by omega)]
    by_cases e : i + 1 < 8 <;> simp [e] <;> omega
  refine H.br H.ok.bL (by at_pc hp1) h13 _ hz (fun hT u hs hpu => hg (by simpa using hT) u (J.same hs) hpu)
    fun hF u hs hpu => ReachT.done ⟨by at_pc hpu, (hs.2 13 (by decide)).trans h13, ?_⟩
  have e : i + 1 = 8 := by have : ¬ (i + 1 < 8) := by simpa using hF
                           omega
  have J' := J.same hs
  apply List.ext_getElem (by rw [bytesAt_length, Ob, fm_len, ← J'.h, hOf_len]) fun j h1 h2 => ?_
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [J'.ob j (by simp [bytesAt] at h1; omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem out_run (H : Hy base P m1 Tb) (hI : OI P m1 0 t) (hpc : t.pc = base + BitVec.ofNat 32 (O + oL)) :
    RF base P t (Qf P m1 base) (wTr (oB base P) Nat.succ 8 0) :=
  ReachT.wloop (I := fun i u => OI P m1 i u ∧ i < 8 ∧ u.pc = base + BitVec.ofNat 32 (O + oL))
    (go := fun i => decide (i + 1 < 8)) (fun i => 7 - i) (fun i h => by simp at h; omega)
    (fun i u Ψ hI' hc => out_step H hI'.1 hI'.2.1 hI'.2.2 fun hg u' hu hp => hc (by simpa using hg) u' ⟨hu, hg, hp⟩)
    _ 0 t (by omega) ⟨hI, by omega, hpc⟩

/-- **From the second zero loop**: the length field, the last block and the output. -/
theorem t2_run (H : Hy base P m1 Tb) {f j : Nat} (hf : f = fL P) (hI : ZI P m1 f 112 j t)
    (hpc : t.pc = base + BitVec.ofNat 32 (O + oZ2)) : RF base P t (Qf P m1 base) (t2 Tb base P j) := by
  have L := H.L; fin_lay L; have := H.cb
  subst hf
  refine zl_run H H.ok.z2 hI hpc fun u hu hpu => ?_
  have hW : sregions u sLn.wg = [⟨P 0 + BitVec.ofNat 32 180, 16⟩] := by
    simp [sregions, sLn, bL, SExpr.denote, hu.r0, cw, BitVec.add_comm]
  refine H.seg (H.ok.sg 6) (by at_pc hpu) hu.c.r13 hu.c.fr (by glue_tac [sLn, bL, hu.r0, cw, Wc, Rc])
    (by simp [sLn, bL, SExpr.denote, hu.r0, cw]) fun hp1 h13 hm => ?_
  rw [hW] at hm
  have E := eff_run (eff 8) u
  have hmem : (execAll sLn.g u).mem = write32 (write32 (write32 (write32 u.mem (P 0 + BitVec.ofNat 32 180) 0#32)
      (P 0 + BitVec.ofNat 32 184) 0#32) (P 0 + BitVec.ofNat 32 188) (revBytes (P 3 >>> 29)))
      (P 0 + BitVec.ofNat 32 192) (revBytes (P 3 <<< 3)) := by
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, lA, cw, ld0, hu.r0, hu.c.n, l180]
  have hv : ∀ w < 4, ∀ v : Word, v = [0#32, 0#32, rev32 (P 3 >>> 29), rev32 (P 3 <<< 3)].getD w 0 →
      ∀ i < 4, (leBytes v).getD i 0 = (Zs P m1).getD (fL P + (112 + 4 * w) + i) 0 := by
    intro w hw v hv i hi
    rw [show fL P + (112 + 4 * w) + i = fL P + 112 + (4 * w + i) by omega, Z_len16, c0, length_bytes, hv]
    rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl <;>
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  have c4 : Ct (execAll sLn.g u).mem (P 0) (H₀ P m1) (Zs P m1) (fL P) 128 := by
    rw [hmem]
    exact ct_w32 (ct_w32 (ct_w32 (ct_w32 hu.ct rfl (by decide) (hv 0 (by decide) _ rfl)) rfl (by decide)
      (hv 1 (by decide) _ rfl)) rfl (by decide) (hv 2 (by decide) _ rfl)) rfl (by decide) (hv 3 (by decide) _ rfl)
  have c1 := hu.c.grow h13 hm (by fin_fp) (by fin_fp) (by fin_fp) (by fin_fp)
  have r0' : (execAll sLn.g u).regs 0 = P 0 := by rw [E.reg 0 (by decide) (by decide)]; exact hu.r0
  refine call_run H H.ok.c2 c1 r0' c4 (by simp only [fL]; split <;> rfl) (Nat.le_refl _) (by at_pc hp1)
    fun u3 c3 ct3 hp3 => ?_
  have hA : hOf u3.mem (P 0 + 4#32) = A P m1 := by
    rw [ct3.h, List.take_of_length_le (by rw [Z_len]; omega), A]
  refine H.seg (H.ok.sg 7) (by at_pc hp3) c3.r13 c3.fr (by glue_tac [sO, sg, spA, cw, Wc, Rc, c3.r13])
    (by simp [sO, sg, SExpr.denote, c3.r13]) fun hp4 h134 hm4 => ?_
  have E7 := eff_run (eff 9) u3
  have vm : (execAll sO.g u3).mem = u3.mem := E7.mem _ rfl
  have J : OI P m1 0 (execAll sO.g u3) := by
    refine ⟨?_, ?_, ?_, h134, vm ▸ c3.fr, vm ▸ hA, fun j hj => absurd hj (by omega), by omega⟩
    · rw [E7.reg 0 (by decide) (by decide)]; show read32 u3.mem (u3.regs 13 + BitVec.ofNat 32 0) + BitVec.ofNat 32 4 = _
      rw [c3.r13, c3.s0]
    · rw [E7.reg 1 (by decide) (by decide)]; show read32 u3.mem (u3.regs 13 + BitVec.ofNat 32 4) = _
      rw [c3.r13, c3.s1]; exact (BitVec.add_zero _).symm
    · rw [E7.reg 7 (by decide) (by decide)]; rfl
  exact out_run H J (by at_pc hp4)

theorem same_tr {a b c : State} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.1.trans h1.1, fun r hr => (h2.2 r hr).trans (h1.2 r hr)⟩

/-- **The body** from the entry: `0x80`, the zeros (and a block first when the length field does
not fit), the length field, the last block and the output. -/
theorem fin_run (H : Hy base P m1 Tb) (q0 : t.regs 0 = P 0) (q1 : t.regs 1 = P 1) (q13 : t.regs 13 = fp)
    (qm : t.mem = m1) (qn : read32 m1 (P 0) = P 3) (hpc : t.pc = base + BitVec.ofNat 32 (O + oS0)) :
    RF base P t (Qf P m1 base) (finTr Tb base P) := by
  have L := H.L; fin_lay L; have := H.cb; have hp := pp_lt (P := P)
  have hfr : MemEq (Wc P) m1 t.mem := fun y _ => by rw [qm]
  have hW0 : sregions t s0.wg = [⟨fp + BitVec.ofNat 32 0, 8⟩] := by simp [sregions, s0, sg, spA, cw, SExpr.denote, q13]
  refine H.seg (H.ok.sg 0) hpc q13 hfr (by glue_tac [s0, sg, spA, cw, Wc, Rc, q13]) (by simp [s0, sg, SExpr.denote, q13])
    fun hp1 h13 hm => ?_
  rw [hW0] at hm
  have E := eff_run (eff 0) t
  have hmem : (execAll s0.g t).mem = write32 (write32 t.mem (fp + BitVec.ofNat 32 0) (P 0)) (fp + BitVec.ofNat 32 4) (P 1) := by
    rw [E.mem _ rfl]; simp only [SMem.denote, SExpr.denote, spA, cw, q13, q0, q1]
  have sl := slots2 t.mem fp (P 0) (P 1); rw [← hmem] at sl
  have C0 : Cm P m1 (execAll s0.g t) := ⟨h13, hfr.grow hm (by fin_fp), sl.1, sl.2, by rw [hm.read32 (by fin_fp), qm, qn]⟩
  have r0' : (execAll s0.g t).regs 0 = P 0 := by rw [E.reg 0 (by decide) (by decide)]; exact q0
  have ct1 : Ct (execAll s0.g t).mem (P 0) (H₀ P m1) (Zs P m1) 0 (pp P) :=
    Ct.memEq hm (by fin_fp) (by rw [qm]; exact ct0) (by omega)
  generalize execAll s0.g t = u1 at C0 r0' ct1 hp1
  -- the buffer position
  refine H.seg (H.ok.sg 1) (by at_pc hp1) C0.r13 C0.fr (by glue_tac [s1, r0', Wc, Rc]) (by simp [s1, SExpr.denote, r0'])
    fun hp2 h132 _ => ?_
  have E1 := eff_run (eff 1) u1
  have vm1 : (execAll s1.g u1).mem = u1.mem := E1.mem _ rfl
  have C1 := C0.regs h132 vm1
  have r0₁ : (execAll s1.g u1).regs 0 = P 0 := by rw [E1.reg 0 (by decide) (by decide)]; exact r0'
  have r4₁ : (execAll s1.g u1).regs 4 = BitVec.ofNat 32 (68 + pp P) := by
    rw [E1.reg 4 (by decide) (by decide)]; show (BitVec.ofNat 32 127 &&& read32 u1.mem (u1.regs 0)) + BitVec.ofNat 32 68 = _
    rw [r0', C0.n, show P 3 = BitVec.ofNat 32 (c0 P) by simp [c0], and127]; rfl
  have ct2 : Ct (execAll s1.g u1).mem (P 0) (H₀ P m1) (Zs P m1) 0 (pp P) := by rw [vm1]; exact ct1
  generalize execAll s1.g u1 = u2 at C1 r0₁ r4₁ ct2 hp2
  -- `0x80`
  have hW2 : sregions u2 s2.wg = [⟨P 0 + BitVec.ofNat 32 (68 + pp P), 1⟩] := by simp [sregions, s2, bA, SExpr.denote, r0₁, r4₁]
  refine H.seg (H.ok.sg 2) (by at_pc hp2) C1.r13 C1.fr (by glue_tac [s2, bA, r0₁, r4₁, Wc, Rc])
    (by simp [s2, bA, SExpr.denote, r0₁, r4₁]) fun hp3 h133 hm3 => ?_
  rw [hW2] at hm3
  have E2 := eff_run (eff 2) u2
  have C2 := C1.grow h133 hm3 (by fin_fp) (by fin_fp) (by fin_fp) (by fin_fp)
  have r0₂ : (execAll s2.g u2).regs 0 = P 0 := by rw [E2.reg 0 (by decide) (by decide)]; exact r0₁
  have r4₂ : (execAll s2.g u2).regs 4 = BitVec.ofNat 32 (68 + (pp P + 1)) := by
    rw [E2.reg 4 (by decide) (by decide)]; show u2.regs 4 + BitVec.ofNat 32 1 = _; rw [r4₁, inc]; rfl
  have r5₂ : (execAll s2.g u2).regs 5 = 0#32 := by rw [E2.reg 5 (by decide) (by decide)]; rfl
  have r6₂ : (execAll s2.g u2).regs 6 = BitVec.ofNat 32 180 := by rw [E2.reg 6 (by decide) (by decide)]; rfl
  have ct3 : Ct (execAll s2.g u2).mem (P 0) (H₀ P m1) (Zs P m1) 0 (pp P + 1) := by
    rw [E2.mem _ rfl]; simp only [SMem.denote, SExpr.denote, bA, r0₁, r4₁, cw]
    exact ct2.w8 (v := BitVec.ofNat 32 128) hp (by rw [Nat.zero_add, Z_80]; rfl)
  generalize execAll s2.g u2 = u3 at C2 r0₂ r4₂ r5₂ r6₂ ct3 hp3
  -- `cmp r4, r6; bls`
  refine H.seg (H.ok.sg 3) (by at_pc hp3) C2.r13 C2.fr (by glue_tac [sK, sq]) (by simp [sK, sq]) fun hp4 h134 _ => ?_
  have hs4 := same_of (eff 3) rfl rfl rfl u3
  have hb : condPassed 9 (execAll sK.g u3) = decide (pp P ≤ 111) := by
    rw [(cmp46 u3 r4₂ r6₂ (by omega) (by omega)).2]; simp only [decide_eq_decide]; omega
  refine H.br H.ok.b0 (by at_pc hp4) h134 _ hb (fun hT u hs hpu => ?_) (fun hF u hs hpu => ?_)
  · -- the length field fits
    have e : pp P ≤ 111 := by simpa using hT
    have hs' := same_tr hs4 hs
    refine t2_run H (f := 0) (by simp [fL, e]) ⟨C2.same hs', (hs'.2 0 (by decide)).trans r0₂, (hs'.2 4 (by decide)).trans r4₂,
      (hs'.2 5 (by decide)).trans r5₂, (hs'.2 6 (by decide)).trans r6₂, hs'.1 ▸ ct3, by omega, by omega, by omega,
      by simp [fL, e]⟩ hpu
  -- a block of zeros first
  have e : ¬ pp P ≤ 111 := by simpa using hF
  have hs' := same_tr hs4 hs
  refine H.seg (H.ok.sg 4) (by at_pc hpu) ((hs'.2 13 (by decide)).trans C2.r13) (hs'.1 ▸ C2.fr) (by glue_tac [s3, sq])
    (by simp [s3, sq]) fun hp5 h135 _ => ?_
  have E3 := eff_run (eff 4) u
  have I : ZI P m1 0 128 (pp P + 1) (execAll s3.g u) := by
    have vm : (execAll s3.g u).mem = u.mem := E3.mem _ rfl
    refine ⟨(C2.same hs').regs h135 vm, ?_, ?_, ?_, ?_, vm ▸ hs'.1 ▸ ct3, by omega, by omega, by omega, by simp [fL, e]⟩
    · rw [E3.reg 0 (by decide) (by decide)]; exact (hs'.2 0 (by decide)).trans r0₂
    · rw [E3.reg 4 (by decide) (by decide)]; exact (hs'.2 4 (by decide)).trans r4₂
    · rw [E3.reg 5 (by decide) (by decide)]; exact (hs'.2 5 (by decide)).trans r5₂
    · rw [E3.reg 6 (by decide) (by decide)]; rfl
  refine zl_run H H.ok.z1 I (by at_pc hp5) fun u4 hu hpu4 => ?_
  refine call_run H H.ok.c1 hu.c hu.r0 hu.ct (by decide) (by simp [fL, e]) (by at_pc hpu4) fun u5 c5 ct5 hp5 => ?_
  refine H.seg (H.ok.sg 5) (by at_pc hp5) c5.r13 c5.fr (by glue_tac [sR1, sg, spA, cw, Wc, Rc, c5.r13])
    (by simp [sR1, sg, SExpr.denote, c5.r13]) fun hp6 h136 _ => ?_
  have E5 := eff_run (eff 7) u5
  have vm : (execAll sR1.g u5).mem = u5.mem := E5.mem _ rfl
  refine t2_run H (f := 128) (by simp [fL, e]) ⟨c5.regs h136 vm, ?_, ?_, ?_, ?_, vm ▸ ct5, by omega, by omega, by omega,
    by simp [fL, e]⟩ (by at_pc hp6)
  · rw [E5.reg 0 (by decide) (by decide)]; show read32 u5.mem (u5.regs 13 + BitVec.ofNat 32 0) = _; rw [c5.r13, c5.s0]
  · rw [E5.reg 4 (by decide) (by decide)]; rfl
  · rw [E5.reg 5 (by decide) (by decide)]; rfl
  · rw [E5.reg 6 (by decide) (by decide)]; rfl
end

/-! ## The result -/

/-- **The digest**: from `ShaCtx` of `M` at the entry, the output is `sha512 M`. -/
theorem post_eq {m0 m1 : Mem} {P : Nat → Word} {M : List (BitVec 8)} (hM : ShaCtx m0 (P 0) M) (hl : M.length < 2 ^ 32)
    (h4 : read32 m0 (P 0) = P 3) (hc : Same196 m0 m1 (P 0)) : Ob (A P m1) = Spec.Sha512.sha512 M := by
  rw [Spec.Sha512.sha512, pad_eq hM hl h4 hc, hash_append _ _ _ (by rw [take_full]; simp only [full]; omega), ← hM.2.1,
    ← hOf_congr (fun j hj => hc _ (by simp only [ctxSize]; omega))]; rfl

/-! ## The stack effect -/

open M0Crypto.Release.StackEffect (Ef EffT frame_te GP SIR pass_of sir_pass above_sub reg_in reg_sub_above inRD_of
  site_gp jmp_gp br_gp InRD reg_split winsChk blkChk)
open M0Crypto.Release.Ed25519ShaUpdate (gp_fact reg_le q_gp)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The public values: `r0`, `r1`, `sp` and the stream length at `r0`. -/
def finPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 1, s.regs 13, read32 s.mem (s.regs 0)]
def finFp (base : Word) (P : Nat → Word) : Word → Prop := Has [codeR base, ⟨P 0, ctxSize⟩, ⟨P 1, 64⟩]
def finRq (base : Word) (P : Nat → Word) (y : Word) : Prop := Has [codeR base] y ∨ Region (P 0) (68 + pp P) y
def finWd (P : Nat → Word) : Word → Prop := Region (P 1) 64
/-- **The effect of `m0c_sha512_final`**: it reads the context's bytes before the buffer and its
pending bytes, and writes the 64 output bytes. -/
def finE (base : Word) (P : Nat → Word) : TrP := EffT D (finFp base P) (finRq base P) (finWd P) (P 2)

/-- The GP's hypotheses at public values `P` (as `frame_te`'s). -/
structure GH (base sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Prop where
  room : (sp0 - P 2).toNat + D ≤ n
  n32 : n < 2 ^ 32
  F : ∀ y, finFp base P y → BelowEntry sp0 n y → AtOrAboveSp sp0 (P 2) y
  R : ∀ y, finRq base P y → BelowEntry sp0 n y → U y
end

section
variable {sp0 : Word} {n : Nat} {U : Word → Prop} {P : Nat → Word}

def R0 (U : Word → Prop) (P : Nat → Word) (y : Word) : Prop := U y ∨ Region (P 2 - BitVec.ofNat 32 4) 4 y
/-- Known written: the slots, the context's first `68 + w` bytes and the output's first `o`. -/
def Kn (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (w o : Nat) (y : Word) : Prop :=
  R0 U P y ∨ (Region fp 8 y ∨ Region (P 0) (68 + w) y ∨ Region (P 1) o y) ∧ BelowEntry sp0 n y
abbrev KS (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) (w o : Nat) : Ef → Prop := SIR sp0 fp (Kn sp0 n U P w o)
abbrev Jf (sp0 : Word) (n : Nat) (U : Word → Prop) (P : Nat → Word) : Ef → Prop :=
  SIR sp0 fp fun y => R0 U P y ∨ finWd P y ∧ BelowEntry sp0 n y

theorem reg_one {a y : Word} {w j : Nat} (h : Region a (68 + max w (j + 1)) y) :
    Region a (68 + max w j) y ∨ Region (a + BitVec.ofNat 32 (68 + j)) 1 y := by
  by_cases hj : j < w
  · exact .inl (reg_le h (by omega))
  · rw [show 68 + max w (j + 1) = 68 + j + 1 by omega] at h
    rcases reg_split h with h | h
    · exact .inl (reg_le h (by omega))
    · exact .inr h

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word}

theorem GH.r16 (G : GH base sp0 n U P) : (sp0 - fp).toNat + Ed25519Sha512Pass.D ≤ n := by
  have := G.room; have := G.n32; have : Ed25519Sha512Pass.D = 208 := rfl; simp only [D] at *
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega
theorem GH.up (G : GH base sp0 n U P) {y : Word} (h : AtOrAboveSp sp0 (P 2) y) : AtOrAboveSp sp0 fp y :=
  above_sub h (by have := G.room; have := G.n32; simp only [D] at *; omega)
theorem GH.ctxo (G : GH base sp0 n U P) {y : Word} {x w : Nat} (h : Region (P 0 + BitVec.ofNat 32 x) w y)
    (hw : x + w ≤ ctxSize) (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.up (G.F y ⟨_, .tail _ (.head _), Rgn.of_region (reg_in h hw (by decide))⟩ he)
theorem GH.outo (G : GH base sp0 n U P) {y : Word} {x w : Nat} (h : Region (P 1 + BitVec.ofNat 32 x) w y)
    (hw : x + w ≤ 64) (he : BelowEntry sp0 n y) : AtOrAboveSp sp0 fp y :=
  G.up (G.F y ⟨_, .tail _ (.tail _ (.head _)), Rgn.of_region (reg_in h hw (by decide))⟩ he)
theorem GH.buf (G : GH base sp0 n U P) {y : Word} {x : Nat} (h : Region (P 0) x y) (hx : x ≤ 68 + pp P)
    (he : BelowEntry sp0 n y) : U y := G.R y (.inr (reg_le h hx)) he
theorem GH.code (G : GH base sp0 n U P) {y : Word} (h : Region base BS y) (he : BelowEntry sp0 n y) : U y :=
  G.R y (.inl ⟨_, .head _, Rgn.of_region h⟩) he
theorem GH.fr (G : GH base sp0 n U P) {y : Word} {d : Nat} (h : Region fp d y) (hd : d ≤ 12) : AtOrAboveSp sp0 fp y :=
  reg_sub_above h hd (by have := G.room; have := G.n32; simp only [D] at *; omega)

variable {Tb : Word → (Nat → Word) → List Event}

/-- **The zero loop's GP**: each zero joins the context's written prefix. -/
theorem GH.zl (G : GH base sp0 n U P) {z e w : Nat} {Ψx : TrP} {J : Ef → Prop} (he : e ≤ 128)
    (hx : GP sp0 n (KS sp0 n U P (max w e) 0) Ψx J) :
    ∀ f j, e - j < f → GP sp0 n (fun q => j ≤ e ∧ KS sp0 n U P (max w j) 0 q) (wTr (zB base P z e Ψx) Nat.succ f j) J := by
  refine GP.wloop (K := fun j q => j ≤ e ∧ KS sp0 n U P (max w j) 0 q) (go := fun j => decide (j < e)) (fun j => e - j)
    (fun j h => by simp at h; omega) fun j Ψ h => gp_fact fun hj => ?_
  refine GP.cat (q_gp (by decide) rfl (by decide) (by decide)) (br_gp _ (fun hT => ?_) fun hF => ?_)
  · have e' : j = e := by simpa using hT
    exact e' ▸ hx
  have hje : j < e := by have : j ≠ e := by simpa using hF
                         omega
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0 + BitVec.ofNat 32 (68 + j)]) (Wr := []) (Ww := [(0, 1)])
      rfl (by decide) (by decide) (by simp)
      (by pass_tac []; exact fun y h he => G.ctxo h (by simp only [ctxSize]; omega) he)))
    fun q h => h.mono (R' := Kn sp0 n U P (max w (j + 1)) 0) fun y hy => ?_) (jmp_gp (GP.pre (fun q h => ⟨by omega, h⟩)
      (h (by simpa using hje))))
  rcases hy with hy | ⟨h | h | h, hb⟩
  · exact .inl (.inl hy)
  · exact .inl (.inr ⟨.inl h, hb⟩)
  · rcases reg_one h with h | h
    · exact .inl (.inr ⟨.inr (.inl h), hb⟩)
    · exact .inr ⟨inRD_of (vs := [P 0 + BitVec.ofNat 32 (68 + j)]) rfl (List.mem_singleton_self _)
        (by decide : StackEffect.atomOf [bA] bA = some (0, 0#32)) rfl (by rw [BitVec.add_zero]; exact h), hb⟩
  · exact .inl (.inr ⟨.inr (.inr h), hb⟩)

/-- **A block call's GP**: the block reads the context and the full buffer. -/
theorem GH.call (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) {o : Nat} {Ψ : TrP} {J : Ef → Prop}
    (hk : GP sp0 n (KS sp0 n U P 128 0) Ψ J) : GP sp0 n (KS sp0 n U P 128 0) (cT Tb base P o Ψ) J := by
  refine site_gp (q_gp (by decide) rfl (by decide) (by decide)) rfl rfl rfl
    (show EffT _ _ _ _ fp _ from hbE base (pubOf [P 0 + 4#32, BitVec.ofNat 32 68 + P 0, fp])) G.r16 G.n32
    (fun y h _ => h.elim) (fun y h he => ?_) (GP.pre (fun q h => h.mono fun y hy => .inl hy) hk)
  rcases h with h | h | h
  · exact .inr ⟨.inr (.inl (reg_in (c := 4) (w := 64) h (by omega) (by omega))), he⟩
  · change Region (BitVec.ofNat 32 68 + P 0) 128 y at h
    rw [BitVec.add_comm] at h
    exact .inr ⟨.inr (.inl (reg_in h (by decide) (by decide))), he⟩
  · exact .inl (.inl (G.code h he))

/-- **The output loop's GP**: each pair joins the output's written prefix. -/
theorem GH.oloop (G : GH base sp0 n U P) :
    ∀ f i, 7 - i < f → GP sp0 n (fun q => i < 8 ∧ KS sp0 n U P 128 (8 * i) q) (wTr (oB base P) Nat.succ f i) (Jf sp0 n U P) := by
  refine GP.wloop (K := fun i q => i < 8 ∧ KS sp0 n U P 128 (8 * i) q) (go := fun i => decide (i + 1 < 8)) (fun i => 7 - i)
    (fun i h => by simp at h; omega) fun i Ψ h => gp_fact fun hi => ?_
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0 + BitVec.ofNat 32 (4 + 8 * i), P 1 + BitVec.ofNat 32 (8 * i)])
      (Wr := [(0, 8)]) (Ww := [(1, 8)]) rfl (by decide) (by decide)
      (by pass_tac []; exact fun y h he => .inr ⟨.inr (.inl (reg_in h (by omega) (by omega))), he⟩)
      (by pass_tac []; exact fun y h he => G.outo h (by omega) he)))
    fun q h => h.mono (R' := Kn sp0 n U P 128 (8 * (i + 1))) fun y hy => ?_) (br_gp _ (fun hT => ?_) fun hF => ?_)
  · rcases hy with hy | ⟨h | h | h, hb⟩
    · exact .inl (.inl hy)
    · exact .inl (.inr ⟨.inl h, hb⟩)
    · exact .inl (.inr ⟨.inr (.inl h), hb⟩)
    · rw [show 8 * (i + 1) = 8 * i + 8 by omega] at h
      rcases reg_split h with h | h
      · exact .inl (.inr ⟨.inr (.inr h), hb⟩)
      · exact .inr ⟨inRD_of (vs := [P 0 + BitVec.ofNat 32 (4 + 8 * i), P 1 + BitVec.ofNat 32 (8 * i)]) rfl
          (List.mem_singleton_self _) (by decide : StackEffect.atomOf [.reg0 0, .reg0 1] (.reg0 1) = some (1, 0#32)) rfl
          (by rw [BitVec.add_zero]; exact h), hb⟩
  · have hg : i + 1 < 8 := by simpa using hT
    exact GP.pre (fun q h => ⟨hg, h⟩) (h (by simpa using hg))
  · have e : i + 1 = 8 := by have : ¬ (i + 1 < 8) := by simpa using hF
                             omega
    refine GP.nil fun q h => h.mono fun y hy => ?_
    rcases hy with hy | ⟨h, hb⟩
    · exact .inl hy
    · exact .inr ⟨.inr (.inr (by rw [e]; exact h)), hb⟩

/-- **From the second zero loop**: the length field, the last block and the output. -/
theorem GH.t2 (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) {j w : Nat} (hj : j ≤ 112)
    (hw : w = j ∨ w = 128) : GP sp0 n (KS sp0 n U P w 0) (t2 Tb base P j) (Jf sp0 n U P) := by
  have hm : max w j = w := by omega
  refine GP.pre (fun q h => ⟨hj, hm ▸ h⟩) (G.zl (by decide) ?_ 129 j (by omega))
  have h112 : max w 112 = 112 ∨ max w 112 = 128 := by omega
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0, BitVec.ofNat 32 180 + P 0]) (Wr := [(0, 4)])
      (Ww := [(1, 16)]) rfl (by decide) (by decide)
      (by pass_tac []; exact fun y h he => .inr ⟨.inr (.inl (reg_le h (by omega))), he⟩)
      (by pass_tac []; exact fun y h he => G.ctxo (x := 180) (by rw [BitVec.add_comm]; exact h) (by decide) he)))
    fun q h => h.mono (R' := Kn sp0 n U P 128 0) fun y hy => ?_) (G.call hbE ?_)
  · rcases hy with hy | ⟨h | h | h, hb⟩
    · exact .inl (.inl hy)
    · exact .inl (.inr ⟨.inl h, hb⟩)
    · rcases h112 with e | e
      · rcases reg_split (x := 180) (w := 16) h with h | h
        · exact .inl (.inr ⟨.inr (.inl (by rw [e]; exact h)), hb⟩)
        · exact .inr ⟨inRD_of (vs := [P 0, BitVec.ofNat 32 180 + P 0]) rfl (List.mem_singleton_self _)
            (by decide : StackEffect.atomOf [.reg0 0, bL] bL = some (1, 0#32)) rfl
            (by rw [BitVec.add_zero, BitVec.add_comm]; exact h), hb⟩
      · exact .inl (.inr ⟨.inr (.inl (by rw [e]; exact h)), hb⟩)
    · exact .inl (.inr ⟨.inr (.inr h), hb⟩)
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [fp]) (Wr := [(0, 8)]) (Ww := []) rfl (by decide) (by decide)
      (by pass_tac []; exact fun y h he => .inr ⟨.inl h, he⟩) (by simp)))
    fun q h => h.mono fun y hy => .inl hy) ?_
  exact GP.pre (fun q h => ⟨by decide, h⟩) (G.oloop 8 0 (by decide))

/-- **The body's GP**: from the entry's `R0`, the context's bytes before the buffer and its pending bytes. -/
theorem GH.fin (G : GH base sp0 n U P) (hbE : ∀ b q, blockE (BS := BS) b q (Tb b q)) :
    GP sp0 n (SIR sp0 fp (R0 U P)) (finTr Tb base P) (Jf sp0 n U P) := by
  have hp := pp_lt (P := P)
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [fp]) (Wr := []) (Ww := [(0, 8)]) rfl (by decide) (by decide)
      (by simp) (by pass_tac []; exact fun y h _ => G.fr h (by omega))))
    fun q h => h.mono (R' := Kn sp0 n U P (pp P) 0) fun y hy => ?_) ?_
  · rcases hy with hy | ⟨h | h | h, hb⟩
    · exact .inl hy
    · exact .inr ⟨inRD_of (vs := [fp]) rfl (List.mem_singleton_self _)
        (by decide : StackEffect.atomOf [.reg0 13] (spA 0) = some (0, BitVec.ofNat 32 0)) rfl (by simpa using h), hb⟩
    · exact .inl (.inl (G.buf h (Nat.le_refl _) hb))
    · exact absurd h (by simp [Region])
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0]) (Wr := [(0, 4)]) (Ww := []) rfl (by decide) (by decide)
      (by pass_tac []; exact fun y h he => .inr ⟨.inr (.inl (reg_le h (by omega))), he⟩) (by simp)))
    fun q h => h.mono fun y hy => .inl hy) ?_
  refine GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [P 0 + BitVec.ofNat 32 (68 + pp P)]) (Wr := [])
      (Ww := [(0, 1)]) rfl (by decide) (by decide) (by simp)
      (by pass_tac []; exact fun y h he => G.ctxo h (by simp only [ctxSize]; omega) he)))
    fun q h => h.mono (R' := Kn sp0 n U P (pp P + 1) 0) fun y hy => ?_) ?_
  · rcases hy with hy | ⟨h | h | h, hb⟩
    · exact .inl (.inl hy)
    · exact .inl (.inr ⟨.inl h, hb⟩)
    · rcases reg_one (w := pp P) (j := pp P) (by rw [Nat.max_eq_right (by omega)]; exact h) with h | h
      · exact .inl (.inr ⟨.inr (.inl (by rw [Nat.max_self] at h; exact h)), hb⟩)
      · exact .inr ⟨inRD_of (vs := [P 0 + BitVec.ofNat 32 (68 + pp P)]) rfl (List.mem_singleton_self _)
          (by decide : StackEffect.atomOf [bA] bA = some (0, 0#32)) rfl (by rw [BitVec.add_zero]; exact h), hb⟩
    · exact .inl (.inr ⟨.inr (.inr h), hb⟩)
  refine GP.cat (q_gp (by decide) rfl (by decide) (by decide)) (br_gp _ (fun hT => ?_) fun hF => ?_)
  · have e : pp P ≤ 111 := by simpa using hT
    exact G.t2 hbE (by omega) (.inl rfl)
  refine GP.cat (q_gp (by decide) rfl (by decide) (by decide)) ?_
  refine GP.pre (fun q h => ⟨by omega, by rw [Nat.max_self]; exact h⟩) (G.zl (w := pp P + 1) (by decide) ?_ 129 _ (by omega))
  rw [Nat.max_eq_right (by omega)]
  refine G.call hbE (GP.cat (GP.post (sir_pass (by decide) (pass_of (vs := [fp]) (Wr := [(0, 4)]) (Ww := []) rfl (by decide)
    (by decide) (by pass_tac []; exact fun y h he => .inr ⟨.inl (reg_le h (by omega)), he⟩) (by simp)))
    fun q h => h.mono fun y hy => .inl hy) (G.t2 hbE (by omega) (.inr rfl)))
end
end

/-! ## The routine's TE -/

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

noncomputable def fin_te (ok : Ok B BS) (hb : blockR.TE blockPub (blockE (BS := BS))) : finR.TE finPub finE := by
  have hP : oP = 126 := rfl
  have hN : oN = 130 := rfl
  have hsz := ok.sz
  refine frame_te (f := finR) (pub := finPub) (mask := 0) (k := 2) (epi := O + oP) (spP := fun p => p 2)
    (Ψ := fun b p => finTr hb.T b p) (Fp := finFp) (Rq := finRq) (Wd := fun _ p => finWd p) (by decide) ok.en ok.po ok.cd
    (by simp only [finR]; refine ⟨hsz.2, ?_, ?_, ?_, by decide, by decide⟩ <;> omega) (fun _ _ => rfl)
    (fun base s e F t tpc t13 tr hm hc => ?_)
    (fun _ _ => by repeat (first | (apply wTr_uniq; intro _ _ _) | exact Tr.uniq_is _ | apply Tr.uniq_cat | apply Tr.uniq_cond | assumption))
    (fun _ _ => by repeat (first | (apply wTr_ex; intro _ _ _) | exact Tr.ex_is _ | apply Tr.ex_cat | apply Tr.ex_cond | assumption))
    (fun _ p y h => ⟨_, .tail _ (.tail _ (.head _)), Rgn.of_region h⟩)
    (fun b p sp0 n U hroom hn hF hR => by
      rw [show 4 * nSaved 0 + 4 * 2 = FR by decide, show 4 * nSaved 0 = 4 by decide]
      exact GH.fin ⟨hroom, hn, hF, hR⟩ hb.eff)
  generalize hP' : finPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 13 = P 2 ∧ read32 s.mem (P 0) = P 3 := by
    subst hP'; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨q0, q1, q13, q3⟩ := q
  have hpre := e.pre
  have hsW := e.sepWr; have hroom := e.room; have hsp4 := e.sp4
  simp only [finR, Routine.win, q0, q1, q13] at hpre hsW hroom hsp4
  fp_simp at hsW hpre
  have : D = 220 := rfl
  have L : Lay P := ⟨⟨hroom, hsp4⟩, ⟨hpre.1, hpre.2.1⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩
  fin_lay L
  have hW : lowWin finR 0 s :: finR.wr s = Wc P := by subst hP'; rfl
  rw [hW, q13] at F
  have t13' : t.regs 13 = fp := by rw [t13, q13]; rfl
  have H : Hy base P t.mem hb.T := ⟨F, ok, L, hc, hb.spec⟩
  have hsep : Sep [⟨P 0, ctxSize⟩] [saved 0 s] := by simp only [saved, q13, show 4 * nSaved 0 = 4 from rfl]; fp_tac
  have hs0 : Same196 s.mem t.mem (P 0) := fun j hj => hm _ (Sep.not_has hsep ⟨_, List.mem_singleton.mpr rfl, j, hj, rfl⟩)
  have qn : read32 t.mem (P 0) = P 3 := by
    have := hs0.rd (o := 0) (by decide); simp only [BitVec.add_zero] at this; rw [this, q3]
  refine ReachFT.mono (fin_run H ((tr 0 (by decide) (by decide)).trans q0) ((tr 1 (by decide) (by decide)).trans q1)
      t13' rfl qn (by rw [tpc]; rfl))
    (fun _ h => h) (fun _ h => ?_) (fun _ h => by rw [hW]; exact h)
    (fun _ h => by show InStackWindow (s.regs 13) _ _; rw [q13]; exact h) (fun u hq => ?_)
    (by subst hP'; exact fun _ h => h)
  · obtain ⟨r, hr, hy⟩ := h
    simp only [Rc, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, hy⟩
    · exact ⟨_, .tail _ (.head _), by simpa [Routine.win, finR, q13] using hy⟩
    · exact ⟨_, .tail _ (.tail _ (by simp only [finR, q0]; exact List.mem_singleton_self _)), hy⟩
  refine ⟨hq.1, by rw [hq.2.1, t13'], fun r h4 h11 _ hr => absurd (Ed25519Routines.mem_hiRegs h4 h11) hr, fun M hM hl => ?_⟩
  rw [q0] at hM; rw [q1, hq.2.2]
  exact post_eq hM hl q3 hs0
end

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_sha512_final` in each build**, with its effect. -/
noncomputable def sha512_final_te (b : Build) : letI := b.codeBytes; finR.TE finPub (@finE _ b.size b.codeBytes) :=
  letI := b.codeBytes
  fin_te (ok_b b) (Ed25519Sha512Block.sha512_block_te b)

/-! ## The `Callees` adapter -/

section
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Artifacts.Ed25519Compact (sha512_final)

/-- **The `.final n` field of `Callees`** for build `b`: `m0c_sha512_final`'s adapter and effect, at
relations whose context relation is `ShaCtx`. -/
noncomputable def finAd (b : Build) (Rs : Rels) (hR : Rs.ctx = ShaCtx) (n : List SV) :
    @AdE Rs b.bytes b.size b.codeBytes (eaS (.final n)) := by
  letI := b.codeBytes
  refine Ad.ofTSpec { finR with code := footprint sha512_final } rfl rfl (show D = stackOf sha512_final by decide)
    ((sha512_final_te b).code (footprint sha512_final) (by decide))
    (fun base p tr h => EffT.mono h (show D ≤ stackOf sha512_final by decide) (fun y hy => ?_) (fun y hy => ?_) fun y hy => ?_)
    (semE (.final n))
    (fun c sp base st vs hg hv _ => ⟨hg.1 0 (.head _), hg.1 1 (.tail _ (.head _)), by
      have := hv.2.2 _ (List.mem_singleton_self _)
      simpa [rgnsC, SRgn.rgnC, ALen.val, ctxSize] using this⟩)
    (fun st => by simp [finR, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioFinal, ctxSize])
    (fun st => by simp [finR, rgnsC, SRgn.rgnC, ALen.val, eaS, calleeAt, ioFinal, ctxSize])
    fun c sp st m _ vs hv hi hp => ?_
  all_goals have iR : (eaS (.final n)).io.rd = [⟨0, 0, .k ctxSize⟩] := rfl
  all_goals have iW : (eaS (.final n)).io.wr = [⟨0, 0, .k ctxSize⟩, ⟨1, 0, .k 64⟩] := rfl
  all_goals have iI : (eaS (.final n)).io.ins = [(0, 0, .view (.ctx n))] := rfl
  all_goals have iO : (eaS (.final n)).io.outs = [(1, 0, .bytes 64)] := rfl
  all_goals have hc : ctxSize ≠ 0 := by decide
  · have r0 : (eaS (.final n)).reg p 0 = p 0 := rfl
    have r1 : (eaS (.final n)).reg p 1 = p 1 := rfl
    simp only [CalleeS.Fp, rgnsC, iR, iW, List.flatMap_cons, List.flatMap_nil, SRgn.rgnC, ALen.val, r0, r1,
      BitVec.add_zero, List.append_nil, hc, ↓reduceIte]
    obtain ⟨r, hr, hy⟩ := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, hy⟩
    · exact ⟨_, by simp, hy⟩
    · exact ⟨_, by simp, hy⟩
  · have r0 : (eaS (.final n)).reg p 0 = p 0 := rfl
    have rc : (eaS (.final n)).cnt p = (p 3).toNat := rfl
    simp only [CalleeS.Rq, CalleeS.iniIn, iI, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, ALen.val, r0, rc,
      BitVec.add_zero]
    exact hy
  · have r1 : (eaS (.final n)).reg p 1 = p 1 := rfl
    simp only [CalleeS.Wd, CalleeS.iniOut, iO, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, r1,
      BitVec.add_zero] at hy
    exact hy
  · change ∀ M, ShaCtx st.mem (st.regs 0) M → M.length < 2 ^ 32 → bytesAt m (st.regs 1) 64 = Spec.Sha512.sha512 M at hp
    simp only [InsRel, iI] at hi
    rcases vs with _ | ⟨v1, _ | ⟨v2, vs⟩⟩ <;> simp only [All2, and_false] at hi
    cases v1 <;> simp [Rel, In.kd] at hi
    obtain ⟨hM, hl⟩ := hi
    have hlim := hv.2.1 _ (List.mem_singleton_self _)
    simp only [OutsRel, iO, All2, semE, Rel, BitVec.add_zero, and_true]
    rw [hR] at hM
    exact hp _ hM (by rw [hl]; exact hlim)
end

end M0Crypto.Release.Ed25519ShaFinal
