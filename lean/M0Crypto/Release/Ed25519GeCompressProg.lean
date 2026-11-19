import M0Crypto.Release.Ed25519Safegcd
import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519SignRun
import M0Crypto.Release.Ed25519Encode

/-!
# `m0c_ge_compress` as a callee call program

`m0c_ge_compress(r0 = out, r1 = P)` (`gen_ed25519.py`, `emit_compress`): `ZI = Z^(p−2)` by
`m0c_fe_pow`, `X = x·ZI` and `Y = y·ZI` by `m0c_fe_mul`, both made canonical by `m0c_fe_canon`,
bit 255 of `Y` set to the parity of `X` (the `sign` block), and `Y` stored at `out` (sign's `store`
block). The point's coordinates are read in place as field elements of the entry bytes.

`PtR` is the point relation: the four coordinates at `a`, `a + 32`, `a + 64`, `a + 96` represent
the point that the specification's point represents. `cp_post` proves the 32 bytes at `out` are
`encodePoint P`, through `Ed25519Encode.compressCode_eq` and `encodePoint_rep`.
-/

namespace M0Crypto.Release.Ed25519GeCompressProg

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length MemEq Sep Has)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519FePow
open M0Crypto.Release.Ed25519FeCanon (canonS canonR canon_te canon_eff ioCanon)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Release.Field25519Congr (ModP)
open M0Crypto.Release.Field25519Reduce (pN)
open M0Crypto.Spec.Ed25519 (decodeInt encodeInt)
open M0Crypto.Release.Ed25519Words (wsum wsum_succ wsum_upd upd)
open M0Crypto.Release.Ed25519Field M0Crypto.Release.Ed25519Formulas M0Crypto.Release.Ed25519Bridge
open M0Crypto.Release.Ed25519EdwardsExtended (Ext)
open M0Crypto.Release.Ed25519Group (EdPt)
open M0Crypto.Release.Ed25519 (Build)

/-! ## The point relation -/

/-- The point's coordinates: `X`, `Y`, `Z`, `T` from `0`. -/
def CX : Nat := 0
def CY : Nat := 32
def CZ : Nat := 64
def CT : Nat := 96

/-- The extended coordinates at `a`. -/
def extAt (m : Mem) (a : Word) : Ext Fp :=
  ⟨toF (feVal m (a + BitVec.ofNat 32 CX)), toF (feVal m (a + BitVec.ofNat 32 CY)),
    toF (feVal m (a + BitVec.ofNat 32 CZ)), toF (feVal m (a + BitVec.ofNat 32 CT))⟩

/-- **The point relation**: the coordinates at `a` represent the point `P` represents. -/
def PtR (m : Mem) (a : Word) (P : Spec.Ed25519.Point) : Prop := ∃ A : EdPt, SpecRep P A ∧ Rep (extAt m a) A

theorem extAt_congr {m m' : Mem} {a : Word} (h : ∀ y, Has [⟨a, 128⟩] y → m' y = m y) : extAt m' a = extAt m a := by
  have hc : ∀ o, o + 32 ≤ 128 → feVal m' (a + BitVec.ofNat 32 o) = feVal m (a + BitVec.ofNat 32 o) := fun o ho =>
    Ed25519FeCanon.feVal_congr fun y ⟨_, hr, i, hi, hy⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      have hi : i < 32 := hi
      exact h y ⟨_, List.mem_singleton_self _, o + i, show o + i < 128 by omega, by rw [hy, ofNat_add_assoc]⟩
  simp only [extAt, hc CX (by decide), hc CY (by decide), hc CZ (by decide), hc CT (by decide)]

theorem PtR.memEq {W : List Footprint.Rgn} {m m' : Mem} {a : Word} {P : Spec.Ed25519.Point} (h : MemEq W m m')
    (hs : Sep [⟨a, 128⟩] W) (hp : PtR m a P) : PtR m' a P := by
  rw [PtR, extAt_congr fun y hy => h y (Footprint.Sep.not_has hs hy)]; exact hp

/-! ## `m0c_fe_canon`'s adapter -/

def canonV : List V → List V
  | [.f x] => [.f (x % Field25519Congr.p)]
  | _ => [.none]

theorem dec_fe (m : Mem) (a : Word) : decodeInt (bytesAt m a 32) = feVal m a := by
  have := decode_feVal m a; omega

/-- **`m0c_fe_canon`'s adapter** in build `b`: the canonical value of the element. -/
noncomputable def canonAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) canonS :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by decide) ((canon_te b).code _ (by decide +kernel)) (fun _ _ _ h => Ed25519Leaf.leaf_eff h (by decide +kernel) (by decide) (by decide))
    canonV (fun _ _ _ _ _ hg _ _ => hg.1 0 (by decide)) (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, canonS, calleeAt, ioCanon, canonR, Ed25519Leaf.leafR,
      Ed25519FeCanon.rg0, Routine.sregions, Sym.SExpr.denote])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, canonS, calleeAt, ioCanon, canonR, Ed25519Leaf.leafR,
      Ed25519FeCanon.rg0, Routine.sregions, Sym.SExpr.denote])
    fun _ _ st m _ vs _ hi hp => by
      rcases vs with _ | ⟨_ | x | _ | _ | _ | _, _ | _⟩ <;>
        simp only [InsRel, All2, canonS, calleeAt, ioCanon, Rel, In.kd, and_false, and_true] at hi
      simp only [OutsRel, All2, canonS, calleeAt, ioCanon, canonV, Rel, BitVec.add_zero, and_true] at hi ⊢
      obtain ⟨h1, -⟩ := hp
      unfold ModP at hi
      rw [Field25519Reduce.p_eq] at hi
      rw [h1, Int.natCast_emod, hi, show ((pN : Nat) : Int) = Field25519Congr.p from rfl]
      exact ⟨rfl, Int.emod_lt_of_pos _ (by decide)⟩

/-! ## The `sign` block -/

/-- The frame: `out`, the point's pointer, `Z⁻¹`, `x`, `y`. -/
def OUT : Nat := 0
def PT : Nat := 4
def ZI : Nat := 8
def XS : Nat := 40
def YS : Nat := 72

/-- Bit 255 of `Y` set to the parity of `X`. -/
def signB (X Y : List Byte) : List Byte :=
  if decodeInt Y < 2 ^ 255 then encodeInt (decodeInt Y + 2 ^ 255 * (decodeInt X % 2)) else Y

/-- `ldr r0, [sp, #x]; lsls r0, #31; ldr r1, [sp, #y + 28]; orrs r1, r0; str r1, [sp, #y + 28]`. -/
def signG : List Instr :=
  [.ldrSp 0 (BitVec.ofNat 8 (XS / 4)), .lslImm 0 0 31, .ldrSp 1 (BitVec.ofNat 8 ((YS + 28) / 4)), .dp .orrs 1 0,
   .strSp 1 (BitVec.ofNat 8 ((YS + 28) / 4))]

def ioSign : Iface :=
  { ins := [(13, XS, .view .fc), (13, YS, .view .fc)], outs := [(13, YS, .bytes 32)],
    wr := [⟨13, YS, .k 32⟩], rd := [⟨13, XS, .k 32⟩, ⟨13, YS, .k 32⟩], al := [13] }

/-- `orrs` of word 7 with the parity bit: an addition below bit 31, else the word. -/
theorem or_hi (w x : BitVec 32) :
    (w ||| (x <<< 31)).toNat = if w.toNat < 2 ^ 31 then w.toNat + 2 ^ 31 * (x.toNat % 2) else w.toNat := by
  have hx : (x <<< 31).toNat = 2 ^ 31 * (x.toNat % 2) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_or, hx]
  have hw := w.isLt
  generalize w.toNat = n at hw ⊢
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h]
  · split <;> simp
  · split
    · rename_i hn
      rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hn]; omega
    · obtain ⟨r, rfl, hr⟩ : ∃ r, n = 2 ^ 31 * 1 + r ∧ r < 2 ^ 31 := ⟨n - 2 ^ 31, by omega, by omega⟩
      rw [Nat.two_pow_add_eq_or_of_lt hr, Nat.or_assoc, Nat.or_comm r, ← Nat.or_assoc, Nat.or_self]

theorem sign_mem (t : State) :
    (execAll signG t).mem =
      write32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 ((YS + 28) / 4)).toNat * 4))
        (read32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 ((YS + 28) / 4)).toNat * 4)) |||
          read32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 (XS / 4)).toNat * 4)) <<< 31) := rfl

/-- **The `sign` block's view.** -/
theorem sign_bytes (t : State) :
    bytesAt (execAll signG t).mem (t.regs 13 + BitVec.ofNat 32 YS) 32 =
      signB (bytesAt t.mem (t.regs 13 + BitVec.ofNat 32 XS) 32) (bytesAt t.mem (t.regs 13 + BitVec.ofNat 32 YS) 32) := by
  have e1 : (BitVec.ofNat 8 ((YS + 28) / 4)).toNat * 4 = YS + 4 * 7 := by decide
  have e0 : (BitVec.ofNat 8 (XS / 4)).toNat * 4 = XS := by decide
  rw [sign_mem, e1, e0]
  generalize t.regs 13 = sp
  generalize t.mem = m
  have d8 : ∀ m a, decodeInt (bytesAt m a 32) = wsum (fun j => (read32 m (a + BitVec.ofNat 32 (4 * j))).toNat) 8 :=
    fun m a => decodeInt_words m a 8
  generalize hf : (fun j => (read32 m (sp + BitVec.ofNat 32 YS + BitVec.ofNat 32 (4 * j))).toNat) = f
  have hf7 : f 7 = (read32 m (sp + BitVec.ofNat 32 (YS + 4 * 7))).toNat := by rw [← hf]; simp only [off_add]
  have hfl : ∀ j, j < 8 → f j < 2 ^ 32 := fun j _ => by rw [← hf]; exact (read32 _ _).isLt
  generalize hv : read32 m (sp + BitVec.ofNat 32 (YS + 4 * 7)) ||| read32 m (sp + BitVec.ofNat 32 (XS)) <<< 31 = v
  have hL : decodeInt (bytesAt (write32 m (sp + BitVec.ofNat 32 (YS + 4 * 7)) v) (sp + BitVec.ofNat 32 YS) 32) =
      wsum (upd f 7 v.toNat) 8 := by
    rw [d8]; apply Ed25519Words.wsum_congr; intro j hj
    by_cases h7 : j = 7
    · subst h7; rw [Ed25519Words.upd_same, off_add, Armv6M.read32_write32_same]
    · rw [Ed25519Words.upd_ne _ _ h7, ← hf]
      exact congrArg BitVec.toNat (Frame.read32_congr fun k hk => by
        rw [off_add, off_add, write32_out (by rw [reg_off _ _ _ _ (by omega) (by omega)]; omega)])
  have hY : decodeInt (bytesAt m (sp + BitVec.ofNat 32 YS) 32) = wsum f 8 := by rw [d8, ← hf]
  have hX : decodeInt (bytesAt m (sp + BitVec.ofNat 32 XS) 32) % 2 =
      (read32 m (sp + BitVec.ofNat 32 (XS))).toNat % 2 := by
    rw [d8, show 8 = 1 + 7 from rfl, Ed25519Words.wsum_add]
    simp only [Ed25519Words.wsum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, BitVec.add_zero,
      Nat.reduceMul]
    omega
  have hu := wsum_upd f v.toNat (i := 7) (n := 8) (by omega)
  have h8 : wsum f 8 = wsum f 7 + 2 ^ (32 * 7) * f 7 := wsum_succ f 7
  have h7 := Ed25519Words.wsum_lt (f := f) (n := 7) fun j hj => hfl j (by omega)
  have hor := or_hi (read32 m (sp + BitVec.ofNat 32 (YS + 4 * 7))) (read32 m (sp + BitVec.ofNat 32 (XS)))
  rw [hv, ← hf7] at hor
  have hx2 := Nat.mod_lt (read32 m (sp + BitVec.ofNat 32 (XS))).toNat (show 0 < 2 by decide)
  generalize (read32 m (sp + BitVec.ofNat 32 (XS))).toNat % 2 = x2 at hX hor hx2
  rw [← encodeInt_decodeInt (bytesAt_length (write32 m (sp + BitVec.ofNat 32 (YS + 4 * 7)) v) _ 32), hL]
  unfold signB
  rw [hY, hX]
  simp only [Nat.reduceMul] at hu h8 h7 ⊢
  have hf7l := hfl 7 (by omega)
  split
  · have : f 7 < 2 ^ 31 := by omega
    simp only [this, ↓reduceIte] at hor
    rw [show wsum (upd f 7 v.toNat) 8 = wsum f 8 + 2 ^ 255 * x2 by omega]
  · have : ¬ f 7 < 2 ^ 31 := by omega
    simp only [this, ↓reduceIte] at hor
    rw [show wsum (upd f 7 v.toNat) 8 = wsum f 8 by omega, ← hY, encodeInt_decodeInt (bytesAt_length _ _ 32)]

inductive CB where
  | sign | store
  deriving DecidableEq

def cbS : CB → BlockS
  | .sign => ⟨ioSign, signG, [13]⟩
  | .store => ebS .store

/-! ## The program -/

inductive CA where
  | inv | mul | canon
  deriving DecidableEq

def caS : CA → CalleeS
  | .inv => Ed25519Safegcd.invS
  | .mul => paS .mul
  | .canon => canonS

section
open Op Ld
def cpP : Prog CA CB := Prog.ofList
  [spill 0 OUT, spill 1 PT, call .inv [(0, S ZI), (1, W PT CZ)], call .mul [(0, S XS), (1, W PT CX), (2, S ZI)],
   call .mul [(0, S YS), (1, W PT CY), (2, S ZI)], call .canon [(0, S XS)], call .canon [(0, S YS)], blk .sign [],
   blk .store [(2, W OUT 0), (3, S YS)]]
end

/-- `m0c_ge_compress`: `out` written, the point read. -/
def cpQ : CalleeP CA CB :=
  ⟨eaS .compress, cpP, 104, [(0, ⟨.k 32, true, false, false⟩), (1, ⟨.k 128, false, true, true⟩)], [], [], []⟩

/-! ## The decided checks -/

theorem cp_ok : cpQ.ok caS cbS = true := by decide +kernel

open M0Crypto.Thumb M0Crypto.Release.RoutinePieces in
theorem cp_code (b : Build) : @CalleeP.codeOk _ _ caS cbS cpQ b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]; cases b <;> decide +kernel

/-! ## The adapters -/

def signV : List V → List V
  | [.f x, .f y] => [.b (signB (encodeInt x.toNat) (encodeInt y.toNat))]
  | _ => [.none]

def cbV : CB → List V → List V
  | .sign => signV
  | .store => semB .store

def cbD (Rs : Rels) : ∀ b, Bd Rs (cbS b)
  | .sign => ⟨signV, fun c sp t vs _ _ _ hin => by
      rcases vs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp only [InsRel, All2, cbS, ioSign, and_true, and_false] at hin
      cases x <;> cases y <;> simp only [Rel, In.kd, and_false, false_and] at hin
      simp only [OutsRel, All2, cbS, ioSign, signV, Rel, and_true, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero]
      have be : ∀ a, bytesAt t.mem a 32 = encodeInt (feVal t.mem a) := fun a => by
        rw [← dec_fe, encodeInt_decodeInt (bytesAt_length _ _ 32)]
      rw [sign_bytes, ← hin.1.1, ← hin.2.1, Int.toNat_natCast, Int.toNat_natCast, be, be], fun _ _ _ _ _ _ _ _ _ h => by simp [cbS, ioSign] at h⟩
  | .store => bdS Rs .store

def cpV : CA → List V → List V
  | .inv => powSem 0
  | .mul => fun vs => [paV .mul vs]
  | .canon => canonV

noncomputable def cpAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (caS a)
  | .inv => Ed25519Safegcd.invAd b Rs
  | .mul => mulAd b Rs
  | .canon => canonAd b Rs

theorem cpAd_sem (b : Build) (Rs : Rels) :
    ∀ a vs, @Ad.sem Rs b.bytes b.size b.codeBytes _ (cpAd b Rs a).ad vs = cpV a vs
  | .inv, _ | .mul, _ | .canon, _ => rfl

/-! ## The value and the result -/

/-- `x · Z^(p−2)` made canonical, as bytes. -/
def canonMul (x z : Nat) : List (BitVec 8) := encodeInt (((x : Int) * (z : Int) ^ powE 0) % pN).toNat

/-- What the program leaves at `out`, from the entry bytes `m0`. -/
def cpF (c : Ctx) (m0 : Mem) : List (BitVec 8) :=
  signB (canonMul (feVal m0 (c.ptr 1 + BitVec.ofNat 32 CX)) (feVal m0 (c.ptr 1 + BitVec.ofNat 32 CZ)))
    (canonMul (feVal m0 (c.ptr 1 + BitVec.ofNat 32 CY)) (feVal m0 (c.ptr 1 + BitVec.ofNat 32 CZ)))


/-- `canonMul x z` is the canonical `x · z^(p−2)`. -/
theorem canonMul_val (x z : Nat) : decodeInt (canonMul x z) = (toF x * toF z ^ (Ed25519PrimeCert.p - 2)).val := by
  have hp : Ed25519PrimeCert.p = pN := rfl
  have he : Ed25519PrimeCert.p - 2 = powE 0 := by rw [hp]; show pN - 2 = 2 ^ 255 - 21; unfold pN; omega
  rw [canonMul, show ((x : Int) * (z : Int) ^ powE 0) = ((x * z ^ powE 0 : Nat) : Int) by
    rw [Int.natCast_mul, Int.natCast_pow], ← Int.natCast_emod, Int.toNat_natCast, decodeInt_encodeInt, ← toF_pow,
    ← toF_mul, val_toF, he, hp]
  generalize x * z ^ powE 0 = n
  have : n % pN < pN := Nat.mod_lt _ (by unfold pN; omega)
  have h256 : n % pN < 2 ^ 256 := by unfold pN at this ⊢; omega
  rw [Nat.mod_eq_of_lt h256]

/-- **The stored bytes** are those of `compressCode` of the coordinates. -/
theorem code_eq (x y z t : Nat) :
    signB (canonMul x z) (canonMul y z) = encodeInt (Ed25519Encode.compressCode ⟨toF x, toF y, toF z, toF t⟩) := by
  unfold signB
  rw [canonMul_val, canonMul_val]
  simp only [Ed25519Encode.val_lt, ↓reduceIte]
  rfl

theorem cp_out (c : Ctx) (m0 : Mem) :
    cpQ.outVals (Prog.ev caS cbS cpQ.geo cpV cbV c m0 cpQ.P cpQ.st0 fun _ => .none) = [.b (cpF c m0)] := rfl

/-- **`m0c_ge_compress`'s result**: `encodePoint P` at `out`, with points related by `PtR`. -/
theorem cp_post {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels} (hpt : Rs.pt = PtR)
    {semA : CA → List V → List V} (hA : ∀ a vs, semA a vs = cpV a vs) (c : Ctx) (sp : Word) (st : State) (m : Mem)
    (r0 : Word) (vs : List V) (hi : InsRel Rs c sp cpQ.s.io st vs)
    (hp : cpQ.post caS cbS Rs semA (fun b => (cbD Rs b).sem) st m r0) :
    OutsRel Rs c sp cpQ.s.io st m (semE .compress vs) := by
  obtain ⟨hg, base, m0, -, hm, ho⟩ := hp
  obtain rfl : semA = cpV := funext fun a => funext (hA a)
  have hB : (fun b => (cbD Rs b).sem) = cbV := funext fun b => by cases b <;> rfl
  rw [hB] at ho
  generalize hcc : cpQ.ctx base (cpQ.s.pub base st) = cc at ho hm
  dsimp only at ho
  have p1 : cc.ptr 1 = st.regs 1 := by
    rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pub (r := 1) (by decide)
  have hfe : ∀ o, o + 32 ≤ 128 →
      feVal m0 (cc.ptr 1 + BitVec.ofNat 32 o) = feVal st.mem (st.regs 1 + BitVec.ofNat 32 o) := fun o ho => by
    rw [← p1]
    exact Ed25519FeCanon.feVal_congr fun y ⟨_, hr, i, hi, hy⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      have hi : i < 32 := hi
      exact hm 1 ⟨.k 128, false, true, true⟩ rfl rfl y ⟨⟨cc.ptr 1, 128⟩, by simp [XInfo.rgns, XLen.v],
        ⟨o + i, show o + i < 128 by omega, by rw [hy, ofNat_add_assoc]⟩⟩
  rw [cp_out] at ho
  have hio : cpQ.s.io = ioCompress := rfl
  rw [hio] at hi ho ⊢
  rcases vs with _ | ⟨_ | _ | _ | P | _ | _, _ | _⟩ <;>
    simp only [InsRel, All2, ioCompress, io1, Rel, In.kd, and_true, and_false] at hi
  simp only [BitVec.add_zero, hpt] at hi
  obtain ⟨A, hS, hR⟩ := hi
  simp only [OutsRel, All2, ioCompress, io1, Iface.base, Kd.base, Rel, List.map, and_true, BitVec.add_zero] at ho
  simp only [semE, OutsRel, All2, ioCompress, io1, Rel, and_true, BitVec.add_zero]
  rw [ho, cpF, hfe CX (by decide), hfe CY (by decide), hfe CZ (by decide),
    code_eq _ _ _ (feVal st.mem (st.regs 1 + BitVec.ofNat 32 CT)), Ed25519Encode.encodePoint_rep hS,
    ← Ed25519Encode.compressCode_eq hR.rep2]
  rfl

/-- **`m0c_ge_compress`'s adapter** in build `b`, at relations whose point relation is `PtR`. -/
noncomputable def compressAd (b : Build) (Rs : Rels) (hpt : Rs.pt = PtR) : AdE Rs (cb := b.codeBytes) (eaS .compress) :=
  CalleeP.adE (cb := b.codeBytes) (q := cpQ) (cE := caS) (bE := cbS) (cpAd b Rs) (cbD Rs)
    (CalleeP.ok_parts cp_ok).choose_spec (cp_code b) (semE .compress)
    fun c sp st m r0 vs _ hi hp => cp_post (cb := b.codeBytes) hpt (cpAd_sem b Rs) c sp st m r0 vs hi hp

end M0Crypto.Release.Ed25519GeCompressProg
