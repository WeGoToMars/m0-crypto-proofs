import M0Crypto.Release.Ed25519ScReduceProg

/-!
# `m0c_sc_muladd` as a callee call program

`m0c_sc_muladd(r0 = out, r1 = k, r2 = a, r3 = r)` (`gen_ed25519.py`, `emit_sc_muladd`): `P = k · a`
by `m0c_mp_mul` of 8 words into the frame, `P += r` by an `adds`/`adcs` chain over 16 words (`r`'s
8 words, then zero), then `m0c_sc_reduce(out, P)` as a callee (`Ed25519ScReduceProg.redAd`).
`ma_post` proves the 32 bytes at `out` are `encodeInt ((k a + r) mod L)`.
-/
namespace M0Crypto.Release.Ed25519ScMuladdProg
open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length MemEq)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519ScMuladd (encK encK_decode)
open M0Crypto.Spec.Ed25519 (decodeInt encodeInt L)
open M0Crypto.Release.Ed25519Words (wsum wsum_add add_chain wsum_congr)
open M0Crypto.Release.Ed25519ScalarChain (wv chainI chain_run)
open M0Crypto.Release.Ed25519Routines (EqOrDisj)

/-- The block: `[r0 …] += [r1 …]` over 8 words, then the carry into the 8 words above. -/
def addG : List Instr := chainI false false true 0 1 0 2 3 0 8 ++ [.movImm 3 0] ++ chainI false true false 0 1 0 2 3 8 8

theorem add_regs (b : Bool) : Ed25519ScalarChain.Regs b 0 1 0 2 3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The block's run**: the 64 bytes at `r0` become `[r0] + [r1]` mod `2^512`. -/
theorem add16_run (t : State) (hd : (t.regs 0).toNat + 64 ≤ 2 ^ 32) (hb : EqOrDisj (t.regs 0) (t.regs 1) 32) :
    bytesAt (execAll addG t).mem (t.regs 0) 64 =
      encK 64 ((decodeInt (bytesAt t.mem (t.regs 0) 64) + decodeInt (bytesAt t.mem (t.regs 1) 32)) % 2 ^ 512) := by
  obtain ⟨hm1, hr1, c, c0, cn, hc⟩ := chain_run false false true 0 1 0 2 3 0 8 t (add_regs true) (by omega)
    (by show (t.regs 0).toNat + 4 * (0 + 8) ≤ 2 ^ 32; omega) (.inl rfl) (fun _ => hb) 8 (Nat.le_refl _)
  rw [addG, execAll_append, execAll_append]
  generalize hv : execAll (chainI false false true 0 1 0 2 3 0 8) t = v at hm1 hr1 cn hc
  have h0 : v.regs 0 = t.regs 0 := hr1 0 (by decide) (fun _ => by decide) (by decide)
  generalize hw : execAll [.movImm 3 0] v = w
  have w0 : w.regs 0 = t.regs 0 := by rw [← hw, ← h0]; rfl
  have w3 : w.regs 3 = 0 := by rw [← hw]; rfl
  have wm : w.mem = v.mem := by rw [← hw]; rfl
  have wc : w.c = v.c := by rw [← hw]; rfl
  obtain ⟨hm2, -, c', c0', -, hc'⟩ := chain_run false true false 0 1 0 2 3 8 8 w (add_regs false) (by omega)
    (by show (w.regs 0).toNat + 4 * (8 + 8) ≤ 2 ^ 32; rw [w0]; omega) (.inl rfl) (fun h => absurd h (by decide)) 8 (Nat.le_refl _)
  generalize execAll (chainI false true false 0 1 0 2 3 8 8) w = x at hm2 hc'
  have r0e : (0 : Armv6M.LowReg).toReg = 0 := rfl
  have r1e : (1 : Armv6M.LowReg).toReg = 1 := rfl
  rw [r0e, w0] at hm2 hc'
  rw [r0e] at hm1 hc
  have A : ∀ j, j < 8 → wv v.mem (t.regs 0) j + 2 ^ 32 * (c (j + 1)).toNat =
      wv t.mem (t.regs 0) j + wv t.mem (t.regs 1) j + (c j).toNat := fun j hj => by
    have := hc j hj
    simp only [Nat.zero_add, Field25519AddSubChain.opY, Ed25519ScalarChain.yW, ite_true, Bool.false_eq_true,
      ite_false, r1e] at this
    exact this
  have B : ∀ j, j < 8 → wv x.mem (t.regs 0) (8 + j) + 2 ^ 32 * (c' (j + 1)).toNat =
      wv w.mem (t.regs 0) (8 + j) + 0 + (c' j).toNat := fun j hj => by
    have := hc' j hj
    simp only [Field25519AddSubChain.opY, Ed25519ScalarChain.yW, Bool.false_eq_true, ite_false] at this
    rw [show (3 : Armv6M.LowReg).toReg = 3 from rfl, w3] at this
    exact this
  have := (t.regs 0).isLt
  have M1 : ∀ j, j < 8 → wv w.mem (t.regs 0) (8 + j) = wv t.mem (t.regs 0) (8 + j) := fun j hj => by
    rw [wv, wv, wm, hm1.read32 (by simp only [Footprint.Sep, List.mem_singleton, forall_eq, Frame.Disj]; fp_simp; omega)]
  have M2 : ∀ j, j < 8 → wv x.mem (t.regs 0) j = wv v.mem (t.regs 0) j := fun j hj => by
    rw [wv, wv, hm2.read32 (by simp only [Footprint.Sep, List.mem_singleton, forall_eq, Frame.Disj]; fp_simp; omega), wm]
  have hA := add_chain (wv t.mem (t.regs 0)) (wv t.mem (t.regs 1)) (wv v.mem (t.regs 0)) (fun j => (c j).toNat) 8 A
  have hB := add_chain (fun j => wv w.mem (t.regs 0) (8 + j)) (fun _ => 0) (fun j => wv x.mem (t.regs 0) (8 + j))
    (fun j => (c' j).toNat) 8 B
  rw [wsum_congr M1, Ed25519Words.wsum_const_zero, c0', ite_eq_left rfl, wc, cn (.inl (by decide))] at hB
  simp only [c0, Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero] at hA
  have e : ∀ m a n, decodeInt (bytesAt m a (4 * n)) = wsum (wv m a) n := fun m a n => decodeInt_words m a n
  have hS : decodeInt (bytesAt x.mem (t.regs 0) 64) =
      (decodeInt (bytesAt t.mem (t.regs 0) 64) + decodeInt (bytesAt t.mem (t.regs 1) 32)) % 2 ^ 512 := by
    rw [show (64 : Nat) = 4 * (8 + 8) from rfl, show (32 : Nat) = 4 * 8 from rfl, e, e, e, wsum_add, wsum_add,
      wsum_congr M2]
    have l1 := Ed25519Words.wsum_lt (n := 8) (f := fun j => wv x.mem (t.regs 0) (8 + j)) fun j _ => Ed25519ScalarChain.wv_lt _ _ _
    have l2 := Ed25519Words.wsum_lt (n := 8) (f := wv v.mem (t.regs 0)) fun j _ => Ed25519ScalarChain.wv_lt _ _ _
    have := Bool.toNat_le (c' 8)
    simp only [Nat.reduceMul] at hA hB l1 l2 ⊢
    omega
  rw [← hS, encK_decode (bytesAt_length _ _ _)]

open M0Crypto.Release.Ed25519ScMuladd (mpS mpV)
open M0Crypto.Release.Ed25519 (Build)

/-! ## The callees, the block and the program -/

inductive MA where
  | mp | reduce
  deriving DecidableEq

def maS : MA → CalleeS
  | .mp => mpS 8
  | .reduce => eaS .reduce

inductive MB where
  | add
  deriving DecidableEq

/-- `[r0 …] += [r1 …]`, 64 bytes at `r0` in place, 32 bytes at `r1` apart from them. -/
def ioAdd : Iface :=
  { ins := [(0, 0, .raw (.k 64)), (1, 0, .raw (.k 32))], outs := [(0, 0, .bytes 64)], wr := [⟨0, 0, .k 64⟩],
    rd := [⟨0, 0, .k 64⟩, ⟨1, 0, .k 32⟩], al := [0, 1], eqd := [(0, 1, 32)], nw := [(0, 64)] }

def mbS : MB → BlockS
  | .add => ⟨ioAdd, addG, [0, 1]⟩

/-- Frame words, in bytes from `sp`: `out`, `r` and the product `P`. -/
def OUT : Nat := 0
def RR : Nat := 4
def PR : Nat := 8

section
open Op Ld
def maP : Prog MA MB := Prog.ofList
  [spill 0 OUT, spill 3 RR, ld 0 (S PR), call .mp [(3, K 8)], blk .add [(0, S PR), (1, W RR 0)],
   call .reduce [(0, W OUT 0), (1, S PR)]]
end

/-- `m0c_sc_muladd`: `out` written, `k`, `a` and `r` read. -/
def maQ : CalleeP MA MB :=
  ⟨eaS .muladd, maP, 72, [(0, ⟨.k 32, true, false, true⟩), (1, ⟨.k 32, false, true, true⟩),
    (2, ⟨.k 32, false, true, true⟩), (3, ⟨.k 32, false, true, true⟩)], [], [], []⟩

/-! ## The decided checks -/

theorem ma_ok : maQ.ok maS mbS = true := by decide +kernel

open M0Crypto.Thumb M0Crypto.Release.RoutinePieces in
theorem ma_code (b : Build) : @CalleeP.codeOk _ _ maS mbS maQ b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]; cases b <;> decide +kernel

/-! ## The block's and the callees' adapters -/

def mbV : MB → List V → List V
  | .add, [.b p, .b r] => [.b (encK 64 ((decodeInt p + decodeInt r) % 2 ^ 512))]
  | _, _ => [.none]

def mbD (Rs : Rels) : ∀ b, Bd Rs (mbS b)
  | .add => ⟨mbV .add, fun c sp t vs hp hn _ hi => by
      have hd := hn (0, 64) (by simp [mbS, ioAdd])
      have hb := hp.2.1 (0, 1, 32) (by simp [mbS, ioAdd])
      rcases vs with _ | ⟨x | _ | _ | _ | _ | _, _ | ⟨y | _ | _ | _ | _ | _, _ | _⟩⟩ <;>
        simp only [InsRel, All2, mbS, ioAdd, Rel, In.kd, ALen.val, and_true, and_false, false_and] at hi
      simp only [BitVec.add_zero] at hi
      simp only [OutsRel, All2, mbS, ioAdd, mbV, Rel, BitVec.add_zero, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero, and_true, ← hi.1, ← hi.2]
      exact add16_run t hd hb, fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp [mbS, ioAdd])⟩

def maV : MA → List V → List V
  | .mp => mpV 8
  | .reduce => semE .reduce

noncomputable def maAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (maS a)
  | .mp => Ed25519ScMuladd.mpAd b Rs 8 (by decide) (by decide)
  | .reduce => Ed25519ScReduceProg.redAd b Rs

theorem maAd_sem (b : Build) (Rs : Rels) :
    ∀ a vs, @Ad.sem Rs b.bytes b.size b.codeBytes _ (maAd b Rs a).ad vs = maV a vs
  | .mp, _ | .reduce, _ => rfl

/-! ## The value and the result -/

/-- What the program leaves at `out`, from the entry bytes `m0`. -/
def maF (c : Ctx) (m0 : Mem) : List Byte :=
  encodeInt (decodeInt (encK 64 ((decodeInt (encK (8 * 8) (decodeInt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) 32) *
    decodeInt (bytesAt m0 (c.ptr 2 + BitVec.ofNat 32 0) 32))) + decodeInt (bytesAt m0 (c.ptr 3 + BitVec.ofNat 32 0) 32)) %
      2 ^ 512)) % L)

theorem ma_ev (c : Ctx) (m0 : Mem) :
    Prog.ev maS mbS maQ.geo maV mbV c m0 maP maQ.st0 (fun _ => .none) (.ex 0 0) = .b (maF c m0) := rfl

/-- **`m0c_sc_muladd`'s result**: `(k a + r) mod L`, with `k a + r` below `2^512` as `k`, `r < L`. -/
theorem ma_post {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels} {semA : MA → List V → List V}
    (hA : ∀ a vs, semA a vs = maV a vs) (c : Ctx) (sp : Word) (st : State) (m : Mem) (r0 : Word) (vs : List V)
    (hi : InsRel Rs c sp maQ.s.io st vs) (hp : maQ.post maS mbS Rs semA (fun b => (mbD Rs b).sem) st m r0) :
    OutsRel Rs c sp maQ.s.io st m (semE .muladd vs) := by
  obtain ⟨hg, base, m0, -, hm, ho⟩ := hp
  obtain rfl : semA = maV := funext fun a => funext (hA a)
  have hB : (fun b => (mbD Rs b).sem) = mbV := funext fun b => by cases b; rfl
  rw [hB] at ho
  generalize hcc : maQ.ctx base (maQ.s.pub base st) = cc at ho hm
  dsimp only at ho
  have p1 : cc.ptr 1 = st.regs 1 := by
    rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pub (r := 1) (by decide)
  have p2 : cc.ptr 2 = st.regs 2 := by
    rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pub (r := 2) (by decide)
  have p3 : cc.ptr 3 = st.regs 3 := by
    rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pub (r := 3) (by decide)
  have hin : ∀ (i : Nat) (r : Reg), cc.ptr i = st.regs r → (∃ x, maQ.geo.xs[i]? = some x ∧ x.r = true ∧ x.len = .k 32) →
      bytesAt m0 (cc.ptr i + BitVec.ofNat 32 0) 32 = bytesAt st.mem (st.regs r) 32 := fun i r hr ⟨x, hx, hxr, hl⟩ => by
    rw [BitVec.add_zero, ← hr]
    refine Footprint.bytesAt_eq_of fun k hk => hm i x hx hxr _ ⟨⟨cc.ptr i, 32⟩, ?_, ⟨k, hk, rfl⟩⟩
    simp [XInfo.rgns, hl, XLen.v]
  rw [show maQ.outVals _ = [.b (maF cc m0)] from rfl] at ho
  have hio : maQ.s.io = ioMuladd := rfl
  rw [hio] at hi ho ⊢
  rcases vs with _ | ⟨k | _ | _ | _ | _ | _, _ | ⟨s | _ | _ | _ | _ | _, _ | ⟨r | _ | _ | _ | _ | _, _ | _⟩⟩⟩ <;>
    simp only [InsRel, All2, ioMuladd, Rel, In.kd, and_true, and_false, false_and] at hi
  simp only [BitVec.add_zero] at hi
  obtain ⟨⟨rfl, hk⟩, rfl, rfl, hr⟩ := hi
  simp only [OutsRel, All2, ioMuladd, Iface.base, Kd.base, Rel, List.map, and_true, BitVec.add_zero] at ho
  simp only [semE, OutsRel, All2, ioMuladd, Rel, and_true, BitVec.add_zero]
  rw [ho, maF, hin 1 1 p1 ⟨⟨.k 32, false, true, true⟩, rfl, rfl, rfl⟩, hin 2 2 p2 ⟨⟨.k 32, false, true, true⟩, rfl, rfl, rfl⟩, hin 3 3 p3 ⟨⟨.k 32, false, true, true⟩, rfl, rfl, rfl⟩]
  have hS := Ed25519Bytes.decodeInt_lt (bytesAt st.mem (st.regs 2) 32)
  rw [bytesAt_length] at hS
  rw [Ed25519ScReduceProg.dec_encK, Ed25519ScReduceProg.dec_encK]
  generalize decodeInt (bytesAt st.mem (st.regs 1) 32) = K at hk
  generalize decodeInt (bytesAt st.mem (st.regs 2) 32) = S at hS
  generalize decodeInt (bytesAt st.mem (st.regs 3) 32) = R at hr
  have hKS := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_trans hk Ed25519Barrett.L_lt) hS
  have hL := Ed25519Barrett.L_lt
  generalize K * S = KS at hKS
  simp only [Nat.reduceMul] at hS hKS ⊢
  rw [show ((KS % 2 ^ 512 + R) % 2 ^ 512 % 2 ^ 512) = KS + R by omega]

/-- **`m0c_sc_muladd`'s adapter** in build `b`. -/
noncomputable def muladdAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (eaS .muladd) :=
  CalleeP.adE (cb := b.codeBytes) (q := maQ) (cE := maS) (bE := mbS) (maAd b Rs) (mbD Rs)
    (CalleeP.ok_parts ma_ok).choose_spec (ma_code b) (semE .muladd)
    fun c sp st m r0 vs _ hi hp => ma_post (cb := b.codeBytes) (maAd_sem b Rs) c sp st m r0 vs hi hp

end M0Crypto.Release.Ed25519ScMuladdProg
