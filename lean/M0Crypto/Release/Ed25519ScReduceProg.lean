import M0Crypto.Release.Ed25519ScMuladd
import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519ScReduce
import M0Crypto.Release.Ed25519Barrett

/-!
# `m0c_sc_reduce` as a callee call program

`m0c_sc_reduce(r0 = out, r1 = in)` (`gen_ed25519.py`, `emit_sc_reduce`) is Barrett reduction:
`Q2 = in[7 …] · mu` and `Q4 = Q2[9 …] · L` by `m0c_mp_mul` of 9 words, `R = in − Q4` over
9 words, two rounds of `T = R − L` with the select mask and `m0c_cmov(R, T)`, then
`m0c_copy(out, R)`. Its program reads the code constants `m0c_ed_mu` and `m0c_ed_l9` as code
buffers. `R` is two views, its 8 low words and its top word, so that `cmov`'s 8-word write keeps
the top word. The program leaves 32 bytes at `out`, and `red_post` proves them below `L` and
equal to the input mod `L` (`Ed25519Barrett.barrett`, `two_sub_mod`).
-/

namespace M0Crypto.Release.Ed25519ScReduceProg

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519ScReduceCode (OUT IN Q2 Q4 R T FRAME O a1L a2L selL oD oD2 pl sub9)
open M0Crypto.Release.Ed25519ScalarChain (selMask)
open M0Crypto.Release.Ed25519ScMuladd (mpS mpV encK)
open M0Crypto.Release.Ed25519FePow (ioCopy)
open M0Crypto.Artifacts.Ed25519Compact (sc_reduce cmov copy ed_mu ed_l9)
open M0Crypto.Spec.Ed25519 (decodeInt encodeInt)
open M0Crypto.Release.Ed25519 (Build)

/-! ## The callees and blocks -/

inductive RA where
  | mp | cmov | copy
  deriving DecidableEq

/-- `cmov(r0, r1, 8 words)` under the mask in `r3`: the 8 low words of a view at `r0`, 32 bytes
at `r1`. -/
def ioCmov : Iface :=
  { ins := [(0, 0, .view (.bytes 32)), (1, 0, .raw (.k 32)), (3, 0, .view .rw)], outs := [(0, 0, .bytes 32)],
    wr := [⟨0, 0, .k 32⟩], rd := [⟨0, 0, .k 32⟩, ⟨1, 0, .k 32⟩], al := [0, 1], eqd := [(0, 1, 32)],
    kreq := [(2, 8)] }

def raS : RA → CalleeS
  | .mp => mpS 9
  | .cmov => calleeAt cmov ioCmov [0, 1, 2]
  | .copy => calleeAt copy (ioCopy (.view (.bytes 32)) (.bytes 32)) [0, 1, 2]

inductive RB where
  | s0 | sel
  deriving DecidableEq

/-- `[r3 …] = [r1 …] − [r2 …]` over 9 words, the result apart from or at its operands. -/
def ioSub (ins : List (Reg × Nat × In)) (outs : List (Reg × Nat × Kd)) (ro : List Reg) : Iface :=
  { ins, outs, wr := [⟨3, 0, .k 36⟩], rd := [⟨1, 0, .k 36⟩, ⟨2, 0, .k 36⟩], al := [1, 2, 3],
    eqd := [(3, 1, 36), (3, 2, 36)], nw := [(3, 36)], ro }

/-- `s0`: `R = in − Q4[0 …]`, as `R`'s low words and its top word. `sel`: `T = R − L` and the
select mask in `r3`. -/
def rbS : RB → BlockS
  | .s0 => ⟨ioSub [(1, 0, .raw (.k 36)), (2, 0, .raw (.k 36))] [(3, 0, .bytes 32), (3, 32, .bytes 4)] [],
      sub9 1 2 3, [1, 2, 3]⟩
  | .sel => ⟨ioSub [(1, 0, .view (.bytes 32)), (1, 32, .view (.bytes 4)), (2, 0, .raw (.k 36))]
      [(3, 0, .bytes 36)] [3], sub9 1 2 3 ++ selMask 3, [1, 2, 3]⟩

/-! ## The program -/

section
open Op Ld

/-- A round: `T = R − L` with `L`'s `adr` at `x` and its pool word at `p`, then `cmov(R, T)`. -/
def round (x p : Nat) : List (Op RA RB) :=
  [ld 1 (S R), ld 2 (C 3 0 (litImm x p)), blk .sel [(3, S T)], call .cmov [(0, S R), (1, S T), (2, K 8)]]

def redP : Prog RA RB := Prog.ofList <|
  [spill 0 OUT, spill 1 IN, ld 0 (S Q2), ld 1 (A 28), ld 2 (C 2 0 (litImm (a1L O) (pl O))), call .mp [(3, K 9)],
   ld 0 (S Q4), ld 1 (S (Q2 + 36)), ld 2 (C 3 0 (litImm (a2L O) (pl O + 4))), call .mp [(3, K 9)],
   blk .s0 [(1, W IN 0), (2, S Q4), (3, S R)]] ++
  round (selL (oD O)) (pl O + 8) ++ round (selL (oD2 O)) (pl O + 12) ++
  [call .copy [(0, W OUT 0), (1, S R), (2, K 8)]]

end

/-- `m0c_sc_reduce`: `out` written, `in` read, the code constants `mu` and `L` read. -/
def redQ : CalleeP RA RB :=
  ⟨eaS .reduce, redP, FRAME, [(0, ⟨.k 32, true, false, true⟩), (1, ⟨.k 64, false, true, true⟩)], [],
    [(ed_mu, 36), (ed_l9, 36)], []⟩

/-! ## The decided checks -/

theorem red_ok : redQ.ok raS rbS = true := by decide +kernel

open M0Crypto.Thumb M0Crypto.Release.RoutinePieces in
theorem red_code (b : Build) : @CalleeP.codeOk _ _ raS rbS redQ b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]; cases b <;> decide +kernel

/-! ## The blocks' values -/

section
open M0Crypto.Release.Ed25519Words (wsum wsum_succ pow32_succ add_chain)
open M0Crypto.Release.Ed25519ScalarChain (wv chain_run)
open M0Crypto.Release.Ed25519Routines (EqOrDisj)
open M0Crypto.Release.Ed25519ScMuladd (encK_decode)

/-- The 36 bytes of `X − Y` modulo `2 ^ 288`. -/
def subV (X Y : Nat) : List Byte := encK 36 ((X + 2 ^ 288 - Y) % 2 ^ 288)

theorem wsum_cpl {f : Nat → Nat} : ∀ {n}, (∀ j, j < n → f j < 2 ^ 32) →
    wsum (fun j => 2 ^ 32 - 1 - f j) n + wsum f n + 1 = 2 ^ (32 * n)
  | 0, _ => by simp [wsum]
  | n + 1, h => by
    have ih := wsum_cpl (n := n) fun j hj => h j (by omega)
    have := h n (by omega)
    rw [wsum_succ, wsum_succ, pow32_succ]
    generalize 2 ^ (32 * n) = P at *
    have e : P * (2 ^ 32 - 1 - f n) + P * f n + P = P * 2 ^ 32 := by
      rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega
    grind

/-- **`sub9 1 2 3`**: the 36 bytes at `r3` become `[r1] − [r2]`, and the carry is set when
there is no borrow. -/
theorem sub9_run (t : State) (hd : (t.regs 3).toNat + 36 ≤ 2 ^ 32) (ha : EqOrDisj (t.regs 3) (t.regs 1) 36)
    (hb : EqOrDisj (t.regs 3) (t.regs 2) 36) :
    bytesAt (execAll (sub9 1 2 3) t).mem (t.regs 3) 36 =
      subV (decodeInt (bytesAt t.mem (t.regs 1) 36)) (decodeInt (bytesAt t.mem (t.regs 2) 36)) ∧
    (execAll (sub9 1 2 3) t).c =
      decide (decodeInt (bytesAt t.mem (t.regs 2) 36) ≤ decodeInt (bytesAt t.mem (t.regs 1) 36)) := by
  obtain ⟨-, -, c, c0, cn, hc⟩ := chain_run true false true 1 2 3 4 5 0 9 t Ed25519ScReduce.sub9_regs (by omega)
    hd ha (fun _ => hb) 9 (Nat.le_refl _)
  change bytesAt (execAll (Ed25519ScalarChain.chainI true false true 1 2 3 4 5 0 9) t).mem _ 36 = _ ∧
    (execAll (Ed25519ScalarChain.chainI true false true 1 2 3 4 5 0 9) t).c = _
  generalize execAll (Ed25519ScalarChain.chainI true false true 1 2 3 4 5 0 9) t = v at cn hc ⊢
  have hch := add_chain (wv t.mem (t.regs 1)) (fun j => 2 ^ 32 - 1 - wv t.mem (t.regs 2) j) (wv v.mem (t.regs 3))
    (fun j => (c j).toNat) 9 fun j hj => by
      have := hc j hj
      simp only [Nat.zero_add, Ed25519ScalarChain.yW, ite_true, Field25519AddSubChain.opY, BitVec.toNat_not, wv,
        M0Crypto.Proofs.toReg_1, M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3] at this ⊢
      omega
  have hcp := wsum_cpl (f := wv t.mem (t.regs 2)) (n := 9) fun j _ => Ed25519ScalarChain.wv_lt _ _ _
  have e : ∀ m a, decodeInt (bytesAt m a (4 * 9)) = wsum (wv m a) 9 := fun m a => decodeInt_words m a 9
  rw [show (36 : Nat) = 4 * 9 from rfl, e, e, ← encK_decode (bytesAt_length v.mem (t.regs 3) (4 * 9)), e]
  rw [cn (.inl (by decide))]
  simp only [c0, Bool.false_eq_true, ite_false, Bool.toNat_true] at hch
  have := Ed25519Words.wsum_lt (n := 9) (f := wv v.mem (t.regs 3)) fun j _ => Ed25519ScalarChain.wv_lt _ _ _
  simp only [show 32 * 9 = 288 from rfl] at hch hcp this
  cases h9 : c 9 <;> simp only [h9, Bool.toNat_false, Bool.toNat_true] at hch
  · exact ⟨congrArg _ (by omega), (decide_eq_false (by omega)).symm⟩
  · exact ⟨congrArg _ (by omega), (decide_eq_true (by omega)).symm⟩

theorem sub_pre {ins : List (Reg × Nat × In)} {outs : List (Reg × Nat × Kd)} {ro : List Reg} {regs : Reg → Word}
    (hp : PreG (ioSub ins outs ro) regs) (hn : NoWrap (ioSub ins outs ro) regs) :
    (regs 3).toNat + 36 ≤ 2 ^ 32 ∧ EqOrDisj (regs 3) (regs 1) 36 ∧ EqOrDisj (regs 3) (regs 2) 36 :=
  ⟨hn (3, 36) (by simp [ioSub]), hp.2.1 (3, 1, 36) (by simp [ioSub]), hp.2.1 (3, 2, 36) (by simp [ioSub])⟩

/-- The blocks' values: `R`'s low words and top word, or `T` and the select mask. -/
def rbV : RB → List V → List V
  | .s0, [.b x, .b y] => [.b ((subV (decodeInt x) (decodeInt y)).take 32), .b ((subV (decodeInt x) (decodeInt y)).drop 32)]
  | .sel, [.b r0, .b r8, .b l] => [.b (subV (decodeInt (r0 ++ r8)) (decodeInt l)),
      .w (if decodeInt l ≤ decodeInt (r0 ++ r8) then BitVec.allOnes 32 else 0#32)]
  | _, _ => [.none]

/-- The select mask after `sel`: all ones when `L ≤ R`. -/
theorem sel_mask {Rs : Rels} {c : Ctx} {sp : Word} (t : State) (vs : List V)
    (h : (t.regs 3).toNat + 36 ≤ 2 ^ 32 ∧ EqOrDisj (t.regs 3) (t.regs 1) 36 ∧ EqOrDisj (t.regs 3) (t.regs 2) 36)
    (hi : InsRel Rs c sp (rbS .sel).io t vs) :
    ((rbV .sel vs).drop 1)[0]? = some (.w ((execAll (sub9 1 2 3 ++ selMask 3) t).regs 3)) := by
  rcases vs with _ | ⟨x | _ | _ | _ | _ | _, _ | ⟨y | _ | _ | _ | _ | _, _ | ⟨z | _ | _ | _ | _ | _, _ | _⟩⟩⟩ <;>
    simp only [InsRel, All2, rbS, ioSub, Rel, In.kd, ALen.val, and_true, and_false, false_and] at hi
  simp only [BitVec.add_zero] at hi
  obtain ⟨rfl, rfl, rfl⟩ := hi
  have h36 : bytesAt t.mem (t.regs 1) 32 ++ bytesAt t.mem (t.regs 1 + 32#32) 4 = bytesAt t.mem (t.regs 1) 36 :=
    (bytesAt_split t.mem (t.regs 1) 32 4).symm
  have hm := (Ed25519ScalarChain.selMask_run 3 (execAll (sub9 1 2 3) t)).1
  rw [M0Crypto.Proofs.toReg_3] at hm
  rw [execAll_append, hm, (sub9_run t h.1 h.2.1 h.2.2).2]
  simp only [rbV, h36, List.drop_succ_cons, List.drop_zero, List.getElem?_cons_zero]
  by_cases hle : decodeInt (bytesAt t.mem (t.regs 2) 36) ≤ decodeInt (bytesAt t.mem (t.regs 1) 36) <;> simp [hle]

/-- **The block adapters.** -/
def rbD (Rs : Rels) : ∀ b, Bd Rs (rbS b)
  | .s0 => ⟨rbV .s0, fun c sp t vs hp hn _ hi => by
      obtain ⟨hd, ha, hb⟩ := sub_pre hp hn
      rcases vs with _ | ⟨x | _ | _ | _ | _ | _, _ | ⟨y | _ | _ | _ | _ | _, _ | _⟩⟩ <;>
        simp only [InsRel, All2, rbS, ioSub, Rel, In.kd, ALen.val, and_true, and_false, false_and] at hi
      simp only [BitVec.add_zero] at hi
      have e := bytesAt_split (execAll (sub9 1 2 3) t).mem (t.regs 3) 32 4
      simp only [OutsRel, All2, rbS, ioSub, rbV, Rel, BitVec.add_zero, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero, and_true, ← hi.1, ← hi.2]
      rw [← (sub9_run t hd ha hb).1, show (36 : Nat) = 32 + 4 from rfl, e, List.take_left' (bytesAt_length _ _ _),
        List.drop_left' (bytesAt_length _ _ _)]
      exact ⟨rfl, rfl⟩, fun _ _ _ _ _ _ _ _ _ h => absurd h (by simp [rbS, ioSub])⟩
  | .sel => ⟨rbV .sel, fun c sp t vs hp hn _ hi => by
      obtain ⟨hd, ha, hb⟩ := sub_pre hp hn
      rcases vs with _ | ⟨x | _ | _ | _ | _ | _, _ | ⟨y | _ | _ | _ | _ | _, _ | ⟨z | _ | _ | _ | _ | _, _ | _⟩⟩⟩ <;>
        simp only [InsRel, All2, rbS, ioSub, Rel, In.kd, ALen.val, and_true, and_false, false_and] at hi
      simp only [BitVec.add_zero] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      have h36 : bytesAt t.mem (t.regs 1) 32 ++ bytesAt t.mem (t.regs 1 + 32#32) 4 = bytesAt t.mem (t.regs 1) 36 :=
        (bytesAt_split t.mem (t.regs 1) 32 4).symm
      simp only [OutsRel, All2, rbS, ioSub, rbV, Rel, BitVec.add_zero, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero, and_true, h36]
      rw [execAll_append, (Ed25519ScalarChain.selMask_run 3 _).2.1]; exact (sub9_run t hd ha hb).1,
    fun _ _ t vs hp hn _ hi i h => by
      obtain rfl : i = 0 := by simp [rbS, ioSub] at h; omega
      exact sel_mask t vs (sub_pre hp hn) hi⟩

end

/-! ## The callees' adapters -/

section
open M0Crypto.Release.Ed25519Words (wsum wsum_succ wsum_div wsum_mod wsum_congr)
open M0Crypto.Release.Ed25519ScMuladd (encK_decode)
open M0Crypto.Release.Ed25519FePow (inR_of)
open M0Crypto.Thumb (Event)

/-- Word `j` of `l`'s number. -/
def dW (l : List Byte) (j : Nat) : Word := BitVec.ofNat 32 (decodeInt l / 2 ^ (32 * j))

theorem wsum_digit {f : Nat → Nat} {n j : Nat} (h : ∀ i, i < n → f i < 2 ^ 32) (hj : j < n) :
    wsum f n / 2 ^ (32 * j) % 2 ^ 32 = f j := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + (1 + k) := ⟨n - j - 1, by omega⟩
  rw [wsum_div h, ← show 32 * 1 = 32 from rfl, wsum_mod fun i hi => h _ (by omega)]
  simp [wsum]

/-- Word `j < n` at `a` is word `j` of the `4 n` bytes there. -/
theorem word_dW (m : Mem) (a : Word) {n j : Nat} (hj : j < n) :
    read32 m (a + BitVec.ofNat 32 (4 * j)) = dW (bytesAt m a (4 * n)) j := by
  apply BitVec.eq_of_toNat_eq
  rw [dW, BitVec.toNat_ofNat, decodeInt_words, wsum_digit (fun i _ => (read32 _ _).isLt) hj]

/-- The words `m0c_cmov` stores, under the mask `κ`, from `d` and `s`. -/
def cmovV : List V → List V
  | [.b d, .b s, .w κ] => [.b (encK 32 (wsum (fun j => (Ed25519WordLoop.sel κ (dW d j) (dW s j)).toNat) 8))]
  | _ => [.none]

/-- `m0c_cmov` of 8 words, its count pinned. -/
noncomputable def cmov8 (b : Build) := letI := b.codeBytes
  ((Ed25519WordLoop.cmov_te b).pin 2 2 (BitVec.ofNat 32 8) (fun _ _ => rfl) (fun s => [⟨s.regs 0, 32⟩])
    (fun s => [⟨s.regs 0, 32⟩, ⟨s.regs 1, 32⟩]) (fun _ h => by simp [Ed25519WordLoop.wordR, h])
    fun _ h => by simp [Ed25519WordLoop.wordR, h]).code (footprint cmov) (by decide +kernel)

theorem cmov8_eff {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base : Word} {p : Nat → Word} {tr : List Event}
    (h : Ed25519WordLoop.wloopE true true base (setPub p 2 (BitVec.ofNat 32 8)) tr) :
    (raS .cmov).Eff p base tr := by
  simp only [Ed25519WordLoop.wloopE, setPub, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, true_and] at h
  have r0 : (M0Crypto.Sym.SExpr.reg0 0).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 0 := rfl
  have r1 : (M0Crypto.Sym.SExpr.reg0 1).denote (Ed25519Leaf.blkSt [0, 1, 2] 0 p) = p 1 := rfl
  have hf : ∀ y, Region (p 0) 32 y ∨ Region (p 1) 32 y →
      StackEffect.InR (Ed25519Leaf.blkSt [0, 1, 2] 0 p) [(.reg0 0, 32), (.reg0 1, 32)] y := fun y hy => by
    rcases hy with hy | hy
    · exact inR_of List.mem_cons_self (r0 ▸ hy)
    · exact inR_of (List.mem_cons_of_mem _ List.mem_cons_self) (r1 ▸ hy)
  refine Ed25519Leaf.blk_eff (L := [0, 1, 2]) (pc := 0) (fp := [(.reg0 0, 32), (.reg0 1, 32)])
    (ini := [(.reg0 0, 32), (.reg0 1, 32)]) (wo := [(.reg0 0, 32)])
    (EffT.mono h (Nat.le_refl _) (fun y hy => .inr (hf y hy)) (fun y hy => .inr (hf y hy)) fun y hy => ?_)
    (by decide +kernel) (by decide) (by decide)
  obtain ⟨r, hr, o, ho, rfl⟩ := hy
  simp only [List.mem_singleton] at hr; subst hr
  exact region_lt ho

/-- **`m0c_cmov`'s adapter**: the `ldm`/`stm` loop pinned at 8 words, its words from `cmov_word`'s
`sel`. -/
noncomputable def cmovAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (raS .cmov) :=
  letI := b.codeBytes
  Ad.ofTSpec _ rfl rfl (by show 4 = stackOf cmov; decide) (cmov8 b) (fun _ _ _ h => cmov8_eff h) cmovV
    (fun _ _ _ st _ hg _ _ => by
      have h2 : st.regs 2 = BitVec.ofNat 32 8 := hg.2.2 (2, 8) (by simp [raS, calleeAt, ioCmov])
      refine ⟨⟨by rw [h2]; unfold Ed25519WordLoop.WordsOk; decide, hg.1 0 (by simp [raS, calleeAt, ioCmov]),
        fun _ => ⟨hg.1 1 (by simp [raS, calleeAt, ioCmov]), ?_⟩, trivial⟩, h2⟩
      rw [h2]; exact hg.2.1 (0, 1, 32) (by simp [raS, calleeAt, ioCmov]))
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, raS, calleeAt, ioCmov])
    (fun _ => by simp [rgnsC, SRgn.rgnC, ALen.val, raS, calleeAt, ioCmov])
    fun _ _ st m _ vs _ hi hp => by
      rcases vs with _ | ⟨d | _ | _ | _ | _ | _, _ | ⟨s | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | κ | _, _ | _⟩⟩⟩ <;>
        simp only [InsRel, All2, raS, calleeAt, ioCmov, Rel, In.kd, ALen.val, and_true, and_false,
          false_and] at hi
      simp only [BitVec.add_zero] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      simp only [OutsRel, All2, raS, calleeAt, ioCmov, cmovV, Rel, BitVec.add_zero, and_true]
      rw [← encK_decode (bytesAt_length m (st.regs 0) 32), decodeInt_words m (st.regs 0) 8]
      congr 1; apply wsum_congr; intro j hj
      rw [hp.1 j (by rw [hp.2]; simp; omega), word_dW _ _ hj, word_dW _ _ hj]

/-- **`m0c_copy`'s adapter** for 32 bytes. -/
noncomputable def copyB (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (raS .copy) :=
  Ed25519FePow.copyAd b Rs _ _ (.inr (.inr ⟨rfl, rfl⟩)) id fun _ _ st m vs hi hw => by
    rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩ <;>
      simp only [InsRel, All2, ioCopy, Rel, In.kd, and_true, and_false] at hi
    simp only [OutsRel, All2, ioCopy, Rel, BitVec.add_zero, id, and_true] at hi ⊢
    have e : decodeInt (bytesAt m (st.regs 0) 32) = decodeInt (bytesAt st.mem (st.regs 1) 32) := by
      have := Ed25519FePow.decode_feVal m (st.regs 0); rw [hw, ← Ed25519FePow.decode_feVal] at this; exact_mod_cast this
    rw [← encK_decode (bytesAt_length m (st.regs 0) 32), e, encK_decode (bytesAt_length _ _ _), hi]

/-- The callees' values. -/
def raV : RA → List V → List V
  | .mp => mpV 9
  | .cmov => cmovV
  | .copy => id

/-- **The callees' adapters** in build `b`. -/
noncomputable def raAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (raS a)
  | .mp => Ed25519ScMuladd.mpAd b Rs 9 (by decide) (by decide)
  | .cmov => cmovAd b Rs
  | .copy => copyB b Rs

theorem raAd_sem (b : Build) (Rs : Rels) :
    ∀ a vs, @Ad.sem Rs b.bytes b.size b.codeBytes _ (raAd b Rs a).ad vs = raV a vs
  | .mp, _ | .cmov, _ | .copy, _ => rfl

end

/-! ## The value -/

section
open M0Crypto.Release.Ed25519Words (wsum)

/-- A round on `R`'s low words `lo` and top word `hi`: `R − L` where `L ≤ R`, else `R`, by the
words `m0c_cmov` selects. -/
def rndF (lo hi l : List Byte) : List Byte :=
  encK 32 (wsum (fun j => (Ed25519WordLoop.sel
    (if decodeInt l ≤ decodeInt (lo ++ hi) then BitVec.allOnes 32 else 0#32) (dW lo j)
    (dW (((subV (decodeInt (lo ++ hi)) (decodeInt l)).drop 0).take 32) j)).toNat) 8)

/-- What the program leaves at `out`, from the entry bytes `m0`. -/
def redF (c : Ctx) (m0 : Mem) : List Byte :=
  let l9 := bytesAt m0 (c.ptr 3 + BitVec.ofNat 32 0) 36
  let q2 := encK (8 * 9) (decodeInt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 28) 36) *
    decodeInt (bytesAt m0 (c.ptr 2 + BitVec.ofNat 32 0) 36))
  let q4 := encK (8 * 9) (decodeInt ((q2.drop 36).take 36) * decodeInt l9)
  let d := subV (decodeInt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) 36)) (decodeInt ((q4.drop 0).take 36))
  rndF (rndF (d.take 32) (d.drop 32) l9) (d.drop 32) l9

theorem red_ev (c : Ctx) (m0 : Mem) :
    Prog.ev raS rbS redQ.geo raV rbV c m0 redP redQ.st0 (fun _ => .none) (.ex 0 0) = .b (redF c m0) := rfl

end

/-! ## The result -/

section
open M0Crypto.Release.Ed25519Words (wsum wsum_succ pow32_succ)
open M0Crypto.Spec.Ed25519 (L)
open M0Crypto.Release.Ed25519Barrett (mu)

/-- `l` is its first `n` bytes and the rest. -/
theorem dec_tk (l : List Byte) (n : Nat) (hn : n ≤ l.length) :
    decodeInt l = decodeInt (l.take n) + 2 ^ (8 * n) * decodeInt (l.drop n) ∧ decodeInt (l.take n) < 2 ^ (8 * n) := by
  have h := decodeInt_append (l.take n) (l.drop n)
  have := Ed25519Bytes.decodeInt_lt (l.take n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  rw [List.length_take_of_le hn] at this
  exact ⟨h, this⟩

theorem dec_encK (k N : Nat) : decodeInt (encK k N) = N % 2 ^ (8 * k) := decodeInt_encodeK N k

theorem encK_length (k N : Nat) : (encK k N).length = k := by simp [encK]

/-- The words of `l` sum to its number below `2^(32 n)`. -/
theorem wsum_dW (l : List Byte) : ∀ n, wsum (fun j => (dW l j).toNat) n = decodeInt l % 2 ^ (32 * n)
  | 0 => by simp [wsum, Nat.mod_one]
  | n + 1 => by rw [wsum_succ, wsum_dW l n, pow32_succ, Nat.mod_mul, dW, BitVec.toNat_ofNat]

theorem sel0 (a b : Word) : Ed25519WordLoop.sel 0#32 a b = a := Ed25519WordLoop.sel_zero a b

/-- **A round** on `R`'s low words with a zero top word: `R − L` where `L ≤ R`, else `R`. -/
theorem rndF_eq {lo hi l : List Byte} (hlo : lo.length = 32) (hhi : decodeInt hi = 0) :
    rndF lo hi l = encK 32 (if decodeInt l ≤ decodeInt lo then decodeInt lo - decodeInt l else decodeInt lo) := by
  have hR := Ed25519Bytes.decodeInt_lt lo
  have e : decodeInt (lo ++ hi) = decodeInt lo := by rw [decodeInt_append, hhi, Nat.mul_zero, Nat.add_zero]
  rw [hlo] at hR
  by_cases h : decodeInt l ≤ decodeInt lo
  · obtain ⟨e2, h2⟩ := dec_tk (subV (decodeInt lo) (decodeInt l)) 32 (by rw [subV, encK_length]; omega)
    have e3 : decodeInt (subV (decodeInt lo) (decodeInt l)) =
        (decodeInt lo + 2 ^ 288 - decodeInt l) % 2 ^ 288 % 2 ^ (8 * 36) := dec_encK _ _
    simp only [rndF, e, h, ite_true, Ed25519WordLoop.sel_ones, List.drop_zero, wsum_dW]
    generalize decodeInt (List.take 32 (subV (decodeInt lo) (decodeInt l))) = a at e2 h2 ⊢
    generalize decodeInt (List.drop 32 (subV (decodeInt lo) (decodeInt l))) = b at e2
    generalize decodeInt (subV (decodeInt lo) (decodeInt l)) = c at e2 e3
    generalize decodeInt lo = R at *
    generalize decodeInt l = L' at *
    simp only [Nat.reduceMul] at hR e2 h2 e3 ⊢
    rw [show a % 2 ^ 256 = R - L' by omega]
  · simp only [rndF, e, h, ite_false, sel0, wsum_dW]
    simp only [Nat.reduceMul] at hR ⊢
    rw [Nat.mod_eq_of_lt hR]

theorem dec_at (m : Mem) (a : Word) (k n : Nat) :
    decodeInt (bytesAt m a (k + n)) = decodeInt (bytesAt m a k) + 2 ^ (8 * k) * decodeInt (bytesAt m (a + BitVec.ofNat 32 k) n) ∧
      decodeInt (bytesAt m a k) < 2 ^ (8 * k) := by
  have := Ed25519Bytes.decodeInt_lt (bytesAt m a k)
  rw [bytesAt_length] at this
  rw [bytesAt_split, decodeInt_append, bytesAt_length]; exact ⟨rfl, this⟩

/-- The high and low 36 bytes of an 18-word product. -/
theorem dec_hi (N : Nat) (h : N < 2 ^ 288 * 2 ^ 288) : decodeInt (((encK (8 * 9) N).drop 36).take 36) = N / 2 ^ 288 := by
  change decodeInt (((encK 72 N).drop 36).take 36) = _
  obtain ⟨e, h2⟩ := dec_tk (encK 72 N) 36 (by rw [encK_length]; omega)
  rw [dec_encK] at e
  rw [List.take_of_length_le (by rw [List.length_drop, encK_length]; omega)]
  simp only [Nat.reduceMul] at e h2
  omega

theorem dec_lo (N : Nat) : decodeInt (((encK (8 * 9) N).drop 0).take 36) = N % 2 ^ 288 := by
  change decodeInt (((encK 72 N).drop 0).take 36) = _
  obtain ⟨e, h2⟩ := dec_tk (encK 72 N) 36 (by rw [encK_length]; omega)
  rw [dec_encK] at e
  rw [List.drop_zero]
  simp only [Nat.reduceMul] at e h2
  omega

theorem dec36 (D : Nat) (h : D < 2 ^ 256) :
    decodeInt ((encK 36 D).take 32) = D ∧ decodeInt ((encK 36 D).drop 32) = 0 ∧ ((encK 36 D).take 32).length = 32 := by
  obtain ⟨e, h2⟩ := dec_tk (encK 36 D) 32 (by rw [encK_length]; omega)
  rw [dec_encK] at e
  simp only [Nat.reduceMul] at e h2
  refine ⟨by omega, by omega, List.length_take_of_le (by rw [encK_length]; omega)⟩

/-- **The value is the input mod `L`**: `Ed25519Barrett.barrett` bounds `R` below `3 L`, and
`two_sub_mod` takes the two rounds to `R mod L`. -/
theorem redF_eq (c : Ctx) (m0 : Mem) (hmu : decodeInt (bytesAt m0 (c.ptr 2 + BitVec.ofNat 32 0) 36) = mu)
    (hl : decodeInt (bytesAt m0 (c.ptr 3 + BitVec.ofNat 32 0) 36) = L) :
    redF c m0 = encodeInt (decodeInt (bytesAt m0 (c.ptr 1) 64) % L) := by
  obtain ⟨a1, a2⟩ := dec_at m0 (c.ptr 1) 28 36
  obtain ⟨b1, b2⟩ := dec_at m0 (c.ptr 1) 36 28
  have hX := Ed25519Bytes.decodeInt_lt (bytesAt m0 (c.ptr 1) 64)
  rw [bytesAt_length] at hX
  have h0 : decodeInt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 0) 36) = decodeInt (bytesAt m0 (c.ptr 1) 64) % 2 ^ 288 := by
    rw [BitVec.add_zero]; simp only [Nat.reduceMul, Nat.reduceAdd] at b1 b2 ⊢; omega
  have h1 : decodeInt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 28) 36) = decodeInt (bytesAt m0 (c.ptr 1) 64) / 2 ^ 224 := by
    simp only [Nat.reduceMul, Nat.reduceAdd] at a1 a2 ⊢; omega
  generalize decodeInt (bytesAt m0 (c.ptr 1) 64) = X at hX h0 h1
  simp only [Nat.reduceMul] at hX
  have hb := Ed25519Barrett.barrett X hX
  have hmu' : mu < 2 ^ 288 := by decide +kernel
  have hN : X / 2 ^ 224 * mu < 2 ^ 288 * 2 ^ 288 := by
    have : X / 2 ^ 224 < 2 ^ 288 := by
      have := Ed25519Bytes.decodeInt_lt (bytesAt m0 (c.ptr 1 + BitVec.ofNat 32 28) 36)
      rw [bytesAt_length, h1] at this; simpa only [Nat.reduceMul] using this
    have h2 := Nat.mul_lt_mul_of_lt_of_lt this hmu'; exact h2
  simp only [redF, h0, h1, hmu, hl, dec_hi _ hN, dec_lo]
  generalize X / 2 ^ 224 * mu / 2 ^ 288 = q at hb
  generalize hP : q * L = P at hb
  have h3 := Ed25519Barrett.three_L_lt
  rw [subV, show (X % 2 ^ 288 + 2 ^ 288 - P % 2 ^ 288) % 2 ^ 288 = X - P by omega]
  obtain ⟨d1, d2, d3⟩ := dec36 (X - P) (by omega)
  rw [rndF_eq d3 d2, hl, d1, rndF_eq (encK_length 32 _) d2, hl, dec_encK,
    Nat.mod_eq_of_lt (by simp only [Nat.reduceMul]; split <;> omega), Ed25519Barrett.two_sub_mod L (X - P) (by omega)]
  have e : X % L = (X - P) % L := by
    conv => lhs; rw [show X = X - P + q * L by omega]
    exact Nat.add_mul_mod_self_right _ _ _
  rw [e]; rfl

/-- Bytes of the code at `base`. -/
theorem code_bytes {m : Mem} {base : Word} {B : List (BitVec 8)} (h : CodeAt m base B) {o n : Nat}
    (hn : o + n ≤ B.length) : bytesAt m (base + BitVec.ofNat 32 o) n = (B.drop o).take n := by
  apply List.ext_getElem (by rw [bytesAt_length, List.length_take, List.length_drop]; omega)
  intro i h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [ofNat_add_assoc, h]

/-- **`m0c_sc_reduce`'s result** from the program's value, with `mu` and `L` at the code labels. -/
theorem red_post {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels} {semA : RA → List V → List V}
    (hA : ∀ a vs, semA a vs = raV a vs) (hlen : ed_mu + 36 ≤ B.length ∧ ed_l9 + 36 ≤ B.length)
    (hmu : decodeInt ((B.drop ed_mu).take 36) = mu) (hl : decodeInt ((B.drop ed_l9).take 36) = L)
    (c : Ctx) (sp : Word) (st : State) (m : Mem) (r0 : Word) (vs : List V)
    (hi : InsRel Rs c sp redQ.s.io st vs) (hp : redQ.post raS rbS Rs semA (fun b => (rbD Rs b).sem) st m r0) :
    OutsRel Rs c sp redQ.s.io st m (semE .reduce vs) := by
  obtain ⟨hg, base, m0, hcode, hm, ho⟩ := hp
  obtain rfl : semA = raV := funext fun a => funext (hA a)
  have hB : (fun b => (rbD Rs b).sem) = rbV := funext fun b => by cases b <;> rfl
  rw [hB] at ho
  generalize hcc : redQ.ctx base (redQ.s.pub base st) = cc at ho hm
  dsimp only at ho
  have hp1 : cc.ptr 1 = st.regs 1 := by
    rw [← hcc, CalleeP.ctx_ptr (by decide)]; exact CalleeP.reg_pub (r := 1) (by decide)
  have hp2 : cc.ptr 2 = base + BitVec.ofNat 32 ed_mu := by
    have h := CalleeP.ctx_code (q := redQ) (base := base) (p := redQ.s.pub base st) (j := 0) (by decide)
    rw [show redQ.xr.length + 0 = 2 by decide] at h; rw [← hcc, h]; rfl
  have hp3 : cc.ptr 3 = base + BitVec.ofNat 32 ed_l9 := by
    have h := CalleeP.ctx_code (q := redQ) (base := base) (p := redQ.s.pub base st) (j := 1) (by decide)
    rw [show redQ.xr.length + 1 = 3 by decide] at h; rw [← hcc, h]; rfl
  rw [show redQ.outVals _ = [.b (redF cc m0)] from rfl] at ho
  have hio : redQ.s.io = io1 64 (.bytes 64) 32 .sc := rfl
  rw [hio] at hi ho ⊢
  rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | _⟩ <;>
    simp only [InsRel, All2, io1, Rel, In.kd, and_true, and_false] at hi
  simp only [OutsRel, All2, io1, Iface.base, Kd.base, Rel, List.map, and_true] at ho ⊢
  rename_i h
  have hin : bytesAt m0 (cc.ptr 1) 64 = h := by
    rw [← hi, BitVec.add_zero, hp1]
    exact Footprint.bytesAt_eq_of fun k hk => hm 1 _ rfl rfl _ ⟨_, List.mem_singleton_self _, ⟨k, hk, by rw [hp1]⟩⟩
  have hc2 : decodeInt (bytesAt m0 (cc.ptr 2 + BitVec.ofNat 32 0) 36) = mu := by
    rw [BitVec.add_zero, hp2, code_bytes hcode hlen.1, hmu]
  have hc3 : decodeInt (bytesAt m0 (cc.ptr 3 + BitVec.ofNat 32 0) 36) = L := by
    rw [BitVec.add_zero, hp3, code_bytes hcode hlen.2, hl]
  simp only [semE, All2, and_true]
  rw [ho, redF_eq cc m0 hc2 hc3, hin, decodeInt_encodeInt]
  exact ⟨rfl, Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ Ed25519Barrett.L_pos)⟩

/-- **`m0c_sc_reduce`'s adapter** in build `b`. -/
noncomputable def redAd (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) (eaS .reduce) :=
  CalleeP.adE (cb := b.codeBytes) (q := redQ) (cE := raS) (bE := rbS) (raAd b Rs) (rbD Rs)
    (CalleeP.ok_parts red_ok).choose_spec (red_code b) (semE .reduce)
    fun c sp st m r0 vs _ hi hp => red_post (cb := b.codeBytes) (raAd_sem b Rs) (by cases b <;> decide +kernel)
      (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) c sp st m r0 vs hi hp

end

end M0Crypto.Release.Ed25519ScReduceProg
