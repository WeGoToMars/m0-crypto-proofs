import M0Crypto.Release.Ed25519Sha512Pass

set_option linter.unusedSimpArgs false

/-!
# `m0c_sha512_block`

`block_tspec`: the routine at `O` takes the state `H` at `r0` (eight pairs) and the block at
`r1` (128 bytes), and leaves `compress H block` at `r0`. It reads only the block, `H`, its own
frame and the code (the `K` table and its literal). It writes only `H` and its frame. Its trace
depends only on `r0`, `r1` and `sp`. The steps are the big-endian load of the block into `W`
(`wload_run`, a counted loop), the copy `V = H` (`cpN`), the ten groups (`loop_frag`), and
`H += V` (`hAddN`). `sha512_block_tspec` instantiates it in both builds; the `K` table and the
literal are decided per build (`kOk`, `litOk`).
-/

namespace M0Crypto.Release.Ed25519Sha512Block

open M0Crypto.Armv6M (Word Reg LowReg State Mem read32 write32 slot)
open M0Crypto.Thumb
open M0Crypto.Release.Ed25519Sha512Code
open M0Crypto.Release.Ed25519Sha512Exec
open M0Crypto.Release.Ed25519Sha512Round
open M0Crypto.Release
open M0Crypto.Release.Footprint
open M0Crypto.Release.Frame (Disj)
open M0Crypto.Release.Ed25519Sha512Pass (O D fsp Inv Env Lay lay_of loop_frag)
open M0Crypto.Release.Ed25519Lookup (kS ldS)
open M0Crypto.Release.StackEffect (EffT effT_of_gp GP SIR frameK_gp sir_segR sir_quietC blk_seg blkE_seg blkChk
  winChk atomOf spRg InR inR_append inRD_win hv_at inRD_atom1 inRD_of inR_sp inR_sp_of inR_one reg_split reg_in
  reg_off reg_sub_above addrE_none InRD al_reg)
open M0Crypto.Release.TraceSpec (BelowEntry AtOrAboveSp)
open M0Crypto.Sym
open M0Crypto.Release.Routine

/-- `stm n!, {a, b}`. -/
theorem nx_stm2 (s : State) (n : LowReg) (l : BitVec 8) (a b : LowReg) (hl : listRegs l = [a, b]) :
    ((Instr.stm n l).next s).mem =
      write32 (write32 s.mem (s.regs n.toReg) (s.regs a.toReg)) (s.regs n.toReg + 4#32) (s.regs b.toReg) ∧
    ∀ r : Reg, r ≠ 15 → ((Instr.stm n l).next s).regs r =
      if r = n.toReg then s.regs n.toReg + 8#32 else s.regs r := by
  refine ⟨?_, fun r hr => ?_⟩
  · simp [Instr.next, Instr.exec, hl, bitCount, storeWords, State.setReg, State.reg]
  · simp [Instr.next, Instr.exec, hl, bitCount, storeWords, State.setReg, State.reg, hr]

/-- The pair `x` stored at `a`, low word first. -/
def wpair (m : Mem) (a : Word) (x : BitVec 64) : Mem :=
  write32 (write32 m a (loW x)) (a + 4#32) (hiW x)

/-- **One word of `H += V`** (`hAddW`), `r0` at `H`, `r1` at `V`. -/
theorem hAddW_run (u : State) :
    (execAll hAddW u).regs 0 = u.regs 0 + 8#32 ∧ (execAll hAddW u).regs 1 = u.regs 1 + 8#32 ∧
    (execAll hAddW u).mem = wpair u.mem (u.regs 0) (pairAt u.mem (u.regs 1) + pairAt u.mem (u.regs 0)) := by
  have e : hAddW = [.ldm 1 0x0c, .memImm .ldr 4 0 0, .memImm .ldr 5 0 1] ++ addP 2 3 4 5 ++ [.stm 0 0x0c] := rfl
  have l2 : listRegs 0x0c = [2, 3] := by decide
  rw [e]
  simp only [execAll_append, execAll]
  have m1 := (nx_stm2 (execAll (addP 2 3 4 5) ((Instr.memImm .ldr 5 0 1).next ((Instr.memImm .ldr 4 0 0).next
    ((Instr.ldm 1 0x0c).next u)))) 0 0x0c 2 3 l2)
  refine ⟨?_, ?_, ?_⟩
  · rw [m1.2 0 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 2 3 l2 (by decide)]
  · rw [m1.2 1 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 2 3 l2 (by decide)]
  · rw [m1.1]
    rsimp [nx_ldm2 _ 1 _ 2 3 l2 (by decide), wpair, pairAt]
    rw [show (BitVec.ofNat 32 ((1 : BitVec 5).toNat * 4)) = 4#32 from rfl, show (BitVec.ofNat 32 ((0 : BitVec 5).toNat * 4)) = 0#32 from rfl, BitVec.add_zero]

/-- **One pass of the big-endian load** (`wload`), `r1` at the block, `r2` at `W`, `r3` the count. -/
theorem wload_run (u : State) :
    (execAll wload u).regs 1 = u.regs 1 + 8#32 ∧ (execAll wload u).regs 2 = u.regs 2 + 8#32 ∧
    (execAll wload u).regs 3 = u.regs 3 - 1#32 ∧ (execAll wload u).z = (u.regs 3 - 1#32 == 0) ∧
    (execAll wload u).mem = wpair u.mem (u.regs 2)
      (revBytes (read32 u.mem (u.regs 1)) ++ revBytes (read32 u.mem (u.regs 1 + 4#32))) := by
  have l45 : listRegs 0x30 = [4, 5] := by decide
  have l46 : listRegs 0x50 = [4, 6] := by decide
  have e : wload = [.ldm 1 0x30, .rev 6 4, .rev 4 5, .stm 2 0x50] ++ [.subImm8 3 1] := rfl
  rw [e, execAll_append]
  simp only [execAll]
  have m1 := nx_stm2 ((Instr.rev 4 5).next ((Instr.rev 6 4).next ((Instr.ldm 1 0x30).next u))) 2 0x50 4 6 l46
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [regs_subImm8 _ _ _ _ (by decide), m1.2 1 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 4 5 l45 (by decide), nx_rev]
  · rw [regs_subImm8 _ _ _ _ (by decide), m1.2 2 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 4 5 l45 (by decide), nx_rev]
  · rw [regs_subImm8 _ _ _ _ (by decide), m1.2 3 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 4 5 l45 (by decide), nx_rev]
    rfl
  · rw [z_subImm8, M0Crypto.Proofs.toReg_3, m1.2 3 (by decide)]
    rsimp [nx_ldm2 _ 1 _ 4 5 l45 (by decide), nx_rev]
    rfl
  · rw [mem_subImm8, m1.1]
    rsimp [nx_ldm2 _ 1 _ 4 5 l45 (by decide), nx_rev, wpair, hiW_app, loW_app]

/-- `ldm 0!, {r2-r5}; stm 1!, {r2-r5}`: one chunk of `V = H`. -/
def cpChunk : List Instr := [.ldm 0 0x3c, .stm 1 0x3c]

theorem cpChunk_run (u : State) :
    (execAll cpChunk u).regs 0 = u.regs 0 + 16#32 ∧ (execAll cpChunk u).regs 1 = u.regs 1 + 16#32 ∧
    (execAll cpChunk u).mem = wpair (wpair u.mem (u.regs 1) (pairAt u.mem (u.regs 0))) (u.regs 1 + 8#32)
      (pairAt u.mem (u.regs 0 + 8#32)) := by
  have hl : listRegs 60#8 = [2, 3, 4, 5] := by decide
  have h0 : (60#8).getLsbD 0 = false := by decide
  have h1 : (60#8).getLsbD 1 = false := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) [cpChunk, execAll, Instr.next, Instr.exec, hl, h0, h1, bitCount, loadRegs,
      storeWords, State.setReg, State.reg, State.pc, M0Crypto.Proofs.toReg_0, M0Crypto.Proofs.toReg_1,
      M0Crypto.Proofs.toReg_2, M0Crypto.Proofs.toReg_3, M0Crypto.Proofs.toReg_4, M0Crypto.Proofs.toReg_5,
      wpair, pairAt, BitVec.add_assoc]

/-! ## Pairs written in a row -/

theorem wpair_memEq (m : Mem) (a : Word) (x : BitVec 64) : MemEq [⟨a, 8⟩] m (wpair m a x) := by
  intro y hy
  have h : ∀ o < 8, y ≠ a + BitVec.ofNat 32 o := fun o ho he => hy ⟨_, List.mem_singleton_self _, o, ho, he⟩
  simp only [wpair]
  rw [M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => h (4 + k) (by omega) (by
      rw [he, BitVec.add_assoc, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]),
    M0Crypto.Armv6M.write32_other _ _ _ _ fun k hk he => h k (by omega) he]

theorem pairAt_wpair (m : Mem) (a : Word) (x : BitVec 64) : pairAt (wpair m a x) a = x := by
  have e := read32_write32_slotN (write32 m a (loW x)) a (hiW x) 1 0 (by decide) (by decide)
  simp only [slot, Nat.reduceMul, BitVec.add_zero, show (BitVec.ofNat 32 4 : Word) = 4#32 from rfl,
    Nat.one_ne_zero, ite_false] at e
  simp only [pairAt, wpair, M0Crypto.Armv6M.read32_write32_same, e, hiW_loW]

theorem rep_succ (c : List Instr) (k : Nat) (u : State) :
    execAll (List.replicate (k + 1) c).flatten u = execAll c (execAll (List.replicate k c).flatten u) := by
  rw [List.replicate_succ', List.flatten_append, execAll_append, List.flatten_singleton]

/-- **`k` words of `H += V`**, `r0` at `H`, `r1` at `V`. -/
theorem hAddN (u : State) (hd : Disj (u.regs 0) 64 (u.regs 1) 64) : ∀ k ≤ 8,
    (execAll (List.replicate k hAddW).flatten u).regs 0 = u.regs 0 + BitVec.ofNat 32 (8 * k) ∧
    (execAll (List.replicate k hAddW).flatten u).regs 1 = u.regs 1 + BitVec.ofNat 32 (8 * k) ∧
    MemEq [⟨u.regs 0, 8 * k⟩] u.mem (execAll (List.replicate k hAddW).flatten u).mem ∧
    ∀ i < k, pairAt (execAll (List.replicate k hAddW).flatten u).mem (u.regs 0 + BitVec.ofNat 32 (8 * i)) =
      pairAt u.mem (u.regs 1 + BitVec.ofNat 32 (8 * i)) + pairAt u.mem (u.regs 0 + BitVec.ofNat 32 (8 * i))
  | 0, _ => by simp [MemEq.rfl', execAll]
  | k + 1, hk => by
    obtain ⟨r0, r1, hm, hp⟩ := hAddN u hd k (by omega)
    rw [rep_succ]
    generalize execAll (List.replicate k hAddW).flatten u = v at r0 r1 hm hp
    obtain ⟨e0, e1, em⟩ := hAddW_run v
    have := (u.regs 0).isLt; have := (u.regs 1).isLt
    fp_simp at hd
    have hw := wpair_memEq v.mem (v.regs 0) (pairAt v.mem (v.regs 1) + pairAt v.mem (v.regs 0))
    rw [r0, r1] at hw
    refine ⟨by rw [e0, r0, ofNat_add_assoc, Nat.mul_succ], by rw [e1, r1, ofNat_add_assoc, Nat.mul_succ], ?_,
      fun i hi => ?_⟩
    · rw [em, r0, r1]; refine (hm.trans hw).mono ?_
      simp only [List.cons_append, List.nil_append]; fp_tac
    · rw [em, r0, r1]
      by_cases hik : i < k
      · rw [Ed25519Sha512Pass.MemEq.pairAt hw (by fp_tac), hp i hik]
      · obtain rfl : i = k := by omega
        rw [pairAt_wpair, Ed25519Sha512Pass.MemEq.pairAt hm (by fp_tac), Ed25519Sha512Pass.MemEq.pairAt hm (by fp_tac)]

/-- **`k` chunks of `V = H`**, `r0` at `H`, `r1` at `V`. -/
theorem cpN (u : State) (hd : Disj (u.regs 0) 64 (u.regs 1) 64) : ∀ k ≤ 4,
    (execAll (List.replicate k cpChunk).flatten u).regs 0 = u.regs 0 + BitVec.ofNat 32 (8 * (2 * k)) ∧
    (execAll (List.replicate k cpChunk).flatten u).regs 1 = u.regs 1 + BitVec.ofNat 32 (8 * (2 * k)) ∧
    MemEq [⟨u.regs 1, 8 * (2 * k)⟩] u.mem (execAll (List.replicate k cpChunk).flatten u).mem ∧
    ∀ i < 2 * k, pairAt (execAll (List.replicate k cpChunk).flatten u).mem (u.regs 1 + BitVec.ofNat 32 (8 * i)) =
      pairAt u.mem (u.regs 0 + BitVec.ofNat 32 (8 * i))
  | 0, _ => by simp [MemEq.rfl', execAll]
  | k + 1, hk => by
    obtain ⟨r0, r1, hm, hp⟩ := cpN u hd k (by omega)
    rw [rep_succ]
    generalize execAll (List.replicate k cpChunk).flatten u = v at r0 r1 hm hp
    obtain ⟨e0, e1, em⟩ := cpChunk_run v
    have := (u.regs 0).isLt; have := (u.regs 1).isLt
    fp_simp at hd
    have a8 : ∀ x : Word, x + BitVec.ofNat 32 (8 * (2 * k)) + 8#32 = x + BitVec.ofNat 32 (8 * (2 * k + 1)) :=
      fun x => by rw [ofNat_add_assoc, show 8 * (2 * k) + 8 = 8 * (2 * k + 1) by omega]
    rw [r0, r1, a8, a8] at em
    have hw1 := wpair_memEq v.mem (u.regs 1 + BitVec.ofNat 32 (8 * (2 * k))) (pairAt v.mem (u.regs 0 + BitVec.ofNat 32 (8 * (2 * k))))
    have hw2 := wpair_memEq (wpair v.mem (u.regs 1 + BitVec.ofNat 32 (8 * (2 * k))) (pairAt v.mem (u.regs 0 + BitVec.ofNat 32 (8 * (2 * k)))))
      (u.regs 1 + BitVec.ofNat 32 (8 * (2 * k + 1))) (pairAt v.mem (u.regs 0 + BitVec.ofNat 32 (8 * (2 * k + 1))))
    have e16 : 8 * (2 * k) + 16 = 8 * (2 * (k + 1)) := by omega
    refine ⟨by rw [e0, r0, ofNat_add_assoc, e16], by rw [e1, r1, ofNat_add_assoc, e16], ?_,
      fun i hi => ?_⟩
    · rw [em]; refine ((hm.trans hw1).trans hw2).mono ?_
      simp only [List.cons_append, List.nil_append]; fp_tac
    · rw [em]
      by_cases hik : i < 2 * k
      · rw [Ed25519Sha512Pass.MemEq.pairAt hw2 (by fp_tac), Ed25519Sha512Pass.MemEq.pairAt hw1 (by fp_tac), hp i hik]
      · rcases show i = 2 * k ∨ i = 2 * k + 1 by omega with rfl | rfl
        · rw [Ed25519Sha512Pass.MemEq.pairAt hw2 (by fp_tac), pairAt_wpair, Ed25519Sha512Pass.MemEq.pairAt hm (by fp_tac)]
        · rw [pairAt_wpair, Ed25519Sha512Pass.MemEq.pairAt hm (by fp_tac)]

/-! ## The specification's words -/

open M0Crypto.Spec.Sha512 (compress parse toWord)
open M0Crypto.Release.Ed25519Sha512Rounds (codeGroups compress_code)

/-- The eight words of `H` at `a`, each a pair, low word first. -/
def hOf (m : Mem) (a : Word) : Array (BitVec 64) :=
  ((List.range 8).map fun i => pairAt m (a + BitVec.ofNat 32 (8 * i))).toArray

/-- The 128 bytes of a block at `p`. -/
def blkOf (m : Mem) (p : Word) : List (BitVec 8) := (List.range (8 * 16)).map fun i => m (p + BitVec.ofNat 32 i)

theorem hOf_get (m : Mem) (a : Word) {i : Nat} (hi : i < 8) : (hOf m a)[i]! = pairAt m (a + BitVec.ofNat 32 (8 * i)) := by
  simp [hOf, hi]

/-- Word `j` of the block: the two words at `p + 8 j`, each reversed (`wload`). -/
theorem parse_blk (m : Mem) (p : Word) {j : Nat} (hj : j < 16) :
    (parse (blkOf m p))[j]! = revBytes (read32 m (p + BitVec.ofNat 32 (8 * j))) ++
      revBytes (read32 m (p + BitVec.ofNat 32 (8 * j) + 4#32)) := by
  have e : ((blkOf m p).drop (8 * j)).take 8 = (List.range 8).map fun k => m (p + BitVec.ofNat 32 (8 * j + k)) := by
    apply List.ext_getElem
    · simp [blkOf]; omega
    · intro k h1 h2; simp [blkOf]
  simp only [parse, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, e]
  rw [show (List.range 8).map (fun k => m (p + BitVec.ofNat 32 (8 * j + k))) =
    [m (p + BitVec.ofNat 32 (8 * j + 0)), m (p + BitVec.ofNat 32 (8 * j + 1)), m (p + BitVec.ofNat 32 (8 * j + 2)),
     m (p + BitVec.ofNat 32 (8 * j + 3)), m (p + BitVec.ofNat 32 (8 * j + 4)), m (p + BitVec.ofNat 32 (8 * j + 5)),
     m (p + BitVec.ofNat 32 (8 * j + 6)), m (p + BitVec.ofNat 32 (8 * j + 7))] from rfl,
    Ed25519Sha512Pairs.toWord_pair]
  simp only [Ed25519Sha512Pairs.leWord, read32, ofNat_add_assoc, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd,
    show (1#32 : Word) = BitVec.ofNat 32 1 from rfl, show (2#32 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3#32 : Word) = BitVec.ofNat 32 3 from rfl, show (4#32 : Word) = BitVec.ofNat 32 4 from rfl]
  rfl

/-- Word `i` of `compress`: the variables after the ten groups plus `H`. -/
theorem compress_pairs (H : Array (BitVec 64)) (block : List (BitVec 8)) {i : Nat} (hi : i < 8) :
    (compress H block)[i]! = (codeGroups (fun j => (parse block)[j]!) (fun j => H[j]!) GROUPS).2 i + H[i]! := by
  rw [compress_code]
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl

/-! ## The `K` table and the literal -/

open M0Crypto.Artifacts

/-- The little-endian word at `o` of a byte list. -/
def wordL (l : List (BitVec 8)) (o : Nat) : Word :=
  l.getD (o + 3) 0 ++ l.getD (o + 2) 0 ++ l.getD (o + 1) 0 ++ l.getD o 0

/-- The table at `sha512_K` holds the eighty constants, each a pair, low word first. -/
def kOk (B : List (BitVec 8)) : Bool :=
  ((List.range 80).all fun i => wordL ((B.drop Ed25519Compact.sha512_K).take (8 * 80)) (8 * i + 4) ++
    wordL ((B.drop Ed25519Compact.sha512_K).take (8 * 80)) (8 * i) == M0Crypto.Spec.Sha512.K[i]!)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

theorem codeWord_K {y : Nat} (hy : y + 4 ≤ 8 * 80) :
    Frame.codeWord (Ed25519Compact.sha512_K + y) = wordL ((B.drop Ed25519Compact.sha512_K).take (8 * 80)) y := by
  simp only [Frame.codeWord, wordL, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp only [show y + 3 < 8 * 80 by omega, show y + 2 < 8 * 80 by omega, show y + 1 < 8 * 80 by omega,
    show y < 8 * 80 by omega, ite_true, Nat.add_assoc]

theorem ktab (hK : kOk B = true) (hBS : Ed25519Compact.sha512_K + 8 * 80 ≤ BS) {m : Mem} {base : Word}
    (hc : CodeAt m base B) {i : Nat} (hi : i < 80) :
    pairAt m (base + BitVec.ofNat 32 Ed25519Compact.sha512_K + BitVec.ofNat 32 (8 * i)) = M0Crypto.Spec.Sha512.K[i]! := by
  simp only [kOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hK
  rw [pairAt, ofNat_add_assoc, ofNat_add_assoc, ofNat_add_assoc, Frame.read32_code hc _ (by omega),
    Frame.read32_code hc _ (by omega), codeWord_K (by omega), codeWord_K (by omega)]
  exact hK i hi

/-- The literal word plus the pc of `add r7, pc` is `sha512_K`. -/
def litOk : Bool :=
  Frame.codeWord (B := B) (litOff (oLit O) (Ed25519Sha512Code.litImm O pool)) + BitVec.ofNat 32 (oLit O + 2 + 4) ==
    BitVec.ofNat 32 Ed25519Compact.sha512_K

end

/-! ## The contract -/

open M0Crypto.Release.TraceSpec (InStackWindow)

/-- **`m0c_sha512_block`**: `H` at `r0` (eight pairs, low word first) becomes `compress H block`
for the 128 bytes at `r1`. -/
def blockR : Routine where
  entry := O
  code := Ed25519Sha512Pass.cs
  stack := D
  Pre := fun _ s => (s.regs 0).toNat % 4 = 0 ∧ (s.regs 1).toNat % 4 = 0
  wr := fun s => [⟨s.regs 0, 8 * 8⟩]
  rd := fun s => [⟨s.regs 1, 8 * 16⟩, ⟨s.regs 0, 8 * 8⟩]
  Post := fun s m _ => ∀ i < 8, pairAt m (s.regs 0 + BitVec.ofNat 32 (8 * i)) =
    (compress (hOf s.mem (s.regs 0)) (blkOf s.mem (s.regs 1)))[i]!
  clob := Ed25519Routines.hiRegs

/-- The public values of `m0c_sha512_block`: `H`, the block and `sp`. -/
def blockPub (_ : Word) (s : State) : Nat → Word := pubOf [s.regs 0, s.regs 1, s.regs 13]

/-- The prologue after `push {lr}; sub sp`. -/
def preB : List Instr := [.strSp 0 (wd HP), .addRdSp 2 (wd WOFF), .movImm 3 16]

theorem nx_ldrLit (s : State) (t : LowReg) (imm : BitVec 8) (r : Reg) (hr : r ≠ 15) :
    ((Instr.ldrLit t imm).next s).regs r = if r = t.toReg then
      read32 s.mem (((s.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4)) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg, State.pc, hr]

theorem nx_addPc (s : State) (d : LowReg) (r : Reg) (hr : r ≠ 15) :
    ((Instr.addPc d).next s).regs r = if r = d.toReg then s.regs d.toReg + (s.pc + 4#32) else s.regs r := by
  simp [Instr.next, Instr.exec, State.setReg, State.reg, State.pc, hr]

/-- **`ldr r7, =lit` and `kinit`**: the `K` pointer `lit + pc` and the counter `0` in their slots. -/
theorem kinit_run (u : State) (imm : BitVec 8) :
    (execAll ([.ldrLit 7 imm] ++ kinit) u).mem = write32 (write32 u.mem (u.regs 13 + BitVec.ofNat 32 KP)
      (read32 u.mem (((u.pc + 4#32) &&& ~~~3#32) + BitVec.ofNat 32 (imm.toNat * 4)) + (u.pc + 2#32 + 4#32)))
      (u.regs 13 + BitVec.ofNat 32 GRP) 0 := by
  have hp : ((Instr.ldrLit 7 imm).next u).pc = u.pc + 2#32 := by
    simp (config := {decide := true}) [Instr.next, Instr.exec, State.setReg, State.pc, M0Crypto.Proofs.toReg_7]; rfl
  have m1 : ((Instr.ldrLit 7 imm).next u).mem = u.mem := nx_mem _ rfl u
  have m2 : ∀ v : State, ((Instr.addPc 7).next v).mem = v.mem := fun v => nx_mem _ rfl v
  simp only [kinit, List.cons_append, List.nil_append, execAll]
  rsimp [nx_ldrLit, nx_addPc, hp, Ed25519Sha512Pass.wd_ofs, m1, m2]
  rfl


/-- The load loop's frame before pass `j`: the frame over `m0` but for `HP` and the words, the
block pointer `blk`, `W` at `r2`, the count in `r3`, and the first `j` words `M`. -/
def WI (sp0 h0 blk : Word) (m0 : Mem) (M : Nat → BitVec 64) (j : Nat) (u : State) : Prop :=
  MemEq [⟨fsp sp0, BFRAME⟩] m0 u.mem ∧ read32 u.mem (fsp sp0 + BitVec.ofNat 32 HP) = h0 ∧
  u.regs 1 = blk + BitVec.ofNat 32 (8 * j) ∧ u.regs 2 = fsp sp0 + BitVec.ofNat 32 (WOFF + 8 * j) ∧
  u.regs 3 = BitVec.ofNat 32 (16 - j) ∧ ∀ i < j, pairAt u.mem (fsp sp0 + BitVec.ofNat 32 (WOFF + 8 * i)) = M i

/-- `V = H`, then `ldr r7, =lit` and `kinit`: one block from `oCopy`. -/
def ckI : List Instr := vcopy ++ [.ldrLit 7 (Ed25519Sha512Code.litImm O pool)] ++ kinit

/-- A frame slot, and the literal's address as the executor forms it. -/
def spA (n : Nat) : SExpr := .add (.reg0 13) (kS n)
def litA : SExpr := .add (.and (.add (.add (.reg0 15) (kS (seqSize vcopy))) (kS 4)) (.not (kS 3)))
  (kS ((Ed25519Sha512Code.litImm O pool).toNat * 4))

theorem ck_ok : sglueOk Ed25519Sha512Pass.cs ckI (oCopy O) D D [(.reg0 13, 4), (ldS HP, 4)]
    [(spA VOFF, 8 * 8), (spA KP, 4), (spA GRP, 4)] [(litA, 4), (ldS HP, 8 * 8), (spA HP, 4)] = true ∧
    ckI.all Instr.falls = true ∧ traceOkE ckI [.reg0 13, ldS HP] = true := by decide +kernel

theorem ha_ok : sglueOk Ed25519Sha512Pass.cs hAdd (oEnd O pool) D D [(.reg0 13, 4), (ldS HP, 4)]
    [(ldS HP, 8 * 8)] [(spA HP, 4), (spA VOFF, 8 * 8), (ldS HP, 8 * 8)] = true ∧
    hAdd.all Instr.falls = true ∧ traceOkE hAdd [.reg0 13, ldS HP] = true := by decide +kernel

theorem cnt_sub : ∀ j : Fin 16, BitVec.ofNat 32 (16 - j.val) - 1#32 = BitVec.ofNat 32 (16 - (j.val + 1)) ∧
    (!(BitVec.ofNat 32 (16 - j.val) - 1#32 == 0)) = decide (j.val + 1 < 16) := by decide

/-! ## The byte effect -/

abbrev As2 : List SExpr := [.reg0 13, ldS HP]
abbrev ckR : List (SExpr × Nat) := [(litA, 4)] ++ [(ldS HP, 8 * 8)] ++ [(spA HP, 4)]
abbrev ckW : List (SExpr × Nat) := [(spA VOFF, 8 * 8), (spA KP, 4), (spA GRP, 4)]
abbrev haR : List (SExpr × Nat) := [(spA HP, 4), (spA VOFF, 8 * 8)] ++ [(ldS HP, 8 * 8)]

/-- The pieces' accesses outside the group loop, and the atoms of their regions. -/
theorem eff_ok : blkChk [] (spRg [(HP, 4)]) (spRg [(HP, 4)]) preB = true ∧
    blkChk [(.reg0 1, 8)] [(.reg0 2, 8)] [(.reg0 1, 8), (.reg0 2, 8)] wload = true ∧
    blkChk ckR ckW (ckR ++ ckW) ckI = true ∧ blkChk haR [(ldS HP, 8 * 8)] haR hAdd = true ∧
    winChk As2 (· == 0) 0 BFRAME ckW = true ∧ winChk As2 (· == 0) 0 BFRAME [(spA HP, 4), (spA VOFF, 8 * 8)] = true ∧
    atomOf As2 litA = none ∧ atomOf As2 (ldS HP) = some (1, 0) ∧ atomOf As2 (spA HP) = some (0, BitVec.ofNat 32 HP) ∧
    atomOf As2 (spA VOFF) = some (0, BitVec.ofNat 32 VOFF) ∧ atomOf As2 (spA KP) = some (0, BitVec.ofNat 32 KP) ∧
    atomOf As2 (spA GRP) = some (0, BitVec.ofNat 32 GRP) ∧
    oCopy O + seqSize vcopy + 4 + (Ed25519Sha512Code.litImm O pool).toNat * 4 + 4 ≤ O + size := by decide +kernel

theorem frame_cover {F y : Word} (h : Region F BFRAME y) : Region (F + BitVec.ofNat 32 VOFF) (8 * 8) y ∨
    Region (F + BitVec.ofNat 32 WOFF) (8 * 16) y ∨ Region (F + BitVec.ofNat 32 HP) 4 y ∨
    Region (F + BitVec.ofNat 32 GRP) 4 y ∨ Region (F + BitVec.ofNat 32 KP) 4 y := by
  simp only [Region, BFRAME, VOFF, WOFF, HP, GRP, KP] at h ⊢; bv_omega

/-- The written sets of the block's effect, from the caller's `U`: the saved word, then the `HP`
slot and the first `j` words of `W`, then `V` and the group slots, then `H`. -/
abbrev SetS (U : Word → Prop) (sp y : Word) : Prop :=
  U y ∨ Region (sp - BitVec.ofNat 32 (4 * nSaved 0)) (4 * nSaved 0) y
abbrev SetI (e0 : Word) (n : Nat) (U : Word → Prop) (sp : Word) (j : Nat) (y : Word) : Prop := SetS U sp y ∨
  (Region (fsp sp + BitVec.ofNat 32 HP) 4 y ∨ Region (fsp sp + BitVec.ofNat 32 WOFF) (8 * j) y) ∧ BelowEntry e0 n y
abbrev SetG (e0 : Word) (n : Nat) (U : Word → Prop) (base : Word) (P : Nat → Word) (y : Word) : Prop :=
  SetI e0 n U (P 2) 16 y ∨ InRD (addrE (base + BitVec.ofNat 32 (oCopy O)) As2 [fsp (P 2), P 0]) ckW y ∧ BelowEntry e0 n y
abbrev SetH (e0 : Word) (n : Nat) (U : Word → Prop) (base : Word) (P : Nat → Word) (y : Word) : Prop :=
  SetG e0 n U base P y ∨
    InRD (addrE (base + BitVec.ofNat 32 (oEnd O pool)) As2 [fsp (P 2), P 0]) [(ldS HP, 8 * 8)] y ∧ BelowEntry e0 n y

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- The bytes `m0c_sha512_block` reads outside its stack: `H`, the block and the code. -/
def blockRq (base : Word) (P : Nat → Word) (y : Word) : Prop :=
  Region (P 0) (8 * 8) y ∨ Region (P 1) (8 * 16) y ∨ Region base BS y

/-- **The byte effect of `m0c_sha512_block`**: in `D` bytes of stack it reads `blockRq` and adds `H`. -/
def blockE (base : Word) (P : Nat → Word) : TrP :=
  EffT D (fun _ => False) (blockRq (BS := BS) base P) (Region (P 0) (8 * 8)) (P 2)

noncomputable def block_te (hL : blockAt O pool B size = true) (hbs : O + size ≤ BS) (hK : kOk B = true)
    (hkb : Ed25519Compact.sha512_K + 8 * 80 ≤ BS) (hlit : litOk (B := B) = true) :
    blockR.TE blockPub (blockE (BS := BS)) := by
  have L := lay_of hL
  simp only [litOk, beq_iff_eq] at hlit
  have hpre := L.pre
  rw [show pre = [Instr.push 0 true] ++ ([.subSp (BitVec.ofNat 7 (BFRAME / 4))] ++ preB) from rfl,
    seqAt_append, seqAt_append] at hpre
  simp only [Bool.and_eq_true] at hpre
  have hpo := L.po
  rw [show post = [Instr.addSp (BitVec.ofNat 7 (BFRAME / 4))] ++ [.pop 0 true] from rfl, seqAt_append] at hpo
  simp only [Bool.and_eq_true] at hpo
  have i0 := instrAt_of_seqAt hpre.1
  have i1 := instrAt_of_seqAt hpre.2.1
  have i2 := instrAt_of_seqAt hpo.1
  have i3 := instrAt_of_seqAt hpo.2
  rw [show seqSize [Instr.push 0 true] = 2 from rfl] at i1
  rw [show seqSize [Instr.addSp (BitVec.ofNat 7 (BFRAME / 4))] = 2 from rfl] at i3
  trefine M0Crypto.Release.Routine.Routine.te_by (fun base s e => ?_) (fun _ _ => ?_) (fun _ _ => ?_)
    (fun base P tr h => ?_)
  generalize hP : blockPub base s = P
  have q : s.regs 0 = P 0 ∧ s.regs 1 = P 1 ∧ s.regs 13 = P 2 := by subst hP; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨h0a, h1a⟩ := e.pre
  have F := Caller.of_entry (mask := 0) e
  trefine ReachFT.frameK (f := blockR) (mask := 0) (k := BFRAME / 4) (epi := oPost O pool) (by decide)
    i0 i1 i2 i3 (by decide +kernel) (by decide +kernel) (Nat.le_trans (by decide +kernel) hbs)
    (Nat.le_trans (by decide +kernel) hbs) (by decide +kernel) (by decide) (by decide) e q.2.2 ?_
  intro t tpc t13 tr hm hc
  have hroom := e.room; have hsp4 := e.sp4; have := (s.regs 13).isLt; have hb4 := e.base4
  have hsC := e.sepCode; have hsW := e.sepWr; have hsR := e.sepRd; have hcb := F.code32
  have hBS : BS < 2 ^ 32 := CodeBytes.lt
  have hK4 : Ed25519Compact.sha512_K % 4 = 0 := by decide
  simp only [blockR, Routine.win, codeR, D, BFRAME] at hroom hsC hsW hsR
  fp_simp at hsC hsW hsR
  have hlw : lowWin blockR 0 s = ⟨fsp (s.regs 13), BFRAME⟩ := by simp only [lowWin, blockR]; rfl
  simp only [hlw] at F ⊢
  have t13' : t.regs 13 = fsp (s.regs 13) := by rw [t13]; rfl
  have E : Env (B := B) base (s.regs 13) (base + BitVec.ofNat 32 Ed25519Compact.sha512_K)
      (codeR base :: blockR.win s :: blockR.rd s) (⟨fsp (s.regs 13), BFRAME⟩ :: blockR.wr s) := by
    refine ⟨F, L, hbs, ?_, ?_, ?_, ?_, ?_, fun m hc i hi => ktab hK hkb hc hi⟩ <;>
      (try simp only [blockR, Routine.win, codeR, fsp, D, BFRAME]) <;> fp_tac
  have hb2 : base.toNat % 2 = 0 := by omega
  have blk := blkOf s.mem (s.regs 1)
  -- `str r0, [sp, #HP]; add r2, sp, #WOFF; movs r3, #16`
  have hq1 : seqAt B (O + 4) preB = true := hpre.2.2
  have tpc' : t.pc = base + BitVec.ofNat 32 (O + 4) := tpc
  trefine ReachFT.glue E.F preB [((13 : Reg), 4)] [((13 : Reg), BitVec.ofNat 32 HP, 4)] [] hq1 tpc' t13' hc ?g1
    (tr_block [13] tpc' [t13', q.2.2]) (fun hp1 h131 hc1 hm1 => ?_) (by decide +kernel)
  case g1 =>
    refine Ed25519Sha512Pass.GlueSides.mono ?_ E.rc E.wc
    glue_tac [t13', fsp, D, BFRAME, HP]
  have u1r1 : (execAll preB t).regs 1 = s.regs 1 := by
    simp only [preB]; rsimp [nx_addRdSp]; exact tr 1 (by decide) (by decide)
  have u1r2 : (execAll preB t).regs 2 = fsp (s.regs 13) + BitVec.ofNat 32 WOFF := by
    simp only [preB]; rsimp [nx_addRdSp, Ed25519Sha512Pass.wd_ofs, t13']
  have u1r3 : (execAll preB t).regs 3 = BitVec.ofNat 32 (16 - 0) := by
    simp only [preB]; rsimp [nx_addRdSp]
  have u1m : (execAll preB t).mem = write32 t.mem (fsp (s.regs 13) + BitVec.ofNat 32 HP) (s.regs 0) := by
    simp only [preB]; rsimp [nx_addRdSp, Ed25519Sha512Pass.wd_ofs, t13', tr 0 (by decide) (by decide)]
  generalize execAll preB t = u1 at hp1 h131 hc1 hm1 u1r1 u1r2 u1r3 u1m
  simp only [saved, show nSaved 0 = 1 from rfl] at hm
  have hp1' : u1.pc = base + BitVec.ofNat 32 (oWL O) := by rw [hp1]; rfl
  -- the big-endian load of the block into `W`
  trefine ReachFT.loop (o := oWL O) (ob := oWL O + seqSize wload) (d := D) E.F 1 _ L.wlb 16
    (WI (s.regs 13) (s.regs 0) (s.regs 1) t.mem (fun i => (parse (blkOf s.mem (s.regs 1)))[i]!))
    ?wpc ?wbody ?wexit ?wok 0 u1 (by decide) hp1' ?w0 h131 hc1
  case wok =>
    simp only [loopOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨⟨⟨by decide +kernel, by decide +kernel⟩, Nat.le_trans (by decide +kernel) hbs⟩, by decide +kernel⟩,
      Nat.le_refl _⟩
  case w0 =>
    refine ⟨hm1.mono ?_, by rw [u1m]; exact M0Crypto.Armv6M.read32_write32_same _ _ _, by rw [u1r1]; simp,
      by rw [u1r2]; simp, u1r3, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    simp only [regions, List.map, t13']; nrm; fp_tac
  case wpc =>
    intro j u v ⟨a, b, c, d, f, g⟩
    exact ⟨a, b, by rw [RoutineBranch.setReg15_regs _ _ _ (by decide)]; exact c,
      by rw [RoutineBranch.setReg15_regs _ _ _ (by decide)]; exact d,
      by rw [RoutineBranch.setReg15_regs _ _ _ (by decide)]; exact f, g⟩
  case wbody =>
    intro j u hj hpu ⟨hmu, hHP, h1, h2, h3, hW⟩ h13u hcu
    trefine ReachFT.glue E.F wload [((1 : Reg), 4), ((2 : Reg), 4)] [((2 : Reg), BitVec.ofNat 32 0, 8)] [((1 : Reg), BitVec.ofNat 32 0, 8)]
      L.wl hpu h13u hcu ?gs (tr_block [1, 2] hpu [h1, h2, q.1, q.2.1, q.2.2]) (fun hpA h13A hcA hmA => ?_)
      (by decide +kernel)
    case gs => glue_tac [h1, h2, fsp, D, BFRAME, WOFF, blockR, Routine.win]
    obtain ⟨e1, e2, e3, ez, em⟩ := wload_run u
    obtain ⟨c1, c2⟩ := cnt_sub ⟨j, hj⟩
    simp only [regions, List.map, h2, BitVec.add_zero] at hmA
    refine ReachT.done ⟨hpA, h13A, hcA, ⟨hmu.grow hmA (by nrm; fp_tac), ?_, by rw [e1, h1, ofNat_add_assoc, show 8 * j + 8 = 8 * (j + 1) by omega], ?_,
      by rw [e3, h3, c1], fun i hi => ?_⟩, by rw [RoutineBranch.cond_ne, ez, h3, c2]⟩
    · nrm at hmA ⊢; keep_simp; exact hHP
    · rw [e2, h2, ofNat_add_assoc, show WOFF + 8 * j + 8 = WOFF + 8 * (j + 1) by omega]
    · by_cases hij : i < j
      · rw [Ed25519Sha512Pass.MemEq.pairAt hmA (by nrm; fp_tac)]; exact hW i hij
      · obtain rfl : i = j := by omega
        show _ = (parse (blkOf s.mem (s.regs 1)))[i]!
        rw [em, h2, pairAt_wpair, h1, parse_blk _ _ hj]
        nrm at hmu
        keep_simp
  case wexit =>
    intro v hpv ⟨hmv, hHPv, h1v, h2v, h3v, hWv⟩ h13v hcv
    have hpv' : v.pc = base + BitVec.ofNat 32 (oCopy O) := by rw [hpv]; rfl
    have hq : seqAt B (oCopy O) ckI = true := by
      rw [ckI, seqAt_append, seqAt_append, L.vc, show oCopy O + seqSize vcopy = oLit O from rfl, L.lit,
        show oCopy O + seqSize (vcopy ++ [.ldrLit 7 (Ed25519Sha512Code.litImm O pool)]) = oLit O + 2 from rfl, L.ki]
      rfl
    obtain ⟨ok, hf, htr⟩ := ck_ok
    have hlo : litOff (oLit O) (Ed25519Sha512Code.litImm O pool) + 4 ≤ BS := Nat.le_trans (by decide +kernel) hbs
    have hlitA : litA.denote v = base + BitVec.ofNat 32 (litOff (oLit O) (Ed25519Sha512Code.litImm O pool)) := by
      show ((v.pc + BitVec.ofNat 32 (seqSize vcopy) + BitVec.ofNat 32 4) &&& ~~~BitVec.ofNat 32 3) +
        BitVec.ofNat 32 ((Ed25519Sha512Code.litImm O pool).toNat * 4) = _
      rw [hpv', ofNat_add_assoc base (oCopy O)]
      exact Frame.lit_addr base hb4 (oLit O) _ (by simp only [litOff] at hlo; omega)
    trefine ReachFT.sglue E.F ckI _ _ _ hq hpv' h13v hcv ?ck
      (traceAll_blockTrE hf htr hpv' (vs := [fsp (P 2), P 0])
        (by have h := hHPv; rw [q.2.2, q.1] at h
            simp only [List.map_cons, List.map_nil, ldS, kS, SExpr.denote, SMem.denote, h13v, q.2.2, h]; try rfl))
      (fun hpA h13A hcA hmA => ?_) ok
    case ck =>
      simp only [SGlueSides, sregions, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true, and_true, SExpr.denote, SMem.denote, ldS, spA, kS, hlitA, h13v, hHPv]
      simp only [blockR, Routine.win, codeR]; nrm
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> fp_tac
    -- `V = H` (`cpN`), then the `K` pointer and the counter (`kinit_run`)
    have ev : vcopy = [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] ++ (List.replicate 4 cpChunk).flatten := rfl
    have v2pc : (execAll vcopy v).pc = base + BitVec.ofNat 32 (oLit O) := by
      rw [execAll_pc _ _ (by decide), hpv', ofNat_add_assoc]; rfl
    have v213 : (execAll vcopy v).regs 13 = fsp (s.regs 13) := by
      rw [execAll_regs_other _ _ 13 (by decide) (by decide), h13v]
    have hd : Disj (s.regs 0) (8 * 8) (fsp (s.regs 13) + BitVec.ofNat 32 VOFF) (8 * 8) := by nrm; fp_simp; omega
    have hv1 : (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] v).regs 0 = s.regs 0 ∧
        (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] v).regs 1 = fsp (s.regs 13) + BitVec.ofNat 32 VOFF ∧
        (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] v).mem = v.mem := by
      refine ⟨?_, ?_, ?_⟩ <;> rsimp [nx_addRdSp, Ed25519Sha512Pass.wd_ofs, h13v, hHPv]
    obtain ⟨-, -, cm, cp⟩ := cpN _ (by rw [hv1.1, hv1.2.1]; exact hd) 4 (Nat.le_refl _)
    simp only [hv1.1, hv1.2.1, hv1.2.2] at cm cp
    rw [← execAll_append, ← ev] at cm cp
    have hcv2 : CodeAt (execAll vcopy v).mem base B := CodeAt.of_memEq hcv cm (by simp only [codeR]; nrm; fp_tac)
    have hlv : read32 (execAll vcopy v).mem ((((execAll vcopy v).pc + 4#32) &&& ~~~3#32) +
        BitVec.ofNat 32 ((Ed25519Sha512Code.litImm O pool).toNat * 4)) =
        Frame.codeWord (litOff (oLit O) (Ed25519Sha512Code.litImm O pool)) := by
      rw [v2pc, Frame.lit_addr base hb4 (oLit O) _ (by simp only [litOff] at hlo; omega)]
      exact Frame.read32_code hcv2 _ hlo
    have hkp : Frame.codeWord (litOff (oLit O) (Ed25519Sha512Code.litImm O pool)) +
        ((execAll vcopy v).pc + 2#32 + 4#32) = base + BitVec.ofNat 32 Ed25519Compact.sha512_K := by
      rw [v2pc, ofNat_add_assoc, ofNat_add_assoc, ← BitVec.add_assoc, BitVec.add_comm (Frame.codeWord _) base,
        BitVec.add_assoc, hlit]
    have em : (execAll ckI v).mem = write32 (write32 (execAll vcopy v).mem (fsp (s.regs 13) + BitVec.ofNat 32 KP)
        (base + BitVec.ofNat 32 Ed25519Compact.sha512_K)) (fsp (s.regs 13) + BitVec.ofNat 32 GRP) 0 := by
      rw [ckI, List.append_assoc, execAll_append, kinit_run, hlv, hkp, v213]
    have hk1 := Ed25519WordLoop.memEq_write32 (execAll vcopy v).mem (fsp (s.regs 13) + BitVec.ofNat 32 KP)
      (base + BitVec.ofNat 32 Ed25519Compact.sha512_K)
    have hk2 := Ed25519WordLoop.memEq_write32 (write32 (execAll vcopy v).mem (fsp (s.regs 13) + BitVec.ofNat 32 KP)
      (base + BitVec.ofNat 32 Ed25519Compact.sha512_K)) (fsp (s.regs 13) + BitVec.ofNat 32 GRP) 0
    rw [← em] at hk2
    simp only [sregions, List.map_cons, List.map_nil, SExpr.denote, spA, kS, h13v] at hmA
    have hI0 : Inv (fsp (s.regs 13)) (base + BitVec.ofNat 32 Ed25519Compact.sha512_K) (s.regs 0) t.mem 0
        (fun j => (hOf s.mem (s.regs 0))[j]!) (fun j => (parse (blkOf s.mem (s.regs 1)))[j]!)
        (execAll ckI v).mem := by
      refine ⟨hmv.grow hmA (by nrm; fp_tac), ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
      · nrm at hmA ⊢; keep_simp; exact hHPv
      · rw [em]; exact M0Crypto.Armv6M.read32_write32_same _ _ _
      · rw [MemEq.read32 hk2 (by nrm; fp_tac), M0Crypto.Armv6M.read32_write32_same]; simp
      · rw [Ed25519Sha512Pass.MemEq.pairAt hk2 (by nrm; fp_tac), Ed25519Sha512Pass.MemEq.pairAt hk1 (by nrm; fp_tac),
          ← ofNat_add_assoc, cp i (by omega)]
        show _ = (hOf s.mem (s.regs 0))[i]!
        rw [hOf_get _ _ hi]
        nrm at hmv ⊢; keep_simp with [Ed25519Sha512Pass.MemEq.pairAt]
      · rw [Ed25519Sha512Pass.MemEq.pairAt hmA (by nrm; fp_tac)]; exact hWv i hi
    -- the ten groups
    have hpA' : (execAll ckI v).pc = base + BitVec.ofNat 32 (oG O) := by rw [hpA]; rfl
    have t13'' := t13'
    rw [q.2.2] at E hI0 h13A t13'' ⊢
    trefine (loop_frag (B := B) base (P 2) _).run.1 E _ hpA' hI0 h13A hcA fun w hpw h13w hcw hIw => ?_
    -- `H += V`
    obtain ⟨hm1, hHP, -, -, hV, -⟩ := hIw
    obtain ⟨okH, hfH, htrH⟩ := ha_ok
    have hpw' : w.pc = base + BitVec.ofNat 32 (oEnd O pool) := hpw
    have hHP' := hHP; rw [q.1] at hHP'
    trefine ReachFT.sglue E.F hAdd _ _ _ L.ha hpw' h13w hcw ?hs
      (traceAll_blockTrE hfH htrH hpw' (vs := [fsp (P 2), P 0])
        (by simp only [List.map_cons, List.map_nil, ldS, kS, SExpr.denote, SMem.denote, h13w, hHP']; try rfl))
      (fun hpB h13B hcB hmB => ?_) okH
    case hs =>
      simp only [SGlueSides, sregions, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
        false_implies, implies_true, and_true, SExpr.denote, SMem.denote, ldS, spA, kS, h13w, hHP]
      rw [← q.2.2]
      simp only [blockR, Routine.win, codeR]; nrm
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> fp_tac
    have eh : hAdd = [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] ++ (List.replicate 8 hAddW).flatten := rfl
    have hw1 : (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] w).regs 0 = s.regs 0 ∧
        (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] w).regs 1 = fsp (P 2) + BitVec.ofNat 32 VOFF ∧
        (execAll [.ldrSp 0 (wd HP), .addRdSp 1 (wd VOFF)] w).mem = w.mem := by
      refine ⟨?_, ?_, ?_⟩ <;> rsimp [nx_addRdSp, Ed25519Sha512Pass.wd_ofs, h13w, hHP]
    have hd' := hd; rw [q.2.2] at hd'
    obtain ⟨-, -, -, ha⟩ := hAddN _ (by rw [hw1.1, hw1.2.1]; exact hd') 8 (Nat.le_refl _)
    simp only [hw1.1, hw1.2.1, hw1.2.2] at ha
    rw [← execAll_append, ← eh] at ha
    refine ReachT.done ⟨by rw [hpB]; rfl, by rw [h13B, t13''], fun r h4 h11 _ hn =>
      absurd (Ed25519Routines.mem_hiRegs h4 h11) hn, fun i hi => ?_⟩
    rw [ha i hi, ofNat_add_assoc (fsp (P 2)), hV i hi, compress_pairs _ _ hi, hOf_get _ _ hi]
    rw [← q.2.2] at hm1
    nrm at hm1 ⊢; keep_simp with [Ed25519Sha512Pass.MemEq.pairAt]
  · intro _ _; uniq_tac
  · ex_tac
  -- the effect: the frame, the load of `W`, `V`, the groups once the frame is written, then `H`
  obtain ⟨cP, cW, cC, cH, wC, wH, aL, aH, aHP, aV, aK, aG, hlo⟩ := eff_ok
  have hBS : BS < 2 ^ 32 := CodeBytes.lt
  refine effT_of_gp fun e0 n U hroom hn _ hR => GP.is_of ?_ h
  have hD : 4 * nSaved 0 + 4 * (BFRAME / 4) = D := by decide
  have hfa : ∀ y, Region (fsp (P 2)) BFRAME y → AtOrAboveSp e0 (fsp (P 2)) y := fun y h =>
    reg_sub_above h (by decide) (by omega)
  have hG : ∀ y, (Region (fsp (P 2)) BFRAME y ∨ Region (base + BitVec.ofNat 32 Ed25519Compact.sha512_K) (8 * 80) y) →
      BelowEntry e0 n y → SetG e0 n U base P y := by
    rintro y (h | h) hb
    · rcases frame_cover h with h | h | h | h | h
      · exact .inr ⟨inRD_of rfl (.head _) aV rfl h, hb⟩
      · exact .inl (.inr ⟨.inr h, hb⟩)
      · exact .inl (.inr ⟨.inl h, hb⟩)
      · exact .inr ⟨inRD_of rfl (.tail _ (.tail _ (.head _))) aG rfl h, hb⟩
      · exact .inr ⟨inRD_of rfl (.tail _ (.head _)) aK rfl h, hb⟩
    · exact .inl (.inl (.inl (hR _ (.inr (.inr (reg_in h hkb hBS))) hb)))
  refine frameK_gp (U := U) (R2 := SetH e0 n U base P) (by decide) (by rw [hD]; omega) ?_
    (fun y h => .inl (.inl (.inl (.inr h)))) (fun y h => .inl (h.elim id fun h => hR y (.inl h.1) h.2))
    (fun y h => .inl (.inl (.inl (.inl h))))
  rw [sub_sub_ofNat, hD]
  refine GP.cat (K := SIR e0 (fsp (P 2)) (SetI e0 n U (P 2) 0)) ?_
    (GP.repI (I := fun j => SIR e0 (fsp (P 2)) (SetI e0 n U (P 2) j)) _ 0 (fun j _ hj => ?_)
      (GP.cat (K := SIR e0 (fsp (P 2)) (SetG e0 n U base P)) ?_
        ((loop_frag (B := B) base (P 2) _).run.2 e0 n _ _ _ hG (GP.cat ?_ (GP.nil fun _ h => h)))))
  · -- `str r0, [sp, #HP]`
    refine sir_segR (fun _ => blk_seg cP _ (fun _ h => h) fun y hy _ => hfa y (inR_sp (by decide) hy))
      (fun y ⟨_, h, _⟩ => absurd h List.not_mem_nil) fun y h => ?_
    rcases h with h | ⟨h | h, hb⟩
    · exact .inl h
    · exact .inr ⟨inR_sp_of (by simp) h, hb⟩
    · simp [Region] at h
  · -- the words of `W`
    have hj' : j < 16 := by omega
    have d1 : (SExpr.reg0 1).denote (regState (base + BitVec.ofNat 32 (oWL O)) [1, 2]
        [P 1 + BitVec.ofNat 32 (8 * j), fsp (P 2) + BitVec.ofNat 32 (WOFF + 8 * j)]) = P 1 + BitVec.ofNat 32 (8 * j) := rfl
    have d2 : (SExpr.reg0 2).denote (regState (base + BitVec.ofNat 32 (oWL O)) [1, 2]
        [P 1 + BitVec.ofNat 32 (8 * j), fsp (P 2) + BitVec.ofNat 32 (WOFF + 8 * j)]) =
        fsp (P 2) + BitVec.ofNat 32 (WOFF + 8 * j) := rfl
    have wx : ∀ y, InR (regState (base + BitVec.ofNat 32 (oWL O)) [1, 2]
        [P 1 + BitVec.ofNat 32 (8 * j), fsp (P 2) + BitVec.ofNat 32 (WOFF + 8 * j)]) [(.reg0 1, 8)] y →
        BelowEntry e0 n y → SetI e0 n U (P 2) j y := by
      rintro y ⟨r, hr, o, ho, rfl⟩ hb
      simp only [List.mem_singleton] at hr; subst hr; simp only at ho
      exact .inl (.inl (hR _ (.inr (.inl (by rw [d1]; exact reg_off (by omega)))) hb))
    refine GP.cat (GP.cat (sir_segR (fun hA => blk_seg cW _ (fun _ h => h) fun y hy hb => ?_) wx fun y h => ?_)
      (GP.nil fun _ h => h)) (sir_quietC rfl rfl rfl)
    · obtain ⟨r, hr, o, ho, rfl⟩ := hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hA _ (wx _ ⟨_, .head _, o, ho, rfl⟩ hb)
      · simp only at ho; rw [d2]; exact hfa _ (reg_off (by simp only [WOFF, BFRAME]; omega))
    · rcases h with h | ⟨h | h, hb⟩
      · exact .inl (.inl h)
      · exact .inl (.inr ⟨.inl h, hb⟩)
      · rcases reg_split (x := 8 * j) (w := 8) (by rwa [show 8 * j + 8 = 8 * (j + 1) by omega]) with h | h
        · exact .inl (.inr ⟨.inr h, hb⟩)
        · exact .inr ⟨inR_one (by rw [d2, BitVec.ofNat_add, ← BitVec.add_assoc]; exact h), hb⟩
  · -- `V = H`, the `K` pointer and the counter
    have cx : ∀ y, InRD (addrE (base + BitVec.ofNat 32 (oCopy O)) As2 [fsp (P 2), P 0]) ckR y →
        BelowEntry e0 n y → SetI e0 n U (P 2) 16 y := by
      intro y hy hb
      rcases inR_append.1 hy with hy | hy
      · rcases inR_append.1 hy with hy | hy
        · obtain ⟨r, hr, o, ho, rfl⟩ := hy
          simp only [List.mem_singleton] at hr; subst hr; simp only at ho
          have e : litA.denote (regState (base + BitVec.ofNat 32 (oCopy O)) [] []) + BitVec.ofNat 32 o =
              ((base + BitVec.ofNat 32 (oCopy O + seqSize vcopy + 4)) &&& ~~~3#32) +
                BitVec.ofNat 32 ((Ed25519Sha512Code.litImm O pool).toNat * 4) + BitVec.ofNat 32 o := by
            simp only [litA, kS, SExpr.denote, regState, ite_true, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
          have hr := al_reg e (by omega) (show _ < BS by omega) hBS
          rw [addrE_none aL] at hb ⊢
          exact .inl (.inl (hR _ (.inr (.inr hr)) hb))
        · exact .inl (.inl (hR _ (.inl (by simpa using inRD_atom1 rfl aH rfl hy)) hb))
      · exact .inr ⟨.inl (inRD_atom1 rfl aHP rfl hy), hb⟩
    refine sir_segR (fun hA => blkE_seg cC (fun _ h => h) fun y hy hb => ?_) cx fun _ h => h
    rcases inR_append.1 hy with hy | hy
    · exact hA _ (cx _ hy hb)
    · exact hfa _ (inRD_win rfl wC (hv_at rfl) hy)
  · -- `H += V`
    have hx : ∀ y, InRD (addrE (base + BitVec.ofNat 32 (oEnd O pool)) As2 [fsp (P 2), P 0]) haR y →
        BelowEntry e0 n y → SetG e0 n U base P y := by
      intro y hy hb
      rcases inR_append.1 hy with hy | hy
      · exact hG y (.inl (inRD_win rfl wH (hv_at rfl) hy)) hb
      · exact .inl (.inl (.inl (hR _ (.inl (by simpa using inRD_atom1 rfl aH rfl hy)) hb)))
    exact sir_segR (fun hA => blkE_seg cH (fun _ h => h) fun y hy hb => hA _ (hx _ hy hb)) hx fun _ h => h

end

open M0Crypto.Release.Ed25519 (Build) in
/-- **`m0c_sha512_block` in each build.** -/
noncomputable def sha512_block_te (b : Build) : letI := b.codeBytes
    blockR.TE blockPub (@blockE b.size) := by
  have hL : blockAt O pool b.bytes size = true := by cases b; exact compact_at; exact fast_at
  have hK : kOk b.bytes = true := by cases b <;> decide +kernel
  have hlit : @litOk _ _ b.codeBytes = true := by cases b <;> decide +kernel
  exact @block_te _ _ b.codeBytes hL (by cases b <;> decide) hK (by cases b <;> decide) hlit

end M0Crypto.Release.Ed25519Sha512Block
