import M0Crypto.Release.X25519OpRun
import M0Crypto.Release.X25519Decode

set_option linter.unusedSimpArgs false

/-!
The output stores of `m0c_x25519`.

`storeOut` is `ldr r2, [sp, #LV_OUT]` and eight word stores `storeLe32 r1 r0 r2 i (4i)`
(`X25519EntryCode.storeOut`). `words_run_w` runs the first `n` word stores by induction on `n`,
from the one generic word-store lemma `X25519Bytes.storeLe32_run_w`: byte `4i + j` at the
destination is byte `j` of word `i` at the source, nothing else is written. `feVal_byte` turns
the bytes into the bytes of the value `feVal` of the source (via `X25519Decode.out_byte`).
`storeOut_run_w` is the whole segment, generic in its SP and pointers; `storeOut_at` is the
instance at `oStore` in the entry, with its `seqAt` taken from `entry_at`.
-/

namespace M0Crypto.Release.X25519OutStore
open M0Crypto.Armv6M (Word Reg LowReg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release (ReachW InRegion Region B)
open M0Crypto.Release.Frame (Disj toNat_add_ofNat)
open M0Crypto.Release.X25519Bytes (storeLe32 storeLe32_run_w toReg_ne)
open M0Crypto.Release.X25519Routines (feVal)
open M0Crypto.Release.X25519Layout
open M0Crypto.Release.X25519EntryCode

/-- The first `n` word stores of `storeOut`. -/
def stores (rv rs rd : LowReg) (n : Nat) : List Instr :=
  (List.range n).flatMap fun i => storeLe32 rv rs rd i (4 * i)

theorem stores_succ (rv rs rd : LowReg) (n : Nat) :
    stores rv rs rd (n + 1) = stores rv rs rd n ++ storeLe32 rv rs rd n (4 * n) := by
  simp [stores, List.range_succ, List.flatMap_append]

theorem stores_falls (rv rs rd : LowReg) (n : Nat) : (stores rv rs rd n).all Instr.falls = true := by
  simp only [stores, List.all_flatMap, List.all_eq_true]
  intro i _
  have := X25519Bytes.storeLe32_falls rv rs rd i (4 * i)
  simpa [List.all_eq_true] using this

/-- **The word stores**, by induction on the number of words: after `n ≤ 8` stores, byte `j`
of word `i < n` of the source is at `dst + 4i + j`, the rest of memory is unchanged, and only
`rv` (and the flags) changed among the registers. The source words must not overlap the
destination bytes (`Disj`). -/
theorem words_run_w {base src dst : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {rv rs rd : LowReg} (hvs : rv ≠ rs) (hvd : rv ≠ rd) (hal : src.toNat % 4 = 0)
    (hdj : Disj src 32 dst 32) (hwr : ∀ k < 32, Wr (dst + BitVec.ofNat 32 k)) {Q : State → Prop} :
    ∀ (n : Nat) (off : Nat) (s : State), n ≤ 8 → seqAt B off (stores rv rs rd n) = true →
    off % 2 = 0 → s.pc = base + BitVec.ofNat 32 off → s.regs rs.toReg = src →
    s.regs rd.toReg = dst → InRegion Pc base off (seqSize (stores rv rs rd n)) →
    (∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize (stores rv rs rd n)) →
      (∀ r : Reg, r ≠ rv.toReg → r.val ≠ 15 → t.regs r = s.regs r) →
      (∀ i < n, ∀ j < 4, t.mem (dst + BitVec.ofNat 32 (4 * i + j)) =
        BitVec.ofNat 8 ((read32 s.mem (src + BitVec.ofNat 32 (4 * i))).toNat / 2 ^ (8 * j))) →
      (∀ y, ¬ Region dst (4 * n) y → t.mem y = s.mem y) →
      ReachW base Pc Wr t Q) →
    ReachW base Pc Wr s Q
  | 0, off, s, _, _, _, hpc, _, _, _, k =>
    k s (by simpa [stores, seqSize] using hpc) (fun _ _ _ => rfl) (fun i hi => absurd hi (by omega))
      (fun _ _ => rfl)
  | n + 1, off, s, hn, hseq, ho, hpc, hs, hd, hr, k => by
    rw [stores_succ, seqAt_append, Bool.and_eq_true] at hseq
    rw [stores_succ, seqSize_append] at hr k
    have hd1 := hdj.2.1
    refine words_run_w hb hvs hvd hal hdj hwr n off s (by omega) hseq.1 ho hpc hs hd
      (hr.prefix (by omega)) ?_
    intro u upc ureg umem uoth
    have he := X25519OpRun.seqSize_even (stores rv rs rd n)
    have us : u.regs rs.toReg = src := by rw [ureg _ (toReg_ne hvs).symm (by
      have := toReg_ne_15 rs; exact fun e => this (Fin.ext e))]; exact hs
    have ud : u.regs rd.toReg = dst := by rw [ureg _ (toReg_ne hvd).symm (by
      have := toReg_ne_15 rd; exact fun e => this (Fin.ext e))]; exact hd
    refine storeLe32_run_w hb hvs hvd (by omega) (by omega) hseq.2 (by omega) upc us ud hal
      (fun j hj => by rw [show 4 * n + j = 4 * n + j from rfl]; exact hwr _ (by omega))
      (hr.sub (by omega)) ?_
    intro t tpc treg tbytes toth
    -- the source word `n` was not touched by the earlier stores
    have hsrc : read32 u.mem (src + BitVec.ofNat 32 (4 * n)) = read32 s.mem (src + BitVec.ofNat 32 (4 * n)) := by
      apply Frame.read32_congr
      intro q hq
      rw [ofNat_add_assoc]
      apply uoth
      show ¬ ((_ - dst).toNat < _)
      have := hdj.1; have := dst.isLt; have := hdj.2.2
      rw [BitVec.toNat_sub, toNat_add_ofNat _ _ (by omega)]
      by_cases h : dst.toNat ≤ src.toNat + (4 * n + q)
      · rw [show 2 ^ 32 - dst.toNat + (src.toNat + (4 * n + q)) =
          (src.toNat + (4 * n + q) - dst.toNat) + 2 ^ 32 by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    have dne : ∀ q, q < 4 * n → ∀ j < 4, dst + BitVec.ofNat 32 q ≠ dst + BitVec.ofNat 32 (4 * n + j) :=
      fun q hq j hj e => by
        have := congrArg BitVec.toNat e
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at this
        omega
    refine k t (by rw [tpc, Nat.add_assoc]) (fun r h1 h15 => by rw [treg r h1 h15, ureg r h1 h15])
      ?_ ?_
    · intro i hi j hj
      by_cases hin : i < n
      · rw [toth _ (fun j' hj' => dne _ (by omega) j' hj')]
        exact umem i hin j hj
      · obtain rfl : i = n := by omega
        rw [tbytes j hj, hsrc]
    · intro y hy
      have hy' : ¬ Region dst (4 * n) y := fun h => hy (by
        show (y - dst).toNat < _; have : (y - dst).toNat < 4 * n := h; omega)
      rw [toth y (fun j hj e => hy (by
        subst e; show ((dst + BitVec.ofNat 32 (4 * n + j)) - dst).toNat < _
        rw [Frame.sub_ofNat_toNat _ _ (by omega)]; omega)), uoth y hy']

/-! ## Bytes of the value -/

theorem sum_val (f : Nat → Nat) : ∀ n : Nat,
    ((List.range n).map fun i => f i * 2 ^ (32 * i)).sum = X25519Val.val ((List.range n).map f)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, sum_val f n,
      X25519Val.val_append]
    simp [X25519Val.val, Nat.mul_comm]

/-- Byte `4i + j` of `feVal m p` is byte `j` of word `i` at `p`. -/
theorem feVal_byte (m : Mem) (p : Word) {i j : Nat} (hi : i < 8) (hj : j < 4) :
    BitVec.ofNat 8 ((read32 m (p + BitVec.ofNat 32 (4 * i))).toNat / 2 ^ (8 * j)) =
      BitVec.ofNat 8 (feVal m p / 2 ^ (8 * (4 * i + j))) := by
  have e : feVal m p = X25519Val.val ((List.range 8).map fun i => (read32 m (p + BitVec.ofNat 32 (4 * i))).toNat) :=
    sum_val _ 8
  rw [e, X25519Decode.out_byte _ (fun w hw => by
    simp only [List.mem_map] at hw; obtain ⟨_, _, rfl⟩ := hw; exact BitVec.isLt _) i j (by simpa using hi) hj]
  simp

/-! ## The segment -/

theorem storeOut_eq : storeOut = .ldrSp 2 (BitVec.ofNat 8 (lvOut / 4)) :: stores 1 0 2 8 := rfl

theorem lvOut_off : (BitVec.ofNat 8 (lvOut / 4)).toNat * 4 = lvOut := by decide
theorem lvOut_off' : lvOut / 4 % 256 * 4 = lvOut := by decide

/-- **`storeOut`**: from `pc = base + off`, with SP `sp`, `r0 = src` (8 words) and the word
`dst` at `sp + LV_OUT`, the segment writes the 32 little-endian bytes of `feVal` of the source
to `dst`, writes nothing else, and changes no register other than `r1`, `r2` and the flags. -/
theorem storeOut_run_w {base src dst sp : Word} (hb : base.toNat % 2 = 0) {Pc Wr : Word → Prop}
    {s : State} {off : Nat} (hseq : seqAt B off storeOut = true) (ho : off % 2 = 0)
    (hpc : s.pc = base + BitVec.ofNat 32 off) (hsp : s.regs 13 = sp) (hsp4 : sp.toNat % 4 = 0)
    (h0 : s.regs 0 = src) (hout : read32 s.mem (sp + BitVec.ofNat 32 lvOut) = dst)
    (hal : src.toNat % 4 = 0) (hdj : Disj src 32 dst 32)
    (hwr : ∀ k < 32, Wr (dst + BitVec.ofNat 32 k))
    (hr : InRegion Pc base off (seqSize storeOut)) {Q : State → Prop}
    (cont : ∀ t, t.pc = base + BitVec.ofNat 32 (off + seqSize storeOut) →
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → r.val ≠ 15 → t.regs r = s.regs r) →
      (∀ k < 32, t.mem (dst + BitVec.ofNat 32 k) = BitVec.ofNat 8 (feVal s.mem src / 2 ^ (8 * k))) →
      (∀ y, ¬ Region dst 32 y → t.mem y = s.mem y) →
      ReachW base Pc Wr t Q) :
    ReachW base Pc Wr s Q := by
  rw [storeOut_eq] at hseq hr cont
  have hseq' : seqAt B off ([.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4))] ++ stores 1 0 2 8) = true := hseq
  rw [seqAt_append, Bool.and_eq_true] at hseq'
  have hsz : seqSize (Instr.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4)) :: stores 1 0 2 8) =
      seqSize [Instr.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4))] + seqSize (stores 1 0 2 8) :=
    seqSize_append [_] _
  rw [hsz] at hr cont
  have hl1 : seqSize [Instr.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4))] = 2 := rfl
  rw [hl1] at hr cont hseq'
  refine ReachW.block hb [.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4))] off hpc ho hseq'.1 rfl ?_
    (WritesTo.of_noWritesMem _ _ rfl Wr) (hr.prefix (by omega)) ?_
  · simp only [alignedAll, Instr.accesses, State.sp, hsp, lvOut_off, List.all_cons, List.all_nil,
      Access.aligned, Bool.and_true, beq_iff_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [lvOut]; omega
  · generalize hu : execAll [Instr.ldrSp 2 (BitVec.ofNat 8 (lvOut / 4))] s = u
    have upc : u.pc = base + BitVec.ofNat 32 (off + 2) := by
      rw [← hu, execAll_pc _ _ rfl, hpc, ofNat_add_assoc]; rfl
    have um : u.mem = s.mem := by rw [← hu]; exact execAll_mem _ _ rfl
    have u2 : u.regs (LowReg.toReg 2) = dst := by
      rw [← hu, ← hout]
      simp [execAll, Instr.next, Instr.exec, State.setReg, State.sp, hsp, lvOut_off, lvOut_off', X25519Mem.toReg2]
    have uo : ∀ r : Reg, r ≠ 2 → r.val ≠ 15 → u.regs r = s.regs r := fun r h2 h15 => by
      rw [← hu]
      have h15' : r ≠ 15 := fun e => h15 (by rw [e]; rfl)
      simp [execAll, Instr.next, Instr.exec, State.setReg, X25519Mem.toReg2, h2, h15']
    have u0 : u.regs (LowReg.toReg 0) = src := by
      rw [X25519Mem.toReg0, uo 0 (by decide) (by decide), h0]
    refine words_run_w hb (rv := 1) (rs := 0) (rd := 2) (by decide) (by decide) hal hdj hwr 8 (off + 2) u
      (Nat.le_refl _) hseq'.2 (by omega) upc u0 u2 (hr.sub (by omega)) ?_
    intro t tpc treg tbytes toth
    refine cont t (by rw [tpc, Nat.add_assoc]) (fun r h1 h2 h15 => ?_) (fun k hk => ?_) (fun y hy => ?_)
    · rw [treg r (by rw [X25519Mem.toReg1]; exact h1) h15, uo r h2 h15]
    · have e := tbytes (k / 4) (by omega) (k % 4) (by omega)
      rw [um, feVal_byte _ _ (by omega) (by omega), show 4 * (k / 4) + k % 4 = k by omega] at e
      exact e
    · rw [toth y hy, um]

end M0Crypto.Release.X25519OutStore
