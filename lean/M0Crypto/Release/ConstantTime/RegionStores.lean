import M0Crypto.Release.ConstantTime.SiteCheck

/-!
# Store sites bounded by a region

A store at a listed site discharges the certificate's `BufferStoreOk` when every byte it writes
lies in a region (`buf`, `len`) that is separated from the code and from the stack window. The
region is the context or the caller's buffer; the bound on the bytes comes from the pc-aware
write bound of the run (`PcWr`).
-/

namespace M0Crypto.Release.ConstantTime
open M0Crypto.Armv6M (Word State)
open M0Crypto.Thumb
open M0Crypto.Release.Frame (Disj)

theorem bitCount_le_eight (l : BitVec 8) : bitCount l ≤ 8 := by
  revert l; decide +kernel

/-- A store whose written bytes lie in a region separated from the code and the stack window
satisfies the certificate's separation obligation. -/
theorem bufferStoreOk_of_region {env : Env} {p : Params} {bytes : List (BitVec 8)} {st : AbsState}
    {y : State} {i : Instr} {buf : Word} {len : Nat}
    (hc : Disj p.base bytes.length buf len)
    (hs : Disj (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above) buf len)
    (hlen : len + 32 ≤ 2 ^ 32)
    (hw : ∀ a, Writes (i.accesses y) a → ∃ o < len, a = buf + BitVec.ofNat 32 o)
    (hstm : ∀ n l, i = .stm n l → 0 < bitCount l) :
    BufferStoreOk env p bytes st y i := by
  have ends : ∀ (a : Word) (w : Nat), 0 < w → w ≤ 32 →
      Writes (i.accesses y) a → Writes (i.accesses y) (a + BitVec.ofNat 32 (w - 1)) →
      Disj p.base bytes.length a w ∧
      Disj (p.sp0 - BitVec.ofNat 32 env.win.below) (env.win.below + env.win.above) a w := by
    intro a w hw0 hw32 h1 h2
    obtain ⟨o, ho, hfo⟩ := hw a h1
    obtain ⟨o', ho', hlo⟩ := hw _ h2
    exact ⟨disj_of_ends hw0 hc (by omega) ⟨o, ho, hfo⟩ ⟨o', ho', hlo⟩,
      disj_of_ends hw0 hs (by omega) ⟨o, ho, hfo⟩ ⟨o', ho', hlo⟩⟩
  cases i with
  | memImm op t n k =>
    intro _ hop
    have hw0 : 0 < op.width := by cases op <;> decide
    have hw4 : op.width ≤ 4 := by cases op <;> decide
    have wr : ∀ j, j < op.width →
        Writes ((Instr.memImm op t n k).accesses y)
          (y.reg n + BitVec.ofNat 32 (k.toNat * op.width) + BitVec.ofNat 32 j) :=
      fun j hj => ⟨⟨.write, y.reg n + BitVec.ofNat 32 (k.toNat * op.width), op.width⟩, by
        simp [Instr.accesses, hop], rfl, j, hj, rfl⟩
    apply ends _ _ hw0 (by omega) (by simpa using wr 0 hw0) (wr _ (by omega))
  | memReg op t n m =>
    intro _ hop
    have hw0 : 0 < op.width := by cases op <;> decide
    have hw4 : op.width ≤ 4 := by cases op <;> decide
    have wr : ∀ j, j < op.width →
        Writes ((Instr.memReg op t n m).accesses y) (y.reg n + y.reg m + BitVec.ofNat 32 j) :=
      fun j hj => ⟨⟨.write, y.reg n + y.reg m, op.width⟩, by
        simp [Instr.accesses, hop], rfl, j, hj, rfl⟩
    apply ends _ _ hw0 (by omega) (by simpa using wr 0 hw0) (wr _ (by omega))
  | stm n l =>
    intro _
    have hl := hstm n l rfl
    have hle := bitCount_le_eight l
    have wr : ∀ j k, j < bitCount l → k < 4 →
        Writes ((Instr.stm n l).accesses y) (y.reg n + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 k) :=
      fun j k hj hk => ⟨⟨.write, y.reg n + BitVec.ofNat 32 (4 * j), 4⟩, by
        simp only [Instr.accesses, wordAccesses, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩,
        rfl, k, hk, rfl⟩
    have e2 : y.reg n + BitVec.ofNat 32 (4 * (bitCount l - 1)) + BitVec.ofNat 32 3 =
        y.reg n + BitVec.ofNat 32 (4 * bitCount l - 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    refine ends (y.reg n) (4 * bitCount l) (by omega) (by omega) (by simpa using wr 0 0 hl (by omega))
      (by rw [← e2]; exact wr _ 3 (by omega) (by omega))
  | _ => trivial

end M0Crypto.Release.ConstantTime
