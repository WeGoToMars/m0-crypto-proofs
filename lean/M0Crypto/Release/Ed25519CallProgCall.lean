import M0Crypto.Release.Ed25519CallProgEntryRun
import M0Crypto.Release.Ed25519TraceSpec

/-!
# Call programs: an entry's run as the released claim forms

For a call of a build: pcs inside the build, writes outside it and a return address outside it
(`CodeOk`) turn an entry's `ReachFT` run into `Returns`, the read form and the stack form
(`call_returns`, `call_reads`, `call_stack`). `call_result` gives `Returned` and `Wiped` from
`entry_run`'s facts, and `memOut_of` gives `MemOut` from the bytes of the output and the bytes
left alone.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem read32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.TraceSpec (InStackWindow ReadsFrom)
open M0Crypto.Release.Ed25519 (Build Call)

section
variable {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS] {base ret : Word} {Pc Rd Wr Sp : Word → Prop}

/-- The code facts of a call: pcs inside the build, writes and the return address outside it. -/
structure CodeOk (BS : Nat) (base ret : Word) (Pc Wr : Word → Prop) : Prop where
  pc : ∀ y, Pc y → Region base BS y
  wr : ∀ y, Wr y → ¬ Region base BS y
  ret : ¬ Region base BS ret

theorem CodeOk.pc_ne (h : CodeOk BS base ret Pc Wr) : ∀ y, Pc y → y ≠ ret :=
  fun y hy e => h.ret (e ▸ h.pc y hy)

theorem CodeOk.wc (h : CodeOk BS base ret Pc Wr) :
    ∀ y, Wr y → ∀ i < B.length, y ≠ base + BitVec.ofNat 32 i := fun y hy _ hi e =>
  h.wr y hy (e ▸ region_add base (CodeBytes.len (B := B) ▸ hi) (CodeBytes.lt (B := B)))

/-- The pcs of code ranges inside the build. -/
theorem pcIn_region {cs : List (Nat × Nat)} (hBS : BS < 2 ^ 32) (hcs : rangesSub cs [(0, BS)] = true)
    {y : Word} (hy : PcIn base cs y) : Region base BS y := by
  obtain ⟨p, hp, k, h1, h2, rfl⟩ := PcIn.mono hcs hy
  simp only [List.mem_singleton] at hp; subst hp
  exact region_add base h2 hBS

variable (k : Call) {s : State} {Q R : State → Prop} {Φ : TrP}

theorem call_returns {W : Word → Prop} (h : CodeOk BS k.base k.ret Pc Wr) (hc : CodeAt s.mem k.base B)
    (hq : ∀ t, Q t → t.pc = k.ret ∧ R t) (hW : ∀ y, Wr y → W y)
    (hr : ReachFT k.base Pc Rd Wr Sp s Q Φ) : k.Returns s R W := by
  obtain ⟨n, hn⟩ := returns_of h.pc_ne h.wc hc (fun t ht => (hq t ht).1) hr
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, h1, h2, -, h4⟩ := hn fuel hf
  exact ⟨t, tr, h1, (hq t h2).2, fun e he y hy => hW y (h4 e he y hy)⟩

theorem call_reads {RR : Word → Prop} (h : CodeOk BS k.base k.ret Pc Wr) (hc : CodeAt s.mem k.base B)
    (hq : ∀ t, Q t → t.pc = k.ret) (hR : ∀ y, Rd y → RR y) (hr : ReachFT k.base Pc Rd Wr Sp s Q Φ) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ t tr, Thumb.runUntil k.ret fuel s = .ok (t, tr) ∧ ReadsFrom RR tr := by
  obtain ⟨n, hn⟩ := returns_of h.pc_ne h.wc hc hq hr
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨t, tr, h1, -, h3, -⟩ := hn fuel hf
  exact ⟨t, tr, h1, fun e he y hy => hR y (h3 e he y hy)⟩

theorem call_stack {n : Nat} (h : CodeOk BS k.base k.ret Pc Wr) (hc : CodeAt s.mem k.base B)
    (hq : ∀ t, Q t → t.pc = k.ret ∧ t.regs 13 = k.sp0)
    (hr : ReachFT k.base Pc Rd Wr (InStackWindow k.sp0 n) s Q Φ) :
    ∃ m, ∀ fuel, m ≤ fuel → ∃ states tr, runStates k.ret fuel s = .ok (states, tr) ∧
      ∀ u ∈ states, InStackWindow k.sp0 n (u.regs 13) :=
  states_of h.pc_ne h.wc hc (fun t ht => ⟨(hq t ht).1, 0, Nat.zero_le _, by
    rw [(hq t ht).2]; simp⟩) hr

end

/-! ## The result -/

theorem saved_addr (x : Word) (N i : Nat) :
    x - BitVec.ofNat 32 (36 + N) + BitVec.ofNat 32 (36 + N - Ed25519.savedBytes + 4 * i) =
      x - 36#32 + BitVec.ofNat 32 (4 * i) := by
  rw [show 36 + N - Ed25519.savedBytes + 4 * i = N + 4 * i by simp [Ed25519.savedBytes], BitVec.ofNat_add,
    BitVec.ofNat_add]
  bv_omega

theorem add_sub_self (a y : Word) : a + BitVec.ofNat 32 (y - a).toNat = y := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

/-- **`Returned` and `Wiped`** from `entry_run`'s facts, at an entry state with the call's
registers. -/
theorem call_result (k : Call) {N : Nat} {s u : State} (hs : s.regs = k.regs0)
    (hpc : u.pc = s.regs 14 &&& ~~~1#32) (h13 : u.regs 13 = k.sp0)
    (hcal : ∀ r : Reg, 4 ≤ r.val → r.val < 12 → u.regs r = s.regs r)
    (h1 : u.regs 1 = 0) (h2 : u.regs 2 = 0) (h3 : u.regs 3 = 0) (h12 : u.regs 12 = 0)
    (hsv : ∀ i < 9, read32 u.mem (k.sp0 - 36#32 + BitVec.ofNat 32 (4 * i)) = s.regs Ed25519.savedRegs[i]!)
    (hz : ∀ y, Region (k.sp0 - BitVec.ofNat 32 (36 + N)) N y → u.mem y = 0) :
    k.Returned u ∧ k.Wiped (36 + N) u := by
  rw [hs] at hpc hcal hsv
  have hN : 36 + N - Ed25519.savedBytes = N := by simp [Ed25519.savedBytes]
  refine ⟨⟨hpc, h13, hcal⟩, ⟨h1, h2, h3, h12, fun y hy => hz y (by rw [hN, Call.fp] at hy; exact hy),
    fun i hi => ?_⟩⟩
  rw [Call.fp, saved_addr]; exact hsv i hi

/-- **`MemOut`** from the output's bytes and the bytes left alone, outside the window. -/
theorem memOut_of (k : Call) {n : Nat} {out : Word} {len : Nat} {bs : List Ed25519.Byte} {u : State}
    {mb : Mem} (hout : ∀ y, ¬ Region (k.fp n) n y → u.mem y = mb y)
    (hin : ∀ i < len, mb (out + BitVec.ofNat 32 i) = bs[i]!)
    (hrest : ∀ y, ¬ Region (k.fp n) n y → ¬ Region out len y → mb y = k.m0 y) :
    k.MemOut n out len bs u := fun y hy => by
  rw [hout y hy]
  by_cases h : Region out len y
  · simp only [h, ↓reduceIte]
    rw [← hin _ h, add_sub_self]
  · simp only [h, ↓reduceIte]; exact hrest y hy h

/-! ## Regions of a call -/

theorem disj_not {a b y : Word} {n m : Nat} (hd : Frame.Disj a n b m) (h1 : Region a n y) (h2 : Region b m y) :
    False := by
  obtain ⟨d1, d2, d3⟩ := hd; have := y.isLt
  simp only [Region, BitVec.toNat_sub] at h1 h2; omega

theorem Disj.shrink {a b : Word} {n m m' : Nat} (hd : Frame.Disj a n b m) (h : m' ≤ m) : Frame.Disj a n b m' :=
  ⟨hd.1, by have := hd.2.1; omega, by have := hd.2.2; omega⟩

theorem sub_one {r : Rgn} {l : List Rgn} (h : r ∈ l) (hb : r.a.toNat + r.n ≤ 2 ^ 32) : Sub [r] l := by
  intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact ⟨q, h, Nat.le_refl _, Nat.le_refl _, hb⟩

/-- Entry bytes apart from the saved words are the caller's. -/
theorem enter_bytes {s : State} {sp0 a : Word} {n : Nat}
    (h : ∀ j < n, ¬ Region (sp0 - 36#32) 36 (a + BitVec.ofNat 32 j)) :
    bytesAt (enterMem s sp0) a n = Frame.Ctx.bytesAt s.mem a n := by
  rw [ctx_bytesAt]; exact bytesAt_congr fun j hj => enterMem_other s sp0 (h j hj)

theorem byte_of {m : Mem} {a : Word} {n i : Nat} {L : List Ed25519.Byte} (h : bytesAt m a n = L) (hi : i < n) :
    m (a + BitVec.ofNat 32 i) = L[i]! := by
  subst h; simp [bytesAt, hi]

/-- The output's bytes after `MemOut`, when the output lies apart from the window. -/
theorem memOut_bytes {k : Call} {n : Nat} {out : Word} {len : Nat} {bs : List Ed25519.Byte} {u : State}
    (h : k.MemOut n out len bs u) (hd : Frame.Disj out len (k.fp n) n) (hl : bs.length = len) :
    Frame.Ctx.bytesAt u.mem out len = bs := by
  rw [ctx_bytesAt]
  apply List.ext_getElem (by rw [bytesAt_length, hl])
  intro i hi _
  have hr : Region out len (out + BitVec.ofNat 32 i) := by
    simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp only [bytesAt_length] at hi
    simp only [BitVec.toNat_ofNat]; have := hd.1; omega
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h _ fun h' => disj_not hd hr h']; simp only [hr, ↓reduceIte]
  rw [BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [bytesAt_length] at hi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hd.1; omega), getElem!_pos bs i (by omega)]

theorem half_in {a y : Word} {e n m : Nat} (h : Rgn.Has ⟨a + BitVec.ofNat 32 e, n⟩ y) (hm : e + n ≤ m)
    (h32 : m < 2 ^ 32) : Region a m y := by
  obtain ⟨o, ho, rfl⟩ := h
  dsimp only at ho
  simp only [Region]; rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem region_off {a : Word} {n j : Nat} (h : a.toNat + n ≤ 2 ^ 32) (hj : j < n) :
    Region a n (a + BitVec.ofNat 32 j) := by
  simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp only [BitVec.toNat_ofNat]; omega

end M0Crypto.Release.Ed25519CallProg
