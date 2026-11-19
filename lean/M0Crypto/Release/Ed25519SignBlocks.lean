import M0Crypto.Release.Ed25519SignProg
import M0Crypto.Release.Ed25519CallProgBytes
import M0Crypto.Release.Ed25519CallProgEntryRun

/-!
# Sign's inline blocks

`clamp(4q)` prunes the 32-byte scalar of a 64-byte digest view in place: its view becomes the
clamped scalar's 32 bytes and the unchanged prefix (`clampB`). `store` copies the 32 bytes at the
word-aligned `r3` to `r2`, equal or apart.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Armv6M (Word Reg State Mem read32 write32)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (bytesAt bytesAt_length)
open M0Crypto.Spec.Ed25519 (Byte decodeInt encodeInt)
open M0Crypto.Release.Ed25519Words (wsum)
open M0Crypto.Release.Ed25519Bytes (clampNat)
open M0Crypto.Release.Ed25519Routines (EqOrDisj)

/-! ## Offsets from one base, each in its own context -/

theorem reg_off (b : Word) (d e n : Nat) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    Region (b + BitVec.ofNat 32 d) n (b + BitVec.ofNat 32 e) ↔ (e + 2 ^ 32 - d) % 2 ^ 32 < n := by
  have := b.isLt
  simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem write32_out {m : Mem} {a v y : Word} (h : ¬ Region a 4 y) : write32 m a v y = m y :=
  Armv6M.write32_other m a v y fun k hk e => h (by subst e; exact region_add a hk (by decide))

theorem off_add (b : Word) (x y : Nat) : b + BitVec.ofNat 32 x + BitVec.ofNat 32 y = b + BitVec.ofNat 32 (x + y) :=
  ofNat_add_assoc b x y

/-! ## `clamp` -/

/-- The clamp's view: the clamped scalar's 32 bytes, then the prefix. -/
def clampB (h : List Byte) : List Byte := encodeInt (clampNat (decodeInt (h.take 32))) ++ h.drop 32

/-- The clamped scalar's 32 bytes, from the digest's first 32. -/
def clampSc (h : List Byte) : List Byte := encodeInt (clampNat (decodeInt h))

theorem clampNat_lt (s : Nat) : clampNat s < 2 ^ 255 := by
  unfold clampNat; have := Nat.mod_lt s (Nat.two_pow_pos 254); omega

/-- The clamped scalar's number is below `2 ^ 255`. -/
theorem clampSc_lt (h : List Byte) : decodeInt (clampSc h) < 2 ^ 255 := by
  rw [clampSc, decodeInt_encodeInt, Nat.mod_eq_of_lt (Nat.lt_trans (clampNat_lt _) (by decide))]
  exact clampNat_lt _

theorem clamp_mem (q : Nat) (t : State) :
    (execAll (clampG q) t).mem =
      write32 (write32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 q).toNat * 4))
        ((read32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 q).toNat * 4)) >>> 3) <<< 3))
        (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 (q + 7)).toNat * 4))
        (((read32 (write32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 q).toNat * 4))
          ((read32 t.mem (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 q).toNat * 4)) >>> 3) <<< 3))
          (t.regs 13 + BitVec.ofNat 32 ((BitVec.ofNat 8 (q + 7)).toNat * 4)) <<< 2) >>> 2) |||
          (1#32 <<< 30)) := rfl

/-- **`clamp(4q)`'s view.** -/
theorem clamp_bytes (q : Fin 249) (t : State) :
    bytesAt (execAll (clampG q.val) t).mem (t.regs 13 + BitVec.ofNat 32 (4 * q.val)) 64 =
      clampB (bytesAt t.mem (t.regs 13 + BitVec.ofNat 32 (4 * q.val)) 64) := by
  have hq := q.isLt
  have e0 : (BitVec.ofNat 8 q.val).toNat * 4 = 4 * q.val := by simp; omega
  have e7 : (BitVec.ofNat 8 (q.val + 7)).toNat * 4 = 4 * q.val + 28 := by simp; omega
  rw [clamp_mem, e0, e7]
  generalize t.regs 13 = b
  generalize t.mem = m
  generalize hw0 : read32 m (b + BitVec.ofNat 32 (4 * q.val)) = w0
  generalize hm1 : write32 m (b + BitVec.ofNat 32 (4 * q.val)) ((w0 >>> 3) <<< 3) = m1
  -- bytes outside the first written word, and outside both
  have out1 : ∀ e, e < 4 * q.val + 64 → 4 * q.val + 4 ≤ e → m1 (b + BitVec.ofNat 32 e) = m (b + BitVec.ofNat 32 e) :=
    fun e he1 he2 => by rw [← hm1, write32_out (by rw [reg_off _ _ _ _ (by omega) (by omega)]; omega)]
  have out : ∀ e, e < 4 * q.val + 64 → (4 * q.val + 4 ≤ e ∧ e < 4 * q.val + 28 ∨ 4 * q.val + 32 ≤ e) →
      ∀ v, write32 m1 (b + BitVec.ofNat 32 (4 * q.val + 28)) v (b + BitVec.ofNat 32 e) =
        m (b + BitVec.ofNat 32 e) := fun e he1 he2 v => by
    rw [write32_out (by rw [reg_off _ _ _ _ (by omega) (by omega)]; omega), out1 e he1 (by omega)]
  have w7e : read32 m1 (b + BitVec.ofNat 32 (4 * q.val + 28)) = read32 m (b + BitVec.ofNat 32 (4 * q.val + 28)) :=
    Frame.read32_congr fun k hk => by rw [off_add, out1 _ (by omega) (by omega)]
  rw [w7e]
  generalize hw7 : read32 m (b + BitVec.ofNat 32 (4 * q.val + 28)) = w7
  simp only [clampB]
  rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_split, bytesAt_split, List.take_left' (bytesAt_length _ _ _),
    List.drop_left' (bytesAt_length _ _ _)]
  congr 1
  · -- the scalar: words 0 and 7 clamped, the others kept
    have d8 : ∀ m a, decodeInt (bytesAt m a 32) = wsum (fun j => (read32 m (a + BitVec.ofNat 32 (4 * j))).toNat) 8 :=
      fun m a => decodeInt_words m a 8
    rw [← encodeInt_decodeInt (bytesAt_length _ _ 32), d8, d8]
    congr 1
    refine Ed25519Bytes.clamp_words (fun j _ => (read32 _ _).isLt) ?_ ?_ fun j h1 h2 => ?_
    · simp only [Nat.mul_zero, off_add, Nat.add_zero]
      rw [Frame.read32_congr (m := m1) fun k hk => by
          rw [off_add, write32_out (by rw [reg_off _ _ _ _ (by omega) (by omega)]; omega)],
        ← hm1, Armv6M.read32_write32_same, hw0]
      exact Ed25519Bytes.clamp_lo w0
    · simp only [off_add, show 4 * q.val + 4 * 7 = 4 * q.val + 28 by omega, Armv6M.read32_write32_same, hw7]
      exact Ed25519Bytes.clamp_hi w7
    · simp only [off_add]
      exact congrArg BitVec.toNat (Frame.read32_congr fun k hk => by
        rw [off_add]; exact out _ (by omega) (by omega) _)
  · exact Footprint.bytesAt_congr fun i hi => by
      simp only [off_add]; exact out _ (by omega) (by omega) _

/-! ## `store` -/

/-- Word `i` of `store`: load it, store its four bytes. -/
def stGrp (i : Nat) : List Instr :=
  [.memImm .ldr 1 3 (BitVec.ofNat 5 i), .memImm .strb 1 2 (BitVec.ofNat 5 (4 * i))] ++
    (List.range 3).flatMap fun j => [.lsrImm 1 1 8, .memImm .strb 1 2 (BitVec.ofNat 5 (4 * i + j + 1))]

theorem storeG_eq : storeG = (List.range 8).flatMap stGrp := rfl

theorem stGrp_run (i : Nat) (u : State) :
    (execAll (stGrp i) u).regs 2 = u.regs 2 ∧ (execAll (stGrp i) u).regs 3 = u.regs 3 ∧
    (execAll (stGrp i) u).mem =
      let w := read32 u.mem (u.regs 3 + BitVec.ofNat 32 ((BitVec.ofNat 5 i).toNat * 4))
      let a := fun k => u.regs 2 + BitVec.ofNat 32 ((BitVec.ofNat 5 k).toNat * 1)
      write8 (write8 (write8 (write8 u.mem (a (4 * i)) w) (a (4 * i + 0 + 1)) (w >>> 8))
        (a (4 * i + 1 + 1)) (w >>> 8 >>> 8)) (a (4 * i + 2 + 1)) (w >>> 8 >>> 8 >>> 8) :=
  ⟨rfl, rfl, rfl⟩

theorem bytes_of (a3 a2 a1 a0 : BitVec 8) :
    (a3 ++ a2 ++ a1 ++ a0).extractLsb' 0 8 = a0 ∧ ((a3 ++ a2 ++ a1 ++ a0) >>> 8).extractLsb' 0 8 = a1 ∧
    ((a3 ++ a2 ++ a1 ++ a0) >>> 8 >>> 8).extractLsb' 0 8 = a2 ∧
    ((a3 ++ a2 ++ a1 ++ a0) >>> 8 >>> 8 >>> 8).extractLsb' 0 8 = a3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i hi <;>
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append] <;>
    (repeat' split) <;> first | omega | (congr 1; omega) | simp_all <;> omega

theorem off_eq {b : Word} {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    b + BitVec.ofNat 32 x = b + BitVec.ofNat 32 y ↔ x = y := by
  constructor
  · intro h; have e := congrArg BitVec.toNat h; have := b.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at e; omega
  · rintro rfl; rfl

theorem ofNat_eq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    BitVec.ofNat 32 x = BitVec.ofNat 32 y ↔ x = y := by
  simpa using off_eq (b := 0) hx hy

/-- The four byte stores of a word, at a byte they store. -/
theorem w8_in (m : Mem) (b w : Word) {o j : Nat} (ho : o + 4 < 2 ^ 32) (hj : j < 4) :
    write8 (write8 (write8 (write8 m (b + BitVec.ofNat 32 o) w) (b + BitVec.ofNat 32 (o + 1)) (w >>> 8))
      (b + BitVec.ofNat 32 (o + 2)) (w >>> 8 >>> 8)) (b + BitVec.ofNat 32 (o + 3)) (w >>> 8 >>> 8 >>> 8)
      (b + BitVec.ofNat 32 (o + j)) =
    (if j = 0 then w else if j = 1 then w >>> 8 else if j = 2 then w >>> 8 >>> 8 else w >>> 8 >>> 8 >>> 8).extractLsb' 0 8 := by
  obtain _ | _ | _ | _ | j := j
  all_goals first | omega | simp (disch := omega) [write8, ofNat_eq]

/-- The four byte stores of a word, elsewhere. -/
theorem w8_out (m : Mem) (b w y : Word) (o : Nat) (h : ∀ j < 4, y ≠ b + BitVec.ofNat 32 (o + j)) :
    write8 (write8 (write8 (write8 m (b + BitVec.ofNat 32 o) w) (b + BitVec.ofNat 32 (o + 1)) (w >>> 8))
      (b + BitVec.ofNat 32 (o + 2)) (w >>> 8 >>> 8)) (b + BitVec.ofNat 32 (o + 3)) (w >>> 8 >>> 8 >>> 8) y = m y := by
  rw [write8_other _ _ _ _ (h 3 (by omega)), write8_other _ _ _ _ (h 2 (by omega)),
    write8_other _ _ _ _ (h 1 (by omega)), write8_other _ _ _ _ (by simpa using h 0 (by omega))]

theorem src_out {r2 r3 : Word} (hd : EqOrDisj r2 r3 32) {k j : Nat} (hk : k < 8) (hj : j < 4) :
    ¬ Region r2 (4 * k) (r3 + BitVec.ofNat 32 (4 * k + j)) := by
  rcases hd with rfl | ⟨h1, h2, h3⟩
  · simp only [Region]; rw [BitVec.add_comm, BitVec.add_sub_cancel]; simp; omega
  · simp only [Region, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- After `k` words: `r2`, `r3` kept, the first `4k` bytes copied, nothing else written. -/
theorem store_inv (t : State) (hd : EqOrDisj (t.regs 2) (t.regs 3) 32) : ∀ k, k ≤ 8 →
    (execAll ((List.range k).flatMap stGrp) t).regs 2 = t.regs 2 ∧
    (execAll ((List.range k).flatMap stGrp) t).regs 3 = t.regs 3 ∧
    (∀ e < 4 * k, (execAll ((List.range k).flatMap stGrp) t).mem (t.regs 2 + BitVec.ofNat 32 e) =
      t.mem (t.regs 3 + BitVec.ofNat 32 e)) ∧
    ∀ y, ¬ Region (t.regs 2) (4 * k) y → (execAll ((List.range k).flatMap stGrp) t).mem y = t.mem y
  | 0, _ => ⟨rfl, rfl, fun e he => absurd he (by omega), fun _ _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨i2, i3, iw, io⟩ := store_inv t hd k (by omega)
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      execAll_append]
    generalize execAll ((List.range k).flatMap stGrp) t = u at i2 i3 iw io
    obtain ⟨g2, g3, gm⟩ := stGrp_run k u
    have h5 : ∀ n, n < 32 → (BitVec.ofNat 5 n).toNat = n := fun n hn => by simp; omega
    simp (disch := omega) only [h5, Nat.mul_one, i2, i3] at gm
    rw [show 4 * k + 0 + 1 = 4 * k + 1 by omega, show 4 * k + 1 + 1 = 4 * k + 2 by omega,
      show 4 * k + 2 + 1 = 4 * k + 3 by omega, Nat.mul_comm k 4] at gm
    have hr : ∀ j < 4, u.mem (t.regs 3 + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 j) =
        t.mem (t.regs 3 + BitVec.ofNat 32 (4 * k + j)) := fun j hj => by
      rw [off_add]; exact io _ (src_out hd (by omega) hj)
    refine ⟨g2.trans i2, g3.trans i3, fun e he => ?_, fun y hy => ?_⟩
    · rw [gm]
      by_cases he' : e < 4 * k
      · rw [w8_out _ _ _ _ _ fun j _ h => by rw [off_eq (by omega) (by omega)] at h; omega]; exact iw e he'
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ e = 4 * k + j := ⟨e - 4 * k, by omega, by omega⟩
        rw [w8_in _ _ _ (by omega) hj, ← hr j hj]
        obtain ⟨b0, b1, b2, b3⟩ := bytes_of (u.mem (t.regs 3 + BitVec.ofNat 32 (4 * k) + 3#32))
          (u.mem (t.regs 3 + BitVec.ofNat 32 (4 * k) + 2#32)) (u.mem (t.regs 3 + BitVec.ofNat 32 (4 * k) + 1#32))
          (u.mem (t.regs 3 + BitVec.ofNat 32 (4 * k)))
        obtain _ | _ | _ | _ | j := j
        · simpa [read32] using b0
        · simpa [read32] using b1
        · simpa [read32] using b2
        · simpa [read32] using b3
        · omega
    · rw [gm, w8_out _ _ _ _ _ fun j hj e => hy (by rw [e]; exact region_add _ (by omega) (by omega))]
      exact io y fun h => hy (by simp only [Region] at h ⊢; omega)

/-- **`store`'s view**: the 32 bytes at `r3`, at `r2`. -/
theorem store_bytes (t : State) (hd : EqOrDisj (t.regs 2) (t.regs 3) 32) :
    bytesAt (execAll storeG t).mem (t.regs 2) 32 = bytesAt t.mem (t.regs 3) 32 := by
  obtain ⟨-, -, hw, -⟩ := store_inv t hd 8 (by omega)
  rw [storeG_eq]
  exact Footprint.bytesAt_eq_of fun i hi => hw i (by omega)

/-! ## The block adapters -/

/-- The blocks' semantics. -/
def semB : EB → List V → List V
  | .clamp _, [.b lo, .b hi] => [.b (clampSc lo), .b hi]
  | .store, [.b l] => [.b l]
  | _, _ => [.none]

/-- **Sign's block adapters.** -/
def bdS (Rs : Rels) : ∀ b, Bd Rs (ebS b)
  | .clamp q => ⟨semB (.clamp q), fun c sp t vs _ _ _ hin => by
      rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [InsRel, All2, ebS, ioClamp, and_true, and_false] at hin
      cases v <;> cases w <;> simp only [Rel, In.kd, and_false, false_and] at hin
      rename_i lo hi
      obtain ⟨h1, h2⟩ := hin
      rw [← Thumb.ofNat_add_assoc] at h2
      have cb := clamp_bytes q t
      have hs : ∀ m : Mem, bytesAt m (t.regs 13 + BitVec.ofNat 32 (4 * q.val)) 64 = _ := fun m =>
        bytesAt_split m _ 32 32
      have hl : lo.length = 32 := by rw [← h1, bytesAt_length]
      rw [hs, hs, h1, h2, clampB, List.take_left' hl, List.drop_left' hl] at cb
      obtain ⟨e1, e2⟩ := List.append_inj cb (by rw [bytesAt_length, encodeInt_length])
      rw [Thumb.ofNat_add_assoc] at e2
      simp only [OutsRel, All2, ebS, ioClamp, semB, Rel, and_true, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero]
      exact ⟨⟨e1, clampSc_lt lo⟩, e2⟩, fun _ _ _ _ _ _ _ _ _ h => by simp [ebS, ioClamp] at h⟩
  | .store => ⟨semB .store, fun c sp t vs hp _ _ hin => by
      rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp only [InsRel, All2, ebS, ioStore, and_true, and_false] at hin
      cases v <;> simp only [Rel, In.kd] at hin
      simp only [OutsRel, All2, ebS, ioStore, semB, Rel, and_true, List.length_cons, List.length_nil,
        List.take_succ_cons, List.take_zero]
      have hd := hp.2.1 (2, 3, 32) (by simp [ebS, ioStore])
      simp only [BitVec.add_zero] at hin ⊢
      rw [store_bytes t hd, hin], fun _ _ _ _ _ _ _ _ _ h => by simp [ebS, ioStore] at h⟩

end M0Crypto.Release.Ed25519CallProg
