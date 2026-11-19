import M0Crypto.Spec.Ed25519
import M0Crypto.Release.Ed25519Build

/-!
# The flash tables and constants of the Ed25519 unit

What each table and constant of a build must hold, from the specification
(`Spec.Ed25519`, `Spec.Sha512`), and how the kernel evaluates it.

Layout (generator `emit_data`): a field element is 8 little-endian words (32 bytes, the value
below `p`), `mu` and `L` are 9 words, a SHA-512 word is two words, low first (8 bytes little
endian). A table entry stores the affine point `(x, y)` in Niels form `(y + x, y − x, 2dxy) mod p`
(`niels`). `m0c_ed_odd_b` holds `[2k + 1]B` for `k < 8`; `m0c_ed_comb` holds, for comb `c < n`
and entry `j < 8`, `[combVal n c j]B` with
`combVal n c j = 2^(s(4c+3)) + Σ_{k<3} (2 bit_k(j) − 1) 2^(s(4c+k))`, `s = 64 / n`.

The specification computes `[k]B` by `scalarMul` (well-founded recursion) and inverses by
`powp x (p − 2) = x^(p−2) % p`, neither of which the kernel evaluates. `mulFuel` and `powFuel`
are the same algorithms with a fuel argument; `mulFuel_eq` and `powFuel_eq` prove them equal to
the specification, so `nielsFast_eq` turns every expected entry into a value the kernel computes.
-/

namespace M0Crypto.Release.Ed25519Tables

open M0Crypto.Spec.Ed25519
open M0Crypto.Release.Ed25519 (Build)

/-! ## Reading the bytes -/

/-- The little-endian value of the first `n` bytes of `bs`. -/
def leVal : Nat → List Byte → Nat
  | 0, _ => 0
  | n + 1, bs => (bs.headD 0).toNat + 256 * leVal n bs.tail

/-- `k` consecutive `w`-byte little-endian values from the start of `bs`. -/
def leVals (w : Nat) : Nat → List Byte → List Nat
  | 0, _ => []
  | k + 1, bs => leVal w bs :: leVals w k (bs.drop w)

/-! ## Evaluation of the specification -/

/-- `x^e % p` by square-and-multiply on at most `fuel` bits of `e`. -/
def powFuel : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % p
  | fuel + 1, x, e =>
    if e = 0 then 1 % p else
      let r := powFuel fuel x (e / 2)
      if e % 2 = 0 then r * r % p else r * r % p * x % p

theorem powFuel_eq : ∀ (fuel x e : Nat), e < 2 ^ fuel → powFuel fuel x e = powp x e
  | 0, x, e, h => by
    obtain rfl : e = 0 := by rw [Nat.pow_zero] at h; omega
    simp [powFuel, powp]
  | fuel + 1, x, e, h => by
    rw [powFuel, powp]
    by_cases h0 : e = 0
    · simp [h0]
    · have ih := powFuel_eq fuel x (e / 2) (by rw [Nat.pow_succ] at h; omega)
      simp only [h0, ↓reduceIte, ih, powp]
      have hsq : x ^ (e / 2) % p * (x ^ (e / 2) % p) % p = x ^ (e / 2 * 2) % p := by
        rw [← Nat.mul_mod, ← Nat.pow_add]; congr 2; omega
      by_cases he : e % 2 = 0
      · simp only [he, ↓reduceIte, hsq]; congr 2; omega
      · simp only [he, ↓reduceIte, hsq]
        rw [Nat.mod_mul_mod, ← Nat.pow_succ]; congr 2; omega

/-- `[s]P` by double-and-add on at most `fuel` bits of `s`, as `scalarMul`. -/
def mulFuel : Nat → Nat → Point → Point
  | 0, _, _ => neutral
  | fuel + 1, s, P =>
    if s = 0 then neutral else
      let Q := mulFuel fuel (s / 2) (add P P)
      if s % 2 = 1 then add Q P else Q

theorem mulFuel_eq : ∀ (fuel s : Nat) (P : Point), s < 2 ^ fuel → mulFuel fuel s P = scalarMul s P
  | 0, s, P, h => by
    obtain rfl : s = 0 := by rw [Nat.pow_zero] at h; omega
    rw [mulFuel, scalarMul]; simp
  | fuel + 1, s, P, h => by
    rw [mulFuel, scalarMul]
    by_cases h0 : s = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte, mulFuel_eq fuel (s / 2) (add P P) (by rw [Nat.pow_succ] at h; omega)]

/-! ## Expected contents -/

/-- An affine point `(x, y)` in Niels form: `y + x`, `y − x`, `2dxy`, each mod `p`. -/
def niels (xy : Nat × Nat) : List Nat :=
  [(xy.2 + xy.1) % p, fsub xy.2 xy.1, 2 * d * xy.1 * xy.2 % p]

/-- The table entry of `[k]B`. -/
def entry (k : Nat) : List Nat := niels (scalarMul k B).xy

/-- `entry` as the kernel evaluates it, for `k < 2^256`. -/
def entryFast (k : Nat) : List Nat :=
  let P := mulFuel 256 k B
  let zi := powFuel 255 P.Z (p - 2)
  niels (P.X * zi % p, P.Y * zi % p)

theorem entryFast_eq {k : Nat} (hk : k < 2 ^ 256) : entryFast k = entry k := by
  have hp : p - 2 < 2 ^ 255 := by unfold p; omega
  simp only [entryFast, entry, Point.xy, inv, mulFuel_eq 256 k B hk, powFuel_eq 255 _ _ hp]

/-- Entry `j < 8` of comb `c` for `n` combs: `2^(s(4c+3)) + Σ_{k<3} (2 bit_k(j) − 1) 2^(s(4c+k))`,
`s = 64 / n`. -/
def combVal (n c j : Nat) : Int :=
  let s := 64 / n
  2 ^ (s * (4 * c + 3)) + ((List.range 3).map fun k =>
    (2 * ((j / 2 ^ k % 2 : Nat) : Int) - 1) * 2 ^ (s * (4 * c + k))).sum

/-- `m0c_ed_comb` for `n` combs: comb `c`, then entry `j`, each as three field elements. -/
def combTable (n : Nat) : List Nat :=
  (List.range n).flatMap fun c => (List.range 8).flatMap fun j => entry (combVal n c j).toNat

/-- `m0c_ed_odd_b`: `[2k + 1]B` for `k < 8`. -/
def oddTable : List Nat := (List.range 8).flatMap fun k => entry (2 * k + 1)

/-- The field constants `0, 1, d, 2d, sqrt(−1)` in the generator's order, each below `p`.
`sqrt(−1)` is the `2^((p−1)/4)` of section 5.1.3, step 3. -/
def feConsts : List Nat := [0, 1, d, 2 * d % p, powp 2 ((p - 1) / 4)]

/-- Barrett's `mu = ⌊2^512 / L⌋` and `L`, 9 words each. -/
def scConsts : List Nat := [2 ^ 512 / L, L]

def shaK : List Nat := M0Crypto.Spec.Sha512.K.toList.map BitVec.toNat
def shaIV : List Nat := M0Crypto.Spec.Sha512.H0.toList.map BitVec.toNat

open M0Crypto.Artifacts.Ed25519Compact (ed_zero ed_one ed_d ed_d2 ed_sqrtm1 ed_mu ed_l9 sha512_K
  sha512_IV ed_odd_b ed_comb) in
/-- The constants and tables that build `b` holds at its data labels (the `compact` offsets, the
same in both builds: `Ed25519.offsets_same`) equal the specification's values. The comb table
of `b.combs` combs ends the unit. -/
structure TablesOk (b : Build) : Prop where
  fe : [ed_zero, ed_one, ed_d, ed_d2, ed_sqrtm1].map (fun o => leVal 32 (b.bytes.drop o)) = feConsts
  sc : [ed_mu, ed_l9].map (fun o => leVal 36 (b.bytes.drop o)) = scConsts
  k : leVals 8 80 (b.bytes.drop sha512_K) = shaK
  iv : leVals 8 8 (b.bytes.drop sha512_IV) = shaIV
  odd : leVals 32 24 (b.bytes.drop ed_odd_b) = oddTable
  comb : leVals 32 (24 * b.combs) (b.bytes.drop ed_comb) = combTable b.combs
  comb_end : ed_comb + 32 * (24 * b.combs) = b.size

/-! ## Kernel-evaluable forms -/

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

def combFast (n : Nat) : List Nat :=
  (List.range n).flatMap fun c => (List.range 8).flatMap fun j => entryFast (combVal n c j).toNat

/-- Every comb multiple is below `2^256`, so `entryFast` evaluates it. -/
def combBound (n : Nat) : Bool :=
  (List.range n).all fun c => (List.range 8).all fun j => decide ((combVal n c j).toNat < 2 ^ 256)

theorem combFast_eq {n : Nat} (h : combBound n = true) : combFast n = combTable n := by
  simp only [combBound, List.all_eq_true, decide_eq_true_eq] at h
  exact flatMap_congr fun c hc => flatMap_congr fun j hj => entryFast_eq (h c hc j hj)

def oddFast : List Nat := (List.range 8).flatMap fun k => entryFast (2 * k + 1)

theorem oddFast_eq : oddFast = oddTable :=
  flatMap_congr fun k hk => entryFast_eq (by simp only [List.mem_range] at hk; omega)

def feConstsFast : List Nat := [0, 1, d, 2 * d % p, powFuel 255 2 ((p - 1) / 4)]

theorem feConstsFast_eq : feConstsFast = feConsts := by
  have h : (p - 1) / 4 < 2 ^ 255 := by unfold p; omega
  simp only [feConstsFast, feConsts, powFuel_eq 255 2 _ h]

end M0Crypto.Release.Ed25519Tables
