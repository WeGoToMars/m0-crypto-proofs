import M0Crypto.Release.ConstantTime.Cert

/-! # Checking a certificate in chunks

The kernel keeps its reduction caches for the whole of one declaration. For a large
certificate, `decide +kernel` on `certOk` therefore holds every block's intermediate terms
at once (for `m0c_x25519`, mostly the `bytes.drop b.off` of `blkFailure`). These lemmas let
an entry check the entry block once and the blocks in chunks, one declaration per chunk, and
then conclude `certOk`. The chunk size only changes memory, not what is checked. -/

namespace M0Crypto.Release.ConstantTime

/-- The entry block exists and covers the entry state. -/
def certEntryOk (entry : Nat) (init : AbsState) (c : Cert) : Bool :=
  match findBlk c entry none with
  | none => false
  | some b => init.le b.st

/-- One block passes its check. -/
def blkOk (env : Env) (bytes : List (BitVec 8)) (c : Cert) (b : Blk) : Bool :=
  (blkFailure env bytes c b).isNone

theorem certOk_of_blocks {env : Env} {bytes : List (BitVec 8)} {entry : Nat} {init : AbsState}
    {c : Cert} (he : certEntryOk entry init c = true)
    (hb : c.all (blkOk env bytes c) = true) : certOk env bytes entry init c = true := by
  rw [certOk_iff]
  unfold certEntryOk at he
  unfold certFailure
  split at he
  · contradiction
  · rename_i b hf
    simp only [hf, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [List.findSome?_eq_none_iff]
    intro x hx
    simpa [blkOk] using List.all_eq_true.mp hb x hx

/-- A list passes `p` if its first `n` chunks of `k` elements and the rest do. -/
theorem all_of_chunks {α : Type} (p : α → Bool) (c : List α) (k n : Nat)
    (h : ∀ i < n, ((c.drop (i * k)).take k).all p = true)
    (hrest : (c.drop (n * k)).all p = true) : c.all p = true := by
  have hpre : ∀ m ≤ n, (c.take (m * k)).all p = true := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      rw [Nat.succ_mul, List.take_add, List.all_append, ih (by omega), h m (by omega)]
      rfl
  rw [← List.take_append_drop (n * k) c, List.all_append, hpre n (Nat.le_refl _), hrest]
  rfl

end M0Crypto.Release.ConstantTime
