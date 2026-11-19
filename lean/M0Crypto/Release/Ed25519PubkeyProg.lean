import M0Crypto.Release.Ed25519SignRun

/-!
# `m0c_ed25519_pubkey` as a call program

The entry's body between `abi_enter` and `abi_leave` (`gen_ed25519.py`, `emit_pubkey`): two
spills of the arguments, one SHA-512 run of the seed, the clamp, the base multiplication into PT
and the compression into `pk`. The frame layout is `emit_pubkey`'s (`Frame.alloc` order); PT
shares CTX, live only after the hash. The callees and blocks are sign's (`eaS`, `ebS`).
-/

namespace M0Crypto.Release.Ed25519PubkeyProg

open M0Crypto.Armv6M (Word Reg State)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.RoutinePieces
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519 (Build Call)
open M0Crypto.Artifacts.Ed25519Compact (ed25519_pubkey)

/-! ## The program -/

/-- `emit_pubkey`'s frame, in `Frame.alloc` order. -/
def PK := 0
def SEED := 4
def HS := 8
def CTX := 72
def PT := CTX

section
open Op Ld

/-- `hash_parts(out, parts)` with the context at frame offset `ctx`; a part is its source, its
length and the length's value. -/
def hashPartsAt (ctx out : Nat) (parts : List (Ld × Ld × SV)) : List (Op EA EB) :=
  call .init [(0, S ctx)] :: go [] parts
where
  go (n : List SV) : List (Ld × Ld × SV) → List (Op EA EB)
    | [] => [call (.final n) [(0, S ctx), (1, S out)]]
    | (src, len, ℓ) :: ps => call (.update n ℓ) [(1, src), (2, len), (0, S ctx)] :: go (n ++ [ℓ]) ps

/-- The body of `m0c_ed25519_pubkey`. The external buffers: `0` is `pk`, `1` the seed. -/
def pubkeyProg : Prog EA EB := Prog.ofList <|
  [spill 0 PK, spill 1 SEED] ++ hashPartsAt CTX HS [(W SEED 0, K 32, .k 32)] ++
  [blk (.clamp ⟨HS / 4, by decide⟩) [], call .mulBase [(0, S PT), (1, S HS)],
   call .compress [(0, W PK 0), (1, S PT)]]

end

/-- The registers at the body's start: the two arguments and `sp`. -/
def pubkeyσ : List (Reg × SV) := [(0, .ext 0 0), (1, .ext 1 0), (13, .sp 0)]

def pubkeySt : St := { Γ := [], σ := pubkeyσ, X := [] }

/-- The body's geometry: the window below the saved registers, the frame, the two buffers. -/
def pubkeyGeo : Geo :=
  { N := stackOf ed25519_pubkey - Ed25519.savedBytes,
    top := ((fnAt ed25519_pubkey).map (·.own)).getD 0 - Ed25519.savedBytes,
    xs := [⟨.k 32, true, false, false⟩, ⟨.k 32, false, true, false⟩],
    cs := footprint ed25519_pubkey }

/-! ## The decided checks, both builds -/

section checks
open M0Crypto.Release.Ed25519

/-- The body's start: after `abi_enter` of the frame. -/
def pubkeyBody : Nat := ed25519_pubkey + seqSize (abiEnter pubkeyGeo.top)

/-- `abi_leave` after the body: the frame and the deepest callee window. -/
def pubkeyLeave : List RoutinePieces.Piece :=
  abiLeave pubkeyGeo.top (pubkeyGeo.N - pubkeyGeo.top) (pubkeyBody + pubkeyProg.size eaS ebS)

theorem pubkey_bok (b : Build) :
    @Prog.bok _ _ b.codeBytes _ _ eaS ebS pubkeyGeo [] pubkeyProg pubkeyBody = true := by
  cases b <;> decide +kernel

theorem pubkey_pieces (b : Build) :
    seqAt b.bytes ed25519_pubkey (abiEnter pubkeyGeo.top) = true ∧
    piecesAt b.bytes pubkeyBody (Prog.emit eaS ebS [] pubkeyBody pubkeyProg ++ pubkeyLeave) = true := by
  cases b <;> exact ⟨by rw [seqAt_eq_scan]; decide +kernel, by rw [piecesAt_eq_scan]; decide +kernel⟩

theorem pubkey_entryOk : entryOk eaS ebS pubkeyGeo pubkeyProg ed25519_pubkey = true := by decide +kernel

theorem pubkey_geo : 36 + pubkeyGeo.N = Ed25519.Pubkey.stackBytes ∧ pubkeyGeo.top ≤ pubkeyGeo.N ∧
    pubkeyGeo.top % 4 = 0 := by decide +kernel

theorem pubkey_cs (b : Build) : rangesSub pubkeyGeo.cs [(0, b.size)] = true ∧ b.pubkeyAt = ed25519_pubkey := by
  cases b <;> decide +kernel

end checks

/-! ## The call's regions -/

/-- The body's context: `sp` below the saved words, the buffers `pk` and `seed`. -/
def pubkeyCtx (c : Ed25519.Pubkey.Ctx) : Ctx :=
  ⟨c.base, c.sp0 - 36#32, fun i => [c.pk, c.seed].getD i 0, fun _ => 0⟩

def pubkeyWc (c : Ed25519.Pubkey.Ctx) : List Rgn := [pubkeyGeo.win (pubkeyCtx c), ⟨c.pk, 32⟩]

def pubkeyRc (b : Build) (c : Ed25519.Pubkey.Ctx) : List Rgn :=
  [⟨c.base, b.size⟩, pubkeyGeo.win (pubkeyCtx c), ⟨c.seed, 32⟩]

section
variable (b : Build) (c : Ed25519.Pubkey.Ctx)

theorem win_eq : pubkeyGeo.win (pubkeyCtx c) = ⟨c.fp, pubkeyGeo.N⟩ := by
  simp only [Geo.win, pubkeyCtx, Ed25519.Pubkey.Ctx.fp, Call.fp]; rw [ad_sub36, pubkey_geo.1]

variable {b c}

theorem saved_S {y : Word} (h : Region (c.sp0 - 36#32) 36 y) : Region c.fp Ed25519.Pubkey.stackBytes y := by
  have := saved_in_all (N := pubkeyGeo.N) h; rwa [pubkey_geo.1] at this

theorem win_S {y : Word} (h : (pubkeyGeo.win (pubkeyCtx c)).Has y) : Region c.fp Ed25519.Pubkey.stackBytes y := by
  rw [win_eq] at h
  have hS := pubkey_geo.1; have : Ed25519.Pubkey.stackBytes < 2 ^ 32 := by decide
  have := rgn_region h (by omega)
  simp only [Region] at this ⊢; omega

theorem wr_cases {y : Word} (h : Has (savedR c.sp0 :: pubkeyWc c) y) : Ed25519.Pubkey.WrOk c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [pubkeyWc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact .inl (saved_S (rgn_region hy (by decide)))
  · exact .inl (win_S hy)
  · exact .inr (rgn_region hy (by decide))

theorem rd_cases {y : Word} (h : Has (savedR c.sp0 :: pubkeyRc b c) y) : Ed25519.Pubkey.ReadRegion b c y := by
  obtain ⟨q, hq, hy⟩ := h
  simp only [pubkeyRc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact .inr (.inr (saved_S (rgn_region hy (by decide))))
  · exact .inr (.inl (rgn_region hy (size_lt b)))
  · exact .inr (.inr (win_S hy))
  · exact .inl (rgn_region hy (by decide))

/-- The saved words lie apart from a buffer apart from the stack window. -/
theorem off_saved {a : Word} {n : Nat} (hd : Frame.Disj a n c.fp Ed25519.Pubkey.stackBytes) :
    ∀ j < n, ¬ Region (c.sp0 - 36#32) 36 (a + BitVec.ofNat 32 j) := fun _ hj hy =>
  disj_not hd (region_off hd.1 hj) (saved_S hy)

theorem pubkey_geoOk (hv : Ed25519.Pubkey.Valid b c) : GeoOk (pubkeyCtx c) pubkeyGeo (pubkeyWc c) (pubkeyRc b c) := by
  have hS := pubkey_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hw : (pubkeyCtx c).sp0 - BitVec.ofNat 32 pubkeyGeo.N = c.fp := congrArg Rgn.a (win_eq c)
  have hwb : (pubkeyGeo.win (pubkeyCtx c)).a.toNat + (pubkeyGeo.win (pubkeyCtx c)).n ≤ 2 ^ 32 := by
    rw [win_eq]; dsimp only
    have : Ed25519.Pubkey.stackBytes < 2 ^ 32 := by decide
    simp only [Ed25519.Pubkey.Ctx.fp, Call.fp, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsp : ((pubkeyCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [pubkeyCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hxs : pubkeyGeo.xs = [⟨.k 32, true, false, false⟩, ⟨.k 32, false, true, false⟩] := rfl
  refine ⟨by omega, by omega, pubkey_geo.2.1, pubkey_geo.2.2, sub_one (by simp [pubkeyWc]) hwb,
    sub_one (by simp [pubkeyRc]) hwb, fun i x hx => ?_, fun _ _ h => by simp [pubkeyGeo] at h,
    fun _ _ h => by simp [pubkeyGeo] at h, fun _ _ h => by simp [pubkeyGeo] at h⟩
  rw [hxs] at hx
  rcases i with _ | _ | i <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, List.getElem?_nil, reduceCtorEq] at hx <;> subst hx
  · refine ⟨.inr ?_, fun _ => sub_one (by simp [pubkeyWc, XLen.v, pubkeyCtx]) hv.pkS.1,
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [hw]; exact Disj.shrink hv.pkS (by omega)
  · refine ⟨.inr ?_, fun h => absurd h (by decide),
      fun _ => sub_one (by simp [pubkeyRc, XLen.v, pubkeyCtx]) hv.seedS.1, fun h => absurd h (by decide)⟩
    rw [hw]; exact Disj.shrink hv.seedS (by omega)

theorem pubkey_caller (hv : Ed25519.Pubkey.Valid b c) :
    @Caller b.bytes b.size b.codeBytes (pubkeyCtx c).base (pubkeyCtx c).sp0 pubkeyGeo.N (pubkeyWc c) := by
  have hS := pubkey_geo.1; have hlo := hv.call.spLo; have h4 := hv.call.sp4; have hl := c.sp0.isLt
  have hsp : ((pubkeyCtx c).sp0).toNat = c.sp0.toNat - 36 := by
    simp only [pubkeyCtx, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  letI := b.codeBytes
  refine ⟨hv.call.base4, by omega, by omega, fun r hr q hq => ?_, hv.codeO.1⟩
  simp only [List.mem_singleton] at hr; subst hr
  simp only [pubkeyWc, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · rw [win_eq]; exact Disj.shrink hv.call.codeS (by dsimp only; omega)
  · exact hv.codeO

theorem pubkey_codeOk (hv : Ed25519.Pubkey.Valid b c) :
    CodeOk b.size c.base c.ret (PcIn c.base pubkeyGeo.cs) (Has (savedR c.sp0 :: pubkeyWc c)) := by
  letI := b.codeBytes
  exact ⟨fun _ hy => pcIn_region (size_lt b) (pubkey_cs b).1 hy,
    fun _ hy h => (wr_cases hy).elim (disj_not hv.call.codeS h) (disj_not hv.codeO h), hv.call.retOut⟩

end

end M0Crypto.Release.Ed25519PubkeyProg
