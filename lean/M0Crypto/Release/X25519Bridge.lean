import M0Crypto.Release.ConstantTime.X25519Entry
import M0Crypto.Release.ConstantTime.EntrySound
import M0Crypto.Release.ConstantTime.ContractBridges
import M0Crypto.Release.TraceSpec
import M0Crypto.Release.X25519TraceSpec

/-!
# From the X25519 contract to the certificate's parameters

The constant-time certificate of `m0c_x25519` (`ConstantTime/X25519Entry.lean`) is checked
against an `Env` and used with `Params`. The generic run theorems
(`EntryReads.certificate_run_reads`, `RegionStores.bufferStoreOk_of_region`, `certAt_initial`)
take the facts below as hypotheses. This file derives each of them from `X25519.Valid` or
`X25519.Pre`, as `ContractBridges.lean` does for ChaCha20 and the AEAD.

Nothing here restates a number: the window is `x25519Env.win`, the code length is
`Release.bytes.length`, and the contract's sizes are `X25519.stackBytes` and the buffer length
of `Valid`. The two window facts (`x25519_win_bytes`, `x25519_win_lo`) are the only places
where the certificate's window and the contract's stack window meet; both hold by `rfl`.
-/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Armv6M (Word State)
open M0Crypto.Artifacts
open M0Crypto.Release.Frame (Disj)

/-- The certificate parameters of a call: link base, entry SP, entry LR, artifact length. -/
def x25519Params (c : X25519.Ctx) : Params :=
  ⟨c.base, c.sp0, c.regs0 14, Release.bytes.length⟩

/-! ## The certificate's window is the contract's stack window -/

/-- Width of the certificate's window: the contract's stack bytes. -/
theorem x25519_win_bytes : x25519Env.win.below + x25519Env.win.above = X25519.stackBytes := rfl

/-- Lowest address of the certificate's window: the contract's `fp`. -/
theorem x25519_win_lo (c : X25519.Ctx) :
    (x25519Params c).sp0 - BitVec.ofNat 32 x25519Env.win.below = c.fp := rfl

theorem x25519_win_width : x25519Env.win.below + x25519Env.win.above < 2 ^ 32 := by
  rw [x25519_win_bytes]; decide

theorem x25519_env_size : x25519Env.size = Release.bytes.length := Release.bytes_length.symm

/-! ## Code -/

/-- The code is separated from the certificate's whole stack window. -/
theorem x25519_code_stack_disjoint {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj (x25519Params c).base Release.bytes.length
      ((x25519Params c).sp0 - BitVec.ofNat 32 x25519Env.win.below)
      (x25519Env.win.below + x25519Env.win.above) := by
  rw [x25519_win_lo, x25519_win_bytes, Release.bytes_length]
  exact hv.codeS

theorem x25519_code_no_wrap {c : X25519.Ctx} (hv : X25519.Valid c) :
    (x25519Params c).base.toNat + Release.bytes.length ≤ 2 ^ 32 := by
  rw [Release.bytes_length]
  exact hv.codeS.1

theorem x25519_base4 {c : X25519.Ctx} (hv : X25519.Valid c) :
    (x25519Params c).base.toNat % 4 = 0 := hv.base4

theorem x25519_base2 {c : X25519.Ctx} (hv : X25519.Valid c) :
    (x25519Params c).base.toNat % 2 = 0 := by
  have := hv.base4
  show c.base.toNat % 2 = 0
  omega

theorem x25519_code {c : X25519.Ctx} (hv : X25519.Valid c) :
    M0Crypto.Thumb.CodeAt c.m0 (x25519Params c).base Release.bytes := hv.code

/-! ## Return address -/

theorem x25519_lr {c : X25519.Ctx} {s : State} (h : X25519.Pre c s) :
    (x25519Params c).lr0.getLsbD 0 = true := h.thumb

/-- The certificate's stop address is the contract's return address. -/
theorem x25519_stop (c : X25519.Ctx) : (x25519Params c).lr0 &&& ~~~1#32 = c.ret := rfl

/-- The return address is not an address of the code. -/
theorem x25519_ret_not_code {c : X25519.Ctx} {s : State} (h : X25519.Pre c s) :
    ∀ i < Release.size, c.ret ≠ c.base + BitVec.ofNat 32 i :=
  Region.ne h.retOut

/-! ## Buffers against code and window

`out` is the only buffer the entry writes; these are the premises of
`bufferStoreOk_of_region` with `buf := c.out` and `len := 32`. `scalar` and `point` are only
read; their separation from the window is listed for the read-site lemma. -/

theorem x25519_out_code {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj (x25519Params c).base Release.bytes.length c.out 32 := by
  rw [Release.bytes_length]
  exact hv.codeO

theorem x25519_out_window {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj ((x25519Params c).sp0 - BitVec.ofNat 32 x25519Env.win.below)
      (x25519Env.win.below + x25519Env.win.above) c.out 32 := by
  rw [x25519_win_lo, x25519_win_bytes]
  exact disj_symm hv.outS

theorem x25519_scalar_window {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj ((x25519Params c).sp0 - BitVec.ofNat 32 x25519Env.win.below)
      (x25519Env.win.below + x25519Env.win.above) c.scalar 32 := by
  rw [x25519_win_lo, x25519_win_bytes]
  exact disj_symm hv.scalarS

theorem x25519_point_window {c : X25519.Ctx} (hv : X25519.Valid c) :
    Disj ((x25519Params c).sp0 - BitVec.ofNat 32 x25519Env.win.below)
      (x25519Env.win.below + x25519Env.win.above) c.point 32 := by
  rw [x25519_win_lo, x25519_win_bytes]
  exact disj_symm hv.pointS

/-! ## Entry -/

/-- Two valid calls with equal public inputs start in the certificate's entry relation. -/
theorem x25519_entry_related {c₁ c₂ : X25519.Ctx} {s₁ s₂ : State}
    (h₁ : X25519.Pre c₁ s₁) (h₂ : X25519.Pre c₂ s₂) (hpub : c₁.pub = c₂.pub) :
    LowEq (x25519Params c₁) Release.bytes Release.x25519 x25519Init s₁ s₂ := by
  simp only [X25519.Ctx.pub, Prod.mk.injEq] at hpub
  rcases hpub with ⟨hbase, hsp, hlr, hout, hsc, hpt⟩
  have e₁ := h₁.entry
  have e₂ := h₂.entry
  apply entryStateP_sound (np := 3) (by decide)
  · simp [M0Crypto.Armv6M.State.pc, e₁.regs, e₁.pc, x25519Params]
  · simp [M0Crypto.Armv6M.State.pc, e₁.regs, e₂.regs, e₁.pc, e₂.pc, hbase]
  · simp [x25519Params, e₁.regs, e₁.sp]
  · simp [e₁.regs, e₂.regs, e₁.sp, e₂.sp, hsp]
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [regAt, e₁.regs, e₂.regs, e₁.r0, e₂.r0, e₁.r1, e₂.r1, e₁.r2, e₂.r2, hout, hsc, hpt]
  · simp [regAt, x25519Params, e₁.regs]
  · simp [regAt, e₁.regs, e₂.regs, hlr]
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rfl
  · rw [e₁.mem]; exact h₁.valid.code
  · rw [e₂.mem]; show M0Crypto.Thumb.CodeAt c₂.m0 c₁.base Release.bytes
    rw [hbase]; exact h₂.valid.code

/-- Two valid calls with equal public inputs start in the checked reachable-pair relation. -/
theorem x25519_entry_reachable {c₁ c₂ : X25519.Ctx} {s₁ s₂ : State}
    (h₁ : X25519.Pre c₁ s₁) (h₂ : X25519.Pre c₂ s₂) (hpub : c₁.pub = c₂.pub) :
    CertAt x25519Env x25519Cert (x25519Params c₁) Release.bytes s₁ s₂ :=
  certAt_initial x25519_certOk x25519_indicesFailure_eq_none
    (x25519_entry_related h₁ h₂ hpub)

/-! ## Return state -/

/-- A returned call's SP lies in the certificate's stack window. -/
theorem x25519_result_stack_window {c : X25519.Ctx} {t : State} (h : X25519.Result c t) :
    TraceSpec.InStackWindow c.sp0 x25519Env.win.below (t.regs 13) :=
  restored_sp_in_stack_window h.sp _

end M0Crypto.Release.ConstantTime
