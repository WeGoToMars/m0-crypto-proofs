import M0Crypto.Release.ConstantTime.ChaCha20ExactStoreSites
import M0Crypto.Release.ConstantTime.StmCertificate
import M0Crypto.Release.ConstantTime.ChaCha20Entry

/-! Checking that untracked single-register stores sit at output-store instruction offsets
in a certificate without declassified contexts. -/
namespace M0Crypto.Release.ConstantTime
open M0Crypto.Thumb

/-- First offset in a block's walk where an untracked store is not at an output-store
offset, or where the transfer function fails. -/
def walkOutputSiteFailure (env : Env) (ctx : Option Nat) : Nat → AbsState → List Instr → Option Nat
  | _, _, [] => none
  | off, st, i :: is =>
    if untrackedStore st i && !outputStoreOffset off then some off
    else
      match xfer env off ctx i st with
      | .error _ => some off
      | .ok out =>
        match out.succs with
        | [(_, next)] => walkOutputSiteFailure env ctx (off + i.size) next is
        | _ => walkOutputSiteFailure env ctx (off + i.size) st is

/-- First failing site of a certificate: the offset of its block and the failing offset. -/
def certOutputSiteFailure (env : Env) (cert : Cert) : Option (Nat × Nat) :=
  cert.findSome? fun b =>
    (walkOutputSiteFailure env b.ctx b.off b.st b.code).map fun off => (b.off, off)

/-- Boolean counterpart to `certOutputSiteFailure = none`. -/
def certOutputSiteCheck (env : Env) (cert : Cert) : Bool :=
  (certOutputSiteFailure env cert).isNone

theorem certOutputSiteFailure_eq_none_iff (env : Env) (cert : Cert) :
    certOutputSiteFailure env cert = none ↔ certOutputSiteCheck env cert = true := by
  unfold certOutputSiteCheck
  cases certOutputSiteFailure env cert <;> simp

theorem blockPoint_outputSiteFailure {env : Env} {b : Blk} {off : Nat} {st : AbsState}
    {code : List Instr} (hc : walkOutputSiteFailure env b.ctx b.off b.st b.code = none)
    (hp : BlockPoint env b off st code) : walkOutputSiteFailure env b.ctx off st code = none := by
  induction hp with
  | entry => exact hc
  | next _ hx hs ih =>
    simp only [walkOutputSiteFailure, hx, hs] at ih
    split at ih
    · cases ih
    · exact ih

/-- At a checked position, an untracked single-register store is at an output-store offset. -/
theorem certPoint_outputSite {env : Env} {cert : Cert} {b : Blk} {off : Nat} {st : AbsState}
    {i : Instr} {is : List Instr} (hc : certOutputSiteFailure env cert = none) (hm : b ∈ cert)
    (hp : BlockPoint env b off st (i :: is)) (hu : untrackedStore st i = true) :
    outputStoreOffset off = true := by
  have hb : walkOutputSiteFailure env b.ctx b.off b.st b.code = none := by
    unfold certOutputSiteFailure at hc
    have := List.findSome?_eq_none_iff.mp hc b hm
    cases h : walkOutputSiteFailure env b.ctx b.off b.st b.code with
    | none => rfl
    | some o => simp [h] at this
  have hw := blockPoint_outputSiteFailure hb hp
  simp only [walkOutputSiteFailure] at hw
  split at hw
  · cases hw
  · rename_i hn
    simp only [hu, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false', ite_eq_right_iff] at hn
    cases ho : outputStoreOffset off
    · simp [hu, ho] at hn
    · rfl

theorem chacha20_outputSiteCheck : certOutputSiteCheck chacha20Env chacha20Cert = true := by
  decide +kernel

theorem chacha20_outputSiteFailure_eq_none : certOutputSiteFailure chacha20Env chacha20Cert = none :=
  (certOutputSiteFailure_eq_none_iff chacha20Env chacha20Cert).mpr chacha20_outputSiteCheck

theorem chacha20_stmStack : certStmStack chacha20Env chacha20Cert = true := by
  decide +kernel

end M0Crypto.Release.ConstantTime
