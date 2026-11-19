import M0Crypto.Release.Ed25519ShaInit
import M0Crypto.Release.Ed25519ShaUpdate
import M0Crypto.Release.Ed25519ShaFinal
import M0Crypto.Release.Ed25519ScMuladdProg
import M0Crypto.Release.Ed25519MulBaseAd

/-!
# The callee adapters of a build

`callees b`: the seven callees of sign's call program in build `b`, at the relations `shaRels PtR`
(contexts by `ShaCtx`, points by `PtR`). Each adapter is its routine's own.
-/

namespace M0Crypto.Release.Ed25519CallProg

open M0Crypto.Release
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519GeCompressProg (PtR)

/-- The relations of the callees: SHA-512 contexts by `ShaCtx`, points by `PtR`. -/
def calleeRels : Rels := Ed25519ShaUpdate.shaRels PtR PtR.memEq

/-- The adapters other than `.init`. -/
noncomputable def calleeAd (b : Build) : ∀ a, a ≠ .init → @AdE calleeRels b.bytes b.size b.codeBytes (eaS a)
  | .init, h => absurd rfl h
  | .update n ℓ, _ => Ed25519ShaUpdate.updAd b calleeRels rfl n ℓ
  | .final n, _ => Ed25519ShaFinal.finAd b calleeRels rfl n
  | .reduce, _ => Ed25519ScReduceProg.redAd b calleeRels
  | .mulBase, _ => Ed25519MulBaseAd.mulBaseAd b calleeRels rfl
  | .compress, _ => Ed25519GeCompressProg.compressAd b calleeRels rfl
  | .muladd, _ => Ed25519ScMuladdProg.muladdAd b calleeRels

/-- **The callee adapters of build `b`.** -/
noncomputable def callees (b : Build) : Callees b :=
  Callees.ofInit b calleeRels (fun _ _ h => Ed25519ShaUpdate.ShaCtx.init h) (fun a h => (calleeAd b a h).ad)
    (fun a h => by cases a <;> first | exact absurd rfl h | rfl) fun a h => (calleeAd b a h).ef

end M0Crypto.Release.Ed25519CallProg
