import M0Crypto.Release.Ed25519VerifyRun

/-!
# `m0c_ed25519_verify`'s body trace admits one trace

`VAd.bodyTr_uniq`: for any adapters `D`, the body's trace condition `D.bodyTr c m0` admits at most
one trace. The straight lines by `Prog.tr_uniq`, the block `b2` as a one-op program, the stitched
calls, the tests and the ends by `Tr.uniq_is`, `Tr.uniq_cat` and `Tr.uniq_cond`; each callee's
trace is a single list.
-/

namespace M0Crypto.Release.Ed25519VerifyProg

open M0Crypto.Armv6M (Mem)
open M0Crypto.Release
open M0Crypto.Release.Ed25519CallProg

section
open VAd
variable {Rs : Rels} {B : List (BitVec 8)} {BS : Nat} [CodeBytes B BS]

/-- **The body's trace condition admits one trace.** -/
theorem VAd.bodyTr_uniq (D : VAd Rs B BS) (c : Ctx) (m0 : Mem) : Tr.Uniq (D.bodyTr c m0) := by
  have ts : ∀ {o g cc T d Ψk Ψx}, Tr.Uniq Ψk → Tr.Uniq Ψx → Tr.Uniq (tstTr verifyGeo c o g cc T d Ψk Ψx) :=
    fun hk hx => Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cond hk (Tr.uniq_cat (Tr.uniq_is _) hx)))
  have xc : ∀ {o as e Tw Ψ}, Tr.Uniq Ψ → Tr.Uniq (xcallTr verifyGeo c o as e Tw Ψ) :=
    fun h => Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) h))
  have pt : ∀ {P o S Ψ}, Tr.Uniq Ψ → Tr.Uniq (Prog.tr vpS vbS verifyGeo (fun a => (D.ap a).T) c P o S Ψ [] []) :=
    fun h => Prog.tr_uniq _ _ _ h fun _ hx => absurd hx List.not_mem_nil
  have fl : Tr.Uniq (tFail c) := Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_is _)
  have ok : Tr.Uniq (tOk c) := Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_cat (Tr.uniq_is _) (Tr.uniq_is _))
  have m3 : Tr.Uniq (D.tM3 c m0) := pt (xc (ts (pt (xc (ts ok fl))) fl))
  have p3 : Tr.Uniq (D.tP3 c m0) := pt (xc (xc (xc m3)))
  have b2 : Tr.Uniq (D.tB2 c m0) :=
    Prog.tr_uniq (cE := vxS) (bE := vbS) (G := verifyGeo) (T := fun _ _ _ => []) (c := c) (.op b2 .nil) oB2 v3
      (J := []) (ts p3 fl) fun _ hx => absurd hx List.not_mem_nil
  exact pt (xc (ts (xc (ts (pt b2) fl)) fl))

end

end M0Crypto.Release.Ed25519VerifyProg
