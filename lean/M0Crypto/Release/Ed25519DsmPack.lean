import M0Crypto.Release.Ed25519DsmGood
import M0Crypto.Release.Ed25519MulBaseAd
import M0Crypto.Release.Ed25519FePow
import M0Crypto.Release.Ed25519WordAd

/-!
# `m0c_ge_dsm`'s adapter

`dsmAd b Rs` is `ge_dsm`'s adapter at a stitched site in build `b`. Its trace is the frame's
around `ΨD`, a function of the public registers and the 128 digit words (`xpD`). The input
premise is `dsmPre`: the digit widths `xpreD` follow from it by `verify_digits`, and under it the
outputs are `dsmSem b` of the inputs. The effect holds under `ppD`, the table bounds of the digits
read from the public words, which follow from `dsmPre` the same way. The callees' adapters are the
field operations', the copies' and `zero`'s; the block is `set_identity`'s.
-/

namespace M0Crypto.Release.Ed25519DsmPack

open M0Crypto.Armv6M (Word Reg LowReg State Mem)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Routine
open M0Crypto.Release.Footprint
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519DsmProg
open M0Crypto.Release.Ed25519DsmRun
open M0Crypto.Release.Ed25519DsmPass
open M0Crypto.Release.Ed25519DsmBody
open M0Crypto.Release.Ed25519DsmSem
open M0Crypto.Release.Ed25519DsmAd
open M0Crypto.Release.Ed25519DsmGood
open M0Crypto.Release.Ed25519DsmVal (dsV dsBV dig3 dig5)
open M0Crypto.Release.Ed25519DsmBlocks (sext_toInt digOf)
open M0Crypto.Release.Ed25519WnafAd (bytesOfW)
open M0Crypto.Release.Ed25519VerifyVal (verify_digits)
open M0Crypto.Release.Ed25519VerifyProg (vaS ioDsm)
open M0Crypto.Release.Ed25519 (Build)

/-! ## The callees' adapters -/

/-- The callees' adapters in build `b`. -/
noncomputable def dsAd (b : Build) (Rs : Rels) : ∀ a, AdE Rs (cb := b.codeBytes) (dsS a)
  | .f a => Ed25519MulBaseAd.mbAd b Rs (.f a)
  | .copy => Ed25519FePow.paAd b Rs .copyOut
  | .copy2 => Ed25519WordAd.copyAd2 b Rs
  | .copy3 => Ed25519WordAd.copyAd3 b Rs
  | .zero => Ed25519WordAd.zeroAd b Rs 4 Ed25519WordAd.zeroOk_34.2

theorem dsAd_sem (b : Build) (Rs : Rels) : ∀ a, @Ad.sem Rs b.bytes b.size b.codeBytes _ (dsAd b Rs a).ad = dsV a
  | .f a => funext fun vs => Ed25519MulBaseAd.mbAd_sem b Rs (.f a) vs
  | .copy => funext fun vs => Ed25519FePow.paAd_sem b Rs .copyOut vs
  | .copy2 | .copy3 | .zero => rfl

/-- The block's: `set_identity`. -/
def dsBd (Rs : Rels) : ∀ k, Bd Rs (dbS k)
  | .ident => Ed25519MulBaseAd.mbD Rs .ident

theorem dsBd_sem (Rs : Rels) : ∀ k, (dsBd Rs k).sem = dsBV k
  | .ident => Ed25519MulBaseAd.mbD_sem Rs .ident

/-! ## The frame's decided checks -/

theorem code_okW : ∀ b : Build, @CalleeP.codeOkW DS DB dq bszD b.bytes b.size b.codeBytes = true := by
  intro b; cases b <;> decide +kernel

/-- The effect's region check: the inputs cover the first reads, the outputs are within the footprint. -/
theorem eff_ok : effOk dq.s.io dq.fpE dq.iniE (dq.s.io.outs.filterMap outE) = true := by decide +kernel

theorem wo_fp : subR (dq.s.io.outs.filterMap outE) dq.fpE = true := by decide +kernel

/-! ## The call lemma and the adapter -/

/-- The callees' traces in build `b`. -/
noncomputable abbrev TD (b : Build) (Rs : Rels) : DS → Word → (Nat → Word) → List Event := letI := b.codeBytes; fun a => (dsAd b Rs a).ad.T

/-- **`ge_dsm`'s call lemma** in build `b`: the frame's trace around `ΨD`. -/
noncomputable def dsmTE (b : Build) (Rs : Rels) :=
  letI := b.codeBytes
  CalleeP.teW (cb := b.codeBytes) (Rs := Rs) (q := dq) (bsz := bszD) (Post := PostD b Rs) (xpre := xpreD)
    (pub := pubD) (Ψ := ΨD (TD b Rs)) (E := fun base p tr => dq.trW bszD base p (ΨD (TD b Rs) base p) tr)
    (CalleeP.okF_parts dq_facts.2.2.2) (code_okW b) (fun _ _ _ h => CalleeP.reg_pubX h)
    (fun base s e t g F hcR hat hrd => dsm_body b rfl (code_b b) (codeL_b b) (codeB_b b) (fun a => (dsAd b Rs a).ad)
      (dsBd Rs) (dsAd_sem b Rs) (dsBd_sem Rs) base s e t g F hcR hat hrd)
    (fun _ _ => ψD_uniq _ _ _) (fun _ _ => ψD_ex _ _ _) fun _ _ _ h => h

/-- **The effect** under `ppD`. -/
theorem dsm_eff (b : Build) (Rs : Rels) (base : Word) (p : Nat → Word) (tr : List Event) (hp : ppD p)
    (h : dq.trW bszD base p (ΨD (TD b Rs) base p) tr) : @CalleeS.Eff (vaS .dsm) p b.bytes b.size b.codeBytes base tr :=
  letI := b.codeBytes
  CalleeP.effW (cb := b.codeBytes) (q := dq) (s' := dq.s) (pp := ppD) (CalleeP.okF_parts dq_facts.2.2.2) (code_okW b)
    rfl rfl eff_ok wo_fp
    (fun base p hp sp0 n X0 fm hcode => dsm_gp (fun a => (dsAd b Rs a).ef) (code_b b) (codeL_b b) base p hp sp0 n X0 fm hcode)
    base p hp h

/-! ## The entry facts -/

/-- The digit arrays at entry. -/
theorem ins_b {Rs : Rels} {c : Ctx} {sp : Word} {st : State} {vs : List V} (hi : InsRel Rs c sp (vaS .dsm).io st vs) :
    ∃ l1 l2 xs, vs = .b l1 :: .b l2 :: xs ∧ bytesAt st.mem (st.regs 1) 256 = l1 ∧
      bytesAt st.mem (st.regs 2) 256 = l2 := by
  rcases vs with _ | ⟨_ | _ | _ | _ | _ | _, _ | ⟨_ | _ | _ | _ | _ | _, xs⟩⟩ <;>
    simp only [InsRel, All2, vaS, calleeAt, io_eq.1, Rel, In.kd, BitVec.add_zero, and_false,
      false_and] at hi
  exact ⟨_, _, xs, rfl, hi.1, hi.2.1⟩

/-- A digit from the public values, as an integer. -/
theorem dP_toInt (base : Word) (st : State) {o : Nat} {r : Reg}
    (hb : bytesOfW (fun j => pubD base st (o + j)) 64 = bytesAt st.mem (st.regs r) 256) {i : Nat} (hi : i < 256) :
    (dP (pubD base st) o i).toInt = digOf st.mem (st.regs r) i := by
  rw [dP, hb, Ed25519WnafAd.bytesAt_getD hi]
  exact sext_toInt _

/-- **`ge_dsm`'s adapter** in build `b`. -/
noncomputable def dsmAd (b : Build) (Rs : Rels) : AdX Rs (cb := b.codeBytes) (vaS .dsm) :=
  AdX.ofTE (dq.RW (PostD b Rs) xpreD) rfl rfl rfl xpD xpvD
    (fun _ _ st vs hi => by
      obtain ⟨l1, l2, xs, rfl, h1, h2⟩ := ins_b hi
      simp only [xpD, xpvD, Ed25519WnafAd.wordsAt_eq]
      rw [← h1, ← h2])
    (dsmTE b Rs) ppD (dsm_eff b Rs) dsmPre (dsmSem b)
    (fun _ _ _ st vs hg _ hi hv => by
      obtain ⟨s, h, hs, hh, xs, A, rfl, -⟩ := hv
      obtain ⟨l1, l2, xs', he, h1, h2⟩ := ins_b hi
      simp only [List.cons.injEq, V.b.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact ⟨⟨hg, fun _ hp => absurd hp List.not_mem_nil⟩, verify_digits hs hh h1 h2⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun c sp _ _ _ vs hv hi hpre hp => hp c sp vs hv hi hpre)
    (fun _ _ st vs _ _ hi hv => by
      obtain ⟨s, h, hs, hh, xs, A, rfl, -⟩ := hv
      obtain ⟨l1, l2, xs', he, h1, h2⟩ := ins_b hi
      simp only [List.cons.injEq, V.b.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      have hd := verify_digits hs hh h1 h2
      have pb := pub_bytes 0 st
      show ppD (pubD 0 st)
      intro i hi'
      simp only [Ed25519DsmLoop.kOf]
      rw [dP_toInt 0 st pb.2 hi', dP_toInt 0 st pb.1 hi']
      exact ⟨fun h0 => (dig3 (hd i hi').2 h0).2, fun h0 => (dig5 (hd i hi').1 h0).2⟩)

end M0Crypto.Release.Ed25519DsmPack
