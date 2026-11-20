import M0Crypto.Release.Ed25519GeCompressProg
import M0Crypto.Release.Ed25519GeProg

/-! The same compression bytes also accept the three projective coordinates
produced by double-scalar multiplication. -/

namespace M0Crypto.Release.Ed25519CompressP2

open M0Crypto.Armv6M (Mem State Word)
open M0Crypto.Thumb
open M0Crypto.Release
open M0Crypto.Release.Footprint (Has)
open M0Crypto.Release.Ed25519 (Build)
open M0Crypto.Release.Ed25519CallProg
open M0Crypto.Release.Ed25519GeCompressProg
open M0Crypto.Release.Ed25519GeProg (fI fI_nat fI_modP)
open M0Crypto.Release.Ed25519Encode (compressCode)
open M0Crypto.Release.Field25519Routines (feVal)
open M0Crypto.Spec.Ed25519 (encodeInt)
open M0Crypto.Artifacts.Ed25519Compact (ge_compress)

def io : Iface :=
  { ioCompress with
    ins := [(1,CX,.view .fe),(1,CY,.view .fe),(1,CZ,.view .fe)]
    rd := [⟨1,0,.k 96⟩] }

def cp2S : CalleeS := calleeAt ge_compress io [0,1]

def cp2Q : CalleeP CA CB :=
  { cpQ with s := cp2S, xr := [(0, ⟨.k 32, true, false, false⟩), (1, ⟨.k 96, false, true, true⟩)] }

theorem cp2_ok : cp2Q.ok caS cbS = true := by decide +kernel

open M0Crypto.Release.RoutinePieces in
theorem cp2_code (b : Build) : @CalleeP.codeOk _ _ caS cbS cp2Q b.bytes b.size b.codeBytes b.dataRanges = true := by
  simp only [CalleeP.codeOk, seqAt_eq_scan, piecesAt_eq_scan]
  cases b <;> decide +kernel

def cp2V : List V → List V
  | [.f x,.f y,.f z] => [.b (encodeInt (compressCode ⟨fI x,fI y,fI z,0⟩))]
  | _ => [.none]

private theorem out (c : Ctx) (m0 : Mem) :
    cp2Q.outVals (Prog.ev caS cbS cp2Q.geo cpV cbV c m0 cp2Q.P cp2Q.st0 fun _ => .none) =
      [.b (cpF c m0)] := rfl

set_option linter.unusedSimpArgs false in
theorem cp2_post {B : List (BitVec 8)} {BS : Nat} [cb : CodeBytes B BS] {Rs : Rels}
    {semA : CA → List V → List V} (hA : ∀ a vs, semA a vs = cpV a vs) (c : Ctx) (sp : Word) (st : State) (m : Mem)
    (r0 : Word) (vs : List V) (hi : InsRel Rs c sp cp2S.io st vs)
    (hp : cp2Q.post caS cbS Rs semA (fun b => (cbD Rs b).sem) st m r0) :
    OutsRel Rs c sp cp2S.io st m (cp2V vs) := by
  obtain ⟨_,base,m0,_,hm,ho⟩ := hp
  obtain rfl : semA = cpV := funext fun a => funext (hA a)
  have hB : (fun b => (cbD Rs b).sem) = cbV := funext fun b => by cases b <;> rfl
  rw [hB] at ho
  generalize hcc : cp2Q.ctx base (cp2Q.s.pub base st) = cc at ho hm
  have hptr : cc.ptr 1 = st.regs 1 := by
    rw [← hcc,CalleeP.ctx_ptr (by decide)]
    exact CalleeP.reg_pub (r := 1) (by decide)
  have hfe : ∀ o, o+32 ≤ 96 →
      feVal m0 (cc.ptr 1+BitVec.ofNat 32 o) = feVal st.mem (st.regs 1+BitVec.ofNat 32 o) := by
    intro o h
    rw [← hptr]
    apply Ed25519FeCanon.feVal_congr
    rintro y ⟨_,hr,i,hi,hy⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hi : i < 32 := hi
    exact hm 1 ⟨.k 96,false,true,true⟩ rfl rfl y ⟨⟨cc.ptr 1,96⟩,by simp [XInfo.rgns,XLen.v],
      o+i,by show o+i < 96; omega,by rw [hy,ofNat_add_assoc]⟩
  dsimp only at ho
  rw [out] at ho
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;>
    simp only [InsRel,All2,cp2S,calleeAt,io,and_false,false_and,and_true] at hi
  cases a <;> simp only [Rel,In.kd,and_false,false_and] at hi
  rename_i x
  cases b <;> simp only [Rel,In.kd,and_false,false_and] at hi
  rename_i y
  cases c <;> simp only [Rel,In.kd,and_false,false_and,BitVec.add_zero] at hi
  rename_i z
  simp only [OutsRel,All2,cp2Q,cp2S,io,ioCompress,io1,calleeAt,Iface.base,Kd.base,Rel,
    List.map,and_true,BitVec.add_zero] at ho
  simp only [OutsRel,All2,cp2S,io,ioCompress,io1,calleeAt,Rel,and_true,BitVec.add_zero,cp2V]
  rw [ho,cpF,hfe CX (by decide),hfe CY (by decide),hfe CZ (by decide),code_eq _ _ _ 0,
    ← fI_nat,← fI_nat,← fI_nat,fI_modP hi.1,fI_modP hi.2.1,fI_modP hi.2.2]
  rfl

/-- Projective compression uses the same verified subcalls and frame. -/
noncomputable def cp2Ad (b : Build) (Rs : Rels) : AdE Rs (cb := b.codeBytes) cp2S :=
  CalleeP.adE (cb := b.codeBytes) (q := cp2Q) (cE := caS) (bE := cbS) (cpAd b Rs) (cbD Rs)
    (CalleeP.ok_parts cp2_ok).choose_spec (cp2_code b) cp2V
    fun c sp st m r0 vs _ hi hp => cp2_post (cb := b.codeBytes) (cpAd_sem b Rs) c sp st m r0 vs hi hp

end M0Crypto.Release.Ed25519CompressP2
