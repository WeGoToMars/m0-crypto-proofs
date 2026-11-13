import M0Crypto.Release.ConstantTime.EntriesDefs
import M0Crypto.Release.ConstantTime.StackCertificates
import M0Crypto.Release.ConstantTime.IndexCertificates
import M0Crypto.Release.ConstantTime.SiteCheck
import M0Crypto.Release.ConstantTime.ReadBounds
import M0Crypto.Release.ConstantTime.CertGen
import M0Crypto.Release.ConstantTime.CertChunks
import M0Crypto.Release.X25519Sites

/-! # Certificate for `m0c_x25519`

The entry calls its three field routines from 47 sites. With `shareCalls` each routine is
analysed once for all its call sites (its saved return value lists every return offset), so
the certificate covers each instruction once: 3,462 positions in 73 blocks. Followed per call
site instead, the callees would be copied 47 times (about 46,000 positions, over the plan's
checking budget). `genFast` builds the certificate (the association lists of `gen` are
quadratic at this size). The generator is untrusted: the kernel checks the result with
`certOk` and the companion checks below.

The three register arguments (`out`, `scalar`, `point`) are public; nothing is passed on the
stack. The stack window is the call's 516 bytes below the entry `sp`. -/

namespace M0Crypto.Release.ConstantTime

open M0Crypto.Artifacts M0Crypto.Release

/-- Bytes of stack below the entry `sp` that a call uses: the entry's frame and the deepest
callee's. -/
def x25519StackBytes : Nat := 516

def x25519Env : Env := ⟨⟨x25519StackBytes, 0⟩, Release.size, none, [], true⟩

/-- Entry state: `r0` to `r2` public, no stack argument. -/
def x25519Init : AbsState := entryStateP 3 0

/-- Joins at one point before widening. The return lists of the field routines grow by one
offset per call site, so a block head in a routine is joined once per call site: widening must
wait for all of them (47 here), or it would turn the ascending chain of return lists into
a stack value that `pop pc` rejects. -/
def x25519WidenAt : Nat := 80

def x25519Cert : Cert :=
  ct_cert% genFast x25519Env Release.bytes Release.x25519 x25519Init 3000000 x25519WidenAt

/-! `certOk` is checked in chunks of `x25519Chunk` blocks (`CertChunks`): in one declaration
the kernel would hold about 10 GB; in chunks of 10 the file peaks near 3 GB. -/

def x25519Chunk : Nat := 10

theorem x25519_entryOk : certEntryOk Release.x25519 x25519Init x25519Cert = true := by
  decide +kernel

theorem x25519_blocks_0 :
    ((x25519Cert.drop (0 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_1 :
    ((x25519Cert.drop (1 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_2 :
    ((x25519Cert.drop (2 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_3 :
    ((x25519Cert.drop (3 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_4 :
    ((x25519Cert.drop (4 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_5 :
    ((x25519Cert.drop (5 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
theorem x25519_blocks_6 :
    ((x25519Cert.drop (6 * x25519Chunk)).take x25519Chunk).all
      (blkOk x25519Env Release.bytes x25519Cert) = true := by decide +kernel
/-- All remaining blocks, however many: a larger certificate only costs memory here. -/
theorem x25519_blocks_rest :
    (x25519Cert.drop (7 * x25519Chunk)).all (blkOk x25519Env Release.bytes x25519Cert) = true := by
  decide +kernel

theorem x25519_certOk :
    certOk x25519Env Release.bytes Release.x25519 x25519Init x25519Cert = true :=
  certOk_of_blocks x25519_entryOk <| all_of_chunks _ _ x25519Chunk 7
    (fun i hi => match i, hi with
      | 0, _ => x25519_blocks_0 | 1, _ => x25519_blocks_1 | 2, _ => x25519_blocks_2
      | 3, _ => x25519_blocks_3 | 4, _ => x25519_blocks_4 | 5, _ => x25519_blocks_5
      | 6, _ => x25519_blocks_6 | _ + 7, h => absurd h (by omega))
    x25519_blocks_rest

theorem x25519_indicesCheck : certIndicesCheck x25519Cert x25519Env = true := by decide +kernel

theorem x25519_indicesFailure_eq_none : certIndicesFailure x25519Cert x25519Env = none :=
  (certIndicesFailure_eq_none_iff x25519Cert x25519Env).mpr x25519_indicesCheck

theorem x25519_slotsCheck : certSlotsCheck x25519Env x25519Cert = true := by decide +kernel

theorem x25519_certAligned : certAligned x25519Cert = true := by decide +kernel

/-- Every untracked store is one of the entry's byte stores. -/
theorem x25519_sites : certSites x25519Env X25519Code.storeSites x25519Cert = true := by
  decide +kernel

/-- Every untracked load is one of the entry's byte loads. -/
theorem x25519_loadFailure :
    certLoadFailure (fun off => X25519Code.loadSites.contains off) x25519Env x25519Cert = none := by
  decide +kernel

end M0Crypto.Release.ConstantTime
