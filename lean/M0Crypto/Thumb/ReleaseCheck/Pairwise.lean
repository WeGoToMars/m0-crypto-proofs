import M0Crypto.Thumb.ReleaseCheck.Cases

namespace M0Crypto.Thumb.ReleaseCheck
open M0Crypto.Spec.AEAD M0Crypto.Artifacts

/-! ## Pairwise constant-time checks -/

-- Pairwise ChaCha20 trace equality with different keys, nonces, inputs, caller registers:
#guard
  let o1 := callWithRegs Release.chacha20_xor [0x20002000, 0x20001000, 64, 0x20003000]
    [0x20003100, 1] [(0x20001000, gen 64 1), (0x20003000, gen 32 2), (0x20003100, gen 12 3)] sentinel
  let o2 := callWithRegs Release.chacha20_xor [0x20002000, 0x20001000, 64, 0x20003000]
    [0x20003100, 1] [(0x20001000, gen 64 10), (0x20003000, gen 32 20), (0x20003100, gen 12 30)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

-- Pairwise Encrypt trace equality with different keys, nonces, plaintexts, AAD, caller registers:
#guard
  let o1 := callWithRegs Release.chacha20poly1305_encrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, gen 32 1), (0x20003300, gen 16 2), (0x20003000, gen 32 3), (0x20003100, gen 12 4)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_encrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, gen 32 10), (0x20003300, gen 16 20), (0x20003000, gen 32 30), (0x20003100, gen 12 40)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

-- Pairwise Decrypt trace equality when both calls accept:
#guard
  let k1 := gen 32 1; let n1 := gen 12 2; let a1 := gen 16 3; let p1 := gen 32 4
  let (ct1, t1) := encrypt k1 n1 a1 p1
  let k2 := gen 32 10; let n2 := gen 12 20; let a2 := gen 16 30; let p2 := gen 32 40
  let (ct2, t2) := encrypt k2 n2 a2 p2
  let o1 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct1), (0x20003300, a1), (0x20003200, t1), (0x20003000, k1), (0x20003100, n1)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct2), (0x20003300, a2), (0x20003200, t2), (0x20003000, k2), (0x20003100, n2)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

-- Pairwise Decrypt trace equality when both calls reject:
#guard
  let k1 := gen 32 1; let n1 := gen 12 2; let a1 := gen 16 3; let p1 := gen 32 4
  let (ct1, t1) := encrypt k1 n1 a1 p1
  let badTag1 := t1.modify 0 (· ^^^ 1#8)
  let k2 := gen 32 10; let n2 := gen 12 20; let a2 := gen 16 30; let p2 := gen 32 40
  let (ct2, t2) := encrypt k2 n2 a2 p2
  let badTag2 := t2.modify 0 (· ^^^ 1#8)
  let o1 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct1), (0x20003300, a1), (0x20003200, badTag1), (0x20003000, k1), (0x20003100, n1)] sentinel
  let o2 := callWithRegs Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct2), (0x20003300, a2), (0x20003200, badTag2), (0x20003000, k2), (0x20003100, n2)] sentinel2
  match o1, o2 with
  | .ok r1, .ok r2 => r1.trace == r2.trace
  | _, _ => false

-- Decryptions with different verdicts take different traces.
-- This documents why the declassification is needed and that it is the only one:
#guard
  let k := gen 32 1; let n := gen 12 2; let a := gen 16 3; let p := gen 32 4
  let (ct, tag) := encrypt k n a p
  let badTag := tag.modify 0 (· ^^^ 1#8)
  let oAccept := call Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct), (0x20003300, a), (0x20003200, tag), (0x20003000, k), (0x20003100, n)]
  let oReject := call Release.chacha20poly1305_decrypt [0x20002000, 0x20003200, 0x20001000, 32]
    [0x20003300, 16, 0x20003000, 0x20003100]
    [(0x20001000, ct), (0x20003300, a), (0x20003200, badTag), (0x20003000, k), (0x20003100, n)]
  match oAccept, oReject with
  | .ok rA, .ok rR => rA.trace != rR.trace
  | _, _ => false

end M0Crypto.Thumb.ReleaseCheck
