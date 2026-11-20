# m0-crypto proofs

Lean 4 proofs that the machine code of [m0-crypto](https://github.com/WeGoToMars/m0-crypto-lib) computes ChaCha20 and ChaCha20-Poly1305 as specified in [RFC 8439](https://www.rfc-editor.org/info/rfc8439/), X25519 as specified in [RFC 7748](https://www.rfc-editor.org/rfc/rfc7748), Ed25519 as specified in [RFC 8032](https://www.rfc-editor.org/rfc/rfc8032) and unkeyed BLAKE2s-256 as specified in [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693), and that its instruction and memory-address trace does not depend on secret data. The proofs are about the exact `.text` bytes of each release object, run in a Lean model of ARMv6-M. This repository is the `proofs/` submodule of the library and is not meant to be used on its own.

## Release assets

Each primitive of the library is its own independently released asset: one relocation-free object, built by the library's `tools/build_lib.sh`, with its own proofs and checks.

| Asset | Library object | `.text` | Lake workspace |
|---|---|---|---|
| ChaCha20, ChaCha20-Poly1305 | `m0crypto_chacha20poly1305.o` | 3,030 bytes, sha256 `b85f137f8356ea1d290578ce03616b3e00cff08aac7cc1104b3e9fdadfc990d3` | `assets/chacha20poly1305` |
| BLAKE2s-256 | `m0crypto_blake2s.o` | 4,748 bytes, sha256 `baf869bf5a30e81fc79956d2d61fde332555816d1cc0b0b0daede80a3dd4c68b` | `assets/blake2s` |
| X25519 | `m0crypto_x25519.o` | 9,722 bytes, sha256 `a378c6bba91e6946036815951e127f14bf08adbc2bdd80201eb61a05c6f6d419` | `assets/x25519` |
| Ed25519, compact build | `m0crypto_ed25519_compact.o` | 18,920 bytes, sha256 `301c66aa336269e2b6b3591c51b46965fa5251b26ff1c85be70097805b54246c` | `assets/ed25519` |
| Ed25519, fast build | `m0crypto_ed25519_fast.o` | 29,672 bytes, sha256 `f5344c1621c0e441e187c749166a1653d085e47e014117e55a9d14e9b60a5f70` | `assets/ed25519` |

The Lean sources in `lean/` are shared. Each asset's Lake workspace compiles them against that asset's own artifact, `assets/ASSET/artifact/M0Crypto/Artifacts/Release.lean`, and builds only the asset root `M0Crypto.Assets.*` and its imports. So `Artifacts.Release.bytes` in an asset's theorems is that asset's `.text`. The Ed25519 asset has two builds, `compact` and `fast`, with one artifact module each (`Artifacts/Ed25519Compact.lean`, `Ed25519Fast.lean`); its judgments take the build's bytes as a parameter, and its `Artifacts.Release` is empty. The X25519 and Ed25519 workspaces share the safegcd arithmetic and Thumb proofs. Each workspace proves that the linked inversion bytes match the shared routine and establishes the conditions of the call. X25519 also imports the shared `Field25519` field multiply and square proofs. Each workspace holds the asset's axiom audit (`Audit.lean`, which lists the claims) and the printed statements of its claims and of every trusted definition they reach (`statements.golden`).

## Check

From the library checkout (with submodules):

```sh
proofs/tools/check.sh                      # every asset
proofs/tools/check.sh x25519               # one asset
```

Needs Lean v4.35.0 (via `elan`), LLVM/LLD 23.1.4 and QEMU 11.1.3. Set `M0C_LIB` if the library is not the parent directory. For each selected asset, the script:

1. builds the asset and checks that its `.text` equals the asset's checked-in artifact.
2. builds the asset's proofs with `lake build` in its workspace, including executions of the artifact in the model against the specification.
3. checks that the model's decoder agrees with `llvm-objdump` on every instruction.
4. evaluates the Lean specification on the library's test vectors: RFC 8439, Wycheproof and pyca/cryptography for ChaCha20-Poly1305 (including ChaCha20 at the 2^32 counter boundary and AEAD inputs longer than 65,535 bytes); `hashlib` digests at 204 lengths for BLAKE2s (one-shot and streaming); RFC 7748 and Wycheproof for X25519. The specifications also carry `#guard` vectors (for BLAKE2s, `Spec/Blake2sVectors.lean`: RFC 7693 appendix B and `hashlib`).
5. rejects `sorry` and new axioms. The asset's `Audit.lean` lists its claims; every claim may depend only on `propext`, `Classical.choice` and `Quot.sound`. Its `statements.golden` locks the claim statements and every trusted definition they reach, as text and as a sha256 of their kernel terms.
6. runs the library's QEMU tests for the selected assets.
7. single-steps calls in QEMU that together execute every instruction a call can execute, and requires the model to have the same registers and flags after every instruction, and the same RAM at the return (for X25519, windows of one call, since a whole call is too long to single-step; for Ed25519, test programs for the five instruction forms it adds).

`tools/comparator.sh [ASSET...]` judges each asset root with the pinned toolchain's `lake comparator` against `assets/ASSET/challenge/Challenge.lean`, which states the claims over the statement files only: each claim must state the same term, reaching the same declarations, and use only the three axioms. `lake check` then replays every declaration the asset root reaches, Lean core included, in an empty kernel environment. It is not part of `check.sh`; the library's CI runs it whenever its workflow runs.

`tools/mutate_aead.py`, `tools/mutate_blake2s.py` and `tools/mutate_x25519.py` apply deliberate bugs to the assembly or the object and check that the tests, the model checks or (for BLAKE2s) the proofs detect each one. They are not part of `check.sh`; the library's CI runs them whenever its workflow runs. A Lean build catches a mutant only when Lean reports an error in a failing module; a killed worker or a timeout fails the run. They run each asset's executable release checks as a native program (the `release_check` target of the asset's lakefile); the proofs build runs the same checks in Lean's interpreter. CI requires all 20 AEAD mutants to be detected (19 by the tests or the executable checks, a tag comparison that exits at the first differing byte by the constant-time certificate), the BLAKE2s proofs to reject all 13 BLAKE2s mutants, and all 15 X25519 mutants to be detected (14 by the executable checks, including a branch to the next instruction that the decoder rejects, the timing mutant by the constant-time certificate). For development builds, release check sharding, and memory budgeting, see [docs/BUILD.md](docs/BUILD.md).

## Contents

- `lean/M0Crypto/Spec`: the specifications (RFC 8439, RFC 7748, RFC 7693) and their test vectors.
- `lean/M0Crypto/Thumb`: the ARMv6-M model of the release code (decoder and executor).
- `lean/M0Crypto/Armv6M`, `Proofs`, `fixtures/`, `link/`: a six-instruction model and proofs for two standalone ChaCha20 fragments (quarter round, double round).
- `lean/M0Crypto/Sym`: a symbolic executor used by some of the ChaCha20 proofs.
- `lean/M0Crypto/Artifacts`: the standalone ChaCha20 fragments. Each release asset's machine code is in `assets/ASSET/artifact` (generated by `tools/extract_release.py`).
- `lean/M0Crypto/Release`: the proofs about the release code.
- `lean/M0Crypto/Assets`: one root module per release asset.
- `assets/`: one Lake workspace per release asset (see above).
- `docs/`: reviewer guide ([REVIEW.md](docs/REVIEW.md)), build instructions ([BUILD.md](docs/BUILD.md)), naming conventions ([NAMING.md](docs/NAMING.md)), and the routine and call proof tooling ([ROUTINES.md](docs/ROUTINES.md)).

## Claims

Each asset's `Audit.lean` lists its claims: for each exported function a correctness, a constant-time, a read-bound, a stack-bound, a stack-discipline and an interrupted-call theorem, and three non-vacuity witnesses: a concrete call that satisfies the correctness precondition and is passed to the correctness theorem, two concrete calls that satisfy the hypothesis of the constant-time theorem and differ in a secret input, and a call with 256 bytes of handler room and a handler that writes them; then the asset's composition claims. Ed25519's sign has one more claim, `sign_correct_rfc`. Every claim of a function assumes the same hypothesis, a valid call (`Pre`), which includes the entry state, the buffer placement rules and a return address outside the code; the interrupted-call theorem also assumes the handler room. Internal routines (Poly1305 `init`/`blocks`/`finish`, BLAKE2s `compress`/`copy`, X25519 `fe_mul`/`fe_sqr`/`fe_mulc_add`, the Ed25519 field, group, scalar and SHA-512 routines) are local symbols, not claims: their proved contracts are used inside the claims of the functions that call them.

| Asset | Functions | Claims |
|---|---|---:|
| ChaCha20-Poly1305 | `m0c_chacha20_xor`, `m0c_chacha20poly1305_encrypt`, `m0c_chacha20poly1305_decrypt`; composition `Aead.rejected_writes` | 28 |
| X25519 | `m0c_x25519` | 9 |
| BLAKE2s-256 | `m0c_blake2s_init`, `m0c_blake2s_update`, `m0c_blake2s_final`; composition `Blake2s.hash_correct`, `Blake2s.hash_constant_time` and their witnesses | 31 |
| Ed25519 (compact and fast builds) | `m0c_ed25519_pubkey`, `m0c_ed25519_sign`, `m0c_ed25519_verify`: 19 claim theorems, each for both builds, and 9 non-vacuity witnesses | 28 |

### Preconditions (`Pre`, `APre`)

Every claim assumes a valid call (`Pre`, or `APre` for the AEAD): the entry state of an AAPCS32 call, SP aligned with the function's stack window (its stack bound, in the table below) under it, the library code 4-byte aligned, a Thumb return address outside that code, and buffers that do not overlap the stack window. The buffer rules are no stricter than the C headers' rules (they also allow, for example, read-only inputs inside the code), so every placement a header allows meets them. [docs/REVIEW.md](docs/REVIEW.md#35-contracts-and-statements) section 3.5 lists the exact rules for each function.

## Functional correctness

The functional theorems connect the release bytes to the specifications in `lean/M0Crypto/Spec`. Each says that every valid call returns, writes only the allowed memory, and restores SP and r4-r11.

- **ChaCha20** (`ChaCha20Xor.xor_correct`): output = RFC 8439 ChaCha20, and rejection of messages that would wrap the 32-bit block counter; after an accepted non-empty call r1-r3, r12 and the 140 frame bytes below the saved registers are zero, otherwise they keep their entry values; the 36 bytes above hold the caller's saved r4-r11 and LR.
- **ChaCha20-Poly1305** (`Aead.encrypt_correct`, `Aead.decrypt_correct`): ciphertext and tag = RFC 8439 §2.8; decryption checks the tag before it writes, and leaves `out` unchanged on failure; r1-r3, r12 and the 96 bytes `[sp0 - 136, sp0 - 40)` of the AEAD's own frame (Poly1305 context, one-time key, lengths and expected tag) are zero; the whole 320-byte stack window, callee frames included, is one function of only the entry registers, the nonce pointer, the window's entry bytes and, for decryption, the verdict. The Poly1305 arithmetic and the init → blocks → finish composition are proved as internal lemmas.
- **X25519** (`X25519.x25519_correct`): `out` = RFC 7748 `X25519(scalar, point)`, for any alignment and any overlap of the three buffers; r0 = 0 (`M0C_OK`); r0-r3 and r12 zero; the 480 stack bytes below the saved registers zero and the 36 above them the caller's saved r4-r11 and LR. There is no low-order-point check, as in RFC 7748 section 5.
- **BLAKE2s-256** (`Blake2s.Init.init_correct`, `Update.update_correct`, `Final.final_correct`): `init` puts the empty stream in the context; `update` absorbs its input into the stream the context holds; `final` writes the RFC 7693 digest of that stream; `update` and `final` return with r0-r3 zero, `final` also r12; the stack window, and r12 after `update`, are one function of only the entry registers, the number of pending bytes and the window's entry bytes; `init` returns with r0 = `c + 36`, r1 and r2 the last two IV words, r3 zero, r12 unchanged, and the 4 stack bytes the caller's LR. The composed `Blake2s.hash_correct` says that `init; update*; final` on one context, with any caller code between calls that leaves the 112 context bytes alone, returns and writes the BLAKE2s-256 digest of the concatenated inputs.

- **Ed25519** (`Ed25519.pubkey_correct`, `sign_correct`, `sign_correct_rfc`, `verify_correct`), for both builds and any alignment and overlap of the buffers: pubkey writes the RFC 8032 §5.1.5 public key of `seed` to `pk`; sign writes to `sig` the RFC 8032 §5.1.6 signature computed with `sk[32..64)` as the public key, which is the RFC 8032 signature when `sk[32..64)` is the public key of `sk[0..32)` (`sign_correct_rfc`); pubkey and sign return with r1-r3 and r12 zero, the stack bytes below the saved registers zero and the 36 above them the caller's saved r4-r11 and LR. Verify returns 0 exactly when R and `pk` decode as in RFC 8032 §5.1.3, S < L and the cofactorless [S]B = R + [k]A' holds with k = SHA-512(R ‖ pk ‖ m) reduced modulo L as in RFC 8032 §6, and -1 otherwise; it writes nothing outside its 1,764-byte stack window.

Clearing of working state is proved as each contract states it, as listed above: every function of the ChaCha20-Poly1305, X25519 and BLAKE2s assets, and Ed25519's pubkey and sign, fixes every byte of its stack window at return. Ed25519's verify takes only public inputs and clears nothing. The BLAKE2s context (chain value and up to 64 pending message bytes) is left to the caller to wipe. [docs/REVIEW.md](docs/REVIEW.md) lists the exact limits per asset.

The ARMv6-M model describes sequential, byte-addressed, ordinary memory. An interrupt handler is modelled by its effect alone: it restores every register and flag and preserves the call's buffers and every byte the call may read or write outside a given number of bytes below SP (`TraceSpec.Handlers`). Its decoder is compared with LLVM on every instruction of each object, and its execution with QEMU instruction by instruction as in step 7 above.

## Constant-time traces, read bounds and stack bounds

The trace, read and stack statements are Props in `lean/M0Crypto/Release/ChaCha20TraceSpec.lean`, `X25519TraceSpec.lean`, `Blake2sTraceSpec.lean` and `Ed25519TraceSpec.lean`, under the same hypothesis as the functional theorems:

| Function | Equal traces | Read bounds | Stack bound |
|---|---|---|---:|
| `m0c_chacha20_xor` | `ChaCha20Xor.xor_constant_time` | `ChaCha20Xor.xor_reads` | 176 |
| `m0c_chacha20poly1305_encrypt` | `Aead.encrypt_constant_time` | `Aead.encrypt_reads` | 320 |
| `m0c_chacha20poly1305_decrypt` | `Aead.decrypt_constant_time` | `Aead.decrypt_reads` | 320 |
| `m0c_x25519` | `X25519.x25519_constant_time` | `X25519.x25519_reads` | 516 |
| `m0c_blake2s_init` | `Blake2s.Init.init_constant_time` | `Blake2s.Init.init_reads` | 4 |
| `m0c_blake2s_update` | `Blake2s.Update.update_constant_time` | `Blake2s.Update.update_reads` | 160 |
| `m0c_blake2s_final` | `Blake2s.Final.final_constant_time` | `Blake2s.Final.final_reads` | 160 |
| `m0c_ed25519_pubkey` | `Ed25519.pubkey_constant_time` | `Ed25519.pubkey_reads` | 1,060 |
| `m0c_ed25519_sign` | `Ed25519.sign_constant_time` | `Ed25519.sign_reads` | 1,260 |
| `m0c_ed25519_verify` | `Ed25519.verify_constant_time` | `Ed25519.verify_reads` | 1,764 |

All names are in `M0Crypto.Release`; the stack theorems are the `*_stack` of the same namespaces. The Ed25519 theorems hold for both builds.

- **Equal traces.** Two valid calls that agree on the public inputs produce identical trace events (PC, instruction, data access addresses and widths). Public inputs: addresses, SP, return address and lengths; for ChaCha20 the counter; for decryption the verdict bit; for BLAKE2s `update` and `final` the number of bytes pending in the context, which is a function of the lengths absorbed. For Ed25519 verify, which is variable time, also the bytes of the signature, the message and the public key. Keys, nonces, messages, scalars, points and the hash state are secret. `Blake2s.hash_constant_time` extends this to a whole `init; update*; final` sequence.
- **Read bounds.** Every data read lies in the caller's inputs, the code or the function's stack window. Encryption also reads `out`, where its MAC reads the ciphertext. Decryption reads `out` only where `in`, the key or the nonce overlaps it.
- **Stack bounds.** At every step SP lies in `[sp0 - N, sp0]`, with N in bytes as in the table, including internal callees.
- **Stack discipline** (`*_stack_discipline`). In every step, each byte the call accesses among the N bytes below `sp0` lies at or above SP before or after the step, and each such byte it reads was written since SP last moved to or below it.
- **Interrupted calls** (`*_interrupted`). Take a valid call whose `K` bytes below the stack window hold none of its inputs, outputs or code, and handlers that may run before any of its instructions, each restoring every register and flag and preserving the call's buffers and every byte the call may read or write outside the `K` bytes below SP (including caller stack arguments for ChaCha20 and AEAD). The call returns with the events of the uninterrupted call, its registers and flags, and its memory on its buffers and every byte the call may read or write outside the window, and SP stays in the window. On ARMv6-M, hardware exception entry stores up to 36 bytes below the interrupted SP (`r0-r3`, `r12`, `LR`, `PC` and `xPSR`, and 4 bytes if needed to align SP to 8), so `K` is at least 36 bytes for each exception that can be active on the same stack at once (a nested exception stores another frame) plus whatever those handlers push. Clearing covers uninterrupted calls: the exception frame holds the call's registers at the interrupt.

Equal traces are a statement about the model. That equal traces take equal time on the chip is an assumption, tested by cycle measurements on one MSPM0L2228, not proved: the Cortex-M0+ core has no cache or branch prediction, and the MSPM0's flash prefetch and instruction and literal caches respond only to the addresses fetched, which the trace includes. Proofs use kernel-checked abstract interpretation certificates in `Release/ConstantTime/`. For the trusted base and how to review these theorems, see [docs/REVIEW.md](docs/REVIEW.md).

## License

MIT.
