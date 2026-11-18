# Reviewing the m0-crypto proofs: ChaCha20-Poly1305, X25519, BLAKE2s and the ARMv6-M model

This guide lists exactly which parts of the Lean code a person has to read to trust the proofs of ChaCha20, Poly1305, the ChaCha20-Poly1305 AEAD, X25519 and BLAKE2s, which document each part must be checked against, and how to keep that true as the proofs change. It assumes no background in formal verification.

**Scope.** This guide describes the proofs of library 0.3.1, three release assets:

| Asset | Object | `.text` | sha256 | Sections |
|---|---|---:|---|---|
| ChaCha20, ChaCha20-Poly1305 | `m0crypto_chacha20poly1305.o` | 3,030 bytes | `b85f137f8356ea1d290578ce03616b3e00cff08aac7cc1104b3e9fdadfc990d3` | 2 to 8 |
| X25519 | `m0crypto_x25519.o` | 7,022 bytes | `bb9c315f5a91a6fb35f81859c1c7562a8e084efef1bddfef2ef949dbd37fec94` | 9 |
| BLAKE2s-256 | `m0crypto_blake2s.o` | 4,748 bytes | `baf869bf5a30e81fc79956d2d61fde332555816d1cc0b0b0daede80a3dd4c68b` | 10 |

The sizes and hashes are those in the header of each asset's `assets/ASSET/artifact/M0Crypto/Artifacts/Release.lean`. The ChaCha20-Poly1305 bytes are those of 0.2.0. The declaration and line counts in sections 3, 9.2 and 10.2 are the output of [`tools/trusted_defs.lean`](../tools/trusted_defs.lean), which computes them from the theorem statements themselves (section 6).

**Release assets.** The three assets are released and verified separately. Each is a relocation-free object with its own Lake workspace `assets/ASSET`, which compiles the shared sources in `lean/` against that asset's artifact file and holds its `Audit.lean` (its claims) and `statements.golden`. In an asset's theorems, `Artifacts.Release` (and its abbreviation `B`) is that asset's `.text`. Sections 2 to 8 cover the ChaCha20-Poly1305 asset and the parts every asset shares: the machine model and decoder (3.1, 3.2), the artifact tooling (3.3), the shared statement vocabulary (3.5), the trusted tools (4), the assumptions (5) and the review habits (6). Section 9 covers what X25519 adds, section 10 what BLAKE2s adds.

## 1. What a proof gives you, and what it does not

A Lean theorem has two parts: a **statement** (what is claimed) and a **proof** (why it holds). Lean's kernel checks every proof mechanically, so you never need to read a proof to know it is valid. That is the whole point: of about 80,000 lines of Lean in `lean/`, the ChaCha20-Poly1305 asset trusts 1,042 hand-written lines in 12 files. 941 of them need a careful human reading. The other 101 are the instruction decoding functions, which are compared with LLVM on every instruction of the code instead (section 3.2). The X25519 and BLAKE2s assets share the model, the decoder and the shared vocabulary, and add their own specification and statement files (sections 9.2 and 10.2).

What you *do* have to read is the statement, and every definition the statement mentions, recursively. Together these are the **trusted base**. If a definition in the trusted base is wrong, the theorem can be proved and still say something other than what you think.

A fully checked proof can still mislead in six ways. Each has a defence in this repository:

| # | Failure | Example | Defence | Where |
|---|---|---|---|---|
| 1 | The **specification** is wrong | A wrong index in a diagonal round of `Spec/ChaCha20.lean`. The code is "proved" equal to a wrong cipher. | Read the spec against the RFC; the spec is run on RFC, Wycheproof and pyca/cryptography vectors. | 3.4 |
| 2 | The **machine model** is wrong | `adcs` computes the carry incorrectly. Proofs about the model then say nothing about the chip. | Read the model against the ARM manual; decoder compared with LLVM; model compared with QEMU after every instruction. | 3.1, 3.2 |
| 3 | The **statement is weaker than you think** | A precondition no real call can satisfy (the theorem is then *vacuous*: true but useless); a secret listed as public; a read region that allows everything. | Read every contract and statement; non-vacuity witnesses. | 3.5, 6 |
| 4 | The **proved bytes are not the shipped bytes** | The library is rebuilt after a change, but the proofs still refer to the old binary. | `check.sh` step 2b rebuilds the library, regenerates the artifact file from it and requires it to equal the checked-in one. | 3.3, 4 |
| 5 | The **proof is incomplete** | `sorry`, a new `axiom`, or `native_decide` (trusts compiled code instead of the kernel). | Source scan (step 5) and axiom audit (step 6) in `check.sh`, with `Audit.lean`. | 4 |
| 6 | **Assumptions outside the model** | A handler that changes a byte the call uses outside the modelled room, a core whose timing depends on data, power analysis. | Stated in the README; tested on hardware, never proved. | 5 |

The rest of the Lean code (proofs, tactics, helper lemmas and the constant-time certificate checker in `Release/ConstantTime/`) needs no review for correctness: it is checked by the kernel against the statements.

## 2. Top-level theorems

These are the roots from which the trusted base is computed. A reviewer reads each statement once, in full, and checks that it says what the release notes claim.

| Theorem | File | Claim |
|---|---|---|
| `ChaCha20Xor.xor_correct : Correct` | [`ChaCha20Xor.lean`](../lean/M0Crypto/Release/ChaCha20Xor.lean) | ChaCha20 output = RFC 8439; every stack byte, r1-r3 and r12 fixed at return |
| `Aead.encrypt_correct : EncryptCorrect` | [`AeadEncrypt.lean`](../lean/M0Crypto/Release/AeadEncrypt.lean) | AEAD encryption = RFC 8439 §2.8; r12 zero; the 320 stack bytes one function of public values |
| `Aead.decrypt_correct : DecryptCorrect` | [`AeadDecrypt.lean`](../lean/M0Crypto/Release/AeadDecrypt.lean) | Checked decryption; `out` untouched on failure; r12 and the stack as for encryption, also of the verdict |
| `ChaCha20Xor.xor_constant_time` | [`ChaCha20XorConstantTime.lean`](../lean/M0Crypto/Release/ChaCha20XorConstantTime.lean) | Trace depends only on public inputs |
| `ChaCha20Xor.xor_reads` | [`ChaCha20XorReads.lean`](../lean/M0Crypto/Release/ChaCha20XorReads.lean) | Reads stay in allowed regions |
| `ChaCha20Xor.xor_stack` | [`ChaCha20XorStack.lean`](../lean/M0Crypto/Release/ChaCha20XorStack.lean) | SP within 176 bytes of entry |
| `Aead.encrypt_constant_time`, `_reads`, `_stack` | [`AeadEncryptConstantTime.lean`](../lean/M0Crypto/Release/AeadEncryptConstantTime.lean), [`AeadReads.lean`](../lean/M0Crypto/Release/AeadReads.lean), [`AeadEncryptStack.lean`](../lean/M0Crypto/Release/AeadEncryptStack.lean) | Same, encryption (320 bytes) |
| `Aead.decrypt_constant_time`, `_reads`, `_stack` | [`AeadDecryptConstantTime.lean`](../lean/M0Crypto/Release/AeadDecryptConstantTime.lean), [`AeadReads.lean`](../lean/M0Crypto/Release/AeadReads.lean), [`AeadDecryptStack.lean`](../lean/M0Crypto/Release/AeadDecryptStack.lean) | Same, decryption (320 bytes; the verdict bit is public) |
| `ChaCha20Xor.xor_stack_discipline`, `_interrupted`; `Aead.encrypt_…`, `Aead.decrypt_…` | [`ChaCha20XorDiscipline.lean`](../lean/M0Crypto/Release/ChaCha20XorDiscipline.lean), [`AeadDiscipline.lean`](../lean/M0Crypto/Release/AeadDiscipline.lean) | `StackDiscipline` and `InterruptedCall` (section 3.5) |

All eighteen are in `assets/chacha20poly1305/Audit.lean`, with the composition claim `Aead.rejected_writes` and the nine non-vacuity witnesses (28 claims), so their axioms are checked. The X25519 claims (section 9.1) are in `assets/x25519/Audit.lean`, the BLAKE2s claims (section 10.1) in `assets/blake2s/Audit.lean`.

The correctness statements are Props: `Correct` in [`ChaCha20Contract.lean`](../lean/M0Crypto/Release/ChaCha20Contract.lean), `EncryptCorrect`, `DecryptCorrect` and `RejectedWrites` in [`AeadContract.lean`](../lean/M0Crypto/Release/AeadContract.lean). The fifteen trace, read and stack statements are written once, as Props, in [`ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean) (shared vocabulary in [`TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean)); those theorems only say `: TraceSpec.X`.

All six theorems about one function assume the same thing, a valid call: `ChaCha20Xor.Pre c s` for ChaCha20, and `Aead.APre c off s` for the two AEAD functions (`off` selects encryption or decryption).

**What the golden file locks.** Each asset's `assets/ASSET/Audit.lean` lists its claims, and `assets/ASSET/statements.golden` holds the printed statement of every claim, then the printed body of every trusted definition those statements reach (`tools/trusted_defs.lean`, `printTrusted`): the machine model and decoder, the contracts (`Pre`, `Valid`, `AValid`, `ABuf`, `pub`, `Result`, the read regions), the `TraceSpec` Props and the specification. Each is followed by a `sha256` line: the hash of its kernel terms (`printFingerprint`: type, value or constructors, and the generated helpers it uses, names and literals in full), so terms that print alike still differ. A recursive definition compiles to a term that names only generated helpers, so for it the file also prints its unfolding theorem `f.eq_def`, which states the body as written; the tool stops with an error if there is none. `check.sh` fails if any of them changes. The artifact bytes are not printed; step 2b pins them. What the file cannot show is whether a changed definition still means what its reference says; that is the review of section 3.

## 3. What to review, in order

| Order | Part | Files | Hand-written lines | Main reference |
|---|---|---:|---:|---|
| 1 | [Machine model](#31-machine-model) | 4 | 289 | ARMv6-M Architecture Reference Manual |
| 2 | [Decoder](#32-decoder) | 1 | 66 to read, 101 cross-checked | `Instr.exec`; `llvm-objdump` |
| 3 | [Artifact](#33-artifact) | 1 | generated (196) | the build; review the generator instead |
| 4 | [Specifications](#34-specifications) | 2 | 117 | RFC 8439 |
| 5 | [Contracts and statements](#35-contracts-and-statements) | 5 | 469 | public headers, AAPCS, README claims |

`tools/trusted_defs.sh ASSET` (section 6) prints the trusted declarations of each file with their line ranges. The counts here are its output; they include doc comments. For each part, read every listed declaration with its doc comment and compare it with the reference; the lists below say what to look for. If you disagree, the finding is a **specification or model bug**: report it, do not patch the proofs around it.

### 3.1 Machine model

The model is what "the code runs on a Cortex-M0+" means inside Lean. Every theorem relies on it, and nothing else checks it against hardware, so it deserves the most careful reading.

**Check against:** *ARMv6-M Architecture Reference Manual* (Arm DDI 0419), mainly §A2.2 (`AddWithCarry`, `LSL_C`, `LSR_C`, `ROR_C` pseudocode), §A2.3 (`BXWritePC`, for `pop {..., pc}`), §A3 (alignment, endianness), §A6.3 (condition codes), §A6.4 (shifts applied to a register: `DecodeImmShift`, `Shift_C`) and the §A6.7 page of each instruction. The module headers of [`Thumb/Exec.lean`](../lean/M0Crypto/Thumb/Exec.lean) and [`Armv6M/State.lean`](../lean/M0Crypto/Armv6M/State.lean) state the scope; read them first.

- For every instruction in `Instr.exec` (94 lines, the core of the model): result value, flags written (and flags *not* written: `muls` sets only N and Z), destination and writeback registers, as on its A6.7 page.
- Immediate scaling, which happens here and not in the decoder: `imm5 × width` for `ldr`/`ldrh`/`ldrb` and their stores, `imm8 × 4` for SP-relative and literal forms, `imm7 × 4` for `add sp`/`sub sp`. The one exception is `bl`, whose offset the decoder delivers already scaled.
- `Instr.accesses` and `Instr.exec` compute each address separately. The trace records the first; the memory changes by the second. Two proved lemmas tie them together. Read their statements instead of comparing the addresses: `exec_mem_other` ([`Thumb/Program.lean`](../lean/M0Crypto/Thumb/Program.lean)), an instruction changes memory only at the bytes of its write accesses, and `exec_reads_only` ([`Thumb/ExecReads.lean`](../lean/M0Crypto/Thumb/ExecReads.lean)), its result depends on memory only at the bytes of its read accesses. So no byte an instruction uses is missing from the trace.
- The lemmas do not show the converse, that the trace records no more than the instruction uses. Check in `Instr.accesses` that each access has the instruction's size: 1, 2 or 4 bytes, and one 4-byte access per register for `push`, `pop`, `ldm` and `stm`. The alignment fault in `step` uses the same sizes. With the right size, a wrong address or direction would contradict the lemmas.
- PC reads as instruction address + 4; literal loads use `Align(PC + 4, 4)`.
- Branch targets: `b`, `bcond`, `bl` add a sign-extended, halfword-scaled offset to PC + 4.
- `bl` writes LR = return address | 1; `pop {pc}` faults if bit 0 of the loaded value is clear.
- Carry on subtraction is NOT borrow (ARM convention). This includes `sbcs`, which computes `Rdn + NOT(Rm) + C`, so C = 0 on entry subtracts one more. `addWithCarry` transcribes the manual's pseudocode: carry = unsigned overflow, V = signed overflow. `cmp` is `addFlags` with `write := false`: only the flags change.
- Shifts: `lslC` with n = 0 is `movs Rd, Rm` (31 sites in the code), value and carry unchanged; `lsrs #0` encodes a shift by 32; `rorC` by 0 leaves value and carry, by a non-zero multiple of 32 leaves the value and sets carry = bit 31.
- `condPassed`: each of the 14 conditions of the A6.3 table, especially HI (C ∧ ¬Z), LS, GE (N = V), GT, LT, LE.
- Memory is little-endian (`read32`, `write32`: the byte at `a` is bits 7:0, and a write changes its four bytes only); unaligned accesses fault (ARMv6-M has no unaligned access). The model has no `ldrsh`/`ldrsb`; the code uses neither, or the listing comparison of section 3.2 would fail.
- `Event` contains everything the constant-time claim should observe: PC, instruction, and the address, width and kind of every access. If something the hardware leaks is not in it, the proofs say nothing about it.
- `runUntil` runs until PC is the return address and records every executed instruction in the trace. A `Fault` stops the run; the theorems show the code returns without one, so faults cannot be hidden.
- Known scope limits are acceptable: `State` is r0-r15, N, Z, C, V and byte-addressed memory (no EPSR, IPSR or PRIMASK; check nothing the code depends on is missing), ordinary RAM, one thread. `step` has no exceptions; an interrupt handler is modelled separately by its effect (`TraceSpec.Handlers`, section 3.5).

**Second check: QEMU.** `check.sh` step 7b ([`tools/qemu_steps.py`](../tools/qemu_steps.py)) single-steps calls of the test images in QEMU and runs the model from the same entry state: calls 1, 2, 3, 5, …, 987 of each function, then every further call that executes an instruction those did not. These 55 calls (including direct calls of the internal `poly1305_blocks`, whose zero-block branch only a direct call reaches) execute exactly the 1,455 instructions a call can execute. The step derives that set from the object: every instruction `llvm-objdump` lists except the four alignment fillers before a literal pool or a function. After each instruction r0-r15 and the N, Z, C, V flags must be equal, and at each return the whole RAM must be equal. This compares the decoder and `Instr.exec` with an independent ARMv6-M implementation, including the flags the code never reads and the proofs therefore cannot see. Know its limits:

- It covers the instructions on the values that occur. A model error that needs a particular operand is found only if a traced call produces it. Reading `Instr.exec` is still required.
- Loads are checked through the registers they fill and stores through the final RAM. `Instr.accesses`, the addresses the trace records, is not compared with QEMU; it is tied to `Instr.exec` by the two lemmas of the list above.
- QEMU is another implementation, not the chip.

The two models handle code differently. The early fragment model keeps code in a separate immutable region. The release model in `Thumb/Exec.lean` fetches code from the same memory as data, and its contracts require that no write reaches the code bytes. The release theorems use the release model. (Some proof files and doc comments say "Harvard run": that is an intermediate proof device. The theorems are stated on `runUntil`, the single-memory run.)

| File | Trusted declarations | Lines |
|---|---|---:|
| [`Armv6M/State.lean`](../lean/M0Crypto/Armv6M/State.lean) | 9 | 21 |
| [`Armv6M/Memory.lean`](../lean/M0Crypto/Armv6M/Memory.lean) | 4: `Mem`, `read32`, `write32`, `slot` | 11 |
| [`Armv6M/Step.lean`](../lean/M0Crypto/Armv6M/Step.lean) | 2: `addWithCarry`, `rorC` | 15 |
| [`Thumb/Exec.lean`](../lean/M0Crypto/Thumb/Exec.lean) | 29 | 242 |

The rest of `Armv6M/Memory.lean` and `Armv6M/Step.lean` belongs to the fragment model and to proofs. In `Thumb/Exec.lean` everything above the closing "Helper checks" examples is trusted.

### 3.2 Decoder

[`Thumb/Decode.lean`](../lean/M0Crypto/Thumb/Decode.lean) has two parts, and they are reviewed differently.

**The instruction set: read it.** `Instr` (47 lines, with the width of every field), `DpOp`, `MemOp` with `width` and `isLoad`, and `Instr.size` (4 bytes for `bl`, 2 for everything else) are what `Instr.exec` is defined over: 66 lines. Read them together with section 3.1.

**The decoding functions: cross-checked, not read.** These turn bytes into an `Instr`: `decode`, `decode16`, `decodeBL`, `decodeDp`, `memOpOfRegForm` and three bit helpers, 101 lines. `check.sh` step 4b decodes every instruction of the release code with them, prints the result with `render` in [`Thumb/Listing.lean`](../lean/M0Crypto/Thumb/Listing.lean), and requires the text to equal `llvm-objdump`'s at every instruction offset (1,459 in the ChaCha20-Poly1305 asset; the step runs on each asset's object). `render` prints every field of every `Instr` constructor: register names, scaled immediates, branch targets, literal addresses. So a decoding that differs from LLVM's in any field, at any instruction of the code, fails the check. A wrong line of the decoder that affects no instruction of the code is harmless, because the theorems are about this code only.

What this argument rests on, and what a reviewer checks instead of the 101 lines:

- `render` and its helpers (67 lines) print each field of each constructor, in the role `Instr.exec` gives it. Read the two side by side: `render` has its own copy of the immediate scaling and of the branch-target arithmetic, and the comparison validates the decoder only as far as the two agree. This includes the `bl` offset, which the decoder delivers already scaled and both add as is.
- No two instructions that `exec` treats differently print alike. `condName` prints each of the 16 conditions as LLVM's printer does, including `al` (14) and `<und>` (15), which the decoder never produces.
- The comparison covers every offset `llvm-objdump` lists, which is every instruction boundary: two `#guard`s in `Listing.lean` require the model's sweep to tile each code range exactly and the code and data ranges to cover the artifact. It does not cover an offset inside a `bl` or inside a literal pool. Execution never gets there if every jump lands on a listed offset. Step 4b requires that of every direct branch (`b`, conditional `b`, `bl`) and of the instruction after every `bl`, where its callee returns. In the ChaCha20-Poly1305 asset there are 55 direct branches, and the only other jumps are six `pop {..., pc}`, which return to the instruction after a `bl` or to the caller. In the `llvm-objdump` listings of the other objects: X25519 has 59 direct branches and four `pop {..., pc}`, BLAKE2s 38 and five, and neither has another instruction that writes PC.
- `llvm-objdump` is the independent decoder and is trusted as such, together with [`tools/check_listing.py`](../tools/check_listing.py), which normalises both texts (for branches it keeps the target address and drops the symbol name).

**Check against:** `Instr.exec` (section 3.1) for the instruction set and for `render`. The encoding tables of DDI 0419 §A5.2 and the BL page in §A6.7 are needed only if you choose to read the decoding functions as well.

### 3.3 Artifact

[`Artifacts/Release.lean`](../assets/chacha20poly1305/artifact/M0Crypto/Artifacts/Release.lean) holds the asset's release `.text` as a byte list plus the function offsets. It is generated, so do not review the bytes. Review instead:

- [`tools/extract_release.py`](../tools/extract_release.py): it copies `.text` and the symbol offsets from the built object without changing them.
- [`tools/check.sh`](../tools/check.sh) step 2b: the library is rebuilt from source, the artifact file is regenerated in memory from the built object and must equal the checked-in file (bytes, offsets and sha256).
- The size and sha256 in the file's header are the ones the library's CHANGELOG and README state for the release. Nothing checks this mechanically: step 2b compares the file with a fresh build, not with a recorded value. (`build/lib/MANIFEST.txt` is written by that same build, so it always agrees and proves nothing here.) Any change of the artifact does show up as a diff of this checked-in file.

### 3.4 Specifications

The specifications are the answer key. They must be readable without any knowledge of the assembly or the model: they import nothing from `Thumb/` or `Release/`. Check that this stays true.

**Check against:** [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439) (§2.1 quarter round, §2.2 quarter round on the state, §2.3 block, §2.4 encryption, §2.5 Poly1305, §2.6 key generation, §2.8 AEAD).

- Each definition against its RFC section, in the RFC's own order.
- Constants digit by digit: "expand 32-byte k", the clamp mask, `2^130 − 5`.
- The test vectors are copied from the RFC, not produced by this spec. They are in [`Spec/ChaCha20Vectors.lean`](../lean/M0Crypto/Spec/ChaCha20Vectors.lean) (§2.1.1 as a kernel-checked theorem, §2.3.2 as a `#guard`) and at the end of [`Spec/Aead.lean`](../lean/M0Crypto/Spec/Aead.lean) (§2.4.2, §2.5.2, §2.8.2 as `#guard`s). A `#guard` is a compiled evaluation: a test, not a kernel proof.
- Anything that is not in the RFC is a design choice and must match the header: the ChaCha20 counter-overflow rule (`counterOk`).

`check.sh` step 4c ([`tools/spec_vectors.py`](../tools/spec_vectors.py)) also runs the specification on the vectors the library itself is tested with ([`../tests/aead_vectors.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/aead_vectors.h)): RFC 8439 §2.8.2, 316 Wycheproof vectors and 46 random ones from pyca/cryptography for the AEAD (303 that must encrypt and decrypt exactly, 60 that must be rejected), and 76 Poly1305 vectors. These come from independent implementations and include empty messages, empty AAD and lengths around the 16- and 64-byte block boundaries. From [`../tests/chacha20_vectors.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/chacha20_vectors.h) (pyca/cryptography) it also runs three AEAD vectors whose AAD, message or both are longer than 65,535 bytes (up to 131,075), so the third byte of both length fields in `macData` is non-zero; their tag authenticates the ciphertext and both lengths. And 13 ChaCha20 calls that start at counters from 2 to 2^32 − 1: `counterOk` must accept those that end exactly at block 2^32 − 1 and reject those one block longer or of 2^32 − 1 bytes, and the accepted ones must give pyca's output. The library's QEMU test runs the same ChaCha20 vectors on the machine code.

Vectors are a second check, but they do not replace reading: a spec bug on a path the vectors do not exercise passes all of them.

**[`Spec/ChaCha20.lean`](../lean/M0Crypto/Spec/ChaCha20.lean)** (15 declarations, 68 lines):

- `quarterRound`, §2.1: a += b; d ^= a; d <<<= 16; c += d; b ^= c; b <<<= 12; then 8 and 7.
- `innerBlock`, §2.3: column rounds, then diagonal rounds. Check the diagonal index sets.
- `initState`, §2.3: constants, key in words 4-11, counter in word 12, nonce in words 13-15.
- `block`, §2.3: 20 rounds (10 double rounds), add the input state, serialize little-endian.

**[`Spec/Aead.lean`](../lean/M0Crypto/Spec/Aead.lean)** (15 declarations, 49 lines):

- `chacha20`, §2.4: keystream from the counter, XOR, last partial block truncated.
- `clamp`, `polyAcc`, `poly1305`, §2.5: r &= 0x0ffffffc0ffffffc0ffffffc0fffffff; each 16-byte block with a 0x01 byte appended (2^128 for a full block, 2^(8·len) for the last partial one), times r, mod p; tag = (acc + s) mod 2^128, little-endian.
- `polyKey`, §2.6: the first 32 bytes of the ChaCha20 block with counter 0.
- `macData`, `encrypt`, `decrypt`, §2.8: AAD ‖ pad16 ‖ ciphertext ‖ pad16 ‖ le64(len AAD) ‖ le64(len ciphertext); encryption starts at counter 1; the tag is compared before plaintext is released. Check what `decrypt` returns on failure.

### 3.5 Contracts and statements

Contracts say *when* a theorem applies (preconditions) and *what* it promises (postconditions). This is where a statement most easily ends up weaker than intended, and where no tool helps you.

They are in statement files, which contain definitions only and import nothing but the specification, the model and the artifact. Read each from top to bottom: [`Contract.lean`](../lean/M0Crypto/Release/Contract.lean) and [`TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean) (shared vocabulary), [`ChaCha20Contract.lean`](../lean/M0Crypto/Release/ChaCha20Contract.lean), [`AeadContract.lean`](../lean/M0Crypto/Release/AeadContract.lean), [`ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean); for X25519, [`X25519Contract.lean`](../lean/M0Crypto/Release/X25519Contract.lean) and [`X25519TraceSpec.lean`](../lean/M0Crypto/Release/X25519TraceSpec.lean) (section 9.2); for BLAKE2s, [`Blake2sContract.lean`](../lean/M0Crypto/Release/Blake2sContract.lean), [`Blake2sTraceSpec.lean`](../lean/M0Crypto/Release/Blake2sTraceSpec.lean) and [`Blake2sStatements.lean`](../lean/M0Crypto/Release/Blake2sStatements.lean) (section 10.2).

Two definitions carry most of the weight, so read them first:

- `Region a n y` says that address `y` is one of the `n` bytes starting at `a`. Every read region, write region and "outside the stack" condition is written with it, and so is the condition on the return address. It is `(y − a) mod 2^32 < n`, so a region that crosses the top of memory continues at address 0; the preconditions exclude that for caller buffers through `Disj`. The proved lemmas `Region.mk` and `Region.exists` (`Release/FrameBase.lean`) show it equals "`y = a + o` for some `o < n`". Three neighbouring notions keep their own definitions: `Disj` (two ranges do not overlap and do not wrap around memory; used in almost every precondition), `InStackWindow` (the closed range SP may be in) and the bytes of one access (`Reads`, `Writes`).
- `Pre` (ChaCha20) and `APre` (AEAD) are the complete hypothesis of every top-level theorem: the preconditions, the entry state, and two conditions on the return address.

**Exact preconditions.** Let `sp0` be SP at entry, `W = [sp0 - N, sp0)` the stack window (`N` below), and `code` the asset's `.text`. "`A` disjoint from `B`" (`Frame.Disj`) means both address ranges end at or below `2^32` and do not overlap; an empty range `[p, p)` still must not start strictly inside the other range. Every function's `Pre` requires `code` 4-byte aligned, `sp0 >= N`, `LR` bit 0 set (Thumb) with return address outside `code`, AAPCS32 entry arguments in registers and stack slots (`Entry` / `AEntry`), and:

- **ChaCha20** (`ChaCha20Xor.Pre`, `N = 176`): `sp0` 8-byte aligned; `[sp0 - 176, sp0 + 8)` (`W` plus the two stack arguments) disjoint from `code` and `out`; `W` disjoint from `in`, `key` and `nonce`; `out` disjoint from `code`; `in = out` or disjoint from `out` (`key`, `nonce` and `in` may overlap `code`; `key` and `nonce` may overlap `out` and `in`).
- **ChaCha20-Poly1305** (`Aead.APre`, `N = 320`): `sp0` 8-byte aligned and `sp0 + 16 <= 2^32`; `[sp0 - 320, sp0 + 16)` (`W` plus the four stack arguments) disjoint from `code`, `out` and `tag`; `W` disjoint from `in`, `aad`, `key` and `nonce`; `out` and `tag` each disjoint from `code`; `aad` and `tag` each disjoint from `out`; `in = out` or disjoint from `out` (`key` and `nonce` may overlap `out`, `aad`, `tag` and `code`; `in` and `aad` may overlap `code`).
- **X25519** (`X25519.Pre`, `N = 516`): `sp0` 4-byte aligned; `W` disjoint from `code`, `out`, `scalar` and `point`; `out` disjoint from `code` (`scalar` and `point` may overlap `code`, each other and `out`).
- **BLAKE2s-256** (`Blake2s.{Init,Update,Final}.Pre`, `N = 4` for `init`, `160` for `update` and `final`): `sp0` and `c` 4-byte aligned; `c[112]`, `W` and `code` pairwise disjoint; for `update` and `final`, `*c` holds a stream state produced by `init; update*` with cumulative bytes (plus `n` for `update`) below `2^64`; for `update`, `[p, p + n)` disjoint from `c[112]` and `W` (may overlap `code`); for `final`, `out[32]` disjoint from `code`, `W` and `c[112]`.

The C headers state idiomatic C rules, which may be stricter (for example, they forbid `key` or `nonce` from overlapping `out`).

**Check against:** [`include/m0crypto/chacha20.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20.h), [`include/m0crypto/chacha20poly1305.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20poly1305.h), the claims in the [library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md#proofs-and-scope) and the [proofs README](../README.md#constant-time-traces-read-bounds-and-stack-bounds), and the Arm *Procedure Call Standard* (AAPCS32: arguments in r0-r3 then the stack, r4-r11 and SP preserved).

For every precondition, ask:

- Does every C call permitted by the header — compiled for ARMv6-M AAPCS32 and linked normally, with the header's stack budget — satisfy it, and does the list above state the Lean condition exactly? Headers state idiomatic C rules that may be stricter than `Pre` (see `docs/HEADERS.md` in the library), whereas a precondition that neither AAPCS32/linking nor the header enforces means the theorem covers fewer calls than the header promises.
- `Pre` and `APre` add two conditions to the precondition structures: LR has its Thumb bit set, and the return address is not inside the library's own code. Check that every call from outside the library meets them.
- Can a real call satisfy all preconditions at once? If not, the theorem is vacuous. See "non-vacuity" in section 6 for what exists.
- Is it about public values only? A precondition on secret data would quietly restrict the constant-time claim.

For every postcondition and statement, ask:

- Does it say what the READMEs and the headers claim, with nothing missing? Go through the claims one by one: output bytes, return value, restored registers, write regions, output on decryption failure, **and the clearing of working state** (summarized as secret-independence in the headers and detailed by byte and register in [README.md](../README.md#functional-correctness)).
- For constant time: is everything in `pub` really public, and is every secret absent from it?
- For read regions: is each allowed region needed, and is none of them "all memory"?

| File | Trusted declarations | Lines |
|---|---:|---:|
| [`Contract.lean`](../lean/M0Crypto/Release/Contract.lean) | 6 | 31 |
| [`TraceSpec.lean`](../lean/M0Crypto/Release/TraceSpec.lean) | 13 | 71 |
| [`ChaCha20Contract.lean`](../lean/M0Crypto/Release/ChaCha20Contract.lean) | 19 | 102 |
| [`AeadContract.lean`](../lean/M0Crypto/Release/AeadContract.lean) | 26 | 132 |
| [`ChaCha20TraceSpec.lean`](../lean/M0Crypto/Release/ChaCha20TraceSpec.lean) | 22 | 133 |

**ChaCha20** (`ChaCha20Contract.lean`):

- `Valid` against `chacha20.h`. `Entry`: PC at the function, r0-r3 hold `out`, `in`, `len`, `key`, and the two stack arguments hold `nonce` and `counter`.
- `Result`: return to LR, SP and r4-r11 restored, r0 = 0 or −1 by the counter rule, the output bytes, all other memory outside the 176 stack bytes unchanged. `scratch` and `frame`: r1-r3, r12 and the 35 frame words are zero for an accepted call with `len ≠ 0`, else as at entry. `saved`: the 9 words above hold the caller's registers.
- `WrOk`: the 176 stack bytes, and `out` only if the call is accepted. `Correct`: every valid call returns with `Result` and writes only `WrOk`.
- `Ctx.outB` reads expected output byte `i` with `[i]!`, which returns 0 past the end of the list; the list has `len` elements.

**AEAD** (`AeadContract.lean`):

- `AValid` and `ABuf` against `chacha20poly1305.h` and the AEAD rule above; `SWr` is the stack region `[sp0 - 320, sp0)`.
- `EncryptResult`: `RetPost` (return address, SP, r4-r11, r0 = result, r1-r3 zero), ciphertext and tag equal `Spec.Aead.encrypt`, memory unchanged outside `AWr` (the stack region, `out` and `tag`). `zero`: 96 bytes of the AEAD's own frame (Poly1305 context and key block) are zero. `DecryptResult`: on failure r0 = −2 and `out` is unchanged; on success r0 = 0 and the plaintext equals the spec.
- `EncryptCorrect`, `DecryptCorrect`: every valid call returns with its result, writes only `AWr` or `DAllowed` (`out` only if the tag verifies), r12 is zero, and the 320 stack bytes equal `window` of the entry registers, the nonce pointer and their entry bytes, for decryption also of the verdict: one `window` for all calls. Check that no secret is an argument of `window`.
- `RejectedWrites`: a rejected decryption that writes only `DAllowed` writes only its stack.

**Trace statements** (`ChaCha20TraceSpec.lean`, with `ReadsFrom` and `InStackWindow` of `TraceSpec.lean`):

- `Ctx.pub` and `ACall.pub` are **what counts as public** for constant time. Everything not listed may differ between the two runs, and a field wrongly listed weakens the theorem without any failure. `ACall.verdict` is the one secret bit allowed to influence decryption's trace: whether the tag verifies.
- `…ConstantTime`: two valid calls (`Pre` twice) with equal `pub`, for decryption also equal `verdict`, give equal `runUntil` results (trace or fault) for **every** fuel. With too little fuel both sides are `.error .fuel` and no trace is compared; the content is at the fuel values where the runs return, which exist by the read-bound theorem.
- Read regions: one `Region` per buffer; check that none is wider than the function needs. The ChaCha20 stack region starts at `fp` and includes the 8 bytes of stack arguments above the 176, the AEAD one the 16 above the 320. Decryption's is encryption's without `out`, plus the tag; in place (`out = in`) the `in` region is the output buffer.
- `…Stack`: SP is in [sp0 − N, sp0] at every state of the run.

**Stack discipline and interrupts** (`TraceSpec.lean`):

- `StackDiscipline`, over the `n` bytes below the entry SP: each byte a step reads or writes there lies at or above the SP before or after the step, and every byte read there was written by an earlier step, with SP at or below it ever since.
- `Handlers` is **the interrupt model**. `H k` runs before the call's `k`-th instruction (the identity is allowed). It restores registers and flags and preserves every byte the call may read or write (`P`) outside the `K` bytes below SP. Check that this matches what the caller's handlers do, exception entry and return included.
- `InterruptedCall` is **the interrupted-call claim**. Given `HandlerRoom` (the `K` bytes below the window lie above address 0 and hold no byte of `P`), for all handlers: the uninterrupted call returns with `Result`; the interrupted one (`irunStates`) returns with the same events, its registers and flags and its memory on every byte of `P` outside the window, and keeps SP in the window.
- Each exported function of the three assets has two Props built from these, next to its stack-bound Prop: `…StackDiscipline` (8 lines), which is `StackDiscipline` over its stack window on every run long enough to return, and `…Interrupted` (6 lines), which is `InterruptedCall` with its `Result` and with `P` its read region or its allowed writes (`WrOk`, `AWr`, `DAllowed`). Both assume the function's `Pre`.

## 4. Trusted code that is not a Lean definition

These files decide whether the proofs are about the shipped library and whether they are complete. Review each once, then review every diff to them.

| File | Lines | What it guarantees |
|---|---:|---|
| [`tools/check.sh`](../tools/check.sh) | 186 | The release gate, per asset (`tools/check.sh [ASSET...]`). Step 2b: rebuilds each asset and compares the regenerated artifact file with the checked-in one. Step 4: builds each asset's proofs in its workspace. Step 4b: compares the decoder with `llvm-objdump`. Step 4c: runs the ChaCha20-Poly1305, BLAKE2s and X25519 specifications on the library's test vectors. Step 5: rejects `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/`extern` in sources. Step 6: audits axioms. Step 6b: compares statements with the golden file. Step 7: runs the QEMU tests. Step 7b: compares the model with QEMU instruction by instruction. |
| [`../tools/build_lib.sh`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tools/build_lib.sh) | 63 | Builds each asset's object, whose `.text` is proved, with the pinned toolchain. |
| [`tools/extract_release.py`](../tools/extract_release.py) | 181 | Generates an asset's `Artifacts/Release.lean` from its built object. |
| [`tools/check_listing.py`](../tools/check_listing.py), [`lean/DumpListing.lean`](../lean/DumpListing.lean), [`lean/M0Crypto/Thumb/Listing.lean`](../lean/M0Crypto/Thumb/Listing.lean) | 93 + 5 + 130 | The decoder-versus-LLVM comparison, including `render`, which prints the model's decoding. This is what stands in for reading the decoding functions (section 3.2). |
| [`tools/spec_vectors.py`](../tools/spec_vectors.py), [`lean/SpecVectors.lean`](../lean/SpecVectors.lean), [`lean/SpecVectorsX25519.lean`](../lean/SpecVectorsX25519.lean), [`lean/SpecVectorsBlake2s.lean`](../lean/SpecVectorsBlake2s.lean) | 135 + 77 + 55 + 55 | Runs the specification on the library's test vectors (sections 3.4, 9.2 and 10.2). A test: an error here could hide a specification bug, not create a false theorem. |
| [`tools/qemu_steps.py`](../tools/qemu_steps.py), [`tools/qemu_x25519_windows.py`](../tools/qemu_x25519_windows.py), [`lean/StepTrace.lean`](../lean/StepTrace.lean) | 285 + 421 + 84 | Compares the model with QEMU after every instruction of traced calls that reach every instruction a call can execute (sections 3.1, 9.3, 10.4). Also a test. |
| `assets/ASSET/Audit.lean` | | Per asset: the claims (section 6, "Claim policy"). `check.sh` requires one axiom report per claim, drawn only from `propext`, `Classical.choice`, `Quot.sound`. |
| [`tools/statements.sh`](../tools/statements.sh), [`tools/claims.sh`](../tools/claims.sh) + `assets/ASSET/statements.golden` | | Per asset: printed statement and term hash of every claim and trusted definition. See section 2. |
| [`lean-toolchain`](../lean-toolchain), [`tools/versions.txt`](../tools/versions.txt), [`../tools/versions.txt`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tools/versions.txt) | — | Pinned Lean, LLVM and QEMU versions. |
| [`tools/trusted_defs.lean`](../tools/trusted_defs.lean) | 261 | Computes the reading list (section 6) and the definitions printed into the golden files. An error here would hide trusted code from the reviewer. `check.sh` runs it through `statements.sh`. |
| [`tools/comparator.sh`](../tools/comparator.sh) + `assets/ASSET/challenge/Challenge.lean` | 32 | Run by the library's CI ([`ci.yml`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/.github/workflows/ci.yml)) whenever its workflow runs. Each challenge, a statement file, states the asset's claims (no witnesses) with `sorry`. `lake comparator` requires each claim of the asset root to state the same term, reaching the same declarations, with only the three axioms; `lake check` replays every declaration the root reaches. |

Also trusted, outside this repository:

- The Lean kernel and the Lean core library (`BitVec`, `List`; `omega`'s proof output is kernel-checked). Whenever its workflow runs, the library's CI requires [`tools/comparator.sh`](../tools/comparator.sh) to accept the three asset roots against their challenges, and Lean's kernel to accept every declaration each root reaches, Lean core included, replayed into an empty environment.
- Lean's elaborator, for the meaning of what you read: the kernel checks the elaborated statement, and you read its source text.
- Whatever puts the library on the chip (linker, image conversion, flashing): the proofs are about each asset's `.text` bytes at a 4-byte-aligned address. The objects have no relocations, so a linker has nothing to patch.

The assembler is *not* trusted. The proofs are about its output bytes, whatever the source says.

## 5. Assumptions no review can remove

These are stated in the [library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md#proofs-and-scope). A reviewer checks that they are stated, not that they hold:

- Execution is sequential, and nothing but the modelled handlers modifies memory a function uses while it runs (another bus master such as DMA could). The interrupted-call theorems model an interrupt by its effect alone: exception entry, handler and exception return together restore every register and flag and preserve every byte the call may read or write outside the `K` bytes below SP. The exception entry stores r0-r3, r12, LR, PC and xPSR there, and the handler sees the call's working state. Clearing covers uninterrupted calls.
- Memory is ordinary RAM: no faults, no device side effects.
- Execution time depends only on the trace (instructions, addresses, branches): the constant-time claims are about the model's trace. The Cortex-M0+ has no cache and no branch prediction, and its multiplier (`muls`, used by X25519) is single-cycle or 32-cycle iterative by build option, with a fixed time either way, per Arm's documentation.
- Physical side channels and fault injection (power analysis, electromagnetic leakage, glitching) are out of scope.

## 6. Keeping the proofs robust

Every change to the code or proofs can move the trusted base. These habits keep the review small and valid.

**Check the reading list before every review.**

```sh
(cd assets/chacha20poly1305 && lake build)
tools/trusted_defs.sh chacha20poly1305      # likewise blake2s, x25519
```

The tool prints every trusted declaration with its file and line range, then one `FILE` line per file. Every asset's list names the model and decoder (`Armv6M/Memory.lean`, `Armv6M/State.lean`, `Armv6M/Step.lean`, `Thumb/Exec.lean`, `Thumb/Decode.lean`), the shared vocabulary (`Release/Contract.lean`, `Release/TraceSpec.lean`) and the asset's artifact file, plus:

| Asset | Files of its own |
|---|---|
| `chacha20poly1305` | `Spec/ChaCha20.lean`, `Spec/Aead.lean`, `ChaCha20Contract.lean`, `AeadContract.lean`, `ChaCha20TraceSpec.lean` (section 3) |
| `x25519` | `Spec/X25519.lean`, `X25519Contract.lean`, `X25519TraceSpec.lean` (section 9.2) |
| `blake2s` | `Spec/Blake2s.lean`, `Blake2sContract.lean`, `Blake2sTraceSpec.lean`, `Blake2sStatements.lean` (section 10.2) |

A file that appears for the first time holds new trusted code: move that definition into a statement file, or review the new file. The roots are the claims in the asset's `Audit.lean` without the non-vacuity witnesses, so adding a claim there is the only step.

The declaration and line counts in sections 1, 3, 9.2 and 10.2 are this output. Correct them when it changes.

**Claim policy (every asset).** An asset's `Audit.lean` lists exactly its claims, in this order: for each global function of the asset's object, a correctness, a constant-time, a read-bound, a stack-bound, a stack-discipline and an interrupted-call theorem, and three non-vacuity witnesses (`*_nonvacuous`): the correctness precondition at a concrete call; the whole hypothesis of the constant-time theorem at two concrete calls (both preconditions, equal `pub` and, for decryption, equal verdict) with an inequality that shows a secret input differs between them; and a call with handler room and a handler that writes outside the call's regions; then the asset's composition claims (AEAD `rejected_writes`; BLAKE2s `hash_correct`, `hash_constant_time` and their witnesses `hash_correct_nonvacuous`, `hash_constant_time_nonvacuous`). Supporting lemmas are not listed: `#print axioms` on a claim already follows its whole proof, and step 5 scans every source for `sorry` and axioms. Internal routines (local symbols: Poly1305 `init`/`blocks`/`finish`, BLAKE2s `compress`/`copy`, X25519 `fe_*`) are not claims; their contracts are proved and used inside the claims of the functions that call them, and the artifact file marks each function offset `exported` or `internal`. A composed claim with many hypotheses names them as a structure (BLAKE2s `HashCorrectHyp`, `HashConstantTimeHyp`) so that its witness can state them at a concrete call.

**Review statement diffs, not proof diffs.** For any change, the questions are:

1. Did an asset's `statements.golden` change? Read every changed statement in full.
2. Did a trusted file change? The golden file shows that a trusted definition changed; this diff shows whether it is still right. Read it against its reference:

   ```sh
   git diff <reviewed commit> -- lean/M0Crypto/Spec lean/M0Crypto/Armv6M \
     lean/M0Crypto/Thumb/Decode.lean lean/M0Crypto/Thumb/Exec.lean lean/M0Crypto/Thumb/Listing.lean \
     lean/M0Crypto/Release/Contract.lean lean/M0Crypto/Release/ChaCha20Contract.lean \
     lean/M0Crypto/Release/AeadContract.lean lean/M0Crypto/Release/TraceSpec.lean \
     lean/M0Crypto/Release/ChaCha20TraceSpec.lean lean/M0Crypto/Release/X25519TraceSpec.lean \
     lean/M0Crypto/Release/X25519Contract.lean lean/M0Crypto/Release/Blake2sContract.lean \
     lean/M0Crypto/Release/Blake2sTraceSpec.lean lean/M0Crypto/Release/Blake2sStatements.lean \
     lean/M0Crypto/Assets \
     assets tools ../tools/build_lib.sh
   ```

3. Did `check.sh` pass from a clean checkout?

If all three are fine, the proof changes need no correctness review.

**Watch for these patterns.** An agent (or a person) under pressure to make a proof go through tends to change the statement instead of the proof:

- a new or stronger hypothesis (smaller set of calls covered);
- a new helper definition used in a statement (new trusted code);
- a `pub` tuple that grows (weaker constant-time claim);
- a write or read region that grows;
- a postcondition that is dropped or replaced by something weaker;
- `sorry`, `axiom`, `native_decide`, or a raised `maxRecDepth`/`maxHeartbeats` to force a `decide` through (the last two are not unsound, only a cost signal).

**Non-vacuity.** Each function has a concrete call that satisfies `Pre` (or `APre`), the whole hypothesis of its correctness, read and stack theorems: [`Release/ChaCha20Poly1305NonVacuity.lean`](../lean/M0Crypto/Release/ChaCha20Poly1305NonVacuity.lean) proves this for the three ChaCha20-Poly1305 functions (X25519: section 9.1; BLAKE2s: section 10.1), with calls that are in place, unaligned and non-empty, and passes each witness to its correctness theorem. Each `*_constant_time_nonvacuous` gives two valid calls with equal `pub` and different keys: for `xor` and encryption that call and the same call with another key; for decryption two such calls that each carry the tag of their own key, so both are accepted. In all three assets, each `*_interrupted_nonvacuous` is the function's correctness witness with 256 bytes of handler room and a handler that zeroes them and increments a byte outside the call's regions, passed to its interrupted-call theorem. Check that the witnesses are realistic rather than degenerate.

**Keep the trusted base where it is.** Statements mention only definitions from `Spec/`, the model, and the statement files. A new definition that a statement needs goes into a statement file, never into a proof file.

**Known gaps.**

- The golden file locks every claim statement and trusted definition as printed text and as the hash of its kernel terms. The Lean core definitions they use (`List`, `BitVec`) are trusted with Lean (section 4).
- The decoding functions are trusted through the comparison with LLVM, not through reading (section 3.2).
- The model is compared instruction by instruction with QEMU, on calls that execute every instruction a call can execute (section 3.1). It is compared with the chip only through the outputs and cycle counts of whole function calls.

## 7. Learning by breaking things

The fastest way to understand what each part protects is to break it on purpose and watch what fails, on a scratch branch. Build only the modules you need (`lake build +Module.Name`).

1. **Read a statement in full.** `tools/statements.sh chacha20poly1305` prints every claim with full names, then every trusted definition. Pick `xor_correct` and trace each name to its definition, first in that output, then in its file. Then pick `xor_constant_time`: the statement is only a name, and its body is printed further down.
2. **See the axiom audit.** `lake env lean Audit.lean` in `assets/chacha20poly1305` prints the axioms of each theorem. Replace a proof step in `Release/ChaCha20Xor.lean` by `sorry`, run `lake build`, and run it again: `sorryAx` appears for every audited theorem that depends on that proof, and `check.sh` fails.
3. **Break the spec.** In `Spec.ChaCha20.quarterRound`, change the rotation 12 to 11. The vectors in `Spec/ChaCha20Vectors.lean` fail. Then ask: which spec errors would the vectors *not* catch? (Hint: the high bytes of the length fields of `macData`.)
4. **Break the model.** In `Armv6M.addWithCarry`, return the carry negated. Build the release proofs and see which theorems fail: that shows you how much depends on one line. Then try an error in a flag: remove `.setNZ x` from the `movImm` case of `Instr.exec`, build `+M0Crypto.Thumb.FastRun` and run the step 7b command from `check.sh`. It stops at the first instruction after which the model and QEMU differ.
5. **See who protects a contract.** Add a field to `Valid` in `ChaCha20Contract.lean` (for example `short : c.len.toNat < 64`) and build `+M0Crypto.Release.AeadKey`. The golden file would show the new field, but the build stops first: the AEAD proof must establish `Valid` for its own inner ChaCha20 call, and the witness in `ChaCha20Poly1305NonVacuity.lean` no longer fits. A contract is protected by whoever has to satisfy it. A definition nobody has to satisfy, such as `pub` or a read region, is protected only by review.
6. **Mutate the assembly.** [`tools/mutate_aead.py`](../tools/mutate_aead.py) applies 20 deliberate bugs to the AEAD source. The QEMU tests or the model's executable release checks must detect 19 of them. The decryption constant-time certificate must reject the timing mutant, a tag comparison that exits at the first differing byte, which keeps every result and passes both; the library's CI ([`ci.yml`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/.github/workflows/ci.yml)) runs it whenever its workflow runs and fails if one is missed. Read its mutant list and predict which check catches each mutant before running it.

Background reading: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) (propositions, quantifiers, structures) and [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

## 8. Reference documents

| Document | Used for |
|---|---|
| [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439), ChaCha20 and Poly1305 for IETF Protocols | `Spec/ChaCha20.lean`, `Spec/Aead.lean`, vectors (§2.1.1, §2.3.2, §2.4.2, §2.5.2, §2.8.2) |
| [ARMv6-M Architecture Reference Manual](https://developer.arm.com/documentation/ddi0419/latest) (DDI 0419) | Machine model and decoder |
| [Procedure Call Standard for the Arm Architecture](https://github.com/ARM-software/abi-aa/releases) (AAPCS32) | Entry contracts: argument registers, stack arguments, callee-saved registers |
| [Cortex-M0+ Technical Reference Manual](https://developer.arm.com/documentation/ddi0484/latest) (DDI 0484) and [Generic User Guide](https://developer.arm.com/documentation/dui0662/latest) (DUI 0662) | Timing assumption (instruction cycle counts, no cache or branch prediction) |
| [`include/m0crypto/chacha20.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20.h), [`chacha20poly1305.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/chacha20poly1305.h) | Contracts: what callers must guarantee and what they are promised |
| [Library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md), [proofs README](../README.md) | The claims the theorems must support |
| [RFC 7748](https://www.rfc-editor.org/rfc/rfc7748), Elliptic Curves for Security | `Spec/X25519.lean` (RFC section 5), vectors (RFC sections 5.2 and 6.1) |
| [`include/m0crypto/x25519.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/x25519.h) | X25519 contract (section 9) |
| [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693), The BLAKE2 Cryptographic Hash and Message Authentication Code | `Spec/Blake2s.lean` (RFC sections 2 and 3), vector (appendix B) |
| [`include/m0crypto/blake2s.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/blake2s.h), [`src/blake2s_internal.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/src/blake2s_internal.h) | BLAKE2s contract and context layout (section 10) |

## 9. X25519 (`m0c_x25519`)

The X25519 asset (`m0crypto_x25519.o`, 7,022 bytes of `.text`) has four functions: the exported entry `m0c_x25519` (offset `Artifacts.Release.x25519`) and the internal field routines `m0c_fe_mul`, `m0c_fe_sqr` and `m0c_fe_mulc_add` (local symbols), which only the entry calls. It is reviewed like the other functions: read the statements and the definitions they use, never the proofs. This section lists what is specific to X25519. Sections 3.1-3.3 (model, decoder, artifact), 4, 5 and 6 apply unchanged.

### 9.1 Top-level theorems

| Theorem | File | Claim |
|---|---|---|
| `X25519.x25519_correct : X25519.Correct` | [`X25519Correct.lean`](../lean/M0Crypto/Release/X25519Correct.lean) | Every valid call returns; `out` holds RFC 7748 `X25519(scalar, point)`; all other memory outside the stack window is unchanged; the 480 stack bytes below the saved registers are zero and the 36 above them hold the caller's r4-r11 and LR; r4-r11 and SP restored, r0 = 0 (`M0C_OK`), r1-r3 and r12 zero; only the stack window and `out` are written |
| `X25519.x25519_constant_time : TraceSpec.X25519ConstantTime` | [`X25519Trace.lean`](../lean/M0Crypto/Release/X25519Trace.lean) | Trace depends only on the base, entry SP, LR and the three pointers |
| `X25519.x25519_reads : TraceSpec.X25519Reads` | same | Reads only `scalar`, `point`, the artifact and the stack window |
| `X25519.x25519_stack : TraceSpec.X25519Stack` | same | SP within 516 bytes below its entry value at every state |
| `X25519.x25519_stack_discipline`, `x25519_interrupted` | same | `StackDiscipline` over the 516 bytes and `InterruptedCall` (section 3.5) |

All six assume `X25519.Pre c s`. They are the claims in `assets/x25519/Audit.lean`, with the non-vacuity witnesses (`X25519NonVacuity.lean`) `x25519_pre_nonvacuous`, a call where `out` is `point`, at an odd address, and `scalar` is unaligned, on RFC 7748 vector 1, `x25519_constant_time_nonvacuous`, that call and the same call with the scalar of vector 2, and `x25519_interrupted_nonvacuous` (section 6).

### 9.2 What to read

| Part | File | Declarations | Lines | Reference |
|---|---|---:|---:|---|
| Specification | [`Spec/X25519.lean`](../lean/M0Crypto/Spec/X25519.lean) | 15 | 68 | RFC 7748 section 5 |
| Contract | [`X25519Contract.lean`](../lean/M0Crypto/Release/X25519Contract.lean) | 16 | 93 | `include/m0crypto/x25519.h`, AAPCS32 |
| Trace statements | [`X25519TraceSpec.lean`](../lean/M0Crypto/Release/X25519TraceSpec.lean): `X25519.Ctx.pub`, `X25519ReadRegion`, `X25519ConstantTime`, `X25519Reads`, `X25519Stack`, `X25519StackDiscipline`, `X25519Interrupted` | 7 | 40 | the claims of section 9.1 |
| Model | `sbcs` in `Thumb.DpOp` and `Instr.exec` (section 3.1) | 1 | 4 | ARMv6-M manual, SBC (register) |
| Artifact | `Artifacts.Release.x25519`, `size`, `bytes` | 3 | generated (444) | `llvm-nm -S` of the built object; section 3.3 |

Produced by `tools/trusted_defs.sh x25519`. With the model (287 lines), the decoder (167) and the shared vocabulary (102), the X25519 asset trusts 757 hand-written lines in 10 files, of which 201 are its own.

**Specification.** `Spec/X25519.lean` follows RFC 7748 section 5 in the RFC's own names and order. Check:

- `decodeScalar25519`: clears bits 0-2 of byte 0, clears bit 7 of byte 31, sets bit 6 of byte 31.
- `decodeUCoordinate`: masks bit 7 of byte 31 (`bits = 255`) and does *not* reduce: values of `p` or more are reduced by the field arithmetic, as the RFC requires.
- `ladderStep`: one loop iteration for `t = 254` down to `0`, with `a24 = 121665`, `z_2 = E * (AA + a24 * E)`, and the swap carried between iterations. The RFC's `z_3 = x_1 * (DA - CB)^2` uses `x_1 = u`, the decoded (unreduced) coordinate; every result is reduced mod `p`.
- `output`: the final `cswap`, then `x_2 * z_2^(p - 2)` written as a power, then `encodeUCoordinate` (`% p`, 32 little-endian bytes). `output_eq_fast` is a theorem marked `@[csimp]`: it changes only how compiled tests evaluate `output`, not its meaning.
- No zero check: the function returns the all-zero output for low-order points, as wolfSSL's low-level `curve25519()` does. Rejecting those is the caller's (protocol's) job.

Vectors, as `#guard`s in [`Spec/X25519Vectors.lean`](../lean/M0Crypto/Spec/X25519Vectors.lean): RFC 7748 section 5.2, both single vectors (the second has the top bit of `u` set) and the iteration after 1 and 1,000 steps. `check.sh` step 4c also runs the specification ([`lean/SpecVectorsX25519.lean`](../lean/SpecVectorsX25519.lean), through `tools/spec_vectors.py`) on all 524 vectors of the library's [`tests/x25519_vectors.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/x25519_vectors.h), the same file the QEMU test uses: RFC 7748 section 5.2 (2), section 6.1 (4: both public keys and the shared secret, both ways) and Wycheproof `x25519_test.json` (518, including low-order points, points on the twist and `u ≥ p`). Their expected values come from Wycheproof and the RFC, and were cross-checked with pyca/cryptography by `tools/gen_x25519_vectors.py`, not produced by this specification. The 1,000,000-step iteration is not run on the specification.

**Contract.** Read `X25519Contract.lean` from top to bottom. Points to check:

- `Pre` = `Valid` + `Entry` + Thumb-mode LR + return address outside the artifact. `Valid` is the X25519 rule of section 3.5. The three buffers may be unaligned and may overlap each other in any way because the entry reads `scalar` and `point` completely before it writes `out`; the witness uses `out = point`.
- `Result.mem` says memory *outside the stack window* is unchanged except `out`. Inside the window, `wipe` says the 480 bytes below the saved registers are zero and `saved` that the top 36 bytes hold the caller's r8-r11, r4-r7 and LR as saved at entry (`savedRegs`), so every byte of the window is fixed.
- `X25519.Ctx.pub` lists what is public: base, entry SP, LR, and the three pointers. Scalar and point bytes, all other memory and the other registers are secret.
- `X25519ReadRegion` is `scalar` ∪ `point` ∪ artifact ∪ stack window. `out` is not in it, so the code never reads `out` unless `out` overlaps an input.

### 9.3 Checks and evidence specific to X25519

- `src/x25519.S` is generated by [`../tools/gen_x25519.py`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tools/gen_x25519.py). `check.sh` step 2b regenerates it and requires the checked-in file to be equal.
- `check.sh` step 7b ([`tools/qemu_x25519_windows.py`](../tools/qemu_x25519_windows.py)) compares the model with QEMU after every instruction of windows of one call: six named windows (prologue, one ladder step, the exit of each loop kind, epilogue) and 41 short ones that start at each instruction those miss. The 47 windows execute 25,780 instructions and all 3,462 instructions of the asset. A fixture covers `sbcs` with both carries, overflow and zero.
- [`tools/mutate_x25519.py`](../tools/mutate_x25519.py): 14 single-instruction mutants over the four symbols, each patched into a copy of the object. On every push, the library's CI requires the executable release checks (`Thumb/ReleaseCheck/X25519*`) to reject the 13 functional mutants and the constant-time certificate to reject the timing mutant.
- [`../tests/test_x25519.c`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/test_x25519.c), run by `check.sh` step 7 (`tools/test_qemu.sh x25519`): the release object on QEMU's Cortex-M0 on the 524 vectors of section 9.2, compared on the 32 output bytes (the function has no low-order check and always returns `M0C_OK`); the section 5.2 iteration after 1 and 1,000 steps (1,000,000 only when built with `-DX25519_ITER_1M`, which `check.sh` does not do); all 64 alignments of the three pointers; overlaps of `out`, `scalar` and `point` in one region; guard bytes around `out`; and, through `tests/check_call8.S`, r4-r11 and SP restored, r0-r3 and r12 zero, the 516-byte stack bound and the 480 cleared bytes.

## 10. BLAKE2s-256 (`m0c_blake2s_init`, `_update`, `_final`)

The BLAKE2s asset (`m0crypto_blake2s.o`, 4,748 bytes of `.text`) has five functions: the exported `m0c_blake2s_init`, `m0c_blake2s_update` and `m0c_blake2s_final`, and the internal `m0c_blake2s_compress` and `m0c_blake2s_copy` (local symbols, called only by `update` and `final`). It computes unkeyed BLAKE2s with a 32-byte digest, incrementally, on a 112-byte caller context. It is reviewed like the other functions: read the statements and the definitions they use, never the proofs. This section lists what is specific to BLAKE2s. Sections 3.1 to 3.3 (model, decoder, artifact), 4, 5 and 6 apply unchanged. The model needs no instruction beyond those of section 3.1.

### 10.1 Top-level theorems

Per function. All six theorems of a function assume its `Pre` (`Blake2s.Init.Pre`, `Blake2s.Update.Pre`, `Blake2s.Final.Pre`). The correctness statements are written once, as Props, in `Blake2sContract.lean` (`Init.Correct`, `Update.Correct`, `Final.Correct`); the trace, read and stack statements in `Blake2sTraceSpec.lean`. The theorems are in [`Blake2sClaims.lean`](../lean/M0Crypto/Release/Blake2sClaims.lean) and only say `: Correct` or `: TraceSpec.X`.

| Theorem | Claim |
|---|---|
| `Blake2s.Init.init_correct : Init.Correct` | Every valid call returns; the context holds the empty stream (`State.init`); r4-r11, r12 and SP restored, r0 = context + 36, r1 and r2 the IV words 6 and 7, r3 zero; the 4 stack bytes hold the caller's LR; only the 4 stack bytes and the context written |
| `Blake2s.Update.update_correct : Update.Correct` | Every valid call returns; the context holds the entry stream with the input absorbed (`absorb`); r4-r11 and SP restored, r0-r3 zero; the 160 stack bytes and r12 are one function of only the entry registers, the number of pending bytes and the window's entry bytes; only the 160 stack bytes and the context written |
| `Blake2s.Final.final_correct : Final.Correct` | Every valid call returns; the 32 bytes at `out` are `finish` of the entry stream, the RFC 7693 digest; r4-r11 and SP restored, r0-r3 and r12 zero; the 160 stack bytes are one function of only the entry registers; only the 160 stack bytes, the context and `out` written |
| `Blake2s.Init.init_constant_time`, `Update.update_constant_time`, `Final.final_constant_time` | Trace depends only on `pub` (10.2): base, entry SP, LR, the pointer arguments, and for `update` the input length; for `update` and `final` also the number of pending bytes |
| `Blake2s.Init.init_reads`, `Update.update_reads`, `Final.final_reads` | `init` reads only the code and its stack window; `update` the context, the input, the code and its stack window; `final` the context, the code and its stack window |
| `Blake2s.Init.init_stack`, `Update.update_stack`, `Final.final_stack` | SP within 4 bytes (`init`) or 160 bytes (`update`, `final`, including the frames of `compress` and `copy`) below its entry value at every state |
| `Blake2s.Init.init_stack_discipline`, `init_interrupted`, and the same for `Update` and `Final` | `StackDiscipline` over the function's stack window and `InterruptedCall` (section 3.5) |

Composition, stated in [`Blake2sStatements.lean`](../lean/M0Crypto/Release/Blake2sStatements.lean) and proved in [`Blake2sComposed.lean`](../lean/M0Crypto/Release/Blake2sComposed.lean):

| Theorem | Claim |
|---|---|
| `Blake2s.hash_correct : HashCorrect` | Total correctness of `init; update*; final` on one context: from a valid `init` call and a total input length below 2^64 bytes (`HashCorrectHyp`), `init` returns; each `update` call whose entry meets `update`'s obligations returns; then a `final` call that meets its obligations returns, and its 32 output bytes are `Spec.Blake2s.blake2s` of the concatenated inputs. Between calls the caller may run any code that leaves the 112 context bytes unchanged (`ContextKept`). No run is assumed. |
| `Blake2s.hash_constant_time : HashConstantTime` | Two such sequences whose calls have equal public inputs, call by call (`HashConstantTimeHyp`: SP, LR, the pointers and the lengths), produce the same event trace for every call, whatever the message bytes. The runs are hypotheses here; `hash_correct` shows they exist. |

Non-vacuity, in [`Blake2sNonVacuity.lean`](../lean/M0Crypto/Release/Blake2sNonVacuity.lean), all in `assets/blake2s/Audit.lean`:

- `init_pre_nonvacuous`, `update_pre_nonvacuous`, `final_pre_nonvacuous`: each `Pre` holds at a concrete call on a context at `0x20000000` that holds a buffered stream (three bytes absorbed, so 3 bytes pending). `init` re-initializes it; `update` absorbs 100 input bytes at an odd address (it completes the pending block, compresses it and buffers the rest); `final` writes the digest to an odd address. Each witness is passed to its correctness theorem.
- `init_constant_time_nonvacuous`, `update_constant_time_nonvacuous`, `final_constant_time_nonvacuous`: each pairs that call with a second valid call with equal `pub` and different secret memory. `init` has no secret argument; its second call runs on a context of zero bytes. The second `update` call absorbs the input bytes 0 to 99 instead of zeros. The second `final` call runs on a context that holds `[4, 5, 6]` pending instead of `[1, 2, 3]`.
- `init_interrupted_nonvacuous`, `update_interrupted_nonvacuous`, `final_interrupted_nonvacuous`: section 6.
- `hash_correct_nonvacuous`: `HashCorrectHyp` at the `init` witness with the one `update` call of `update_pre_nonvacuous`. `HashCorrectHyp` contains only the `init` precondition and the length bound; the obligations of the `update` and `final` calls are premises inside the conclusion, which the per-function witnesses show satisfiable.
- `hash_constant_time_nonvacuous`: `HashConstantTimeHyp` for two executions of `init`, one `update` of three bytes at the same address and `final`, which differ only in the message bytes (`[1, 2, 3]` and `[4, 5, 6]`).

The 31 claims of `assets/blake2s/Audit.lean` are these 18 theorems, the two composition theorems and the 11 witnesses.

### 10.2 What to read

Produced by `tools/trusted_defs.sh blake2s`. The model, decoder and shared vocabulary are those of section 3 (the BLAKE2s asset does not use `Armv6M.slot`, and has its own `Blake2s.bytesAt` instead of `Frame.Ctx.bytesAt`).

| Part | File | Declarations | Lines | Reference |
|---|---|---:|---:|---|
| Specification | [`Spec/Blake2s.lean`](../lean/M0Crypto/Spec/Blake2s.lean) | 26 | 125 | RFC 7693 |
| Contract | [`Blake2sContract.lean`](../lean/M0Crypto/Release/Blake2sContract.lean) | 40 | 284 | `include/m0crypto/blake2s.h`, `src/blake2s_internal.h`, AAPCS32 |
| Trace statements | [`Blake2sTraceSpec.lean`](../lean/M0Crypto/Release/Blake2sTraceSpec.lean) | 21 | 118 | the claims of section 10.1 |
| Composition statements | [`Blake2sStatements.lean`](../lean/M0Crypto/Release/Blake2sStatements.lean) | 17 | 91 | the claims of section 10.1 |
| Artifact | `Artifacts.Release.blake2s_init`, `_update`, `_final`, `size`, `bytes` | 5 | generated (304) | `llvm-nm -S` of the built object; section 3.3 |

With the model (287 lines), the decoder (167) and the shared vocabulary (98), the BLAKE2s asset trusts 1,170 hand-written lines in 11 files, of which 618 are its own.

**Specification.** **Check against:** [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) (§2.1 parameters and rotation constants, §2.4 byte order, §2.5 parameter block, §2.6 IV, §2.7 SIGMA, §3.1 G, §3.2 F, §3.3 padding, counter and digest). `Spec/Blake2s.lean` imports nothing from the model; check that this stays true.

- Each definition against its RFC section, in the RFC's own order. Constants digit by digit: the eight `IV` words (§2.6), the ten `SIGMA` rows (§2.7; a swapped entry is the classic specification bug), `0x01010020` in `h0` (§2.5: h[0] ^= 0x01010000 ^ (kk << 8) ^ nn with kk = 0, nn = 32).
- `rotr` rotates right (ChaCha20 rotates left) and `G` (§3.1) calls it with 16, 12, 8 and 7 (§2.1).
- `round`, §3.2: four column `G`s then four diagonal `G`s, message words in `SIGMA[r % 10]` order. Check the diagonal index sets.
- `initVec` and `compress`, §3.2: v[0..7] = h, v[8..15] = IV, v12 ^= t mod 2^32, v13 ^= t >> 32, v14 inverted for the last block; ten rounds, then h[i] ^= v[i] ^ v[i+8].
- `loop`, §3.3: every block but the last with t = bytes so far and f = false; the last block (1 to 64 bytes, or the empty message) zero-padded, with t = total length (not padded length) and f = true. The digest is the first 32 bytes of the little-endian chain value.
- `blake2s` is the RFC algorithm. `State`, `absorb` and `finish` are a streaming description that is not in the RFC: a design choice, tied to `blake2s` by the proved `finish_absorb` and `stream_partition` (any split of a message into `update` calls gives the digest of the whole message), so only the definitions need reading. `State.push` keeps a full block pending until another byte arrives, because BLAKE2 must know which block is last: check that a full pending block is compressed only then, as a non-final block. `finish` takes the pending bytes as the final block, with t = count + pending length.

Vectors, as `#guard`s in [`Spec/Blake2sVectors.lean`](../lean/M0Crypto/Spec/Blake2sVectors.lean): RFC 7693 appendix B (`"abc"`), and Python `hashlib.blake2s` digests of the empty message and of the bytes `i % 251` at lengths 1, 63, 64, 65, 128 and 129, plus one check that a three-part split through `absorb` and `finish` equals `blake2s`. A `#guard` is a compiled test, not a kernel proof. `check.sh` step 4c also runs the specification on the library's test vectors (`tests/blake2s_vectors.h`, 204 lengths from `hashlib`, through [`lean/SpecVectorsBlake2s.lean`](../lean/SpecVectorsBlake2s.lean)): for each vector both `blake2s` and the streaming `finish (absorb State.init msg)` must equal the digest. The same vectors run against the machine code on QEMU (section 10.4). No vector reaches the high word of the byte counter (2^32 bytes or more), so `t1` in `initVec` and `countHigh` in `ContextHoldsExceptUsed` are checked by reading only.

**Contract.** Read `Blake2sContract.lean` from top to bottom, then `Blake2sTraceSpec.lean`, then `Blake2sStatements.lean`. **Check against:** [`include/m0crypto/blake2s.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/include/m0crypto/blake2s.h), the context offsets pinned by the `_Static_assert`s of [`src/blake2s_internal.h`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/src/blake2s_internal.h) (compiled into the QEMU test of `check.sh` step 7), the claims in the [library README](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/README.md#proofs-and-scope), and AAPCS32. Points to check:

- `ContextHolds` is **the meaning of the context**, how the 112-byte C structure maps to the specification state: `h[8]` at offset 0, the 64-bit count at 32 and 36, the pending bytes at the start of `buf` (40), `used` (104) = number of pending bytes. Only the first `used` bytes of `buf` are constrained; the rest of `buf` may hold anything.
- `Update.Valid` and `Final.Valid` require the context to hold a stream (`holds`) and the total length to stay below 2^64 bytes. The header leaves the length to the caller ("no overflow check").
- Placement: the BLAKE2s rule of section 3.5. Input and output may be at any byte address; the input may overlap the code because it is only read.
- `Update.Valid` allows `len = 0` with a NULL input pointer (`Disj` of an empty range at address 0 holds), which covers the header's NULL rule when `n == 0`.
- `Pre` = `Valid` + `Entry` + Thumb-mode LR + return address outside the artifact, as for the other assets.
- `Result` and `Correct` fix every scratch register and every byte of the stack window at return. `init`: r0-r3 by value, r12 unchanged, the 4 stack bytes the caller's LR. `update` and `final`: r0-r3 zero (`scratch`). `final`: r12 zero. `Update.Correct` (`residue`) and `Final.Correct` (`window`) state the window, and for `update` r12, as one function of public values: the entry registers, for `update` also the number of pending bytes and the window's entry bytes. Check that no secret (context contents, input bytes) is an argument of these functions.
- `WrOk`: `init` and `update` may write the stack window and the context; `final` also `out`. `Final.Result` says nothing about the context after the call: the header's rule that `final` consumes `*c` is the contract, and a later `update` or `final` needs a new `init`.
- `pub` (constant time): `init` has base, entry SP, LR and the context pointer; `update` adds the input pointer, the input length and the number of pending bytes; `final` the output pointer and the number of pending bytes. The chain value, the byte count, the pending bytes, the input bytes, the caller's other registers (including unused argument registers) and all other memory are secret. The number of pending bytes is a function of the lengths absorbed since `init`; in the composed `HashConstantTime` it is not a hypothesis, since it follows from the public lengths.
- Read regions: `init` reads no context byte; `update` and `final` read the whole 112-byte context, the code and their stack window; `update` also the input. `final` does not read `out`.
- Stack sizes are named definitions (`initStackBytes` 4; `streamStackBytes` = 20 saved + 4 for `compress`'s stacked argument + 136 for `compress`'s frame, 100 locals and 36 saved, = 160). Check them against the `push`/`sub sp` of `src/blake2s_*.S` if they change.
- `HashCorrect` asks each `update` and `final` entry (`EntryOn`) to meet that function's `Pre` for whatever stream the context holds (`callAt` reads the call off the entry state; check its field order against `Update.Ctx` and `Final.Ctx`), and the caller to keep the context bytes between calls (`ContextKept`). The input of each `update` is read from its entry memory (`inputAt`), so the caller may change the message buffer between calls. The conclusion is only the digest; registers, other memory and the stack are covered by the per-function theorems.
- `HashConstantTimeHyp` asks equal `pub` of the two `init` calls and equal `pubAt` (SP, LR and the argument registers) of each `update` and `final` entry. Check that nothing secret is required equal.

### 10.3 What the BLAKE2s theorems do not say

- **The context is not cleared.** After `update`, the context holds the chain value and up to 64 pending input bytes: the message tail stays in `buf` by design. After `final`, `Final.Result` says nothing about the context, so the chain value and the message tail may remain there. The header leaves wiping the context to the caller.
- **The number of pending bytes is public** in the per-function constant-time claims. A caller whose update lengths are secret is outside them.

### 10.4 Checks and evidence specific to BLAKE2s

- `check.sh` step 7b runs [`tools/qemu_steps.py`](../tools/qemu_steps.py) on the BLAKE2s test image: it single-steps calls 1, 2, 3, 5, 8, …, 987 of each of `init`, `update` and `final` in QEMU, then the three further `update` calls that execute an instruction those did not, and compares the model after every instruction, as in section 3.1. The 48 calls execute exactly the 2,337 instructions a call can execute: all 2,338 listed instructions except one alignment filler before a literal pool.
- The executable release checks ([`Thumb/ReleaseCheck/Blake2sCases.lean`](../lean/M0Crypto/Thumb/ReleaseCheck/Blake2sCases.lean) and its shards `Blake2sShard0`-`3`, `Blake2sPairwise`) run `init; update*; final` on the real bytes in the model and check read and write ranges, restored registers, the stack bound and the digest against `Spec.Blake2s.blake2s`. As for the other two assets, the asset root `M0Crypto.Assets.Blake2s` imports them, so `check.sh` step 4 builds them. A failing case throws, so a successful build is a pass.
- [`../tests/test_blake2s.c`](https://github.com/WeGoToMars/m0-crypto-lib/blob/main/tests/test_blake2s.c), run by `check.sh` step 7 (`tools/test_qemu.sh blake2s`): the release object on QEMU's Cortex-M0 against `hashlib.blake2s` digests at 204 lengths (0 to 200, 1024, 1025, 4096; `tests/blake2s_vectors.h`); one update at input and output offsets 0 to 3 with guard bytes around the output; chunked updates (nine chunk sizes from 1 to 200 bytes) with an empty `NULL` update after each chunk; and, through `tests/check_call8.S`, r4-r11 and SP restored and the stack depth within 4 and 160 bytes.
- [`tools/mutate_blake2s.py`](../tools/mutate_blake2s.py): 13 deliberate bugs in `src/blake2s_*.S`, each rebuilt and run through the QEMU tests, the executable checks and the BLAKE2s proofs. Whenever its workflow runs, the library's CI requires the proofs to reject all 13.
