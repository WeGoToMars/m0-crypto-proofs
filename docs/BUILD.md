# Build and verification workflow

Instructions for iterating on proofs, running sharded checks, and managing memory during Lake builds.

## Workspaces

Each release asset has its own Lake workspace, `assets/chacha20poly1305`, `assets/blake2s` and `assets/x25519`. Each compiles the shared sources in `lean/` against that asset's artifact and has its own `.lake` directory. Run Lake commands inside the workspace of the asset you are working on. A plain `lake build` there builds the asset root `M0Crypto.Assets.*`.

## Build iteration

Use one Lake invocation to build the modules you are changing:

```sh
cd assets/chacha20poly1305
lake build +M0Crypto.Release.Poly1305Mac
lake build +M0Crypto.Thumb.ReleaseCheck.ChaCha20Poly1305
```

The second command runs the asset's executable release checks in parallel shards (`M0Crypto.Thumb.ReleaseCheck.X25519` for X25519; for BLAKE2s, `Blake2sShard0` to `Blake2sShard3` and `Blake2sPairwise`, which the asset root imports). Their case descriptors are defined once; coverage checks require all 83 ChaCha20 cases, 45 AEAD cases and every shard, and the five pairwise guards remain required. Use a Lake build to refresh these checks after changing the artifact or model: executing the import root with `lake env lean` alone does not rebuild imports. The full `tools/check.sh` remains the release gate.

## Memory-aware build runner

Lake starts one Lean process per core and does not account for memory; four modules of this tree need about 5 GB each. To keep the machine from thrashing while still building in parallel, run the build through the memory-aware runner, which takes the same arguments as `lake build`:

```sh
cd assets/chacha20poly1305
../../tools/membuild.py
../../tools/membuild.py +M0Crypto.Release.Poly1305Mac
```

It pauses the newest Lean processes when the build would exceed its budget (half of physical memory, or `M0C_BUILD_MEM_GB`) and resumes them as others finish. It kills nothing and does not change what Lake builds. `tools/check.sh` calls `lake build` directly.

## Clean-build profiling

For a clean-build profile, run these commands in an isolated source copy with no existing `.lake/build`, preserving the working checkout's incremental cache:

```sh
/usr/bin/time -p lake --no-ansi build > build.log 2>&1
python3 -I tools/build_profile.py build.log --json profile.json
```

The profiler uses the current source graph, so run it in the source snapshot that produced the log. One clean build of the 0.2.0 proofs (ChaCha20-Poly1305 only) took 162 s wall time on an 18-core Apple M5 Pro; the longest import chain (158 s) bounds it, not the core count. Import what a file uses rather than the file before it, so that independent proofs build in parallel.
