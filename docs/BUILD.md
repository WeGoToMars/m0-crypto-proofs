# Build and verification workflow

Instructions for iterating on proofs, running sharded checks, and managing memory during Lake builds.

## Workspaces

Each release asset has its own Lake workspace, `assets/chacha20poly1305`, `assets/blake2s`, `assets/x25519` and `assets/ed25519`. Each compiles the shared sources in `lean/` against that asset's artifact (for `ed25519`, one artifact module per build) and has its own `.lake` directory. Run Lake commands inside the workspace of the asset you are working on. A plain `lake build` there builds the asset root `M0Crypto.Assets.*`.

## Build iteration

Use one Lake invocation to build the modules you are changing:

```sh
cd assets/chacha20poly1305
lake build +M0Crypto.Release.Poly1305Mac
lake build +M0Crypto.Thumb.ReleaseCheck.ChaCha20Poly1305
```

The second command runs the asset's executable release checks in parallel shards (`M0Crypto.Thumb.ReleaseCheck.X25519` for X25519; for BLAKE2s, `Blake2sShard0` to `Blake2sShard3` and `Blake2sPairwise`, which the asset root imports). Their case descriptors are defined once; coverage checks require all 83 ChaCha20 cases, 45 AEAD cases and every shard, and the five pairwise guards remain required. Use a Lake build to refresh these checks after changing the artifact or model: executing the import root with `lake env lean` alone does not rebuild imports. The full `tools/check.sh` remains the release gate.

For a quick run of the same checks while developing, each asset's lakefile also has a native target: `lake build release_check && .lake/build/bin/release_check`, which runs much faster than the interpreted shards. The mutation scripts use it. The release gate uses it only for Ed25519 (`check.sh` step 4d), where one interpreted verify call would take longer than a module may. For the other assets the asset root runs the checks in Lean's interpreter.

## Memory-aware build runner

Lake starts one Lean process per core and does not account for memory; some modules of this tree need several gigabytes each. To keep the machine from thrashing while still building in parallel, run the build through the memory-aware runner, which takes the same arguments as `lake build`:

```sh
cd assets/chacha20poly1305
../../tools/membuild.py
../../tools/membuild.py +M0Crypto.Release.Poly1305Mac
```

It pauses the newest Lean processes when the build would exceed its budget (half of physical memory, or `M0C_BUILD_MEM_GB`) and resumes them as others finish. It does not change what Lake builds. Only when the Lean processes together hold more than `M0C_BUILD_KILL_GB` (default 1.5 times the budget) does it kill them and Lake and exit with status 137. `tools/check.sh` calls `lake build` directly.

`tools/comparator.sh` runs `lake comparator` and `lake check` for one asset at a time, with `--inadvisably-no-sandbox` where `bwrap` is missing (macOS). Run `leanchecker` only as `leanchecker --fresh MODULE`: without `--fresh`, on a prefix such as `M0Crypto`, it replays every module in parallel, each in its own environment, which can exhaust memory.

## Clean-build profiling

For a clean-build profile, run these commands in an isolated source copy with no existing `.lake/build`, preserving the working checkout's incremental cache:

```sh
/usr/bin/time -p lake --no-ansi build > build.log 2>&1
python3 -I tools/build_profile.py build.log --json profile.json
```

The profiler uses the current source graph, so run it in the source snapshot that produced the log. The longest import chain, not the core count, bounds a clean build. Import what a file uses rather than the file before it, so that independent proofs build in parallel.
