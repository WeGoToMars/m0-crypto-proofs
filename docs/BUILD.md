# Build and verification workflow

Instructions for iterating on proofs, running sharded checks, and managing memory during Lake builds.

## Build iteration

Use one Lake invocation to build the modules you are changing:

```sh
lake build +M0Crypto.Release.PolyMac
lake build +M0Crypto.Thumb.ReleaseCheck
```

The second command runs the executable release checks in parallel shards. Their case descriptors are defined once; coverage checks require all 83 ChaCha20 cases, 45 AEAD cases and every shard, and the five pairwise guards remain required. Use a Lake build to refresh these checks after changing the artifact or model: executing the import root with `lake env lean` alone does not rebuild imports. The full `tools/check.sh` remains the release gate.

## Clean-build profiling

For a clean-build profile, run these commands in an isolated source copy with no existing `.lake/build`, preserving the working checkout's incremental cache:

```sh
/usr/bin/time -p lake --no-ansi build > build.log 2>&1
python3 -I tools/build_profile.py build.log --json profile.json
```

The profiler uses the current source graph, so run it in the source snapshot that produced the log.
