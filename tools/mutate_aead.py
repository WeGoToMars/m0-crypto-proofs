#!/usr/bin/env python3
"""Mutation check for the AEAD test image.

    python3 -I tools/mutate_aead.py

Applies each deliberate bug below to src/chacha20poly1305.S (part of the
release asset src/m0crypto_chacha20poly1305.S), one at a time, and runs both checks on it:

* QEMU: tools/test_qemu.sh;
* model: rebuild the asset (the library's tools/build_lib.sh chacha20poly1305), regenerate
  assets/chacha20poly1305/artifact/M0Crypto/Artifacts/Release.lean and build
  M0Crypto.Thumb.ReleaseCheck.ChaCha20Poly1305 (all access-audit and secret-residue shards)
  in that asset's workspace.

A check DETECTS a mutant only if it ran and reported a failing case. A build or
tool error is reported as such and fails the run; it never counts as detection.
Every mutant must be detected by at least one check, and mutants marked "model"
by the model check itself.

The source is restored byte for byte afterwards, also on error or Ctrl-C, its
sha256 is checked, and the library artifact is regenerated from it and checked
against its original content. Exit status 1 if any mutant is MISSED, does not
apply, does not change the library bytes, or hits a build/tool error. Takes about
a minute per mutant.
"""
import hashlib
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIB = os.path.abspath(os.environ.get("M0C_LIB", os.path.join(ROOT, "..")))
SRC = os.path.join(LIB, "src", "chacha20poly1305.S")

# (name, original text, mutated text[, "model"]). Each original must occur exactly
# once. "model": the model check must detect it (not only QEMU).
MUTANTS = [
    ("MAC mid shift 16->15", "    lsls r3, r2, #16\n", "    lsls r3, r2, #15\n"),
    ("drop a MAC term (h3 s1 in d0)", "    MAC  r11, P_S1\n    str  r0, [sp, #0]", "    str  r0, [sp, #0]"),
    ("no fold of h4 (c = 0)", "    adds r5, r4\n    movs r6, #0", "    movs r5, #0\n    movs r6, #0"),
    ("finish: no conditional subtract", "    movs r1, #5\n    ands r1, r0", "    movs r1, #0\n    ands r1, r0"),
    ("finish: drop carry into h4 test", "    ldr  r0, [r7, #P_H4]\n    adcs r0, r6\n    lsrs r0, r0, #2", "    ldr  r0, [r7, #P_H4]\n    lsrs r0, r0, #2"),
    ("clamp r0 with r1 mask", "    ldr  r4, =0x0fffffff", "    ldr  r4, =0x0ffffffc"),
    ("padbit ignored", "    mov  r5, r12                    /* MOV (high register form) keeps the carry */\n    adcs r4, r5", "    movs r5, #0\n    adcs r4, r5"),
    ("compare only 15 tag bytes", "    cmp  r4, #16\n    bne  5b", "    cmp  r4, #15\n    bne  5b"),
    ("decrypt before verify", "    bl   .Lm0c_poly1305_finish        /* expected tag -> BLK[0..15] */", "    bl   .Lm0c_poly1305_finish        /* expected tag -> BLK[0..15] */\n    CRYPT"),
    ("no CLEAR_FRAME in encrypt", "    bl   .Lm0c_poly1305_finish\n    CLEAR_FRAME", "    bl   .Lm0c_poly1305_finish"),
    ("poly_blocks keeps T frame", "    str  r0, [sp, #12]\n    str  r0, [sp, #16]", "    str  r0, [sp, #16]"),
    ("length block swaps aad_len/len", "    ldr  r0, [sp, #A_AADLEN]\n    str  r0, [sp, #BLK+0]", "    ldr  r0, [sp, #S_LEN]\n    str  r0, [sp, #BLK+0]"),
    ("partial block: skip padding zeroing", "    str  r0, [sp, #BLK+12]\n    add  r1, sp, #BLK\n    movs r2, #0\n2:", "    add  r1, sp, #BLK\n    movs r2, #0\n2:"),
    ("encrypt MACs plaintext", "    ldr  r4, [sp, #S_OUT]           /* MAC the ciphertext as written */", "    ldr  r4, [sp, #S_IN]"),
    # Paths that the mutants above do not reach.
    ("blocks leaves h4 in LR", "    movs r0, #0\n    mov  lr, r0\n    str  r0, [sp, #0]", "    movs r0, #0\n    str  r0, [sp, #0]"),
    ("decrypt leaves expected_tag[15] in r5", "    movs r5, #0                     /* expected_tag[15]: do not leave it for CRYPT to save */\n", ""),
    # Over-read: one word past the 16-byte block on the aligned path. Results are
    # unchanged, so only the model's access audit can see it.
    ("aligned blocks over-read one word", "    ldmia r6!, {r0-r3}             /* public alignment; no over-read */\n", "    ldmia r6!, {r0-r3}             /* public alignment; no over-read */\n    ldr  r4, [r6]\n", "model"),
    # Same-size clearing removals: the model detects them through its residue check
    # (the same stack window for different secrets), not its register or access checks.
    ("CLEAR_FRAME stores become moves", "4:  str  r0, [r1]\n    adds r1, #4\n    subs r2, #1\n    bne  4b", "4:  mov  r0, r0\n    adds r1, #4\n    subs r2, #1\n    bne  4b", "model"),
    ("expected_tag[15] clear becomes mov r5, r5", "    movs r5, #0                     /* expected_tag[15]: do not leave it for CRYPT to save */\n", "    mov  r5, r5\n", "model"),
]

WORKSPACE = os.path.join(ROOT, "assets", "chacha20poly1305")
ARTIFACT = os.path.join(WORKSPACE, "artifact", "M0Crypto", "Artifacts", "Release.lean")


def rebuild():
    """Build the library from the (mutated) source and regenerate the Lean artifact."""
    b = subprocess.run([os.path.join(LIB, "tools", "build_lib.sh"), "chacha20poly1305"],
                       capture_output=True, text=True)
    if b.returncode:
        return b
    return subprocess.run([sys.executable, "-I", os.path.join(ROOT, "tools", "extract_release.py"),
                           os.path.join(LIB, "build", "lib", "chacha20poly1305", "m0crypto_chacha20poly1305.o"),
                           ARTIFACT],
                          capture_output=True, text=True)


def model_check():
    """Rebuild the library artifact from the current source and run the release
    model check. Returns (result, message), result in PASS / DETECTED / ERROR."""
    b = rebuild()
    if b.returncode:
        return "ERROR", "library build failed: " + (b.stdout + b.stderr).strip()[-200:]
    if open(ARTIFACT, "rb").read() == ORIG_ARTIFACT:
        return "ERROR", "mutant did not change the library bytes"
    # Building the root invalidates every shard when the artifact changes.
    # `lake env lean` on an import-only root would reuse stale compiled checks.
    r = subprocess.run(["lake", "build", "+M0Crypto.Thumb.ReleaseCheck.ChaCha20Poly1305"],
                       cwd=WORKSPACE, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip().splitlines()
    failed = next((l for l in out if "release check FAILED" in l), None)
    if r.returncode == 0 and failed is None:
        return "PASS", out[-1] if out else ""
    if r.returncode != 0 and failed is not None:
        return "DETECTED", failed
    return "ERROR", "model check did not run cleanly: " + " | ".join(out[-3:])


ORIG_ARTIFACT = b""


def qemu_check():
    """Returns (result, failing check kinds), result in PASS / DETECTED / ERROR."""
    p = subprocess.run([os.path.join(LIB, "tools", "test_qemu.sh")],
                       capture_output=True, text=True)
    out = p.stdout + p.stderr
    aead = out.split("== test_aead")[-1] if "== test_aead" in out else ""
    fails = [l for l in aead.splitlines() if l.startswith("FAIL ")]
    kinds = sorted({l.split(" 0x")[0][5:] for l in fails})
    if p.returncode == 0 and not fails:
        return "PASS", []
    if p.returncode != 0 and fails:
        return "DETECTED", kinds
    return "ERROR", [out.strip()[-200:]]


def main():
    global ORIG_ARTIFACT
    orig = open(SRC, "rb").read()
    art = ORIG_ARTIFACT = open(ARTIFACT, "rb").read()
    digest = hashlib.sha256(orig).hexdigest()
    text = orig.decode()
    print(f"source {os.path.relpath(SRC, LIB)} sha256 {digest}")
    bad = 0
    try:
        for name, a, b, *flags in MUTANTS:
            if text.count(a) != 1:
                print(f"NOAPPLY   {name}: original text occurs {text.count(a)} times")
                bad += 1
                continue
            open(SRC, "w").write(text.replace(a, b))
            q, kinds = qemu_check()
            m, msg = model_check()
            if "ERROR" in (q, m):
                res = "TOOL-ERR"
            elif "model" in flags and m != "DETECTED":
                res = "MISSED"
            elif "DETECTED" in (q, m):
                res = "DETECTED"
            else:
                res = "MISSED"
            bad += res != "DETECTED"
            print(f"{res:9} {name}\n          qemu {q} {kinds[:4]}\n          model {m} {msg[:160]}",
                  flush=True)
    finally:
        open(SRC, "wb").write(orig)
        rebuild()
    assert hashlib.sha256(open(SRC, "rb").read()).hexdigest() == digest
    assert open(ARTIFACT, "rb").read() == art, "library artifact not restored"
    print(f"restored, sha256 {digest}; library artifact regenerated and unchanged")
    print(f"{len(MUTANTS) - bad}/{len(MUTANTS)} detected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
