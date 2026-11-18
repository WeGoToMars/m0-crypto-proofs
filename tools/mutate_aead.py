#!/usr/bin/env python3
"""Mutation check for the AEAD test image.

    python3 -I tools/mutate_aead.py [--cert] [--only NAME ...]

Applies each deliberate bug below to src/chacha20poly1305.S (part of the
release asset src/m0crypto_chacha20poly1305.S), one at a time, and runs both checks on it:

* QEMU: tools/test_qemu.sh;
* model: rebuild the asset (the library's tools/build_lib.sh chacha20poly1305), regenerate
  assets/chacha20poly1305/artifact/M0Crypto/Artifacts/Release.lean and run the asset's native
  `release_check` executable: the access-audit, secret-residue and pairwise checks that the
  proofs build runs in Lean's interpreter (M0Crypto.Thumb.ReleaseCheck.ChaCha20Poly1305).

* certificate (--cert, mutants marked "cert" only): build the decryption constant-time
  certificate (M0Crypto.Release.ConstantTime.AeadDecryptEntry) on the mutated artifact. These
  mutants keep the code size and every result, so only the certificate can reject them.
  Without --cert they are skipped.

A check DETECTS a mutant only if it ran and reported a failing case; the certificate does
when Lean reports an error in its module (tools/mutation_run.py). A build or tool error, a
killed or crashed worker and a timeout are reported as such and fail the run; they never count
as detection. With --cert the certificate must first build on the unmutated source.
Every mutant must be detected by at least one check, mutants marked "model"
by the model check itself and mutants marked "cert" by the certificate. --only runs the
mutants whose names contain one of the given substrings; each substring must match a mutant,
and a run in which no mutant runs fails.

The source is restored byte for byte afterwards, also on error or Ctrl-C, its
sha256 is checked, and the library artifact is regenerated from it and checked
against its original content. Exit status 1 if any mutant is MISSED, does not
apply, does not change the library bytes, or hits a build/tool error.
"""
import argparse
import hashlib
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))   # python3 -I leaves the script directory out
from native_check import native_check
from mutation_run import lake_build, lean_verdict, select
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
    # Timing: leave the tag comparison at the first differing byte. The dead `movs r0, #0`
    # makes room, so the code keeps its size, and every result is unchanged. The pairwise
    # check's two rejected calls both differ at byte 0, so their traces stay equal.
    ("tag compare exits at the first differing byte",
     "    orrs r3, r0\n    adds r4, #1\n    cmp  r4, #16\n    bne  5b\n"
     "    movs r5, #0                     /* expected_tag[15]: do not leave it for CRYPT to save */\n"
     "    movs r0, #0                     /* last byte difference */\n",
     "    orrs r3, r0\n    bne  6f\n    adds r4, #1\n    cmp  r4, #16\n    bne  5b\n"
     "6:  movs r5, #0                     /* expected_tag[15]: do not leave it for CRYPT to save */\n",
     "cert"),
]
CERT_MODULES = ["M0Crypto.Release.ConstantTime.AeadDecryptEntry"]

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
    return native_check(WORKSPACE)


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


def cert_check(timeout):
    """Build the decryption certificate on the current artifact. Returns (result, message):
    DETECTED only when Lean reports an error in the certificate module itself."""
    return lean_verdict(lake_build(WORKSPACE, CERT_MODULES, timeout), CERT_MODULES)


def main():
    global ORIG_ARTIFACT
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--cert", action="store_true", help="also build the certificate for \"cert\" mutants")
    ap.add_argument("--only", nargs="*", default=None, help="substrings of mutant names")
    ap.add_argument("--timeout", type=int, default=3600, help="seconds for each certificate build")
    args = ap.parse_args()
    names = select([m[0] for m in MUTANTS], args.only)
    mutants = [m for m in MUTANTS if m[0] in names]
    ran = sum(1 for m in mutants if args.cert or "cert" not in m[3:])
    if not ran:
        sys.exit("no selected mutant runs (certificate mutants need --cert)")
    orig = open(SRC, "rb").read()
    art = ORIG_ARTIFACT = open(ARTIFACT, "rb").read()
    digest = hashlib.sha256(orig).hexdigest()
    text = orig.decode()
    print(f"source {os.path.relpath(SRC, LIB)} sha256 {digest}")
    if args.cert and any("cert" in m[3:] for m in mutants):
        c, cmsg = cert_check(args.timeout)
        if c != "PASS":
            sys.exit(f"baseline certificate does not build: {c} {cmsg}")
        print("baseline: the certificate builds")
    bad = 0
    try:
        for name, a, b, *flags in mutants:
            if "cert" in flags and not args.cert:
                print(f"SKIPPED   {name}: needs --cert")
                continue
            if text.count(a) != 1:
                print(f"NOAPPLY   {name}: original text occurs {text.count(a)} times")
                bad += 1
                continue
            open(SRC, "w").write(text.replace(a, b))
            q, kinds = qemu_check()
            m, msg = model_check()
            c, cmsg = cert_check(args.timeout) if "cert" in flags else ("not run", "")
            if "ERROR" in (q, m, c):
                res = "TOOL-ERR"
            elif "cert" in flags:
                res = "DETECTED" if c == "DETECTED" else "MISSED"
                if "DETECTED" in (q, m):
                    print(f"NOTE      {name}: expected QEMU and the model check to miss it")
            elif "model" in flags and m != "DETECTED":
                res = "MISSED"
            elif "DETECTED" in (q, m):
                res = "DETECTED"
            else:
                res = "MISSED"
            bad += res != "DETECTED"
            print(f"{res:9} {name}\n          qemu {q} {kinds[:4]}\n          model {m} {msg[:160]}"
                  + (f"\n          certificate {c} {cmsg[:160]}" if "cert" in flags else ""), flush=True)
    finally:
        open(SRC, "wb").write(orig)
        rebuild()
    assert hashlib.sha256(open(SRC, "rb").read()).hexdigest() == digest
    assert open(ARTIFACT, "rb").read() == art, "library artifact not restored"
    print(f"restored, sha256 {digest}; library artifact regenerated and unchanged")
    print(f"{ran - bad}/{ran} detected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
