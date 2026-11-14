#!/usr/bin/env python3
"""Run the library's test vectors against the Lean specification.

The library's on-target tests compare the code with generated headers of external vectors:
  tests/aead_vectors.h    RFC 8439 §2.8.2, Wycheproof and pyca/cryptography vectors; run by
                          lean/SpecVectors.lean (`M0Crypto.Spec.Aead`) in assets/chacha20poly1305
  tests/chacha20_vectors.h  pyca/cryptography ChaCha20 at chosen counters (with the counter rule
                          `counterOk` at the 2^32 boundary) and AEAD tags for AAD and messages
                          longer than 65,535 bytes; run by lean/SpecVectors.lean
  tests/x25519_vectors.h  RFC 7748 §5.2 and §6.1 and Wycheproof vectors; run by
                          lean/SpecVectorsX25519.lean (`M0Crypto.Spec.X25519`) in assets/x25519
  tests/blake2s_vectors.h BLAKE2s-256 digests from Python hashlib of a byte pattern at 204
                          lengths; run by lean/SpecVectorsBlake2s.lean (`M0Crypto.Spec.Blake2s`)
                          in assets/blake2s
This script hands the same vectors to the Lean runner of the header's asset. The specification
is then tested directly against independent implementations, not only through the code.

Usage: spec_vectors.py HEADER [HEADER...]   (headers of one asset)
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def table(text, name):
    """The initialiser rows of the C array `name`, as lists of integers."""
    body = re.search(name + r"\[\] = \{(.*?)\n\};", text, re.S).group(1)
    return [[int(x.strip().rstrip("u"), 0) for x in row.split(",")]
            for row in re.findall(r"\{([^{}]*)\}", body)]


def x25519_lines(text):
    """One `x25519 SOURCE ID SCALAR POINT SHARED` line per row of x25519_vecs."""
    count = int(re.search(r"#define X25519_VEC_COUNT (\d+)", text).group(1))
    body = re.search(r"x25519_vecs\[X25519_VEC_COUNT\] = \{(.*?)\n\};", text, re.S).group(1)
    rows = re.findall(r"\{\{([^{}]*)\}, \{([^{}]*)\}, \{([^{}]*)\}, (\d+), (\d+)\}", body)
    if len(rows) != count:
        sys.exit(f"x25519_vecs: {len(rows)} rows, X25519_VEC_COUNT {count}")
    hx = lambda row: bytes(int(x, 0) for x in row.split(",")).hex()
    return [" ".join(["x25519", src, i, hx(k), hx(u), hx(r)]) for k, u, r, src, i in rows]


def blake2s_lines(text):
    """One `blake2s MESSAGE DIGEST` line per row of b2v_digest; the message is the first
    b2v_len[i] bytes of the header's B2V_PATTERN."""
    a, b = map(int, re.search(r"#define B2V_PATTERN\(i\) \(\(uint8_t\)\(\(i\) \* (\d+)u \+ (\d+)u\)\)",
                              text).groups())
    count = int(re.search(r"#define B2V_COUNT (\d+)", text).group(1))
    lens = [int(x) for x in re.search(r"b2v_len\[B2V_COUNT\] = \{([^}]*)\}", text).group(1).split(",")]
    body = re.search(r"b2v_digest\[B2V_COUNT\]\[32\] = \{(.*?)\n\};", text, re.S).group(1)
    digests = [bytes(int(x, 0) for x in row.split(",")) for row in re.findall(r"\{([^{}]*)\}", body)]
    if not len(lens) == len(digests) == count:
        sys.exit(f"blake2s vectors: {len(lens)} lengths, {len(digests)} digests, B2V_COUNT {count}")
    msg = lambda n: bytes((i * a + b) & 0xFF for i in range(n)).hex() or "-"
    return [f"blake2s {msg(n)} {d.hex()}" for n, d in zip(lens, digests)]


def chacha20_lines(text):
    """`chacha`/`counter` lines per row of chacha_vecs, an `aead-tag` line per row of
    aead_long_vecs. Messages and AAD are the header's CV_PATTERN(s, i)."""
    a, b, c = map(int, re.search(r"#define CV_PATTERN\(s, i\) \(\(uint8_t\)\(\(i\) \* (\d+)u \+ "
                                 r"\(\(i\) >> 8\) \* (\d+)u \+ \(s\) \* (\d+)u\)\)", text).groups())
    pat = lambda s, n: bytes((i * a + (i >> 8) * b + s * c) & 0xFF for i in range(n)).hex() or "-"
    arr = lambda name: bytes(int(x, 0) for x in re.search(
        name + r"\[\d*\] = \{(.*?)\};", text, re.S).group(1).split(","))
    key, nonce, out = arr("cv_key").hex(), arr("cv_nonce").hex(), arr("cv_out")
    maxout = int(re.search(r"#define CV_MAXOUT (\d+)", text).group(1))
    lines = []
    for counter, n, result, off in table(text, "chacha_vecs"):
        if result == 0 and n <= maxout:
            lines.append(" ".join(["chacha", key, nonce, str(counter), pat(0, n),
                                   out[off:off + n].hex() or "-"]))
        else:
            lines.append(" ".join(["counter", str(int(result == 0)), str(counter), str(n)]))
    body = re.search(r"aead_long_vecs\[\] = \{(.*?)\n\};", text, re.S).group(1)
    for alen, n, tag in re.findall(r"\{(\d+)u, (\d+)u, \{([^{}]*)\}\}", body):
        tag = bytes(int(x, 0) for x in tag.split(","))
        lines.append(" ".join(["aead-tag", key, nonce, pat(1, int(alen)), pat(0, int(n)), tag.hex()]))
    return lines


def run(lean_file, asset, lines):
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write("\n".join(lines) + "\n")
        f.flush()
        return subprocess.run(["lake", "env", "lean", "--run", str(ROOT / lean_file), f.name],
                              cwd=ROOT / "assets" / asset).returncode


def aead_lines(text):
    blob = bytes(int(x, 16) for x in re.findall(
        r"0x[0-9a-f]{2}", re.search(r"vec_blob\[\] = \{(.*?)\n\};", text, re.S).group(1)))

    def hx(off, n):
        return blob[off:off + n].hex() or "-"

    lines = []
    for key, nonce, aad, alen, inp, n, ct, tag, valid, _source in table(text, "aead_vecs"):
        lines.append(" ".join(["aead", str(valid), hx(key, 32), hx(nonce, 12), hx(aad, alen),
                               hx(inp, n), hx(ct, n), hx(tag, 16)]))
    for key, msg, n, tag in table(text, "poly_vecs"):
        lines.append(" ".join(["poly", hx(key, 32), hx(msg, n), hx(tag, 16)]))
    return lines


def main(argv):
    if len(argv) < 2:
        sys.exit(__doc__)
    runners = set()
    lines = []
    for header in argv[1:]:
        text = Path(header).read_text()
        if "x25519_vecs" in text:
            runners.add(("lean/SpecVectorsX25519.lean", "x25519"))
            lines += x25519_lines(text)
        elif "b2v_digest" in text:
            runners.add(("lean/SpecVectorsBlake2s.lean", "blake2s"))
            lines += blake2s_lines(text)
        elif "chacha_vecs" in text:
            runners.add(("lean/SpecVectors.lean", "chacha20poly1305"))
            lines += chacha20_lines(text)
        else:
            runners.add(("lean/SpecVectors.lean", "chacha20poly1305"))
            lines += aead_lines(text)
    if len(runners) != 1:
        sys.exit("spec_vectors: the headers belong to different assets")
    sys.exit(run(*runners.pop(), lines))


if __name__ == "__main__":
    main(sys.argv)
