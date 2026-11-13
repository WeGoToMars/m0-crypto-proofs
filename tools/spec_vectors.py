#!/usr/bin/env python3
"""Run the library's test vectors against the Lean specification.

The library's on-target tests compare the code with tests/aead_vectors.h: RFC 8439 §2.8.2,
Wycheproof and pyca/cryptography vectors. This script hands the same vectors to
lean/SpecVectors.lean, which evaluates `M0Crypto.Spec.Aead` on each. The specification is
then tested directly against independent implementations, not only through the code.

Usage: spec_vectors.py HEADER
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
    return [[int(x, 0) for x in row.split(",")] for row in re.findall(r"\{([^{}]*)\}", body)]


def main(argv):
    if len(argv) != 2:
        sys.exit(__doc__)
    text = Path(argv[1]).read_text()
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
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write("\n".join(lines) + "\n")
        f.flush()
        sys.exit(subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "lean/SpecVectors.lean"), f.name],
                                cwd=ROOT / "assets" / "chacha20poly1305").returncode)


if __name__ == "__main__":
    main(sys.argv)
