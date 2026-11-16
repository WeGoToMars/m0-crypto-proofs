#!/usr/bin/env python3
"""Regression checks for fixture identity versus ELF container provenance."""
import importlib.util
import pathlib
import struct
import subprocess
import sys
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "extract_artifact", pathlib.Path(__file__).with_name("extract_artifact.py"))
extractor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extractor)


def elf(code=b"\x00\xbf", base=0x20000000, comment=b"Linker: Homebrew LLD 23.1.4", section=b".text"):
    """A minimal linked ARM ELF with one Thumb function and linker metadata."""
    strings = b"\0frag\0"
    names = b"\0" + section + b"\0.symtab\0.strtab\0.shstrtab\0.comment\0"
    symbols = bytes(16) + struct.pack("<IIIBBH", 1, base | 1, len(code), 0x12, 0, 1)
    data = bytearray(52)
    headers = [bytes(40)]
    for name, typ, flags, addr, contents, link, entsize in [
        (section, 1, 6, base, code, 0, 0),
        (b".symtab", 2, 0, 0, symbols, 3, 16),
        (b".strtab", 3, 0, 0, strings, 0, 0),
        (b".shstrtab", 3, 0, 0, names, 0, 0),
        (b".comment", 1, 0, 0, comment + b"\0", 0, 0),
    ]:
        data.extend(bytes(-len(data) % 4))
        offset = len(data)
        data.extend(contents)
        headers.append(struct.pack("<IIIIIIIIII", names.index(name + b"\0"), typ,
                                   flags, addr, offset, len(contents), link, 0, 4, entsize))
    data.extend(bytes(-len(data) % 4))
    shoff = len(data)
    data.extend(b"".join(headers))
    data[:16] = b"\x7fELF\x01\x01\x01" + bytes(9)
    struct.pack_into("<HHIIIIIHHHHHH", data, 16, 2, 40, 1, base | 1, 0, shoff, 0,
                     52, 0, 0, 40, len(headers), 4)
    return bytes(data)


class FixtureCheck(unittest.TestCase):
    def test_identity(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = pathlib.Path(tmp) / "fixture.elf"
            artifact = pathlib.Path(tmp) / "Fixture.lean"
            source.write_bytes(elf())
            addr, code, sha, section = extractor.extract(source, "frag")
            artifact.write_text(extractor.render("Fixture", "frag", addr, code, sha, section))
            original = artifact.read_bytes()
            for changes, matches in [({}, True), ({"comment": b"Linker: LLD 23.1.4"}, True),
                                     ({"code": b"\x01\x20"}, False),
                                     ({"base": addr + 2}, False),
                                     ({"section": b".other"}, False)]:
                with self.subTest(changes=changes):
                    source.write_bytes(elf(**changes))
                    result = subprocess.run([sys.executable, str(pathlib.Path(extractor.__file__)),
                                             str(source), "frag", "Fixture", str(artifact), "--check"],
                                            capture_output=True, text=True)
                    self.assertEqual(result.returncode == 0, matches, result.stdout + result.stderr)
                    self.assertEqual(artifact.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
