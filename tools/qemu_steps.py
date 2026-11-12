#!/usr/bin/env python3
"""Compare the Lean machine model with QEMU, instruction by instruction.

For selected calls of the library functions in the library's QEMU test images, this script
single-steps QEMU through the call and runs the Lean model (lean/StepTrace.lean) from the
same entry state: the registers, flags and memory QEMU has at the first instruction. After
every instruction, r0-r15 and the N, Z, C, V flags must be equal, and at the return the RAM
must be equal. The model's decoder and executor are thereby checked against an independent
ARMv6-M implementation on every instruction these calls execute.

It checks the model, not timing, and only the instructions the traced calls reach; the
summary line says how many of the artifact's instructions that is.

QEMU is driven through its gdb stub (remote serial protocol over a Unix socket).

Usage: qemu_steps.py QEMU NM TEXT_BIN ELF FUNCTION[,FUNCTION...] [ELF FUNCTIONS ...]
  TEXT_BIN  the release artifact (build/lib/text.bin); the image must contain these bytes
  ELF       a test image (build/test/*.elf)
  FUNCTION  an exported function to trace in that image
"""
import os
import socket
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RAM = (0x20000000, 0x4000)   # QEMU "microbit": 16 KiB of RAM
CALLS = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]   # which calls to trace


class Gdb:
    """Minimal gdb remote-protocol client."""

    def __init__(self, path):
        self.sock = socket.socket(socket.AF_UNIX)
        self.sock.settimeout(120)
        self.sock.connect(path)
        self.buf = b""

    def cmd(self, text):
        body = text.encode()
        self.sock.sendall(b"$" + body + b"#" + b"%02x" % (sum(body) % 256))
        while True:
            start, end = self.buf.find(b"$"), self.buf.find(b"#")
            if 0 <= start < end and len(self.buf) >= end + 3:
                reply, self.buf = self.buf[start + 1:end], self.buf[end + 3:]
                self.sock.sendall(b"+")
                return reply.decode()
            data = self.sock.recv(65536)
            if not data:
                raise EOFError   # QEMU exited: the test program ended
            self.buf += data

    def regs(self):
        """r0-r15 and the flags as the model prints them."""
        raw = bytes.fromhex(self.cmd("g"))
        words = [int.from_bytes(raw[4 * i:4 * i + 4], "little") for i in range(len(raw) // 4)]
        xpsr = words[-1]
        return " ".join(f"{w:08x}" for w in words[:16]) + " " + f"{xpsr >> 28:04b}"

    def read(self, addr, size):
        out = b""
        while len(out) < size:
            out += bytes.fromhex(self.cmd(f"m{addr + len(out):x},{min(1024, size - len(out)):x}"))
        return out

    def run_to(self, addrs):
        """Continue to one of `addrs`; False if the program ends first."""
        try:
            for a in addrs:
                if self.cmd(f"Z1,{a:x},2") != "OK":
                    sys.exit("qemu_steps: cannot set a breakpoint")
            reply = self.cmd("c")
            for a in addrs:
                self.cmd(f"z1,{a:x},2")
        except EOFError:
            return False
        return reply.startswith("T05") or reply.startswith("S05")


def symbols(nm, elf):
    out = subprocess.run([nm, elf], check=True, capture_output=True, text=True).stdout
    return {f[2]: int(f[0], 16) for f in (l.split() for l in out.splitlines()) if len(f) == 3}


def trace_image(qemu, nm, text, elf, functions, cases, qemu_states):
    """Single-step the selected calls; append the model's input and QEMU's states."""
    syms = symbols(nm, elf)
    size = syms["_etext"]
    tmp = tempfile.mkdtemp()
    path = os.path.join(tmp, "gdb")
    proc = subprocess.Popen(
        [qemu, "-machine", "microbit", "-nographic", "-monitor", "none", "-serial", "none",
         "-semihosting-config", "enable=on,target=native", "-kernel", elf, "-S",
         "-chardev", f"socket,id=g,path={path},server=on,wait=on", "-gdb", "chardev:g"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        while not os.path.exists(path):
            if proc.poll() is not None:
                sys.exit("qemu_steps: QEMU did not start")
        gdb = Gdb(path)
        flash = gdb.read(0, size)
        base = flash.find(text)
        if base < 0:
            sys.exit(f"qemu_steps: {elf} does not contain the release artifact")
        cases.append(f"flash 0 {flash.hex()}")
        pcs = set()
        entries = {syms[fn] & ~1: fn for fn in functions}
        calls = dict.fromkeys(functions, 0)
        while min(calls.values()) < CALLS[-1] and gdb.run_to(entries):
            state = gdb.regs()
            words = state.split()
            fn = entries[int(words[15], 16)]
            calls[fn] += 1
            if calls[fn] not in CALLS:
                gdb.cmd("s")   # leave the entry before the breakpoints are set again
                continue
            name = f"{Path(elf).stem}:{fn}:{calls[fn]}"
            stop = int(words[14], 16) & ~1
            cases += [f"case {name}", f"ram {RAM[0]:x} {gdb.read(*RAM).hex()}",
                      f"regs {state}", f"stop {stop:x}"]
            steps = []
            while int(words[15], 16) != stop:
                pcs.add(int(words[15], 16) - base)
                gdb.cmd("s")
                state = gdb.regs()
                words = state.split()
                steps.append(state)
            qemu_states[name] = (steps, gdb.read(*RAM).hex())
        if 0 in calls.values():
            sys.exit(f"qemu_steps: {elf} never calls {[f for f in calls if not calls[f]]}")
        return pcs
    finally:
        proc.kill()
        proc.wait()
        if os.path.exists(path):
            os.unlink(path)
        os.rmdir(tmp)


def main(argv):
    if len(argv) < 6 or len(argv) % 2:
        sys.exit(__doc__)
    qemu, nm, text = argv[1], argv[2], Path(argv[3]).read_bytes()
    cases, qemu_states, pcs = [], {}, set()
    for elf, functions in zip(argv[4::2], argv[5::2]):
        pcs |= trace_image(qemu, nm, text, elf, functions.split(","), cases, qemu_states)
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write("\n".join(cases) + "\n")
        f.flush()
        model = subprocess.run(["lake", "env", "lean", "--run", "lean/StepTrace.lean", f.name],
                               cwd=ROOT, check=True, capture_output=True, text=True).stdout
    model_states, name = {}, None
    for line in model.splitlines():
        if line.startswith("case "):
            name = line[5:]
            model_states[name] = []
        else:
            model_states[name].append(line)
    total = 0
    for name, (steps, ram) in qemu_states.items():
        got = model_states.get(name, [])
        for i, (want, have) in enumerate(zip(steps + ["ram " + ram], got)):
            if want != have:
                before = steps[i - 1] if i else "(entry)"
                sys.exit(f"qemu_steps: {name}: the model and QEMU differ after instruction {i + 1}\n"
                         f"  state before: {before}\n  QEMU:  {want[:160]}\n  model: {have[:160]}")
        if len(got) != len(steps) + 1:
            sys.exit(f"qemu_steps: {name}: QEMU ran {len(steps)} instructions, the model printed "
                     f"{len(got)} lines; last: {got[-1][:160] if got else ''}")
        total += len(steps)
    instructions = len({p for p in pcs if 0 <= p < len(text)})
    print(f"ok: model and QEMU agree after each of {total} instructions in {len(qemu_states)} calls "
          f"({instructions} distinct instructions of the artifact), and on the final RAM")


if __name__ == "__main__":
    main(sys.argv)
