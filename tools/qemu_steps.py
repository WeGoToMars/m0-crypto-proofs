#!/usr/bin/env python3
"""Compare the Lean machine model with QEMU, instruction by instruction.

For selected calls of the library functions in the library's QEMU test images, this script
single-steps QEMU through the call and runs the Lean model (lean/StepTrace.lean) from the
same entry state: the registers, flags and memory QEMU has at the first instruction. After
every instruction, r0-r15 and the N, Z, C, V flags must be equal, and at the return the RAM
must be equal. The model's decoder and executor are thereby checked against an independent
ARMv6-M implementation on every instruction these calls execute.

The selected calls are calls 1, 2, 3, 5, 8, ..., 987 of each listed function (a call made
inside a call of a listed function is part of that call), and then, from a second run of each
image with a breakpoint on every artifact address those calls did not execute, each call
that executes one. So every instruction of the artifact that the images execute is compared;
artifact code running outside a call of the listed functions is an error. The summary line
gives the number of distinct instructions. It checks the model, not timing.

QEMU is driven through its gdb stub (remote serial protocol over a Unix socket).

Usage: qemu_steps.py [--cover OBJECT] ASSET QEMU NM TEXT_BIN ELF FUNCTION[,FUNCTION...] [ELF FUNCTIONS ...]
  --cover   the asset's release object: the calls must execute exactly its instructions, every
            instruction llvm-objdump lists except alignment padding (see `padding`)
  ASSET     the release asset whose built Lake workspace (assets/ASSET) runs the model
  TEXT_BIN  the asset's release artifact (build/lib/ASSET/text.bin); the image must contain
            these bytes
  ELF       a test image (build/test/*.elf)
  FUNCTION  a function to trace in that image: exported, or an internal routine the image
            calls directly
"""
import os
import socket
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))   # python3 -I leaves the script directory out
from check_listing import objdump_lines  # noqa: E402
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


class Image:
    """One test image under QEMU, stopped at its first instruction."""

    def __init__(self, qemu, nm, text, elf):
        self.syms = symbols(nm, elf)
        self.tmp = tempfile.mkdtemp()
        self.path = os.path.join(self.tmp, "gdb")
        self.proc = subprocess.Popen(
            [qemu, "-machine", "microbit", "-nographic", "-monitor", "none", "-serial", "none",
             "-semihosting-config", "enable=on,target=native", "-kernel", elf, "-S",
             "-chardev", f"socket,id=g,path={self.path},server=on,wait=on", "-gdb", "chardev:g"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        while not os.path.exists(self.path):
            if self.proc.poll() is not None:
                sys.exit("qemu_steps: QEMU did not start")
        self.gdb = Gdb(self.path)
        self.flash = self.gdb.read(0, self.syms["_etext"])
        self.base = self.flash.find(text)
        if self.base < 0:
            sys.exit(f"qemu_steps: {elf} does not contain the release artifact")
        self.bps = set()

    def close(self):
        self.proc.kill()
        self.proc.wait()
        if os.path.exists(self.path):
            os.unlink(self.path)
        os.rmdir(self.tmp)

    def pc(self):
        return int(self.gdb.regs().split()[15], 16)

    def run_to(self, addrs):
        """Continue to one of `addrs` (after leaving the current instruction); its PC, or None
        if the program ends first."""
        try:
            for a in self.bps - addrs:
                self.gdb.cmd(f"z1,{a:x},2")
            for a in addrs - self.bps:
                if self.gdb.cmd(f"Z1,{a:x},2") != "OK":
                    sys.exit("qemu_steps: cannot set a breakpoint")
            self.bps = set(addrs)
            self.gdb.cmd("s")
            pc = self.pc()
            if pc in addrs:
                return pc
            reply = self.gdb.cmd("c")
        except (EOFError, OSError):   # QEMU exited: the test program ended
            return None
        if not (reply.startswith("T05") or reply.startswith("S05")):
            return None
        return self.pc()

    def calls(self, functions, watch=frozenset(), watched=None):
        """Yield (function, number, return address) at the entry of each outermost call of
        `functions` (a call of one inside another is part of the outer call). The consumer
        may single-step the call to its return; otherwise the program runs to it. A stop at an
        address in `watch` calls `watched(pc, function, number)`; outside a call it is an
        error."""
        entries = {self.syms[fn] & ~1: fn for fn in functions}
        count = dict.fromkeys(functions, 0)
        while (pc := self.run_to(set(entries) | watch)) is not None:
            if pc not in entries:
                sys.exit(f"qemu_steps: artifact offset {pc - self.base:#x} runs outside a call of "
                         f"{', '.join(functions)}")
            fn, ret = entries[pc], int(self.gdb.regs().split()[14], 16) & ~1
            count[fn] += 1
            yield fn, count[fn], ret
            pc = self.pc()
            while pc != ret:
                if pc in watch:
                    watched(pc, fn, count[fn])
                pc = self.run_to({ret} | watch)
                if pc is None:
                    sys.exit(f"qemu_steps: {fn} call {count[fn]} did not return")
        if 0 in count.values():
            sys.exit(f"qemu_steps: the image never calls {[f for f in count if not count[f]]}")


def trace_image(qemu, nm, text, elf, functions, pick, cases, qemu_states):
    """Single-step the calls `pick` ({function: call numbers}) selects; append the model's
    input and QEMU's states. Returns the artifact offsets they execute."""
    img = Image(qemu, nm, text, elf)
    try:
        cases.append(f"flash 0 {img.flash.hex()}")
        pcs = set()
        done = dict.fromkeys(functions, 0)
        for fn, n, stop in img.calls(functions):
            if n in pick.get(fn, ()):
                gdb = img.gdb
                state = gdb.regs()
                words = state.split()
                name = f"{Path(elf).stem}:{fn}:{n}"
                cases += [f"case {name}", f"ram {RAM[0]:x} {gdb.read(*RAM).hex()}",
                          f"regs {state}", f"stop {stop:x}"]
                steps = []
                while int(words[15], 16) != stop:
                    pcs.add(int(words[15], 16) - img.base)
                    gdb.cmd("s")
                    state = gdb.regs()
                    words = state.split()
                    steps.append(state)
                qemu_states[name] = (steps, gdb.read(*RAM).hex())
            done[fn] = n
            if all(n >= max(pick.get(f, {0})) for f, n in done.items()):
                break   # no selected call is left
        return pcs
    finally:
        img.close()


def find_calls(qemu, nm, text, elf, functions, todo):
    """Run the whole image with a breakpoint on each artifact offset in `todo`; return the
    calls that reach one, as {function: call numbers}, and the offsets they reach."""
    img = Image(qemu, nm, text, elf)
    try:
        watch = {img.base + o for o in todo}
        found, reached = {}, set()

        def watched(pc, fn, n):
            found.setdefault(fn, set()).add(n)
            reached.add(pc - img.base)
            watch.discard(pc)

        for _ in img.calls(functions, watch, watched):
            pass
        return found, reached
    finally:
        img.close()


FILLERS = {"movs r0, r0", "mov r8, r8", "nop"}   # what the assembler emits for .p2align


def padding(listing, starts, end):
    """Alignment padding in an object's listing: a filler halfword at an offset 2 mod 4 that
    a literal pool word, a function or the end of .text follows. Execution can never reach
    one: it is not a branch, so running it would fall into data or into another function."""
    return {o for o, t in listing.items()
            if t in FILLERS and o % 4 == 2 and (o + 2 not in listing or o + 2 in starts or o + 2 == end)}


def required(obj, text):
    """The offsets the calls must execute: every listed instruction except padding."""
    listing = objdump_lines(os.environ.get("OBJDUMP", "llvm-objdump"), obj)
    nm = subprocess.run([os.environ.get("NM", "llvm-nm"), "--defined-only", obj], check=True,
                        capture_output=True, text=True).stdout
    starts = {int(f[0], 16) for f in (l.split() for l in nm.splitlines())
              if len(f) == 3 and f[1] in "Tt"}
    return set(listing) - padding(listing, starts, len(text))


def main(argv):
    cover = None
    if len(argv) > 2 and argv[1] == "--cover":
        cover, argv = argv[2], argv[:1] + argv[3:]
    if len(argv) < 7 or len(argv) % 2 == 0 or not (ROOT / "assets" / argv[1]).is_dir():
        sys.exit(__doc__)
    workspace = ROOT / "assets" / argv[1]
    argv = argv[1:]
    qemu, nm, text = argv[1], argv[2], Path(argv[3]).read_bytes()
    cases, qemu_states, pcs = [], {}, set()
    images = [(elf, functions.split(",")) for elf, functions in zip(argv[4::2], argv[5::2])]
    for elf, functions in images:
        pcs |= trace_image(qemu, nm, text, elf, functions, dict.fromkeys(functions, CALLS),
                           cases, qemu_states)
    # Then every call that executes an instruction the sampled calls did not (every even
    # offset is watched, so literal pools are too; execution never reaches them).
    for elf, functions in images:
        todo = set(range(0, len(text), 2)) - pcs
        found, reached = find_calls(qemu, nm, text, elf, functions, todo)
        if found:
            pcs |= trace_image(qemu, nm, text, elf, functions, found, cases, qemu_states)
        if reached - pcs:
            sys.exit(f"qemu_steps: offsets {sorted(reached - pcs)} were not traced")
    with tempfile.NamedTemporaryFile("w", suffix=".txt") as f:
        f.write("\n".join(cases) + "\n")
        f.flush()
        model = subprocess.run(["lake", "env", "lean", "--run", str(ROOT / "lean/StepTrace.lean"), f.name],
                               cwd=workspace, check=True, capture_output=True, text=True).stdout
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
    executed = {p for p in pcs if 0 <= p < len(text)}
    instructions = len(executed)
    if cover is not None:
        want = required(cover, text)
        missing, extra = sorted(want - executed), sorted(executed - want)
        if missing or extra:
            sys.exit(f"qemu_steps: the calls executed {instructions} distinct instructions of the "
                     f"artifact, not the {len(want)} a call can execute; never executed "
                     f"{[hex(o) for o in missing[:20]]}, executed padding or data "
                     f"{[hex(o) for o in extra[:20]]}")
    print(f"ok: model and QEMU agree after each of {total} instructions in {len(qemu_states)} calls "
          f"({instructions} distinct instructions of the artifact: every one these images execute), "
          f"and on the final RAM")


if __name__ == "__main__":
    main(sys.argv)
