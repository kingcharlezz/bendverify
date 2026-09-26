"""Conformance of the primitive semantics across the three places it is defined.

The extractor maps Base's U32/Nat operations to VerifiedIR primitives whose
meaning is BendVerify.Prim.eval. That correspondence is a trusted assumption
(docs/TRUST_MODEL.md). This test spot-checks it on edge cases, three ways,
against a single expected value R per case:

  1. Lean kernel:        `Prim.eval p args = some R` by `rfl`       (the spec)
  2. reference checker:  `{Op(a, b) == R : T}` accepted by `{==}`    (Base's pure-Bend definitions)
  3. compiled program:   the reference compiler's C prints R        (comp.ts templates)

Run: python3 -m unittest tests/integration/test_prim_conformance.py -v
"""
from __future__ import annotations

import json
import os
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "trusted", "verifier"))
from bendverify import verify as V  # noqa: E402
from bendverify.competition import load  # noqa: E402

M = 2 ** 32
U32_EDGE = [0, 1, 2, 3, 5, 31, 32, 33, 255, 65535, 65536, 2 ** 31 - 1, 2 ** 31, M - 2, M - 1]
NAT_EDGE = [0, 1, 2, 3, 7, 12]

BIN = {  # name: (python semantics, result kind)
    "add": (lambda a, b: (a + b) % M, "u32"), "sub": (lambda a, b: (a - b) % M, "u32"),
    "mul": (lambda a, b: (a * b) % M, "u32"), "div": (lambda a, b: 0 if b == 0 else a // b, "u32"),
    "mod": (lambda a, b: a if b == 0 else a % b, "u32"), "and": (lambda a, b: a & b, "u32"),
    "or": (lambda a, b: a | b, "u32"), "xor": (lambda a, b: a ^ b, "u32"),
    "is_eq": (lambda a, b: a == b, "bool"), "is_ne": (lambda a, b: a != b, "bool"),
    "is_lt": (lambda a, b: a < b, "bool"), "is_le": (lambda a, b: a <= b, "bool"),
    "is_gt": (lambda a, b: a > b, "bool"), "is_ge": (lambda a, b: a >= b, "bool"),
}
UN = {"not": lambda a: M - 1 - a, "shl": lambda a: (a * 2) % M, "shr": lambda a: a // 2,
      "inc": lambda a: (a + 1) % M}
NATBIN = {"add": (lambda a, b: a + b, "nat"), "sub": (lambda a, b: max(a - b, 0), "nat"),
          "mul": (lambda a, b: a * b, "nat"), "div": (lambda a, b: 0 if b == 0 else a // b, "nat"),
          "mod": (lambda a, b: a if b == 0 else a % b, "nat"),
          "is_eq": (lambda a, b: a == b, "bool"), "is_lt": (lambda a, b: a < b, "bool"),
          "is_le": (lambda a, b: a <= b, "bool"), "is_ge": (lambda a, b: a >= b, "bool")}


def cases(seed=7):
    rnd = random.Random(seed)
    out = []
    pairs = [(a, b) for a in U32_EDGE for b in U32_EDGE]
    rnd.shuffle(pairs)
    for name, (f, kind) in BIN.items():
        for a, b in pairs[:6] + [(rnd.randrange(M), rnd.randrange(M)), (7, 0), (M - 1, 1)]:
            out.append(("u32_" + name, [("u32", a), ("u32", b)], kind, f(a, b)))
    for name, f in UN.items():
        for a in U32_EDGE[::3]:
            out.append(("u32_" + name, [("u32", a)], "u32", f(a)))
    for a in (1, 3, M - 1):
        for n in (0, 1, 13, 31, 32, 33, 40):
            out.append(("u32_shln", [("u32", a), ("nat", n)], "u32", (a << n) % M if n < 32 else 0))
            out.append(("u32_shrn", [("u32", a), ("nat", n)], "u32", a >> n if n < 32 else 0))
    for a in (0, 5, M - 1):
        out.append(("u32_is_zero", [("u32", a)], "bool", a == 0))
        out.append(("u32_to_nat", [("u32", a)], "nat", a))
    for n in (0, 9, 300):
        out.append(("u32_from_nat", [("nat", n)], "u32", n % M))
    for a in (False, True):
        out.append(("bool_not", [("bool", a)], "bool", not a))
        for b in (False, True):
            out.append(("bool_and", [("bool", a), ("bool", b)], "bool", a and b))
            out.append(("bool_or", [("bool", a), ("bool", b)], "bool", a or b))
    for name, (f, kind) in NATBIN.items():
        for a, b in [(0, 0), (3, 5), (12, 3), (7, 0), (5, 2)]:
            out.append(("nat_" + name, [("nat", a), ("nat", b)], kind, f(a, b)))
    return out


def lean_val(kind, v):
    if kind == "u32":
        return f"(.u32 {v})"
    if kind == "nat":
        return f"(.nat {v})"
    return f"(.ctr {1 if v else 0} [])"


def bend_lit(kind, v):
    if kind == "u32":
        return str(v)
    if kind == "nat":
        return f"{v}n" if v <= 256 else f"U32.to_nat({v})"
    return "True{}" if v else "False{}"


def bend_op(p):
    ty, name = p.split("_", 1)
    return {"u32": "U32.", "nat": "Nat.", "bool": "Bool."}[ty] + name


class TestPrimConformance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.comp = load(self_check=False)
        cls.tc = V.toolchain(cls.comp)
        cls.cases = cases()
        cls.tmp = tempfile.mkdtemp(dir=os.path.join(ROOT, "work"))

    def test_1_lean_spec(self):
        lines = ["import BendVerify", "open BendVerify", ""]
        for i, (p, args, kind, r) in enumerate(self.cases):
            a = ", ".join(lean_val(k, v) for k, v in args)
            lines.append(f"example : Prim.eval .{p} [{a}] = some {lean_val(kind, r)} := rfl")
        f = os.path.join(self.tmp, "Prims.lean")
        open(f, "w").write("\n".join(lines) + "\n")
        lib = os.path.join(ROOT, "trusted", "spec", "lean", ".lake", "build", "lib", "lean")
        r = subprocess.run([os.path.join(self.tc["lean_toolchain"], "bin", "lean"), f],
                           env={"LEAN_PATH": lib, "PATH": "/usr/bin:/bin"}, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout[-3000:] + r.stderr[-2000:])

    def test_2_reference_checker_base_definitions(self):
        # Nat multiplication/division of unary Nats is slow in the checker: keep them small.
        # Nats are unary in the checker: cases with a Nat above 1000 are covered by
        # legs 1 and 3 only.
        lines = ["import Base", ""]
        for i, (p, args, kind, r) in enumerate(self.cases):
            if any(k == "nat" and v > 1000 for k, v in args) or (kind == "nat" and r > 1000):
                continue
            a = ", ".join(bend_lit(k, v) for k, v in args)
            ty = {"u32": "U32", "nat": "Nat", "bool": "Bool"}[kind]
            lines += [f"def c{i}() -> {{{bend_op(p)}({a}) == {bend_lit(kind, r)} : {ty}}}:", "  {==}", ""]
        f = os.path.join(self.tmp, "prims.bend")
        open(f, "w").write("\n".join(lines))
        check = os.path.join(self.tmp, "check.mjs")
        open(check, "w").write(f'''
import * as Bend from "{ROOT}/reference/bend/bend2/bend.ts";
const book = Bend.book_nil();
try {{ await Bend.book_load(book, process.argv[2], "", new Map()); Bend.book_valid(book, 0);
      console.log(book.hols === 0 ? "OK" : "HOLES"); }}
catch (e) {{ console.log(e?.$ === "Err" ? Bend.err_show(e) : String(e)); process.exit(1); }}
''')
        r = subprocess.run([self.tc["node"], "--stack-size=7800", check, f], capture_output=True, text=True,
                           timeout=1800)
        self.assertEqual(r.stdout.strip().splitlines()[-1:], ["OK"], r.stdout[-3000:] + r.stderr[-1000:])

    def test_3_compiled_c(self):
        lines = ["import Base", ""]
        prints = []
        for i, (p, args, kind, r) in enumerate(self.cases):
            a = ", ".join(bend_lit(k, v) for k, v in args)
            show = {"u32": "U32.show", "nat": "Nat.show", "bool": "Bool.show"}[kind]
            prints.append(f"    IO.print({show}({bend_op(p)}({a})))")
        lines += ["def main() -> IO(Unit):", "  do IO<Unit>:"] + prints
        f = os.path.join(self.tmp, "prims_run.bend")
        open(f, "w").write("\n".join(lines) + "\n")
        c = os.path.join(self.tmp, "prims_run.c")
        r = subprocess.run([self.tc["node"], "--stack-size=7800",
                            os.path.join(ROOT, "trusted", "verifier", "bend", "compile.mjs"),
                            os.path.join(ROOT, "reference", "bend", "bend2"), f, c], capture_output=True, text=True)
        self.assertIn('"ok":true', r.stdout, r.stdout + r.stderr)
        b = os.path.join(self.tmp, "prims_run.bin")
        subprocess.run([self.tc["clang"], "-std=c11", "-O2", c, "-lpthread", "-lm", "-o", b], check=True)
        out = subprocess.run([b, "--gpu", "off"], capture_output=True, text=True).stdout.split("\n")
        want = [("true" if r else "false") if kind == "bool" else str(r) for (_, _, kind, r) in self.cases]
        got = [x.strip() for x in out[:len(want)]]
        bad = [(self.cases[i], got[i]) for i in range(len(want)) if got[i].lower() != want[i]]
        self.assertEqual(bad, [], f"{len(bad)} mismatches, e.g. {bad[:3]}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
