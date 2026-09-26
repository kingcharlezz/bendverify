"""The trusted extractor accepts exactly the modelled fragment and rejects the rest.

Every program here is checked by the reference Bend checker first; the extractor must
then refuse anything VerifiedIR v1 cannot model faithfully.

Run: python3 -m unittest tests/integration/test_extractor.py -v
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
EXTRACT = os.path.join(ROOT, "trusted", "verifier", "bend", "extract.mjs")
BEND2 = os.path.join(ROOT, "reference", "bend", "bend2")
sys.path.insert(0, os.path.join(ROOT, "trusted", "schema"))
import verifiedir  # noqa: E402


def extract(src: str, entry: str = "run"):
    d = tempfile.mkdtemp(dir=os.path.join(ROOT, "work"))
    f = os.path.join(d, "w.bend")
    open(f, "w").write(src)
    out = os.path.join(d, "w.ir.json")
    r = subprocess.run(["node", EXTRACT, BEND2, f, entry, out], capture_output=True, text=True)
    res = json.loads(r.stdout.strip().splitlines()[-1])
    return res, (json.load(open(out)) if res.get("ok") else None)


OK_PROGRAM = """import Base
type T is Data:
  L{v: U32}
  N{l: T, r: T}
def sum(t: T) -> U32:
  match t:
    case L{v}:
      v
    case N{l, r}:
      a b = sum(l) sum(r)
      (a + b : U32)
def build(+d: Nat, +x: U32) -> T:
  match d:
    case 0n:
      L{x}
    case 1n+p:
      N{build(p, U32.shl(x)), build(p, U32.inc(x))}
def run(+d: Nat, x: U32) -> U32:
  sum(build(d, x))
"""


class TestExtractor(unittest.TestCase):
    def test_accepts_fragment(self):
        res, ir = extract(OK_PROGRAM)
        self.assertTrue(res["ok"], res)
        verifiedir.validate(ir)
        self.assertEqual(sorted(f["name"] for f in ir["fns"]), ["build", "run", "sum"])

    def _rejects(self, src, needle):
        res, _ = extract(src)
        self.assertFalse(res["ok"], res)
        self.assertIn(needle, res["reason"])

    def test_rejects_unsafe(self):
        self._rejects("""import Base
@unsafe def loop(x: U32) -> U32:
  loop(x)
def run(x: U32) -> U32:
  loop(x)
""", "@unsafe")

    def test_rejects_question_mark_unsafe_sugar(self):
        self._rejects("""import Base
def loop?(x: U32) -> U32:
  loop(x)
def run(x: U32) -> U32:
  loop(x)
""", "@unsafe")

    def test_rejects_todo_hole(self):
        self._rejects("""import Base
def run(x: U32) -> U32:
  ?TODO
""", "hole")

    def test_rejects_open_law(self):
        self._rejects("""import Base
law secret:
  for x: U32
  U32
def run(x: U32) -> U32:
  x
""", "open law")

    def test_rejects_foreign_import(self):
        # the entry itself is a foreign (C/JS) definition
        self._rejects("""import Base
def run(x: U32) -> IO(U32):
  import "./ext.c"
  import "./ext.js"
""", "")

    def test_unreachable_foreign_code_is_not_extracted(self):
        res, ir = extract("""import Base
def ext(x: U32) -> IO(U32):
  import "./ext.c"
  import "./ext.js"
def run(x: U32) -> U32:
  x
""")
        self.assertTrue(res["ok"], res)
        self.assertEqual([f["name"] for f in ir["fns"]], ["run"])

    def test_rejects_f32(self):
        self._rejects("""import Base
def run(x: U32) -> U32:
  F32.to_u32(F32.add(1.5, 2.5))
""", "")

    def test_rejects_closures(self):
        self._rejects("""import Base
def app(f: U32 -> U32, x: U32) -> U32:
  f(x)
def run(x: U32) -> U32:
  app(y => (y + 1 : U32), x)
""", "")

    def test_rejects_string(self):
        self._rejects("""import Base
def run(x: U32) -> U32:
  String.len("abc")
""", "")

    def test_rejects_templates(self):
        self._rejects("""import Base
def twice(~f: U32 -> U32, x: U32) -> U32:
  f(f(x))
def run(x: U32) -> U32:
  twice(~(y => (y + 1 : U32)), x)
""", "")

    def test_rejects_arrays(self):
        self._rejects("""import Base
def run(x: U32) -> U32:
  a = [0 : U32*8n]
  (a2, v) = Array.get(U32, a, 1)
  v
""", "")


if __name__ == "__main__":
    unittest.main(verbosity=2)
