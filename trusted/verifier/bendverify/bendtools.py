"""Trusted build pipeline around the PINNED reference Bend. TRUSTED.

  extract   : Bend source  -> VerifiedIR   (reference bend.ts checker + extract.mjs)
  lower     : VerifiedIR   -> Bend source  (lower.py, a plain printer)
  compile   : Bend source  -> C            (reference bend.ts check + reference comp.ts)
  cc        : C            -> native binary (clang -std=c11 -O3, CPU target only)
  roundtrip : re-extract the lowered file and require the proven IR back
              (translation validation of `lower`).

Every tool here is trusted code, but it runs on data derived from competitor
input, so each runs confined (no network, writes only to its scratch dir).
"""

from __future__ import annotations

import json
import os

from . import sandbox
from .competition import ROOT

import lower as lower_mod        # trusted/verifier/bend/lower.py
import roundtrip as roundtrip_mod  # trusted/verifier/bend/roundtrip.py
import verifiedir                # trusted/schema/verifiedir.py

BEND_TOOLS = os.path.join(ROOT, "trusted", "verifier", "bend")
REF_BEND2 = os.path.join(ROOT, "reference", "bend", "bend2")


class BuildError(Exception):
    pass


def _node(tc: dict) -> str:
    return tc["node"]


def extract(tc: dict, bend_file: str, entry: str, out_ir: str) -> dict:
    work = os.path.dirname(out_ir)
    r = sandbox.run_confined(
        [_node(tc), "--stack-size=7800", os.path.join(BEND_TOOLS, "extract.mjs"), REF_BEND2, bend_file, entry, out_ir],
        read_paths=[ROOT, os.path.dirname(bend_file), os.path.dirname(os.path.realpath(_node(tc)))],
        write_paths=[work], cpu_seconds=300, wall_seconds=600)
    try:
        res = json.loads(r.stdout.decode().strip().splitlines()[-1])
    except (ValueError, IndexError) as e:
        raise BuildError(f"extractor crashed: {r.stderr.decode(errors='replace')[-400:]}") from e
    if not res.get("ok"):
        raise BuildError(f"extraction rejected: {res.get('reason')}")
    with open(out_ir) as f:
        return verifiedir.validate(json.load(f))


def lower(ir: dict, entry: str, base_names: set[str]) -> str:
    try:
        return lower_mod.lower(ir, entry, base_names)
    except lower_mod.LowerError as e:
        raise BuildError(f"not lowerable: {e}") from e


def compile_c(tc: dict, bend_file: str, out_c: str) -> None:
    work = os.path.dirname(out_c)
    r = sandbox.run_confined(
        [_node(tc), "--stack-size=7800", os.path.join(BEND_TOOLS, "compile.mjs"), REF_BEND2, bend_file, out_c],
        read_paths=[ROOT, os.path.dirname(bend_file), os.path.dirname(os.path.realpath(_node(tc)))],
        write_paths=[work], cpu_seconds=600, wall_seconds=900)
    try:
        res = json.loads(r.stdout.decode().strip().splitlines()[-1])
    except (ValueError, IndexError) as e:
        raise BuildError(f"reference compiler crashed: {r.stderr.decode(errors='replace')[-400:]}") from e
    if not res.get("ok"):
        raise BuildError(f"reference Bend rejected the lowered program: {res.get('reason')}")


def cc(tc: dict, c_file: str, out_bin: str) -> None:
    work = os.path.dirname(out_bin)
    r = sandbox.run_confined(
        [tc["clang"], "-std=c11", "-O3", c_file, "-lpthread", "-lm", "-o", out_bin],
        read_paths=[work, "/Library/Developer", "/Applications/Xcode.app"],
        write_paths=[work, "/private/var/folders", "/private/tmp"], env={"TMPDIR": work},
        cpu_seconds=900, wall_seconds=1200)
    if r.returncode != 0 or not os.path.isfile(out_bin):
        raise BuildError(f"clang failed: {r.stderr.decode(errors='replace')[-800:]}")


def roundtrip(tc: dict, ir: dict, bend_file: str, entry: str, work: str) -> dict:
    rt_path = os.path.join(work, "roundtrip.ir.json")
    rt = extract(tc, bend_file, entry, rt_path)
    try:
        roundtrip_mod.check(ir, rt, entry)
    except roundtrip_mod.RoundTripError as e:
        raise BuildError(f"lowering changed the program: {e}") from e
    return rt


def build(tc: dict, ir: dict, entry: str, work: str, base_names: set[str]) -> dict:
    """IR -> .bend -> .c -> binary, with round-trip validation. Returns paths."""
    os.makedirs(work, exist_ok=True)
    src = lower(ir, entry, base_names)
    bend_file = os.path.join(work, "program.bend")
    with open(bend_file, "w") as f:
        f.write(src)
    c_file = os.path.join(work, "program.c")
    compile_c(tc, bend_file, c_file)
    roundtrip(tc, ir, bend_file, entry, work)
    bin_file = os.path.join(work, "program.bin")
    cc(tc, c_file, bin_file)
    return {"bend": bend_file, "c": c_file, "binary": bin_file,
            "roundtrip_ir": os.path.join(work, "roundtrip.ir.json")}
