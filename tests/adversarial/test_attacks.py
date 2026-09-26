"""Adversarial regression suite: every attack must be rejected (or contained).

Run:  python3 -m unittest tests/adversarial/test_attacks.py -v
(needs Docker/colima, the pinned Lean, node and clang; ~5-10 minutes)
"""
from __future__ import annotations

import json
import os
import shutil
import tarfile
import unittest

import harness as H
from harness import V, canon_hash

import bench
from bendverify import sandbox
from bendverify.competition import CompetitionError, load as load_competition


def rejected(t: unittest.TestCase, rep: dict, stage: str, contains: str = "") -> None:
    t.assertEqual(rep["result"], "INVALID", f"expected rejection, got {rep}")
    t.assertEqual(rep["stage"], stage, f"rejected at the wrong stage: {rep}")
    if contains:
        t.assertIn(contains, rep["reason"])


# --------------------------------------------------------------------------- 1
class T01_Accept(unittest.TestCase):
    def test_correct_candidate_and_correct_proof_is_accepted(self):
        cand = H.fresh("t01")
        rep = H.verify(H.package(cand))
        self.assertEqual(rep["result"], "VALID", rep)


# --------------------------------------------------------------------------- archive level
class T02_Archive(unittest.TestCase):
    def _crafted(self, name, extra):
        out = os.path.join(H.WORK, name + ".tar.zst")
        H.raw_archive(out, H.valid_members_prefix() + extra)
        return H.verify(out)

    def test_symlink_entry(self):
        rep = self._crafted("sym", [(H.tinfo("submission/bend", tarfile.DIRTYPE, mode=0o755), None),
                                    (H.tinfo("submission/bend/evil", tarfile.SYMTYPE, linkname="/etc/passwd"), None)])
        rejected(self, rep, "archive", "symlink")

    def test_path_traversal(self):
        rep = self._crafted("trav", [(H.tinfo("submission/../../escape.txt", size=2), b"hi")])
        rejected(self, rep, "archive")
        self.assertFalse(os.path.exists(os.path.join(H.ROOT, "work", "escape.txt")))

    def test_absolute_path(self):
        rep = self._crafted("abs", [(H.tinfo("/tmp/bendverify-abs-escape", size=2), b"hi")])
        rejected(self, rep, "archive")
        self.assertFalse(os.path.exists("/tmp/bendverify-abs-escape"))

    def test_hard_link(self):
        rep = self._crafted("hl", [(H.tinfo("submission/proof", tarfile.DIRTYPE, mode=0o755), None),
                                   (H.tinfo("submission/proof/x", tarfile.LNKTYPE, linkname="submission/manifest.json"), None)])
        rejected(self, rep, "archive", "hard link")

    def test_device_and_fifo(self):
        rep = self._crafted("dev", [(H.tinfo("submission/dev", tarfile.CHRTYPE), None)])
        rejected(self, rep, "archive", "device")
        rep = self._crafted("fifo", [(H.tinfo("submission/fifo", tarfile.FIFOTYPE), None)])
        rejected(self, rep, "archive", "fifo")

    def test_duplicate_and_case_colliding_entries(self):
        rep = self._crafted("dup", [(H.tinfo("submission/Manifest.json", size=2), b"{}")])
        rejected(self, rep, "archive", "case-colliding")

    def test_decompression_bomb(self):
        out = os.path.join(H.WORK, "bomb.tar.zst")
        big = 600 * 1024 * 1024
        import subprocess
        with open(out, "wb") as f:
            p = subprocess.Popen(["zstd", "-q", "-c", "--no-progress"], stdin=subprocess.PIPE, stdout=f)
            chunk = b"\0" * (1 << 20)
            for _ in range(big >> 20):
                p.stdin.write(chunk)
            p.stdin.close()
            p.wait()
        self.assertLess(os.path.getsize(out), 1 << 20)
        rejected(self, H.verify(out), "archive", "size limit")

    def test_extra_top_level_file_such_as_own_verifier_or_binary(self):
        cand = H.fresh("t02x")
        arc = H.package(cand)
        # re-pack with an extra top-level entry (a candidate-supplied "verifier" and binary)
        tmp = os.path.join(H.WORK, "t02x-unpacked")
        shutil.rmtree(tmp, ignore_errors=True)
        sub = H.archive.unpack(arc, tmp)
        with open(os.path.join(sub, "verify.sh"), "w") as f:
            f.write("#!/bin/sh\necho 'Proof: VALID'\n")
        H.archive.pack(sub, arc)
        rejected(self, H.verify(arc), "archive", "exactly bend/, proof/, manifest.json")


# --------------------------------------------------------------------------- manifest / hashes
class T03_Hashes(unittest.TestCase):
    def test_wrong_competition_id(self):
        cand = H.fresh("t03a")
        arc = H.package(cand)
        tmp = os.path.join(H.WORK, "t03a-x")
        shutil.rmtree(tmp, ignore_errors=True)
        sub = H.archive.unpack(arc, tmp)
        H.edit_json(os.path.join(sub, "manifest.json"),
                    lambda m: m.update(competition_id="sha256:" + "1" * 64))
        H.archive.pack(sub, arc)
        rejected(self, H.verify(arc), "manifest", "different competition")

    def test_fake_candidate_hash_claim(self):
        cand = H.fresh("t03b")
        arc = H.package(cand)
        tmp = os.path.join(H.WORK, "t03b-x")
        shutil.rmtree(tmp, ignore_errors=True)
        sub = H.archive.unpack(arc, tmp)
        H.edit_json(os.path.join(sub, "manifest.json"),
                    lambda m: m.update(candidate_repo_hash="sha256:" + "2" * 64))
        H.archive.pack(sub, arc)
        rejected(self, H.verify(arc), "hash", "candidate digest mismatch")

    def test_proof_modified_after_packaging(self):
        cand = H.fresh("t03c")
        arc = H.package(cand)
        tmp = os.path.join(H.WORK, "t03c-x")
        shutil.rmtree(tmp, ignore_errors=True)
        sub = H.archive.unpack(arc, tmp)
        with open(os.path.join(sub, "proof", "export.json"), "a") as f:
            f.write(" ")
        H.archive.pack(sub, arc)
        rejected(self, H.verify(arc), "hash", "proof digest mismatch")

    def test_candidate_changed_after_proof(self):
        """Change one byte of the candidate (a comment) after proving; repackage honestly."""
        cand = H.fresh("t03d")
        p = os.path.join(cand, "bend", "bend2", "opt", "optimize.mjs")
        with open(p, "a") as f:
            f.write("// one extra byte after the proof was made\n")
        rejected(self, H.verify(H.package(cand)), "proof", "Stamp")

    def test_semantic_line_changed_and_proof_reused(self):
        """Candidate A + proof A passes (T01); change one semantic line, reuse proof A."""
        cand = H.fresh("t03e")
        p = os.path.join(cand, "bend", "bend2", "opt", "optimize.mjs")
        src = open(p).read()
        one_line = 'return ["par", ["call", F, e[1][2]], ["call", F, e[2][2]], lift(arm[3], 4, -1)];'
        self.assertIn(one_line, src)
        src = src.replace(one_line, 'return ["par", ["call", F, e[2][2]], ["call", F, e[1][2]], lift(arm[3], 4, -1)];')
        open(p, "w").write(src)
        H.reclaim(cand)          # honest claims for the new code, stale proof A
        rep = H.verify(H.package(cand))
        rejected(self, rep, "proof")

    def test_manifest_claims_other_candidate_ir(self):
        cand = H.fresh("t03f")
        H.edit_json(os.path.join(cand, "submission.json"),
                    lambda s: s["workloads"]["tree-radix"].update(candidate_ir_hash="sha256:" + "3" * 64))
        rejected(self, H.verify(H.package(cand)), "artifact", "not the one the manifest claims")


# --------------------------------------------------------------------------- boundary / dependencies
class T04_Boundary(unittest.TestCase):
    def test_compiler_dependency_modified(self):
        cand = H.fresh("t04a")
        with open(os.path.join(cand, "bend", "bend2", "comp.ts"), "a") as f:
            f.write("\n// changed after hashing\n")
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "boundary", "bend2/comp.ts")

    def test_unsafe_def_added_to_base(self):
        cand = H.fresh("t04b")
        with open(os.path.join(cand, "bend", "bend2", "base.bend"), "a") as f:
            f.write("\n@unsafe def Evil.loop(x: Nat) -> Nat:\n  Evil.loop(x)\n")
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "boundary", "base.bend")

    def test_foreign_code_added(self):
        cand = H.fresh("t04c")
        with open(os.path.join(cand, "bend", "bend2", "effs", "evil.c"), "w") as f:
            f.write("int evil(void){return 0;}\n")
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "boundary", "new file bend2/effs/evil.c")

    def test_reference_file_deleted(self):
        cand = H.fresh("t04d")
        os.unlink(os.path.join(cand, "bend", "README.md"))
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "boundary", "missing")

    def test_symlink_in_candidate_tree(self):
        cand = H.fresh("t04e")
        os.symlink("/etc/passwd", os.path.join(cand, "bend", "bend2", "opt", "link"))
        with self.assertRaises(Exception):
            H.package(cand)   # the packager refuses; a hand-made archive is caught by T02


# --------------------------------------------------------------------------- trusted base
class T05_TrustedBase(unittest.TestCase):
    def _tamper(self, rel, fn):
        arc = H.package(H.fresh("t05"))
        p = os.path.join(H.ROOT, rel)
        orig = open(p, "rb").read()
        try:
            changed = fn(orig)
            self.assertNotEqual(changed, orig)
            open(p, "wb").write(changed)
            with self.assertRaises((CompetitionError, V.Reject)):
                V.verify(arc, log=lambda *a: None)
        finally:
            open(p, "wb").write(orig)
        load_competition(self_check=True)   # restored

    def test_modified_spec(self):
        self._tamper("trusted/spec/lean/BendVerify/Equiv.lean",
                     lambda b: b.replace(b"Run P c.entry args v \xe2\x86\x94 Run Q c.entry args v", b"True"))

    def test_modified_verifier(self):
        self._tamper("trusted/verifier/bendverify/proofcheck.py",
                     lambda b: b.replace(b'if res.get("result") != "PASS":', b'if False:'))

    def test_modified_rules(self):
        def f(b):
            c = json.loads(b)
            c["rules"]["allowed_axioms"].append("sorryAx")
            return json.dumps(c).encode()
        self._tamper("competition.json", f)


# --------------------------------------------------------------------------- hostile proofs
def _export(cand):
    return os.path.join(cand, "proof", "export.json")


def _add_name(ex, dotted):
    parent = 0
    for comp in dotted.split("."):
        ex["names"].append(["s", parent, comp])
        parent = len(ex["names"])
    return parent


def _const(ex, dotted, levels=()):
    n = _add_name(ex, dotted)
    ex["exprs"].append(["c", n, list(levels)])
    return len(ex["exprs"]) - 1


def _fusion_decl(ex):
    names = [""]
    for j in ex["names"]:
        parent = names[j[1]]
        names.append(f"{parent}.{j[2]}" if parent else str(j[2]))
    for d in ex["decls"]:
        if names[d["n"]] == "Submission.TreeRadix.fusion":
            return d
    raise AssertionError("fusion decl not found")


class T06_Proofs(unittest.TestCase):
    def test_incorrect_candidate_without_proof(self):
        cand = H.fresh("t06a")
        shutil.rmtree(os.path.join(cand, "proof"))
        os.makedirs(os.path.join(cand, "proof"))
        H.edit_json(os.path.join(cand, "submission.json"), lambda s: s.update(proof={"export": None, "imports": []}))
        rejected(self, H.verify(H.package(cand)), "proof", "lemma steps require a proof export")

    def test_missing_law_proof_constant_absent(self):
        cand = H.fresh("t06b")
        def drop(ex):
            d = _fusion_decl(ex)
            ex["decls"].remove(d)
        H.edit_json(_export(cand), drop)
        rejected(self, H.verify(H.package(cand)), "proof", "not in the export")

    def test_weaker_theorem(self):
        """A proof of `True` under the expected name: kernel-valid, wrong statement."""
        cand = H.fresh("t06c")
        def weaken(ex):
            d = _fusion_decl(ex)
            d["t"] = _const(ex, "True")
            d["v"] = _const(ex, "True.intro")
        H.edit_json(_export(cand), weaken)
        rejected(self, H.verify(H.package(cand)), "proof", "proves a different statement")

    def test_open_hole_sorry(self):
        cand = H.fresh("t06d")
        def sorry(ex):
            d = _fusion_decl(ex)
            ex["levels"].append(["z"])
            lz = len(ex["levels"]) - 1
            s = _const(ex, "sorryAx", [lz])
            ex["exprs"].append(["ap", s, d["t"]])
            f = _const(ex, "Bool.false")
            ex["exprs"].append(["ap", len(ex["exprs"]) - 1, f])
            d["v"] = len(ex["exprs"]) - 1
        H.edit_json(_export(cand), sorry)
        rejected(self, H.verify(H.package(cand)), "proof", "sorryAx")

    def test_extra_axiom_declaration(self):
        cand = H.fresh("t06e")
        def ax(ex):
            ex["decls"].append({"k": "axiom", "n": _add_name(ex, "Submission.cheat"), "lp": [],
                                "t": _const(ex, "False"), "v": 0})
        H.edit_json(_export(cand), ax)
        rejected(self, H.verify(H.package(cand)), "proof", "forbidden declaration kind")

    def test_native_decide_reduce_bool_axiom(self):
        cand = H.fresh("t06f")
        def nd(ex):
            d = _fusion_decl(ex)
            d["v"] = _const(ex, "Lean.ofReduceBool")
        H.edit_json(_export(cand), nd)
        rejected(self, H.verify(H.package(cand)), "proof", "Lean.ofReduceBool")

    def test_redeclare_trusted_constant(self):
        cand = H.fresh("t06g")
        def redecl(ex):
            d = dict(_fusion_decl(ex))
            d["n"] = _add_name(ex, "BendVerify.Equiv.trans")
            ex["decls"].append(d)
        H.edit_json(_export(cand), redecl)
        rejected(self, H.verify(H.package(cand)), "proof", "redeclares existing constant")

    def test_declare_into_reserved_namespace(self):
        cand = H.fresh("t06h")
        def res(ex):
            d = dict(_fusion_decl(ex))
            d["n"] = _add_name(ex, "Contest.Certified.root")
            ex["decls"].append(d)
        H.edit_json(_export(cand), res)
        rejected(self, H.verify(H.package(cand)), "proof", "reserved Contest namespace")

    def test_unsafe_constant_in_proof_graph(self):
        cand = H.fresh("t06i")
        def uns(ex):
            d = dict(_fusion_decl(ex))
            d["n"] = _add_name(ex, "Submission.usesUnsafe")
            d["k"] = "def"
            d["h"] = 1
            d["v"] = _const(ex, "unsafeCast", [])
            ex["decls"].append(d)
            _fusion_decl(ex)["v"] = _const(ex, "Submission.usesUnsafe")
        H.edit_json(_export(cand), uns)
        rejected(self, H.verify(H.package(cand)), "proof", "kernel")

    def test_untrusted_import(self):
        cand = H.fresh("t06j")
        H.edit_json(_export(cand), lambda ex: ex["imports"].append("Mathlib.Tactic"))
        H.edit_json(os.path.join(cand, "submission.json"), lambda s: s["proof"]["imports"].append("Mathlib.Tactic"))
        rejected(self, H.verify(H.package(cand)), "proof", "outside the trusted allowlist")

    def test_import_graph_differs_from_declared(self):
        cand = H.fresh("t06k")
        H.edit_json(os.path.join(cand, "submission.json"), lambda s: s["proof"]["imports"].pop())
        rejected(self, H.verify(H.package(cand)), "proof", "import graph differs")

    def test_proof_for_another_candidate(self):
        """Proof A (valid for candidate A) submitted with candidate B = A + a new file."""
        cand = H.fresh("t06l")
        with open(os.path.join(cand, "bend", "bend2", "opt", "NOTES.md"), "w") as f:
            f.write("candidate B\n")
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "proof", "Stamp")

    def test_false_library_rule_claim(self):
        """Chain says `inline` produced a program it did not produce."""
        cand = H.fresh("t06m")
        p = os.path.join(cand, "bend", "bend2", "opt", "optimize.mjs")
        src = open(p).read()
        src = src.replace('steps.push({ kind: "rule", fn: entryIdx, path: found.path, rule: { name: "inline" } });',
                          'steps.push({ kind: "rule", fn: entryIdx, path: found.path, rule: { name: "caseCtr" } });')
        open(p, "w").write(src)
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "proof", "library-rule step")


    def _ind_block(self, ex, type_name, ctor_name, ctor_type_builder, extra=None):
        ex["levels"].append(["z"]); z = len(ex["levels"]) - 1
        ex["levels"].append(["s", z]); one = len(ex["levels"]) - 1
        ex["exprs"].append(["so", one]); ty = len(ex["exprs"]) - 1
        tn = _add_name(ex, type_name)
        cn = _add_name(ex, ctor_name)
        block = {"k": "ind", "lp": [], "np": 0,
                 "types": [{"n": tn, "t": ty, "ctors": [{"n": cn, "t": ctor_type_builder(ex, tn)}]}]}
        if extra:
            block.update(extra)
        ex["decls"].insert(0, block)

    def test_non_positive_inductive(self):
        """`Bad := mk : (Bad → False) → Bad` would prove False; the kernel refuses it."""
        cand = H.fresh("t06n")
        def bad(ex):
            def ctor_ty(ex, tn):
                ex["exprs"].append(["c", tn, []]); b = len(ex["exprs"]) - 1
                f = _const(ex, "False")
                x = _add_name(ex, "x")
                ex["exprs"].append(["pi", x, b, f, "d"]); arrow = len(ex["exprs"]) - 1
                ex["exprs"].append(["pi", x, arrow, b, "d"])
                return len(ex["exprs"]) - 1
            self._ind_block(ex, "Submission.Bad", "Submission.Bad.mk", ctor_ty)
        H.edit_json(_export(cand), bad)
        rejected(self, H.verify(H.package(cand)), "proof", "kernel rejected")

    def test_inductive_redeclares_existing_type(self):
        cand = H.fresh("t06o")
        def redecl(ex):
            def ctor_ty(ex, tn):
                ex["exprs"].append(["c", tn, []])
                return len(ex["exprs"]) - 1
            self._ind_block(ex, "Nat", "Submission.Nat.zero'", ctor_ty)
        H.edit_json(_export(cand), redecl)
        rejected(self, H.verify(H.package(cand)), "proof", "redeclares existing constant Nat")

    def test_forged_recursor_is_unrepresentable(self):
        """Recursors are generated by the kernel; an export cannot supply one."""
        cand = H.fresh("t06p")
        def forged(ex):
            def ctor_ty(ex, tn):
                ex["exprs"].append(["c", tn, []])
                return len(ex["exprs"]) - 1
            self._ind_block(ex, "Submission.U", "Submission.U.mk", ctor_ty, extra={"rec": 0})
        H.edit_json(_export(cand), forged)
        rejected(self, H.verify(H.package(cand)), "proof", "unexpected field rec")


# --------------------------------------------------------------------------- optimizer output
class T07_OptimizerOutput(unittest.TestCase):
    # workloads the attack does not touch get an empty ("no change") chain
    UNTOUCHED = r'''
for (const w of ["tree-radix", "lexer"]) {
  if (!fs.existsSync(o + "/" + w)) {
    fs.mkdirSync(o + "/" + w, {recursive: true});
    fs.writeFileSync(o + "/" + w + "/chain.json", JSON.stringify({format: "bendverify-chain-v1", workload: w, steps: []}));
  }
}
'''

    def _with_optimizer(self, name, js):
        cand = H.fresh(name)
        with open(os.path.join(cand, "bend", "bend2", "opt", "optimize.mjs"), "w") as f:
            f.write(js + self.UNTOUCHED)
        return cand

    def test_ill_formed_ir(self):
        cand = self._with_optimizer("t07a", r'''
import * as fs from "node:fs";
const [i, o] = process.argv.slice(2);
const p = JSON.parse(fs.readFileSync(i + "/tree-radix.ir.json", "utf8"));
p.fns[0].body = ["var", 99];
fs.mkdirSync(o + "/tree-radix", {recursive: true});
fs.writeFileSync(o + "/tree-radix/q.ir.json", JSON.stringify(p));
fs.writeFileSync(o + "/tree-radix/chain.json", JSON.stringify({format:"bendverify-chain-v1",workload:"tree-radix",steps:[{kind:"lemma",proof:"Submission.TreeRadix.fusion",program:"q.ir.json"}]}));
''')
        H.edit_json(os.path.join(cand, "submission.json"),
                    lambda s: s["workloads"]["tree-radix"].update(candidate_ir_hash="sha256:" + "4" * 64))
        rejected(self, H.verify(H.package(cand)), "chain", "out of scope")

    def test_symlink_in_optimizer_output(self):
        cand = self._with_optimizer("t07b", r'''
import * as fs from "node:fs";
const [i, o] = process.argv.slice(2);
fs.mkdirSync(o + "/tree-radix", {recursive: true});
fs.symlinkSync("/etc/passwd", o + "/tree-radix/chain.json");
''')
        rejected(self, H.verify(H.package(cand)), "optimizer", "non-regular")

    def test_unlowerable_ir_is_not_built(self):
        """Match on a let-bound variable: meaningful IR, but Bend cannot express it."""
        cand = self._with_optimizer("t07c", r'''
import * as fs from "node:fs";
const [i, o] = process.argv.slice(2);
const p = JSON.parse(fs.readFileSync(i + "/tree-radix.ir.json", "utf8"));
p.fns[0].body = ["let", ["ctr", 3, 1, []], ["mat", 3, ["var", 0], [[0, ["u32", 0]],
  [0, ["call", 4, [["call", 3, [["call", 2, [["call", 1, [["var", 2], ["var", 1]]]]]]]]]]]]];
fs.mkdirSync(o + "/tree-radix", {recursive: true});
fs.writeFileSync(o + "/tree-radix/q.ir.json", JSON.stringify(p));
fs.writeFileSync(o + "/tree-radix/chain.json", JSON.stringify({format:"bendverify-chain-v1",workload:"tree-radix",steps:[{kind:"lemma",proof:"Submission.TreeRadix.fusion",program:"q.ir.json"}]}));
''')
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "build", "not lowerable")

    def test_reserved_function_name(self):
        cand = self._with_optimizer("t07d", r'''
import * as fs from "node:fs";
const [i, o] = process.argv.slice(2);
const p = JSON.parse(fs.readFileSync(i + "/tree-radix.ir.json", "utf8"));
p.fns[5].name = "harness.args";
fs.mkdirSync(o + "/tree-radix", {recursive: true});
fs.writeFileSync(o + "/tree-radix/q.ir.json", JSON.stringify(p));
fs.writeFileSync(o + "/tree-radix/chain.json", JSON.stringify({format:"bendverify-chain-v1",workload:"tree-radix",steps:[{kind:"lemma",proof:"Submission.TreeRadix.fusion",program:"q.ir.json"}]}));
''')
        H.reclaim(cand)
        rejected(self, H.verify(H.package(cand)), "build", "reserved")


# --------------------------------------------------------------------------- sandbox
class T08_Sandbox(unittest.TestCase):
    """The optimizer is arbitrary code; it runs contained. These call the
    sandbox directly with small limits so that runaway cases finish quickly."""

    def _spec(self, seconds=20):
        comp = load_competition(self_check=False)
        spec = json.loads(json.dumps(comp["rules"]["optimizer"]))
        spec["limits"]["seconds"] = seconds
        return spec

    def _run(self, name, js, seconds=20):
        cand = os.path.join(H.WORK, name)
        shutil.rmtree(cand, ignore_errors=True)
        os.makedirs(os.path.join(cand, "bend2", "opt"))
        with open(os.path.join(cand, "bend2", "opt", "optimize.mjs"), "w") as f:
            f.write(js)
        ind = os.path.join(H.WORK, name + "-in")
        shutil.rmtree(ind, ignore_errors=True)
        os.makedirs(ind)
        open(os.path.join(ind, "request.json"), "w").write("{}")
        out = os.path.join(H.WORK, name + "-out")
        shutil.rmtree(out, ignore_errors=True)
        return sandbox.run_optimizer(cand, ind, out, self._spec(seconds)), out

    def test_arbitrary_command_execution_is_contained(self):
        secret = os.path.join(os.path.expanduser("~"), ".bendverify-test-secret")
        open(secret, "w").write("TOP SECRET")
        victim = os.path.join(H.ROOT, "trusted", "spec", "lean", "BendVerify", "Equiv.lean")
        before = canon_hash.file_digest(victim)
        try:
            res, out = self._run("t08a", r'''
import * as fs from "node:fs";
import * as cp from "node:child_process";
const [i, o] = process.argv.slice(2);
const r = {};
const tryit = (k, f) => { try { r[k] = String(f()).slice(0, 80); } catch (e) { r[k] = "BLOCKED: " + e.code; } };
tryit("net", () => cp.execSync("node -e \"require('https').get('https://example.com',r=>console.log(r.statusCode)).on('error',e=>{console.log('ERR',e.code);process.exit(3)})\"", {timeout: 8000}).toString());
tryit("secret", () => fs.readFileSync("/Users/" + (process.env.USER||"x") + "/.bendverify-test-secret", "utf8"));
tryit("write_cand", () => fs.writeFileSync("/cand/pwned", "x"));
tryit("write_root", () => fs.writeFileSync("/etc/pwned", "x"));
tryit("env", () => JSON.stringify(Object.keys(process.env)));
tryit("uid", () => cp.execSync("id -u").toString());
fs.writeFileSync(o + "/report.json", JSON.stringify(r));
''')
            rep = json.load(open(os.path.join(out, "report.json")))
            self.assertTrue(rep["net"].startswith("BLOCKED") or "ERR" in rep["net"], rep["net"])
            self.assertTrue(rep["secret"].startswith("BLOCKED"), rep["secret"])
            self.assertTrue(rep["write_cand"].startswith("BLOCKED"), rep["write_cand"])
            self.assertTrue(rep["write_root"].startswith("BLOCKED"), rep["write_root"])
            self.assertNotIn("SECRET", json.dumps(rep))
            self.assertNotIn("AWS", rep["env"])
            self.assertEqual(rep["uid"].strip(), "65534")
            self.assertEqual(canon_hash.file_digest(victim), before)
        finally:
            os.unlink(secret)

    def test_infinite_loop_is_killed(self):
        res, _ = self._run("t08b", "for(;;){}\n", seconds=5)
        self.assertNotEqual(res["exit"], 0)

    def test_fork_bomb_is_contained(self):
        res, _ = self._run("t08c", r'''
import * as cp from "node:child_process";
let n = 0;
for (let k = 0; k < 2000; k++) { try { cp.spawn("sleep", ["30"]); n++; } catch (e) { break; } }
console.log("spawned", n);
''', seconds=10)
        self.assertLessEqual(len(res["log"]), 70000)

    def test_output_bomb_is_bounded(self):
        try:
            res, out = self._run("t08d", r'''
import * as fs from "node:fs";
const [i, o] = process.argv.slice(2);
const b = Buffer.alloc(1 << 20, 1);
const fd = fs.openSync(o + "/big", "w");
for (let k = 0; k < 4096; k++) fs.writeSync(fd, b);
''', seconds=60)
            self.assertNotEqual(res["exit"], 0)   # ENOSPC inside the capped tmpfs
            self.assertLess(os.path.getsize(os.path.join(out, "big")), 70 << 20)
        except sandbox.SandboxError:
            pass                                  # or: output stream exceeded the cap


# --------------------------------------------------------------------------- benchmark
class T09_Benchmark(unittest.TestCase):
    def test_unverified_submission_is_not_benchmarked(self):
        cand = H.fresh("t09a")
        with open(os.path.join(cand, "bend", "bend2", "opt", "unverified.txt"), "w") as f:
            f.write("never verified\n")
        with self.assertRaises(bench.Refuse):
            bench.benchmark(H.package(cand), reps=1, log=lambda *a: None)

    def test_artifact_substituted_after_proof(self):
        """Prove artifact A, then try to benchmark a different binary B."""
        cand = H.fresh("t09b")
        arc = H.package(cand)
        self.assertEqual(H.verify(arc)["result"], "VALID")
        comp = load_competition(self_check=False)
        h, _ = canon_hash.tree_digest(os.path.join(cand, "bend"))
        binp = os.path.join(V.store_root(comp), "candidates", h.split(":")[1], "tree-radix", "program.bin")
        orig = open(binp, "rb").read()
        try:
            shutil.copyfile("/bin/echo", binp)       # a "faster" binary
            with self.assertRaises(bench.Refuse) as cm:
                bench.benchmark(arc, reps=1, log=lambda *a: None)
            self.assertIn("preserved binary artifact differs", str(cm.exception))
        finally:
            open(binp, "wb").write(orig)

    def test_certificate_tampered(self):
        cand = H.fresh("t09c")
        arc = H.package(cand)
        self.assertEqual(H.verify(arc)["result"], "VALID")
        comp = load_competition(self_check=False)
        h, _ = canon_hash.tree_digest(os.path.join(cand, "bend"))
        cp = os.path.join(V.store_root(comp), "candidates", h.split(":")[1], "certificate.json")
        orig = open(cp).read()
        try:
            H.edit_json(cp, lambda c: c.update(proof_hash="sha256:" + "5" * 64))
            with self.assertRaises(bench.Refuse):
                bench.benchmark(arc, reps=1, log=lambda *a: None)
        finally:
            open(cp, "w").write(orig)

    def test_submitted_binary_is_ignored(self):
        """A binary shipped inside proof/ is never used: the benchmarked artifact is
        the verifier-built one recorded in the certificate."""
        cand = H.fresh("t09d")
        shutil.copyfile("/bin/echo", os.path.join(cand, "proof", "program.bin"))
        arc = H.package(cand)
        rep = H.verify(arc)
        self.assertEqual(rep["result"], "VALID", rep)   # the extra file is inert data
        cert = json.load(open(rep["certificate"]))
        self.assertNotEqual(cert["workloads"]["tree-radix"]["artifacts"]["binary"],
                            canon_hash.file_digest("/bin/echo"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
