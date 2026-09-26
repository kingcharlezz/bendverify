// INVALID example optimizer (the classic benchmark cheat). It "knows" the
// benchmark inputs and replaces each workload's whole computation by its answer:
//     tree-radix: run(n, x) = 1998173798      (correct for run(22, 0))
//     lexer:      run(d, i) = 2401049475      (correct for run(23, 0))
// Fantastically fast, correct on the benchmark inputs, WRONG for every other input. The submission reuses the valid submission's proof export
// (proof A). No proof can exist: the generated obligation is false.
import * as fs from "node:fs";
import * as path from "node:path";
const [inDir, outDir] = process.argv.slice(2);
const req = JSON.parse(fs.readFileSync(path.join(inDir, "request.json"), "utf8"));
for (const w of req.workloads) {
  const p = JSON.parse(fs.readFileSync(path.join(inDir, w.input), "utf8"));
  const e = p.fns.findIndex((f) => f.name === w.entry);
  const answer = { "tree-radix": 1998173798, "lexer": 2401049475 }[w.name];
  p.fns[e].body = ["u32", answer];
  const dir = path.join(outDir, w.name);
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, "q.ir.json"), JSON.stringify(p));
  fs.writeFileSync(path.join(dir, "chain.json"), JSON.stringify({
    format: "bendverify-chain-v1", workload: w.name,
    steps: [{ kind: "lemma", proof: w.name === "lexer" ? "Submission.Lexer.fusion" : "Submission.TreeRadix.fusion", program: "q.ir.json" }],
  }));
}
