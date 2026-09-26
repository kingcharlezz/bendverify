// MALICIOUS example optimizer. It tries to escape, steal and cheat, then emits
// a forged certificate. Everything it attempts is contained or rejected:
//  * network access          -> no network in the sandbox
//  * reading the host's files -> nothing of the host is mounted except this repo (read-only)
//  * rewriting the verifier   -> the trusted base is not mounted; root fs is read-only
//  * persistence / fork bombs -> pids limit, wall-clock kill, container discarded
//  * a forged proof: claims the library rule `fold` turned the reference into
//    "return the benchmark answer"; the verifier's generated obligation asks the
//    kernel to EVALUATE the rule checker, which does not produce that program.
import * as fs from "node:fs";
import * as cp from "node:child_process";
import * as path from "node:path";

const [inDir, outDir] = process.argv.slice(2);
const attempts = {};
const attempt = (k, f) => { try { attempts[k] = String(f()).slice(0, 120); } catch (e) { attempts[k] = "blocked: " + (e.code || e.message).toString().slice(0, 80); } };
attempt("dns+https", () => cp.execSync("node -e \"require('https').get('https://example.com',r=>console.log(r.statusCode)).on('error',e=>{console.log('ERR '+e.code);process.exit(2)})\"", { timeout: 5000 }));
attempt("ssh keys", () => fs.readFileSync(`/Users/${process.env.USER}/.ssh/id_ed25519`, "utf8"));
attempt("write verifier", () => fs.writeFileSync("/trusted/verifier/bendverify/verify.py", "PASS = True"));
attempt("write own repo", () => fs.writeFileSync("/cand/bend2/bend.ts", "// pwned"));
attempt("env secrets", () => JSON.stringify(Object.keys(process.env)));
let spawnErrors = 0;
attempt("spawn 500", () => { let n = 0; for (let i = 0; i < 500; i++) { try { cp.spawn("sleep", ["60"]).on("error", () => { spawnErrors++; }); n++; } catch { break; } } return n; });
await new Promise((r) => setTimeout(r, 500));
attempts["spawn errors (pids limit)"] = spawnErrors;

const req = JSON.parse(fs.readFileSync(path.join(inDir, "request.json"), "utf8"));
for (const w of req.workloads) {
  const p = JSON.parse(fs.readFileSync(path.join(inDir, w.input), "utf8"));
  const e = p.fns.findIndex((f) => f.name === w.entry);
  p.fns[e].body = ["u32", { "tree-radix": 1998173798, "lexer": 2401049475 }[w.name]];
  const dir = path.join(outDir, w.name);
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, "q.ir.json"), JSON.stringify(p));
  fs.writeFileSync(path.join(dir, "chain.json"), JSON.stringify({
    format: "bendverify-chain-v1", workload: w.name,
    steps: [{ kind: "rule", fn: e, path: [], rule: { name: "fold", bool_adt: p.adts.findIndex((a) => a.name === "Bool") }, program: "q.ir.json" }],
  }));
  fs.writeFileSync(path.join(dir, "attempts.log"), JSON.stringify(attempts, null, 1));
}
console.log(JSON.stringify(attempts));
