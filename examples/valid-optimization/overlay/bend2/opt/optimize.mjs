// Example competitor optimizer (UNTRUSTED). Lives in the candidate Bend repo
// at bend2/opt/optimize.mjs and is run by the verifier in a sandbox:
//
//   node bend2/opt/optimize.mjs <in_dir> <out_dir>
//
// in_dir/request.json lists the workloads; in_dir/<name>.ir.json is the
// reference VerifiedIR. For each workload it writes out_dir/<name>/chain.json
// and the intermediate programs. Nothing it claims is trusted: the verifier
// re-hashes every program, re-checks every rule step in the Lean kernel and
// requires a kernel-checked proof for every lemma step.
//
// Passes:
//  1. inline  — inline small non-recursive wrappers called by the entry
//               (certified by the library rule `inline`).
//  2. fuse    — first-order deforestation: consumer(producer(args)) where the
//               producer builds a tree the consumer immediately folds. Emits a
//               fresh fused function per pair.
//  3. fold    — fold/build fusion: a tail-recursive left fold over a String is
//               pushed into the functions that build the String, which then
//               thread the fold state instead of allocating characters.
//  Passes 2-3 are certified by one lemma step per workload, whose Lean proof
//  ships in the submission's proof/ directory.

import * as fs from "node:fs";
import * as path from "node:path";

const [inDir, outDir] = process.argv.slice(2);
const req = JSON.parse(fs.readFileSync(path.join(inDir, "request.json"), "utf8"));

const clone = (x) => JSON.parse(JSON.stringify(x));

// ---- de Bruijn helpers (mirror BendVerify.Lift) -----------------------------
function lift(e, c, d) {
  switch (e[0]) {
    case "var": return ["var", e[1] < c ? e[1] : e[1] + d];
    case "u32": case "nat": return e;
    case "prim": return ["prim", e[1], e[2].map((a) => lift(a, c, d))];
    case "ctr": return ["ctr", e[1], e[2], e[3].map((a) => lift(a, c, d))];
    case "call": return ["call", e[1], e[2].map((a) => lift(a, c, d))];
    case "let": return ["let", lift(e[1], c, d), lift(e[2], c + 1, d)];
    case "par": return ["par", lift(e[1], c, d), lift(e[2], c, d), lift(e[3], c + 2, d)];
    case "mat": return ["mat", e[1], lift(e[2], c, d), e[3].map(([k, b]) => [k, lift(b, c + k, d)])];
    case "natcase": return ["natcase", lift(e[1], c, d), lift(e[2], c, d), lift(e[3], c + 1, d)];
  }
  throw new Error("lift: " + e[0]);
}
function letsSeq(args, body) {
  const go = (as, j) => (as.length === 0 ? body : ["let", lift(as[0], 0, j), go(as.slice(1), j + 1)]);
  return go(args, 0);
}
// substitute: replace free var (depth c + i) for i < n by vals[i] (in outer scope), removing n binders
function subst(e, c, vals) {
  const n = vals.length;
  switch (e[0]) {
    case "var": {
      const i = e[1];
      if (i < c) return e;
      if (i < c + n) return lift(vals[i - c], 0, c);
      return ["var", i - n];
    }
    case "u32": case "nat": return e;
    case "prim": return ["prim", e[1], e[2].map((a) => subst(a, c, vals))];
    case "ctr": return ["ctr", e[1], e[2], e[3].map((a) => subst(a, c, vals))];
    case "call": return ["call", e[1], e[2].map((a) => subst(a, c, vals))];
    case "let": return ["let", subst(e[1], c, vals), subst(e[2], c + 1, vals)];
    case "par": return ["par", subst(e[1], c, vals), subst(e[2], c, vals), subst(e[3], c + 2, vals)];
    case "mat": return ["mat", e[1], subst(e[2], c, vals), e[3].map(([k, b]) => [k, subst(b, c + k, vals)])];
    case "natcase": return ["natcase", subst(e[1], c, vals), subst(e[2], c, vals), subst(e[3], c + 1, vals)];
  }
  throw new Error("subst: " + e[0]);
}
const calls = (e, f) => JSON.stringify(e).includes(`["call",${f},`);

// ---- pass 1: inline wrappers called from the entry --------------------------
function inlineWrappers(prog, entryIdx, steps, programs) {
  for (;;) {
    let found = null;
    const visit = (e, pathSoFar) => {
      if (found) return;
      if (e[0] === "call") {
        const f = prog.fns[e[1]];
        const simple = !/"(mat|natcase|par|let)"/.test(JSON.stringify(f.body));
        if (e[1] !== entryIdx && simple && !calls(f.body, e[1])) { found = { path: pathSoFar, e }; return; }
        e[2].forEach((a, j) => visit(a, [...pathSoFar, j]));
      }
    };
    visit(prog.fns[entryIdx].body, []);
    if (!found) return prog;
    const callee = prog.fns[found.e[1]];
    const replacement = letsSeq(found.e[2], callee.body);
    const next = clone(prog);
    next.fns[entryIdx].body = replaceAt(next.fns[entryIdx].body, found.path, replacement);
    steps.push({ kind: "rule", fn: entryIdx, path: found.path, rule: { name: "inline" } });
    programs.push(next);
    prog = next;
  }
}
function replaceAt(e, p, r) {
  if (p.length === 0) return r;
  const [k, ...rest] = p;
  const out = clone(e);
  if (e[0] === "call" || e[0] === "prim") out[2][k] = replaceAt(e[2][k], rest, r);
  else if (e[0] === "ctr") out[3][k] = replaceAt(e[3][k], rest, r);
  else throw new Error("replaceAt: unsupported position");
  return out;
}

// ---- pass 2: deforestation --------------------------------------------------
// consumer C: one ADT parameter, body = mat D (var 0) arms; each arm either
// uses only its fields, or is `par (C f1) (C f2) X` over its two fields.
// producer G: body is a natcase/mat whose leaves build D-constructors, and whose
// recursive leaf is `par (G ..) (G ..) (ctr D t [var 1, var 0])`.
function fuse(prog, C, G) {
  const c = prog.fns[C], g = prog.fns[G];
  if (c.params.length !== 1 || c.body[0] !== "mat" || JSON.stringify(c.body[2]) !== '["var",0]') return null;
  const D = c.body[1];
  const F = prog.fns.length; // index of the fused function
  const leaf = (e) => {
    if (e[0] === "ctr" && e[1] === D) {
      const [k, arm] = c.body[3][e[2]];
      // arm sees its k fields then C's parameter; C's parameter must be unused
      if (JSON.stringify(lift(arm, k, 1)) !== JSON.stringify(arm) && /"var"/.test(JSON.stringify(arm))) {
        // (conservative check below instead)
      }
      return subst(arm, 0, e[3].slice().reverse().map((x) => x));
    }
    if (e[0] === "par" && e[1][0] === "call" && e[1][1] === G && e[2][0] === "call" && e[2][1] === G
        && e[3][0] === "ctr" && e[3][1] === D && JSON.stringify(e[3][3]) === '[["var",1],["var",0]]') {
      const [k, arm] = c.body[3][e[3][2]];
      if (k !== 2 || arm[0] !== "par" || JSON.stringify(arm[1]) !== `["call",${C},[["var",1]]]`
          || JSON.stringify(arm[2]) !== `["call",${C},[["var",0]]]`) return undefined;
      return ["par", ["call", F, e[1][2]], ["call", F, e[2][2]], lift(arm[3], 4, -1)];
    }
    return undefined;
  };
  const walk = (e) => {
    if (e[0] === "natcase") { const z = walk(e[2]), s = walk(e[3]); return z && s ? ["natcase", e[1], z, s] : undefined; }
    if (e[0] === "mat") {
      const arms = e[3].map(([k, b]) => [k, walk(b)]);
      return arms.every(([, b]) => b) ? ["mat", e[1], e[2], arms] : undefined;
    }
    return leaf(e);
  };
  const body = walk(g.body);
  if (!body) return null;
  return { name: `${c.name}.${g.name}`, params: g.params, ret: c.ret, body };
}

// Note on `subst(arm, 0, fields)`: arm's free vars are its k fields (var 0 =
// last field) followed by C's own parameter at var k. `subst` with the fields
// list maps var i (i < k) to the i-th element, i.e. vals = fields reversed.

// ---- pass 3: fold/build fusion ---------------------------------------------
// consumer C(s: String, r: State) = match s { SNil -> FIN(r); SCon{h, t} -> ... C(t, NEW) }
// is pushed into the producers of s: every function that builds a String by
// prepending characters onto a `rest` argument gets a twin that threads the
// fold state instead of building the string.
function remapFree(e, map, c = 0) {
  const R = (x, d) => remapFree(x, map, c + d);
  switch (e[0]) {
    case "var": {
      if (e[1] < c) return e;
      const m = map(e[1] - c);
      if (m === undefined) throw new Error("variable escapes");
      return ["var", m + c];
    }
    case "u32": case "nat": return e;
    case "prim": return ["prim", e[1], e[2].map((a) => R(a, 0))];
    case "ctr": return ["ctr", e[1], e[2], e[3].map((a) => R(a, 0))];
    case "call": return ["call", e[1], e[2].map((a) => R(a, 0))];
    case "let": return ["let", R(e[1], 0), R(e[2], 1)];
    case "par": return ["par", R(e[1], 0), R(e[2], 0), R(e[3], 2)];
    case "mat": return ["mat", e[1], R(e[2], 0), e[3].map(([k, b]) => [k, R(b, k)])];
    case "natcase": return ["natcase", R(e[1], 0), R(e[2], 0), R(e[3], 1)];
  }
  throw new Error("remap");
}
const freeIn = (e, i, c = 0) => {
  switch (e[0]) {
    case "var": return e[1] === i + c;
    case "u32": case "nat": return false;
    case "prim": case "call": return e[2].some((a) => freeIn(a, i, c));
    case "ctr": return e[3].some((a) => freeIn(a, i, c));
    case "let": return freeIn(e[1], i, c) || freeIn(e[2], i, c + 1);
    case "par": return freeIn(e[1], i, c) || freeIn(e[2], i, c) || freeIn(e[3], i, c + 2);
    case "mat": return freeIn(e[2], i, c) || e[3].some(([k, b]) => freeIn(b, i, c + k));
    case "natcase": return freeIn(e[1], i, c) || freeIn(e[2], i, c) || freeIn(e[3], i, c + 1);
  }
};

function foldConsumer(prog, ci) {
  const f = prog.fns[ci];
  if (f.params.length !== 2 || f.params[0][0] !== "adt") return null;
  const S = f.params[0][1];
  if (prog.adts[S].name !== "String") return null;
  const b = f.body;
  if (b[0] !== "mat" || b[1] !== S || JSON.stringify(b[2]) !== '["var",1]') return null;
  const [[k0, nil], [k1, cons]] = b[3];
  if (k0 !== 0 || k1 !== 2) return null;
  // find the single tail call C(t, NEW) in the SCon arm and cut it out
  let found = 0;
  const cut = (e, d) => {
    if (e[0] === "call" && e[1] === ci && JSON.stringify(e[2][0]) === `["var",${d}]`) { found++; return e[2][1]; }
    if (e[0] === "mat") return ["mat", e[1], e[2], e[3].map(([k, x]) => [k, cut(x, d + k)])];
    if (e[0] === "let") return ["let", e[1], cut(e[2], d + 1)];
    return e;
  };
  const feedBody = cut(cons, 0);
  if (found !== 1) return null;
  try {
    // cons arm env: t=0, h=1, r=2, s=3  ->  feed(h, r) env: r=0, h=1
    const feed = remapFree(feedBody, (j) => ({ 1: 1, 2: 0 })[j]);
    // nil arm env: r=0, s=1 -> fin(r) env: r=0
    const fin = remapFree(nil, (j) => ({ 0: 0 })[j]);
    return { S, state: f.params[1], ret: f.ret, feed, fin };
  } catch { return null; }
}

function foldFusion(prog) {
  const next = clone(prog);
  let changed = false;
  for (let ci = 0; ci < prog.fns.length; ci++) {
    const info = foldConsumer(prog, ci);
    if (!info) continue;
    const C = prog.fns[ci].name;
    const isStr = (t) => t[0] === "adt" && t[1] === info.S;
    const added = new Map();   // key -> index in next.fns
    const add = (name, fn) => { const i = next.fns.push({ name, ...fn }) - 1; added.set(name, i); return i; };
    const feedI = add(`${C}.feed`, { params: [prog.adts[info.S].ctors[1].fields[0], info.state], ret: info.state, body: info.feed });
    const finI = add(`${C}.fin`, { params: [info.state], ret: info.ret, body: info.fin });
    const fusedFn = (gi, terminal) => {
      const key = `${C}.${prog.fns[gi].name}`;
      if (added.has(key)) return added.get(key);
      const g = prog.fns[gi];
      const i = add(key, null);
      const n = g.params.length;
      let body, params, ret;
      if (terminal) {        // G(args) -> G'(args, r): the state after G's whole string
        params = [...g.params, info.state]; ret = info.state;
        body = fuse(lift(g.body, 0, 1), ["var", 0], true, -1);
      } else {               // P(args, rest) -> P'(args, r)
        params = [...g.params.slice(0, n - 1), info.state]; ret = info.state;
        body = fuse(g.body, ["var", 0], false, 0);
      }
      next.fns[i] = { name: key, params, ret, body };
      return i;
    };
    // fuse a String-valued expression e whose continuation state is St.
    // restVar: index (at depth 0) of the producer's rest parameter, -1 if terminal.
    const fuse = (e, St, terminal, restVar, d = 0) => {
      const L = (x, k) => lift(x, 0, k);
      switch (e[0]) {
        case "var":
          if (!terminal && e[1] === restVar + d) return St;
          throw new Error("string variable is not the rest argument");
        case "ctr":
          if (e[1] !== info.S) throw new Error("not a string");
          if (e[2] === 0) { if (!terminal) throw new Error("producer drops its rest"); return St; }
          if (!terminal && freeIn(e[3][0], restVar, d)) throw new Error("rest inspected");
          return fuse(e[3][1], ["call", feedI, [e[3][0], St]], terminal, restVar, d);
        case "call": {
          const g = prog.fns[e[1]];
          if (!isStr(g.ret)) throw new Error("call does not produce a string");
          const args = e[2];
          if (g.params.length && isStr(g.params.at(-1))) {
            const pre = args.slice(0, -1);
            if (!terminal && pre.some((a) => freeIn(a, restVar, d))) throw new Error("rest inspected");
            const pi = fusedFn(e[1], false);
            return fuse(args.at(-1), ["call", pi, [...pre, St]], terminal, restVar, d);
          }
          if (!terminal) throw new Error("rest dropped by a terminal producer");
          return ["call", fusedFn(e[1], true), [...args, St]];
        }
        case "let": {
          if (!terminal && freeIn(e[1], restVar, d)) throw new Error("rest inspected");
          return ["let", e[1], fuse(e[2], L(St, 1), terminal, restVar, d + 1)];
        }
        case "natcase": {
          if (!terminal && freeIn(e[1], restVar, d)) throw new Error("rest inspected");
          return ["natcase", e[1], fuse(e[2], St, terminal, restVar, d), fuse(e[3], L(St, 1), terminal, restVar, d + 1)];
        }
        case "mat": {
          if (!terminal && freeIn(e[2], restVar, d)) throw new Error("rest inspected");
          return ["mat", e[1], e[2], e[3].map(([k, b]) => [k, fuse(b, L(St, k), terminal, restVar, d + k)])];
        }
      }
      throw new Error("unsupported producer shape");
    };
    // rewrite call sites C(X, S0) where X produces the string
    const site = (e) => {
      if (e[0] === "call" && e[1] === ci && e[2][0][0] === "call") {
        try {
          const r = ["call", finI, [fuse(e[2][0], e[2][1], true, -1)]];
          changed = true;
          return r;
        } catch { return e; }
      }
      if (e[0] === "call" || e[0] === "prim") return [e[0], e[1], e[2].map(site)];
      if (e[0] === "ctr") return ["ctr", e[1], e[2], e[3].map(site)];
      if (e[0] === "let") return ["let", site(e[1]), site(e[2])];
      if (e[0] === "par" || e[0] === "natcase") return [e[0], site(e[1]), site(e[2]), site(e[3])];
      if (e[0] === "mat") return ["mat", e[1], site(e[2]), e[3].map(([k, b]) => [k, site(b)])];
      return e;
    };
    for (let fi = 0; fi < prog.fns.length; fi++) {
      if (fi === ci) continue;
      next.fns[fi].body = site(prog.fns[fi].body);
    }
    if (changed) return next;
    return null;
  }
  return null;
}

const camel = (w) => w.split("-").map((x) => x[0].toUpperCase() + x.slice(1)).join("");
let workloadName = "";
function optimizeEntry(prog, entryIdx) {
  const steps = [];
  const programs = [prog];
  prog = inlineWrappers(prog, entryIdx, steps, programs);
  // repeatedly fuse call C [call G args] patterns reachable in the entry body
  let next = clone(prog);
  let changed = false;
  const letInline = (e) => {
    // let x = e1 in body  where x is used exactly once, unconditionally, as an argument
    if (e[0] === "let") {
      const b = e[2];
      const n = (JSON.stringify(b).match(/\["var",0\]/g) || []).length;
      if (n === 1 && !/"(mat|natcase|par|let)"/.test(JSON.stringify(b))) return subst(b, 0, [e[1]]);
    }
    return e;
  };
  const rewrite = (e) => {
    e = letInline(e);
    if (e[0] === "call" || e[0] === "prim") e = [e[0], e[1], e[2].map(rewrite)];
    if (e[0] === "call" && e[2].length >= 1 && e[2][0][0] === "call") {
      const C = e[1], inner = e[2][0], G = inner[1];
      if (e[2].length === 1) {
        const fused = fuse(next, C, G);
        if (fused) {
          const existing = next.fns.findIndex((f) => f.name === fused.name);
          const idx = existing >= 0 ? existing : next.fns.push(fused) - 1;
          changed = true;
          return ["call", idx, inner[2]];
        }
      }
    }
    return e;
  };
  // fuse from the inside out until nothing changes
  for (let round = 0; round < 8; round++) {
    changed = false;
    next.fns[entryIdx].body = rewrite(next.fns[entryIdx].body);
    if (!changed) break;
  }
  const folded = foldFusion(next);
  if (folded) next = folded;
  if (JSON.stringify(next) !== JSON.stringify(prog)) {
    steps.push({ kind: "lemma", proof: `Submission.${camel(workloadName)}.fusion` });
    programs.push(next);
  }
  return { steps, programs };
}

for (const w of req.workloads) {
  const prog = JSON.parse(fs.readFileSync(path.join(inDir, w.input), "utf8"));
  const entryIdx = prog.fns.findIndex((f) => f.name === w.entry);
  workloadName = w.name;
  const { steps, programs } = optimizeEntry(prog, entryIdx);
  const dir = path.join(outDir, w.name);
  fs.mkdirSync(dir, { recursive: true });
  const chain = { format: "bendverify-chain-v1", workload: w.name, steps: [] };
  steps.forEach((s, k) => {
    const file = `p${k + 1}.ir.json`;
    fs.writeFileSync(path.join(dir, file), JSON.stringify(programs[k + 1]));
    chain.steps.push({ ...s, program: file });
  });
  fs.writeFileSync(path.join(dir, "chain.json"), JSON.stringify(chain, null, 1));
  console.log(`${w.name}: ${steps.length} step(s), ${programs.at(-1).fns.length} functions`);
}
