// Bend -> VerifiedIR extractor (competition v1). TRUSTED.
//
//   node extract.mjs <reference-bend2-dir> <workload.bend> <entry> <out.ir.json>
//
// Loads and checks a workload with the PINNED REFERENCE Bend checker
// (reference/bend/bend2/bend.ts; never a competitor's copy), then translates
// every definition reachable from <entry> into VerifiedIR. Anything outside
// the modelled fragment is REJECTED, never approximated:
//
//   * open laws / ?TODO holes (book.hols != 0)          -> reject
//   * @unsafe / def f? (Def.u), foreign imports (Def.i) -> reject
//   * templates (Def.x > 0), laws used as code          -> reject
//   * types other than U32, Nat, Base Bool/Char/String, parameterless user
//     `is Data` datatypes, and ONE monomorphic pair instance `A & B`  -> reject
//   * F32, Array, closures/lambdas, IO, other Base datatypes          -> reject
//   * Base functions other than the U32/Nat primitives in PRIMS -> reject
//   * U32/String literal patterns, non-exhaustive matches        -> reject
//   * parallel lets with more than two bindings                  -> reject
//
// The meaning of each Base primitive is fixed by BendVerify.Prim.eval; its
// agreement with Base's pure-Bend definition is part of the trusted base and is
// spot-checked by tests/integration/test_prim_conformance.py.

import * as fs from "node:fs";
import * as path from "node:path";
import * as url from "node:url";

const [bendDir, file, entry, out] = process.argv.slice(2);
if (!out) {
  console.error("usage: extract.mjs <bend2-dir> <workload.bend> <entry> <out.ir.json>");
  process.exit(2);
}
const Bend = await import(url.pathToFileURL(path.join(bendDir, "bend.ts")).href);

const PRIMS = {
  "U32.add": "u32_add", "U32.sub": "u32_sub", "U32.mul": "u32_mul", "U32.div": "u32_div",
  "U32.mod": "u32_mod", "U32.and": "u32_and", "U32.or": "u32_or", "U32.xor": "u32_xor",
  "U32.not": "u32_not", "U32.shl": "u32_shl", "U32.shr": "u32_shr", "U32.shln": "u32_shln",
  "U32.shrn": "u32_shrn", "U32.inc": "u32_inc", "U32.is_eq": "u32_is_eq", "U32.is_ne": "u32_is_ne",
  "U32.is_lt": "u32_is_lt", "U32.is_le": "u32_is_le", "U32.is_gt": "u32_is_gt",
  "U32.is_ge": "u32_is_ge", "U32.is_zero": "u32_is_zero", "U32.to_nat": "u32_to_nat",
  "U32.from_nat": "u32_from_nat",
  "Nat.add": "nat_add", "Nat.sub": "nat_sub", "Nat.mul": "nat_mul", "Nat.div": "nat_div",
  "Nat.mod": "nat_mod", "Nat.is_eq": "nat_is_eq", "Nat.is_ne": "nat_is_ne", "Nat.is_lt": "nat_is_lt",
  "Nat.is_le": "nat_is_le", "Nat.is_gt": "nat_is_gt", "Nat.is_ge": "nat_is_ge",
  "Bool.and": "bool_and", "Bool.or": "bool_or", "Bool.not": "bool_not",
};

// Base datatypes admitted with their exact shapes (field types by name).
const BASE_ADTS = {
  Bool: [["False", []], ["True", []]],
  Char: [["Chr", ["u32"]]],
  String: [["SNil", []], ["SCon", ["Char", "String"]]],
};

class Reject extends Error {}
function reject(msg) { throw new Reject(msg); }

function strip(t) {
  while (t && t.$ === "Ann") t = t.x;
  return t;
}

// ---------------------------------------------------------------- load + check
const book = Bend.book_nil();
let loadError = null;
try {
  await Bend.book_load(book, path.resolve(file), "", new Map());
  Bend.book_valid(book, 0);
} catch (e) {
  loadError = `reference Bend checker rejected the program: ${e?.$ === "Err" ? Bend.err_show(e) : e}`;
}
if (loadError === null && book.hols !== 0) loadError = `program has ${book.hols} open law(s) / ?TODO hole(s)`;

// ---------------------------------------------------------------- types
const adtIndex = new Map();   // name -> index
const adts = [];

function usesLevel(t, lvl) {
  if (t === null || typeof t !== "object") return false;
  if (t.$ === "Var" && t.i === lvl) return true;
  for (const [k, v] of Object.entries(t)) if (k !== "s" && usesLevel(v, lvl)) return true;
  return false;
}

// `A & B` is Base `Pair(A, B) = Sigma<&1, &1, A, _ => B>`.
function pairParts(t) {
  if (t.$ === "App") {
    const f = strip(t.f);
    if (f.$ === "App" && strip(f.f).$ === "Ref" && strip(f.f).k === "Pair") return [f.x, t.x];
  }
  if (t.$ === "ADT" && t.k === "Sigma" && t.x.length === 4) {
    const lam = strip(t.x[3]);
    if (lam.$ === "Lam" && !usesLevel(lam.f, lam.i)) return [t.x[2], lam.f];
  }
  return null;
}

function tyName(ty) {
  if (ty === "u32") return "U32";
  if (ty === "nat") return "Nat";
  return adts[ty[1]].name;
}

let pairInstance = null;
function pairRef(A, B) {
  const a = lowerType(A), b = lowerType(B);
  const name = `${tyName(a)} & ${tyName(b)}`;
  if (adtIndex.has(name)) return adtIndex.get(name);
  if (pairInstance !== null) reject(`more than one pair type instance (${adts[pairInstance].name}, ${name}) is outside the v1 fragment`);
  const idx = adts.length;
  adtIndex.set(name, idx);
  adts.push({ name, ctors: [{ name: "Tuple", fields: [a, b] }] });
  pairInstance = idx;
  return idx;
}

function lowerType(T) {
  let t = strip(Bend.term_force ? Bend.term_force(T) : T);
  const pp = pairParts(t);
  if (pp) return ["adt", pairRef(pp[0], pp[1])];
  if (t.$ === "Ref" || (t.$ === "ADT" && t.x.length === 0)) {
    const k = t.k;
    if (k === "U32") return "u32";
    if (k === "Nat") return "nat";
    return ["adt", adtRef(k)];
  }
  reject(`unsupported type ${JSON.stringify(t, (k, v) => (k === "s" ? undefined : v)).slice(0, 120)}`);
}

function adtRef(name) {
  if (adtIndex.has(name)) return adtIndex.get(name);
  if (name.includes(" & ")) reject(`unknown pair instance ${name}`);
  const tld = book.tlds[name];
  if (!tld || tld.$ !== "ADT") reject(`unknown or non-datatype type ${name}`);
  if (tld.b && !(name in BASE_ADTS)) reject(`Base datatype ${name} is outside the v1 fragment`);
  if (tld.n !== 0) reject(`datatype ${name} has parameters (outside the v1 fragment)`);
  // kind must be Data (Kind(&2))
  const K = strip(Bend.term_lower(tld.T));
  if (!(K.$ === "Typ" && K.g.$ === "Qua" && K.g.q.$ === "Many")) reject(`datatype ${name} is not 'is Data'`);
  const idx = adts.length;
  adtIndex.set(name, idx);
  const entryObj = { name, ctors: [] };
  adts.push(entryObj);
  for (const c of tld.c) {
    let T = Bend.term_lower(c.T);
    const fields = [];
    for (let j = 0; j < c.n; j++) {
      T = strip(T);
      if (T.$ !== "All") reject(`constructor ${c.k}: malformed type`);
      if (T.q.$ === "None") reject(`constructor ${c.k}: erased field`);
      fields.push(lowerType(T.A));
      T = T.B;
    }
    entryObj.ctors.push({ name: c.k, fields });
  }
  if (name in BASE_ADTS) {
    const got = JSON.stringify(entryObj.ctors.map((c) => [c.name, c.fields.map(tyName)]));
    if (got !== JSON.stringify(BASE_ADTS[name]).replaceAll('"u32"', '"U32"')) {
      reject(`Base ${name} does not have the expected shape (${got})`);
    }
  }
  return idx;
}

function ctorInfo(k) {
  if (k === "Tuple") {
    if (pairInstance === null) reject("pair constructor without a pair type in any signature");
    return { adt: adts[pairInstance].name, tag: 0, arity: 2, pair: true };
  }
  const c = book.ctrs[k];
  if (!c) reject(`unknown constructor ${k}`);
  // find its datatype
  for (const name of Object.keys(book.tlds)) {
    const t = book.tlds[name];
    if (t.$ === "ADT") {
      const tag = t.c.findIndex((x) => x.k === k);
      if (tag >= 0) return { adt: name, tag, arity: t.c[tag].n };
    }
  }
  reject(`constructor ${k} has no datatype`);
}

// ---------------------------------------------------------------- functions
const fnIndex = new Map();
const fnNames = [];
const fns = [];

function defSig(name) {
  const d = book.tlds[name];
  if (!d || d.$ !== "Def") reject(`unknown definition ${name}`);
  if (d.b) reject(`Base definition ${name} is not a v1 primitive`);
  if (d.u) reject(`${name} is @unsafe (termination unchecked)`);
  if (d.i) reject(`${name} is a foreign import`);
  if (d.x > 0) reject(`${name} is a template (outside the v1 fragment)`);
  if (d.v === null) reject(`${name} is an open law`);
  let T = Bend.term_lower(d.T);
  const params = [];
  const erased = [];
  for (let j = 0; j < d.n; j++) {
    T = strip(T);
    if (T.$ !== "All") reject(`${name}: malformed type`);
    if (T.q.$ === "None") { erased.push(true); params.push(null); }
    else { erased.push(false); params.push(lowerType(T.A)); }
    T = T.B;
  }
  const ret = lowerType(T);
  return { d, params, erased, ret };
}

function fnRef(name) {
  if (fnIndex.has(name)) return fnIndex.get(name);
  const idx = fnNames.length;
  fnIndex.set(name, idx);
  fnNames.push(name);
  fns.push(null);
  return idx;
}

// Scope: a list of IR binder positions; Bend level -> {pos} or {erased:true}
class Scope {
  constructor() { this.depth = 0; this.map = new Map(); }
  bind(level) { const p = this.depth++; if (level !== undefined) this.map.set(level, { pos: p }); return p; }
  alias(level, pos) { this.map.set(level, { pos }); }
  erase(level) { this.map.set(level, { erased: true }); }
  varOf(level) {
    const b = this.map.get(level);
    if (!b) reject(`free variable at level ${level}`);
    if (b.erased) reject("erased variable used in live code");
    return ["var", this.depth - 1 - b.pos];
  }
  save() { return { depth: this.depth, map: new Map(this.map) }; }
  restore(s) { this.depth = s.depth; this.map = s.map; }
}

function spine(t) {
  const args = [];
  t = strip(t);
  while (t.$ === "App") { args.unshift(strip(t.x)); t = strip(t.f); }
  return { head: t, args };
}

function natLit(n) {
  if (!Number.isInteger(n) || n < 0 || n >= 2 ** 48) reject("Nat literal out of range");
  return ["nat", n];
}

// Extract an expression in "value" position.
function expr(t, sc) {
  t = strip(t);
  switch (t.$) {
    case "Var": return sc.varOf(t.i);
    case "Lit":
      if (t.k === "U32") { if (!(Number.isInteger(t.v) && t.v >= 0 && t.v < 2 ** 32)) reject("bad U32 literal"); return ["u32", t.v]; }
      if (t.k === "Nat") return natLit(t.v);
      if (t.k === "String") {
        const str = adtRef("String"), chr = adtRef("Char");
        let e = ["ctr", str, 0, []];
        for (const ch of [...t.v].reverse()) e = ["ctr", str, 1, [["ctr", chr, 0, [["u32", ch.codePointAt(0)]]], e]];
        return e;
      }
      reject(`literal of type ${t.k} is outside the v1 fragment`);
    case "Ctr": {
      if (t.k === "Zero" && t.x.length === 0) return ["nat", 0];
      if (t.k === "Succ" && t.x.length === 1) return ["prim", "nat_add", [["nat", 1], expr(t.x[0], sc)]];
      const ci = ctorInfo(t.k);
      const adt = adtRef(ci.adt);
      if (t.x.length !== ci.arity) reject(`constructor ${t.k}: arity`);
      return ["ctr", adt, ci.tag, t.x.map((a) => expr(a, sc))];
    }
    case "Ref":
    case "App": {
      const { head, args } = spine(t);
      if (head.$ === "Lam" || head.$ === "Mat") return applyExpr(head, args, sc);
      if (head.$ !== "Ref") reject(`unsupported application head ${head.$}`);
      const k = head.k;
      if (PRIMS[k] !== undefined) return ["prim", PRIMS[k], args.map((a) => expr(a, sc))];
      const sig = defSig(k);
      if (args.length !== sig.erased.length) reject(`${k}: partial or over-application is outside the v1 fragment`);
      const live = [];
      args.forEach((a, j) => { if (!sig.erased[j]) live.push(expr(a, sc)); });
      return ["call", fnRef(k), live];
    }
    case "Let": {
      const saved = sc.save();
      const live = t.q.map((q) => q.$ !== "None");
      const vals = [];
      t.v.forEach((v, j) => { if (live[j]) vals.push(expr(v, sc)); });
      if (vals.length > 2) reject("parallel let with more than two bindings is outside the v1 fragment");
      t.i.forEach((lvl, j) => { if (live[j]) sc.bind(lvl); else sc.erase(lvl); });
      const body = expr(t.f, sc);
      sc.restore(saved);
      if (vals.length === 0) return body;
      if (vals.length === 1) return ["let", vals[0], body];
      return ["par", vals[0], vals[1], body];
    }
    case "Lam": case "Mat": reject("closures / unapplied lambdas are outside the v1 fragment");
    default: reject(`term ${t.$} is outside the v1 fragment`);
  }
}

// `head` (a Lam or Mat) applied to argument terms.
function applyExpr(head, args, sc) {
  // Bind non-variable arguments with lets, then apply to variables.
  const saved = sc.save();
  const lets = [];
  const vars = [];
  for (const a of args) {
    const a2 = strip(a);
    if (a2.$ === "Var") { vars.push({ level: a2.i }); continue; }
    lets.push(expr(a2, sc));
    vars.push({ pos: sc.bind(undefined) });
  }
  let body = apply(head, vars, sc);
  sc.restore(saved);
  for (let j = lets.length - 1; j >= 0; j--) body = ["let", lets[j], body];
  return body;
}

// Apply a case tree to pending argument slots ({level} = existing Bend variable, {pos} = IR binder).
function slotVar(slot, sc) {
  if (slot.pos !== undefined) return ["var", sc.depth - 1 - slot.pos];
  return sc.varOf(slot.level);
}

function apply(t, pending, sc) {
  t = strip(t);
  if (pending.length === 0) return expr(t, sc);
  const [a, ...rest] = pending;
  if (t.$ === "Lam") {
    const saved = sc.save();
    if (a.pos !== undefined) sc.alias(t.i, a.pos);
    else {
      const b = sc.map.get(a.level);
      if (!b) reject("free variable");
      sc.map.set(t.i, b);
    }
    const r = apply(t.f, rest, sc);
    sc.restore(saved);
    return r;
  }
  if (t.$ === "Mat") return matchChain(t, a, rest, sc);
  reject(`a definition body applies a ${t.$} to arguments (outside the v1 fragment)`);
}

function matchChain(t, scrutSlot, rest, sc) {
  // collect the chain Mat k1 h1 -> Mat k2 h2 -> ... -> (Efq | default)
  const cases = new Map();
  let dflt = null;
  let cur = strip(t);
  while (cur.$ === "Mat") {
    if (!cases.has(cur.k)) cases.set(cur.k, cur.h);
    cur = strip(cur.m);
  }
  if (cur.$ !== "Efq") dflt = cur;
  const scrut = slotVar(scrutSlot, sc);
  const ks = [...cases.keys()];
  if (ks.every((k) => k === "Zero" || k === "Succ")) {
    const arm = (k) => {
      const saved = sc.save();
      let r;
      if (cases.has(k)) {
        if (k === "Zero") r = apply(cases.get(k), rest, sc);
        else { const p = sc.bind(undefined); r = apply(cases.get(k), [{ pos: p }, ...rest], sc); }
      } else if (dflt) {
        if (k === "Succ") sc.bind(undefined);
        r = apply(dflt, [scrutSlotShift(scrutSlot), ...rest], sc);
      } else reject("non-exhaustive Nat match");
      sc.restore(saved);
      return r;
    };
    return ["natcase", scrut, arm("Zero"), arm("Succ")];
  }
  const infos = ks.map(ctorInfo);
  const adtName = infos[0].adt;
  if (!infos.every((i) => i.adt === adtName)) reject("match mixes constructors of different datatypes");
  const adt = adtRef(adtName);
  const ctorList = infos[0].pair ? [{ k: "Tuple", n: 2 }] : book.tlds[adtName].c;
  const arms = ctorList.map((c) => {
    const saved = sc.save();
    const fieldSlots = [];
    for (let j = 0; j < c.n; j++) fieldSlots.push({ pos: sc.bind(undefined) });
    let r;
    if (cases.has(c.k)) r = apply(cases.get(c.k), [...fieldSlots, ...rest], sc);
    else if (dflt) r = apply(dflt, [scrutSlotShift(scrutSlot), ...rest], sc);
    else reject(`non-exhaustive match: no case for ${c.k}`);
    sc.restore(saved);
    return [c.n, r];
  });
  return ["mat", adt, scrut, arms];
}

// slots referring to IR positions stay valid under new binders (positions are absolute)
function scrutSlotShift(s) { return s; }

function extractFn(name) {
  const sig = defSig(name);
  const sc = new Scope();
  const slots = [];
  sig.erased.forEach((er) => { if (!er) slots.push({ pos: sc.bind(undefined) }); else slots.push({ erased: true }); });
  // The body consumes ALL n parameters (erased ones included) via its Lam/Mat chain.
  // The compiler (comp.ts) compiles the checker's elaborated body Def.e, while the
  // checker's own semantics is stated on Def.v. Translate BOTH and require the
  // same IR, so the extracted meaning is that of the code that gets compiled.
  if (!sig.d.e) reject(`${name}: no elaborated body (not checked?)`);
  const body = applyErasedAware(sig.d.e, slots, sc);
  const sc2 = new Scope();
  const slots2 = [];
  sig.erased.forEach((er) => { if (!er) slots2.push({ pos: sc2.bind(undefined) }); else slots2.push({ erased: true }); });
  const bodyV = applyErasedAware(Bend.term_lower(sig.d.v), slots2, sc2);
  if (JSON.stringify(body) !== JSON.stringify(bodyV)) reject(`${name}: elaborated and source bodies disagree`);
  return { name, params: sig.params.filter((p) => p !== null), ret: sig.ret, body };
}

function applyErasedAware(t, slots, sc) {
  // Erased parameters are consumed by Lams whose variable must not be used live.
  t = strip(t);
  if (slots.length === 0) return expr(t, sc);
  const [s, ...rest] = slots;
  if (s.erased) {
    if (t.$ !== "Lam") reject("erased parameter must be bound by a plain binder");
    const saved = sc.save();
    sc.erase(t.i);
    const r = applyErasedAware(t.f, rest, sc);
    sc.restore(saved);
    return r;
  }
  if (rest.some((r) => r.erased)) {
    // live param followed by erased ones: handle Lam directly, Mat would need
    // erased slots inside arms (not needed by v1 workloads)
    if (t.$ !== "Lam") reject("erased parameter after a matched parameter is outside the v1 fragment");
    const saved = sc.save();
    sc.alias(t.i, s.pos);
    const r = applyErasedAware(t.f, rest, sc);
    sc.restore(saved);
    return r;
  }
  return apply(t, slots, sc);
}

try {
  if (loadError !== null) reject(loadError);
  const e = book.tlds[entry];
  if (!e || e.$ !== "Def") reject(`entry ${entry} not found`);
  // Pre-pass: register the pair instance used in any reachable signature before
  // any body mentions `Tuple` (other datatypes keep discovery order, so programs
  // without pairs extract exactly as before).
  const registerPairs = (t) => {
    if (t === null || typeof t !== "object") return;
    const pp = t.$ ? pairParts(strip(t)) : null;
    if (pp) { pairRef(pp[0], pp[1]); return; }
    for (const [k, v] of Object.entries(t)) if (k !== "s" && typeof v !== "function") registerPairs(v);
  };
  const reach = new Set([entry]);
  const todo = [entry];
  const refs = (t, out) => {
    if (t === null || typeof t !== "object") return;
    if (t.$ === "Ref" && typeof t.k === "string") out.add(t.k);
    for (const [k, v] of Object.entries(t)) if (k !== "s" && typeof v !== "function") refs(v, out);
  };
  while (todo.length) {
    const k = todo.pop();
    const d = book.tlds[k];
    if (!d || d.$ !== "Def" || PRIMS[k] !== undefined) continue;
    registerPairs(Bend.term_lower(d.T));
    const out = new Set();
    if (d.v) refs(Bend.term_lower(d.v), out);
    for (const r of out) {
      if (!reach.has(r) && book.tlds[r]?.$ === "Def" && PRIMS[r] === undefined) { reach.add(r); todo.push(r); }
    }
  }
  fnRef(entry);
  for (let i = 0; i < fnNames.length; i++) fns[i] = extractFn(fnNames[i]);
  const prog = { format: "verifiedir-v1", adts, fns };
  fs.writeFileSync(out, JSON.stringify(prog));
  console.log(JSON.stringify({ ok: true, fns: fnNames.length, adts: adts.map((a) => a.name) }));
} catch (err) {
  if (err instanceof Reject) {
    console.log(JSON.stringify({ ok: false, reason: err.message }));
    process.exit(1);
  }
  throw err;
}
