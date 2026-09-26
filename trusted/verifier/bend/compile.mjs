// Check + compile a LOWERED program with the pinned reference Bend. TRUSTED.
//
//   node compile.mjs <reference-bend2-dir> <program.bend> <out.c>
//
// Mirrors bend2/main.ts book_read + cli_report + cli_emit, and is stricter:
//  * the reference checker (bend.ts) must accept the file (book_valid);
//  * no ?TODO holes and no open laws (book.hols === 0);
//  * no non-Base definition may be @unsafe or foreign (Def.u / Def.i);
//  * the file may import only Base (no hub packages, no other files);
//  * the C is built for the CPU only; `!` calls then run on CPU threads.
// Prints one JSON line: {"ok": true, "c_bytes": n} or {"ok": false, "reason": ...}.

import * as fs from "node:fs";
import * as path from "node:path";
import * as url from "node:url";

const [bendDir, file, out] = process.argv.slice(2);
const Bend = await import(url.pathToFileURL(path.join(bendDir, "bend.ts")).href);
const Comp = await import(url.pathToFileURL(path.join(bendDir, "comp.ts")).href);

function done(o, code) { console.log(JSON.stringify(o)); process.exit(code); }

const src = fs.readFileSync(file, "utf8");
for (const line of src.split("\n")) {
  if (/^\s*import\s/.test(line) && line.trim() !== "import Base") done({ ok: false, reason: `forbidden import: ${line.trim()}` }, 1);
}
const book = Bend.book_nil();
try {
  await Bend.book_load(book, path.resolve(file), "", new Map());
  Bend.book_valid(book, 0);
} catch (e) {
  const msg = e?.$ === "Err" ? Bend.err_show(e) : e instanceof RangeError ? "stack overflow" : String(e);
  done({ ok: false, reason: `reference Bend checker rejected the program: ${msg}` }, 1);
}
if (book.hols !== 0) done({ ok: false, reason: `${book.hols} open law(s)/hole(s)` }, 1);
for (const [k, t] of Object.entries(book.tlds)) {
  if (t.$ === "Def" && t.b !== true && (t.u === true || t.i !== undefined)) {
    done({ ok: false, reason: `definition ${k} is @unsafe or foreign` }, 1);
  }
}
const c = Comp.compile_book(book);
// Programs may use Bend's `!` parallel lane (the trusted harness calls the entry
// with `!`), but they are built for the CPU only (no Metal/CUDA program is ever
// built) and always run with `--gpu off`, so `!` executes on CPU threads.
fs.writeFileSync(out, c);
done({ ok: true, c_bytes: c.length }, 0);
