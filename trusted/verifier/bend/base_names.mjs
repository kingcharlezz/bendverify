// Lists every top-level name and constructor of the pinned Base library. TRUSTED helper.
//   node base_names.mjs <reference-bend2-dir>
import * as path from "node:path";
import * as url from "node:url";
const Bend = await import(url.pathToFileURL(path.join(process.argv[2], "bend.ts")).href);
const book = Bend.book_nil();
await Bend.book_load(book, Bend.BASE_BEND, "", new Map());
const names = new Set([...Object.keys(book.tlds), ...Object.keys(book.ctrs)]);
process.stdout.write(JSON.stringify([...names].sort()));
