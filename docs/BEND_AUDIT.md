# Bend audit (for the BendVerify verified-optimisation competition)

Audited revision: `bendlang/bend` **574b6d39a235b539eb19a5c532993a0abb3d11ad**
("The flake names 2.0.29", 2026-09-26), cloned to `reference/bend`.
Files read in full: `bend2/bend.ts` (3,787 lines), `bend2/comp.ts` (6,352), `bend2/main.ts` (869),
`bend2/bend.lean` (20,988), `bend2/base.bend` (3,018), `guide/GUIDE.md`, `README.md`, `AGENTS.md`,
`WONTFIX.txt`, `gates/*.ts`, every `bench/runtime/*/main.bend`, and a survey of `tests/`.
Every claim below was either read in the source (line numbers given) or **reproduced by running
the pinned code under Node 24.4.1** (no Bun needed: Node's type stripping loads `bend.ts` and
`comp.ts` directly).

The conclusion that drives the whole design is stated first:

> **Bend's own proof machinery does not give the guarantee a compiler-optimisation competition
> needs.** `bend PROOF.bend` checks *laws about Bend programs* with `bend.ts`; nothing (neither
> `bend.ts` nor `bend.lean`) relates a Bend program to the C/JS code `comp.ts` emits, and
> `comp.ts` has no internal IR that could be verified in place. The competition therefore defines its
> own small formal IR (VerifiedIR), extracts it from checked Bend, and requires kernel-checked
> equivalence proofs about it (see `SEMANTICS.md`, `TRUST_MODEL.md`).

---

## A. What `bend.ts` considers a valid Bend Book

**Data structures** (`bend.ts:313-319`):

```ts
type Def  = { $:"Def"; n; x; T: HTerm; v: HTerm|null; e?: LTerm; b?; u?; i?: string[]; m? }
type ADT  = { $:"ADT"; n; g; T: HTerm; c: Ctr[]; b? }
type Ctr  = { k: Name; n: number; T: HTerm }
type Book = { tlds: Record<Name,TLD>; ctrs: Record<Name,Ctr>; order: Name[]; hols: number;
              tmps: Record<Name, Record<string,Name>> }
```

| Def field | meaning |
|---|---|
| `n` | arity (telescope length; for a law, the number of leading `for` clauses) |
| `x` | number of leading `~` template parameters (`x > 0` ⇒ template) |
| `T` | the type, a closed HOAS term |
| `v` | the body **as written** (after pattern flattening), or `null` for an open law, a foreign def, or a bodiless Base law |
| `e` | the **checked, elaborated body** written by `book_valid`/`def_check` (`bend.ts:3780, 3674`): every node wrapped in `Ann(x, type)`, template calls replaced by instances `f~N` |
| `b` | Base flag (set for every TLD parsed from `base.bend`, `bend.ts:1011-1016`) |
| `u` | `@unsafe` / `def f?` (termination check skipped) |
| `i` | foreign import paths (`import "./x.c"`, `"./x.js"`) |
| `m` | declaring file's namespace |

Terms are a tagged union on `$` (`bend.ts:281-304`): `Var Ref Sub Let Typ Qnt Qua Min All Lam App
ADT Ctr Lit Mat Efq Eql Rfl Rwt Hol Ann`. Every node carries a span `s` that contains **the whole
source file** (drop it before serialising). `term_lower` gives a first-order view in which
`Var.i` is the binder's *level*. A `match` is not a node: pattern flattening
(`body_flatten`/`match_flatten`, `bend.ts:2540-2737`) compiles it into λ-case chains
`Mat{k: ctor, h: fields ⇒ …, m: next}` ending in `Efq` or a default arm that receives the whole
scrutinee. A parallel call `a b = f(x) g(y)` is one `Let` with two names; `f!(x)` is a `Ref` with
`b: true`.

**What `book_valid` checks** (`bend.ts:3709-3787`), in order, for every TLD:
bidirectional type checking in one linear pass (`bend.ts:3120-3626`) with quantities
`&0/&1/&2` (erased / affine / reusable), kinds `Type = Kind(&1)`, `Data = Kind(&2)`, the
**live/dead** discipline (types, erased arguments and equations are checked "dead" and may
diverge; live code may not), definition order (a live call may only target an earlier def,
except that Base may call its own later-filled laws, `bend.ts:3233`), and **structural
termination** of live self-calls (left-to-right lexicographic descent on pattern-bound
subterms; mutual recursion is impossible by the ordering rule). `Type : Type` holds and there is
no positivity check; consistency rests on the live/dead wall.

**What `book_valid` does *not* reject** (reproduced):

* **`?TODO` holes and open laws** are only *counted* in `book.hols` (`bend.ts:1921-1923,
  3764-3766`). The rejection lives in `main.ts:778` (`if (hols > 0) throw …`). A tool calling
  `book_valid` directly must check `hols` itself — our extractor and compiler driver do.
* **`@unsafe` defs** (and `def f?`) pass: termination is skipped (`bend.ts:3241`), they may call
  later defs and open laws live (`3233`) and may duplicate non-Data values (`645-647`); a safe def
  may call them. A looping `bottom?: Nat -> Empty` filling a law passes `book_valid`.
  Only `main.ts:cli_report` (`690-729`) *reports* them, and it still exits 0.
* **Foreign defs** are trusted by type only (the result must be Base `IO(…)`, `3765-3777`);
  their `.c/.js` files are never read by the checker.

**Primitives are not built in.** `term_wnf` special-cases no numeric name. `U32` is a Base
datatype over a 32-bit `Word` (LSB first) and every U32/Nat operation is an ordinary Base
definition. Reproduced with `{==}` proofs: U32 arithmetic wraps mod 2^32,
`U32.div(a,0) = 0`, `U32.mod(a,0) = a`, shifts by ≥ 32 give 0, `Nat.sub` truncates,
`Nat.div(a,0) = 0`, `Nat.mod(a,0) = a`. All F32 operations are **bodiless laws**: nothing about
floating point computes (or can be proven) in the checker.

## B. What `comp.ts` consumes

`compile_book(book)` (C) and `js_book(book)` (JS) take the checked Book and read only `tlds`
and `ctrs`. The first consumer of a definition is `fun_of` (`comp.ts:1220-1241`), whose key line is

```ts
const h = tld.e === undefined ? null : Bend.term_higher(tld.e);   // comp.ts:1227
```

i.e. **the compiler compiles the elaborated body `e`, not the source body `v`** (the interpreter
used by `bend file.bend` for a pure `main` normalises `v`). It uses `T` for erasure and layouts,
`n` for arity, `b` to allow native templates only for Base names, `i` for foreign imports and `m`
for namespaces. It **never reads** `u` (`@unsafe` compiles like any other def), `x`
(templates are compiled only through the instances the checker minted), or `book.hols`
(a `?TODO` hole silently compiles to `0` in C and `null` in JS — reproduced: `U32.add(?TODO, 5)`
prints `5`).

## C. Every transformation between the Book and the emitted C / JS

There is **no separate IR**: one monolithic pass interleaves analysis and C-text emission
("The emitter is the analysis", `comp.ts:1346`) and iterates to a whole-program fixpoint of
ownership facts (`comp.ts:2943-2959`). In order:

1. **Name/ownership guard** `book_owned` (1431-1442).
2. **Reachability & call-graph facts** `file_book` (1353-1429): call-site counts, bang targets,
   "flat" = no fork, no `!`, only tail self-calls.
3. **Erasure / arity raising / signatures** `fun_of`, `def_raise` (1220-1263): erased (`-x`)
   parameters dropped, lambdas under all arms opened, parameter and return layouts computed.
4. **Printable-main descriptor** `show_main` (1928-1991).
5. **Fixpoint emission loop** (2943-2959) over every def, with, inside `emit_body`/`emit_expr`:
   on-demand literal expansion (Nat literals > 256 become `U32.to_nat(lit)`); spine flattening and
   argument erasure (`term_spine` 716-748); eta for under-application (750-767); **ANF**
   (`anf` 2000-2092: non-flat calls cut out of argument positions, parallel lets whose values are
   not all calls split into sequential lets, rewrites dropped); **partial evaluation**
   `emit_fold`/`emit_unfold` (2394-2465: a call of a flat def whose matches are decided by
   constant constructor arguments is inlined, `FOLD_FUEL = 8192` nodes per segment; primitive ops
   on constants are *not* evaluated — clang does that); **intrinsics** (Base `U32.add` etc. →
   C/JS templates, `OPERATIONS` 152-293); **constructor layout packing** (flat words vs boxed heap
   nodes, static nodes, `lay_of` 986-1004); **use counting, dup/drop, borrow/own, "hot" sharing
   facts** (1444-1519, 1689-1713, 1853-1893); **match compilation** (tag compares, Nat rows, U32
   bit rows, **lookup tables whose contents are computed at compile time by evaluating the JS
   templates**, 2689-2791); **frees and node reuse** on match (Perceus-like, 1632-1664);
   **closures** (`Clo~apply`); **"once" inlining** of single-call-site defs (2599);
   **spins** (a flat def becomes a C function with a `continue` loop for self tail calls,
   `SPIN_FAR = 256`); **tail calls** (`musttail`); **non-tail calls** split the def into
   continuation segments with explicit frames; **parallel fork/join** tasks for parallel lets;
   **`!` lowering** (a task handed to Metal/CUDA when a GPU was probed, else the CPU pool);
   **IO** (`IO~emit`, effect requests).
6. **Dead segment elimination** (2960-2972), **tables** (CIDs, FID arities, fork flags,
   2863-2924), **literal tables and static image** (2985-2988), **segment text** (2926-2935),
   **leak guard** (dies if the word `undefined` appears in the C, 2990-2992), **assembly** into
   the 2,600-line C runtime template (`runtime_c` 3362-6010).

The JS lane (`js_lib`, 3316-3350) shares reachability/erasure but has no ANF or fold/unfold and
uses native encodings (Nat/U32 as numbers, Bool as `true/false`, Strings as JS strings).

## D. What in `comp.ts` affects semantics

A bug in any of these changes printed values (or crashes a correct program): the primitive
template table (the *only* definition of F32 anywhere), the Nat representation (a u64 in C, a
double in JS, **fail-stop above 2^48 − 1**, `NAT_IMM`, `comp.ts:401-403`), literal handling,
erasure, arity raising/eta, partial evaluation, match compilation including compile-time
tables, layout packing/boxing, refcount/dup/drop/borrow/"hot"/free/reuse (memory safety),
arrays (power-of-two blocks, index wrap), closures, fork/join continuation splitting, the IO
driver and effects, and `show_main` formatting.

## E. What affects only performance / code shape

Thread pool and scheduler (`pool_*`, rings, `monk_step`), `SPIN_FAR`, "once" inlining,
allocator size classes, corpus growth, GPU dispatch shape, register ladders, constant hoisting.
*If correct*, these do not change results. Several perf features can still change semantics if
buggy: `flat_of` (a def wrongly deemed flat recurses on the C stack), `emit_unfold` (substitutes
terms), the table heuristic (switches C to JS-computed constants), `WIDE = 247` (layouts), and
resource limits (ring/heap/refcount/array-class caps are fail-stops).

Measured consequence for this project (`bench/runtime/tree-radix`, Apple M4): the benchmark's
`!` call path is ~25% faster than a plain call even on one CPU thread with `--gpu off`
(5.4 s vs 6.6–7.2 s). Our trusted harness therefore calls the entry with `!` on a CPU-only
build, which reproduces the original benchmark's speed for the reference program.

## F. What `bend.lean` formalises today

`bend.lean` is self-contained core Lean (no imports, no Mathlib, no `sorry`/`axiom`/`unsafe`/
`native_decide`/`set_option`), one `namespace BendCore`: ~900 lines of specification
(`bend.lean:188-1094`) and 1,111 theorems. It **checks** on Lean v4.33.0-rc1 (19 s; an independent
`leanchecker --fresh` replay passes; axioms of the five claims: `propext`, `Classical.choice`,
`Quot.sound`). It does **not** check on v4.27.0 (`List.sum_append` missing from core).

For any `Book.Ok` book it proves: Church–Rosser for strong reduction; subject reduction along
live weak steps of closed live terms; progress; **weak** normalisation; and consistency (no
closed live inhabitant of an emptied family). A scratch witness book shows the claims are not
vacuous. It has **no erasure-correctness theorem** and says **nothing about `comp.ts`, the C/JS
runtimes or the hardware** (`comp.ts` appears only in three comments).

## G. Mismatches between `bend.ts` and `bend.lean`

The model's safety argument needs "model accepts ⊇ bend.ts accepts"; these break it:

* **M1 `+`-lambda promotion** (`bend.ts:3413-3431`): bend.ts lets a `+x` binder be reused under a
  single-use arrow at a Data type; the Lean `lam` rule has no such case. Reproduced: bend.ts accepts
  `def dup(x: Nat) -> Pair(Nat, Nat): match x: case +y: (y, y)`, which the model rejects. Base uses
  this 18+ times (e.g. `Char.cmp`).
* **M2 Base carve-out**: Base helpers call their own later-filled laws without any descent check
  (`bend.ts:3233`), e.g. `Word.adc ↔ Word.adc.con` behind `U32.add`. The shipped Base is therefore
  **not `Book.Ok`**, and since `Book.Ok` quantifies over the whole book, the theorems formally cover
  no book that imports Base.
* **M3** 52 unfilled Base laws (F32, atomics, handle types) and ~40 foreign IO defs are callable live;
  `cli_report` never flags Base ones.
* **M4** two `@unsafe` Base defs (`Array.fork`, `Array.join`).
* **M5** templates (`~`) and **M6** literals are not modelled.
* **M7** conversion is a different algorithm (call-by-need WHNF with sharing and stuck-self-call
  refolding) with no refinement proof; bend.ts compares residual constructor sets ignoring order,
  the model compares lists.
* **M8** `Book.Ok` assumes case-tree/telescope shape premises that bend.ts leaves to the parser.

## H. `@unsafe`, foreign imports, IO, JS/C imports and open laws

* **`@unsafe def` / `def f?`**: skips termination, may call later defs and open laws, may
  duplicate non-Data values; accepted by `book_valid`; reported (not rejected) by the CLI;
  compiled like safe code (`comp.ts` never reads `u`).
* **Foreign defs** (`import "./x.c"` / `"./x.js"` in a def body): result type must be Base `IO(…)`;
  the C source is **pasted verbatim** into the binary (`effect_srcs`, 2824-2837) and registers an
  effect handler from an `__attribute__((constructor))`; the JS source is run with `require`.
  Nothing sandboxes them.
* **IO** is a CPS monad over `IO.OP = Emit | Halt` (`base.bend:114-150`); every primitive effect is a
  Base foreign def with `.c` and `.js` twins (`effs/`). The C `main` consumes `--threads`,
  `--gpu`, `--gpu-build`, `--bend-help` and passes the rest to `IO.args`.
* **JS importing Bend**: `main.ts` registers a loader so `import X from "./x.bend"` works under
  Bun/Node, exporting every non-IO def.
* **Hub imports** `import 0x<hash>/…` **fetch from the network** and write to disk during
  `book_load`: a verifier must never load untrusted Bend with network access (ours rejects every
  import except `import Base` before loading, and runs Node without network).
* **Open laws** (`law` without a filling `def`) are `Def{v: null}` and are counted in `book.hols`;
  only `main.ts` turns that into an error.

## Divergences between the checker and compiled code (reproduced)

| behaviour | checker (`term_snf`) | C | JS |
|---|---|---|---|
| Nat ≥ 2^48 | exact | fail-stop | fail-stop |
| `?TODO` in live code (direct `compile_book`) | counted | compiles to `0` | `null` |
| `Chr{55296}` | accepted | accepted | fail-stop |
| unbalanced `ANode` arrays | evaluates | fail-stop | fail-stop |
| F32 | stuck laws | IEEE binary32, libm | `Math.*` + `fround` |
| evaluation order of a pure `main` | lazy | strict | strict |

For hole-free, `@unsafe`-free, F32-free, array-free programs whose Nats stay below 2^48 — the
fragment VerifiedIR v1 accepts — the observed behaviour of both compiled lanes is "the checker's
value, or a fail-stop". Of the repo's 787 C-lane-eligible tests, 660 matched their expected output
and 0 failed (126 were skipped because their `main` cannot be printed).

## Consequences for the BendVerify design

1. **Trust nothing in the candidate's copy of Bend.** The verifier uses its own pinned copies of
   `bend.ts`/`comp.ts`/`base.bend` (the reference tree is pinned file-by-file in
   `trusted/spec/reference_tree.json`) and, in competition v1, forbids changes outside
   `bend2/opt/`.
2. **Check what `main.ts` checks, and more**: `book.hols == 0`, no `@unsafe`, no foreign defs, no
   imports other than `import Base`, no network while loading.
3. **Extract from what is compiled**: the extractor translates `Def.e` (what `comp.ts` compiles)
   *and* `Def.v` (what the checker's semantics is stated on) and refuses the definition if the two
   translations differ.
4. **Primitives are specified, not extracted**: VerifiedIR's `Prim.eval` gives each U32/Nat Base
   operation the meaning of its Base definition (div/mod by zero, shifts ≥ 32, truncating
   subtraction). That correspondence is a documented trust assumption, spot-checked by
   `tests/integration/test_prim_conformance.py` against the reference checker and compiled C.
5. **Model Nat as unbounded, and document the runtime cap**: compiled Nat values ≥ 2^48 fail-stop.
   Equivalence of IR programs does not cover that behaviour (a Claim-C gap).
6. **There is no IR inside `comp.ts` to verify**, so the optimisation boundary is placed *before*
   `comp.ts`: untrusted optimisation happens on VerifiedIR, the result is lowered back to Bend
   and compiled by the unmodified reference compiler.
