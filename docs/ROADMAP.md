# Roadmap

Competition v1 certifies **Claim B** on a small fragment. The ordering below moves the trusted
boundary downward (towards the executable) and outward (towards the whole Bend repository) one
link at a time; each step replaces a trusted component by either a proven pass or per-artifact
translation validation.

## Near term (extends v1 without changing its trust story)

1. **Bigger fragment.** v1 already covers Base `String`/`Char`, string literals, one monomorphic
   pair instance and `Bool` connectives (which unlocked the `lexer` benchmark and its 3.3×
   fold/build fusion). Next: monomorphic instances of *all* parameterised Base datatypes
   (`List<U32>`, `Maybe<…>`, several pair instances, using the elaborated `Def.e` type annotations to
   pick instances), arrays as a functional model with index wrap-around (`Array.get/set/swap`), and
   F32 only if an IEEE-754 binary32 model is added to the spec and the compiled templates are
   validated against it.
2. **More library rules, with generic proofs**: let-substitution, dead-let elimination for values,
   function specialisation (appending functions needs a simulation lemma for program extension),
   dead-function elimination (needs renumbering), and a *verified generic deforestation rule*, so
   that the demo's lemma step becomes a rule step.
3. **Competitor-defined rules**: a step kind whose proof is a pair (checker function, soundness
   theorem) exported by the competitor, re-checked by the kernel once, then applied at many
   locations by kernel evaluation — "discover a new optimisation once, reuse it everywhere".
4. **Counterexample certificates for rejected candidates**: evaluate P and Q in the Lean kernel
   on small inputs and prove `¬ Equiv` (useful feedback; never needed for soundness).
5. **Stronger isolation**: gVisor/Firecracker for the optimizer, a Linux benchmark host with
   pinned cores and frequency, more repetitions and robust statistics.

## Moving the boundary towards the executable (Claim C)

```
Bend semantics ≡ Bend core ≡ VerifiedIR ≡ lowered IR ≡ generated C ≡ machine execution
      (1)             (2)          (3)          (4)            (5)
```

1. **Bend semantics ≡ Bend core.** Close the `bend.ts`/`bend.lean` mismatches (M1–M8 in
   `BEND_AUDIT.md`), make Base `Book.Ok`, and prove that the elaborated `Def.e` refines `Def.v`.
2. **Bend core ≡ VerifiedIR.** Replace the trusted extractor by a verified one: define the
   extraction as a Lean function on (a Lean model of) checked terms and prove it
   semantics-preserving, or validate each extraction by checking in Lean that the IR evaluates like
   the core term (translation validation).
3. **VerifiedIR ≡ lowered IR.** Already validated per artifact (re-extraction round trip);
   upgrade to a proven printer/parser pair once (1)–(2) exist.
4. **Lowered IR ≡ C.** The big one. `comp.ts` has no internal IR (`BEND_AUDIT.md` §C). Options:
   (a) make `comp.ts` emit a small intermediate "machine IR" (segments, frames, layouts,
   refcounts) plus a certificate, and validate each compilation against VerifiedIR in Lean;
   (b) a verified lowering of VerifiedIR to a C subset with a formal semantics (e.g. via an
   existing verified-C toolchain) for the non-parallel core, then add the runtime.
5. **C ≡ machine.** Use a verified C compiler for the generated code where possible and treat
   the parallel runtime (work-stealing rings, atomics, GPU lanes) as a separately specified,
   separately proven component; hardware remains trusted.

Only when every arrow is a proven pass or a per-artifact checked certificate may the phrase
"fully verified Bend compiler" be used.

## Opening the whole repository to competitors

The long-term model:

```
immutable Bend specification (outside the candidate repository)
        │
        ▼
candidate's entire Bend repo (bend.ts, comp.ts, base.bend, main.ts, …)
        │
        ▼
proof / certificates that the candidate implements the specification
```

Prerequisites, in order: (i) a fixed external mathematical specification of Bend (not `bend.ts`),
(ii) the certificate-producing compiler interface of step 4 above, so a candidate `comp.ts` can be
arbitrary code that must emit checkable certificates, (iii) certificate checking for the front
end (a candidate `bend.ts` must justify its elaboration). Until then competition versions keep
`allowed_modifications = ["bend2/opt/"]` and use the pinned reference front end and compiler.
