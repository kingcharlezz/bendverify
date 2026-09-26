The worked example lives in `../../examples/valid-optimization/`:

* `overlay/bend2/opt/optimize.mjs` — an optimizer (library-rule inlining + generic first-order
  deforestation) that writes a certificate chain;
* `proof-src/Submission/TreeRadix.lean` — the Lean proof of the deforestation step;
* `prove.json` — which proof modules to compile.

`../../examples/materialize` turns it into a full candidate (pinned Bend tree + overlay).
